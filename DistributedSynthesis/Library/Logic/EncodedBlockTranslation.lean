/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.BlockTranslation
import DistributedSynthesis.Library.Logic.FiniteEncoding

/-! # Primitive-recursive block translation of postfix LTL

The stack interpreter mirrors the total source decoder, including underflow
and surplus stack entries. Its output is ordinary postfix LTL, not a new
semantic instruction or a source-program interpreter.
-/
namespace DistributedSynthesis.EncodedBlockTranslation
open EncodedFiniteLTL
variable {A B : Type*}

def nextN (n : Nat) (p : Code B) : Code B := p ++ List.replicate n (.inr 5)

theorem nextN_rep (n : Nat) {p : Code B} {φ : LTL B} (hp : Represents p φ) :
    Represents (nextN n p) (LTL.BlockTranslation.nextN n φ) := by
  induction n with
  | zero => simpa [nextN, LTL.BlockTranslation.nextN] using hp
  | succ n ih =>
    have he : nextN (n+1) p = unary 5 (nextN n p) := by
      simp [nextN, unary, List.replicate_succ', List.append_assoc]
    rw [he]
    exact next_rep ih

theorem nextN_primrec [Primcodable B] : Primrec₂ (nextN : Nat → Code B → Code B) := by
  have h : Primrec (fun x : Nat × Code B ↦ x.2 ++ (List.range x.1).map (fun _ ↦ .inr 5)) :=
    Primrec.list_append.comp Primrec.snd
      (Primrec.list_map (Primrec.list_range.comp Primrec.fst) (Primrec.const (Sum.inr (5 : Fin 8) : Token B)).to₂)
  exact h.of_eq fun x ↦ by simp [nextN, List.map_const']

def operation (L : Nat) (marker : Code B) (k : Fin 8) (p q : Code B) : Code B :=
  if k = 0 then truth else if k = 1 then falsity else
  if k = 2 then unary 2 q else if k = 3 then binary 3 p q else
  if k = 4 then binary 4 p q else if k = 5 then nextN L q else
  if k = 6 then binary 6 (binary 4 (unary 2 marker) p) (binary 3 marker q) else
    unary 2 (binary 6 (binary 4 (unary 2 marker) (unary 2 p))
      (binary 3 marker (unary 2 q)))

def arity (k : Fin 8) : Nat := if k = 0 ∨ k = 1 then 0 else if k = 2 ∨ k = 5 then 1 else 2

def step (L : Nat) (marker : Code B) (atom : A → Code B)
    (token : Token A) (s : List (Code B)) : List (Code B) :=
  match token with
  | .inl a => atom a :: s
  | .inr k =>
    if s.length < arity k then [falsity]
    else operation L marker k s.tail.headI s.headI :: s.drop (arity k)

def finish (s : List (Code B)) : Code B := if s.length = 1 then s.headI else falsity

def translate (L : Nat) (marker : Code B) (atom : A → Code B) (c : Code A) : Code B :=
  finish (c.foldl (fun s t ↦ step L marker atom t s) [])

private theorem neg_rep {p : Code B} {φ : LTL B} (h : Represents p φ) :
    Represents (unary 2 p) (.neg φ) := unary_rep 2 .neg (fun _ _ ↦ rfl) h
private theorem until_rep {p q : Code B} {φ ψ : LTL B}
    (hp : Represents p φ) (hq : Represents q ψ) :
    Represents (binary 6 p q) (.until φ ψ) := binary_rep 6 .until (fun _ _ _ ↦ rfl) hp hq

theorem step_rep (L : Nat) (m : Code B) (M : LTL B) (hm : Represents m M)
    (a : A → Code B) (f : A → LTL B) (ha : ∀ x, Represents (a x) (f x))
    (token : Token A) (s : List (Code B)) (ps : List (LTL A))
    (hs : List.Forall₂ (fun c φ ↦ Represents c (LTL.BlockTranslation.translate L M f φ)) s ps) :
    List.Forall₂ (fun c φ ↦ Represents c (LTL.BlockTranslation.translate L M f φ))
      (step L m a token s) (evalToken token ps) := by
  cases token with
  | inl x => exact .cons (ha x) hs
  | inr k =>
    fin_cases k <;> cases hs with
    | nil => simp [step, arity, operation, evalToken, LTL.BlockTranslation.translate,
        List.Forall₂, truth_rep, falsity_rep]
    | cons hp hs =>
      cases hs with
      | nil => simp [step, arity, operation, evalToken, LTL.BlockTranslation.translate,
          List.Forall₂, truth_rep, falsity_rep, hp, neg_rep hp, nextN_rep L hp]
      | cons hq hs =>
        simp [step, arity, operation, evalToken, List.length_cons, List.length_nil,
          List.tail_cons, List.headI_cons, List.drop_zero, List.drop_succ_cons,
          LTL.BlockTranslation.translate]
        first
        | exact ⟨truth_rep, hp, hq, hs⟩
        | exact ⟨falsity_rep, hp, hq, hs⟩
        | exact ⟨neg_rep hp, hq, hs⟩
        | exact ⟨conj_rep hq hp, hs⟩
        | exact ⟨disj_rep hq hp, hs⟩
        | exact ⟨nextN_rep L hp, hq, hs⟩
        | exact ⟨until_rep (disj_rep (neg_rep hm) hq) (conj_rep hm hp), hs⟩
        | exact ⟨neg_rep (until_rep (disj_rep (neg_rep hm) (neg_rep hq))
            (conj_rep hm (neg_rep hp))), hs⟩

theorem translate_rep (L : Nat) (m : Code B) (M : LTL B) (hm : Represents m M)
    (a : A → Code B) (f : A → LTL B) (ha : ∀ x, Represents (a x) (f x)) (c : Code A) :
    Represents (translate L m a c) (LTL.BlockTranslation.translate L M f (decode c)) := by
  have fold (c : Code A) (s : List (Code B)) (ps : List (LTL A))
      (hs : List.Forall₂ (fun c φ ↦ Represents c (LTL.BlockTranslation.translate L M f φ)) s ps) :
      List.Forall₂ (fun c φ ↦ Represents c (LTL.BlockTranslation.translate L M f φ))
        (c.foldl (fun s t ↦ step L m a t s) s) (eval c ps) := by
    induction c generalizing s ps with
    | nil => exact hs
    | cons t c ih => exact ih _ _ (step_rep L m M hm a f ha t s ps hs)
  have hf := fold c [] [] .nil
  unfold translate decode
  generalize c.foldl (fun s t ↦ step L m a t s) [] = s at hf ⊢
  generalize eval c [] = ps at hf ⊢
  cases hf with
  | nil => exact falsity_rep
  | cons hp hs =>
    cases hs with
    | nil => exact hp
    | cons hq hs => simpa [finish, LTL.BlockTranslation.translate] using (falsity_rep (A := B))

section Computability
variable {X : Type*} [Primcodable X] [Primcodable A] [Primcodable B]

theorem operation_primrec {l : X → Nat} {m p q : X → Code B} {k : X → Fin 8}
    (hl : Primrec l) (hm : Primrec m) (hk : Primrec k) (hp : Primrec p) (hq : Primrec q) :
    Primrec (fun x ↦ operation (l x) (m x) (k x) (p x) (q x)) := by
  unfold operation
  repeat' first
    | apply Primrec.ite
    | exact Primrec.eq.comp hk (Primrec.const _)
    | exact Primrec.const _
    | exact hl
    | exact hm
    | exact hp
    | exact hq
    | exact nextN_primrec.comp hl hq
    | apply (unary_primrec _).comp
    | apply (binary_primrec _).comp
    | apply Primrec.list_append.comp

theorem step_primrec {l : X → Nat} {m : X → Code B} {a : X → A → Code B}
    {t : X → Token A} {s : X → List (Code B)}
    (hl : Primrec l) (hm : Primrec m) (ha : Primrec₂ a) (ht : Primrec t) (hs : Primrec s) :
    Primrec (fun x ↦ step (l x) (m x) (a x) (t x) (s x)) := by
  unfold step
  refine (Primrec.sumCasesOn (g := fun x b ↦ a x b :: s x)
    (h := fun x k ↦ if (s x).length < arity k then [falsity]
      else operation (l x) (m x) k (s x).tail.headI (s x).headI :: (s x).drop (arity k)) ht ?_ ?_).of_eq ?_
  · exact (Primrec.list_cons.comp ha (hs.comp Primrec.fst)).to₂
  · unfold Primrec₂
    have hk : Primrec (fun x : X × Fin 8 ↦ arity x.2) :=
      (Primrec.dom_finite arity).comp Primrec.snd
    exact Primrec.ite (Primrec.nat_lt.comp (Primrec.list_length.comp (hs.comp Primrec.fst)) hk)
      (Primrec.const [falsity])
      (Primrec.list_cons.comp
        (operation_primrec (hl.comp Primrec.fst) (hm.comp Primrec.fst) Primrec.snd
          (Primrec.list_headI.comp (Primrec.list_tail.comp (hs.comp Primrec.fst)))
          (Primrec.list_headI.comp (hs.comp Primrec.fst)))
        (Primrec.list_drop.comp hk (hs.comp Primrec.fst)))
  · intro x
    cases t x <;> rfl

theorem finish_primrec : Primrec (finish : List (Code B) → Code B) :=
  Primrec.ite (Primrec.eq.comp Primrec.list_length (Primrec.const 1))
    Primrec.list_headI (Primrec.const falsity)

/-- All varying parameters, including block length and atomic substitutions,
are accounted for in the primitive-recursive certificate. -/
theorem translate_primrec {l : X → Nat} {m : X → Code B} {a : X → A → Code B}
    {c : X → Code A} (hl : Primrec l) (hm : Primrec m) (ha : Primrec₂ a) (hc : Primrec c) :
    Primrec (fun x ↦ translate (l x) (m x) (a x) (c x)) := by
  apply finish_primrec.comp
  apply Primrec.list_foldl (h := fun x st ↦ step (l x) (m x) (a x) st.2 st.1) hc (Primrec.const [])
  unfold Primrec₂
  apply step_primrec (hl.comp Primrec.fst) (hm.comp Primrec.fst)
    (t := fun x : X × List (Code B) × Token A ↦ x.2.2)
    (s := fun x ↦ x.2.1) _ (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  exact (ha.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

end Computability
end DistributedSynthesis.EncodedBlockTranslation
