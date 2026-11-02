/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.FiniteEncoding

/-! # Verified folds of encoded LTL

The numeric stack evaluator agrees with the structural fold of the existing
total decoder, including underflow recovery and surplus-stack rejection.
-/

namespace DistributedSynthesis.PostfixFold
open EncodedFiniteLTL

structure Algebra (A B : Type*) where
  truth : B
  falsity : B
  atom : A → B
  neg : B → B
  conj : B → B → B
  disj : B → B → B
  next : B → B
  «until» : B → B → B
  «release» : B → B → B

variable {A B : Type*} (alg : Algebra A B)

def formula : LTL A → B
  | .verum => alg.truth
  | .falsum => alg.falsity
  | .atom a => alg.atom a
  | .neg p => alg.neg (formula p)
  | .conj p q => alg.conj (formula p) (formula q)
  | .disj p q => alg.disj (formula p) (formula q)
  | .next p => alg.next (formula p)
  | .until p q => alg.until (formula p) (formula q)
  | .release p q => alg.release (formula p) (formula q)

def arity (k : Fin 8) : Nat := if k = 0 ∨ k = 1 then 0 else if k = 2 ∨ k = 5 then 1 else 2

def operation (k : Fin 8) (p q : B) : B :=
  if k = 0 then alg.truth else if k = 1 then alg.falsity else
  if k = 2 then alg.neg q else if k = 3 then alg.conj p q else
  if k = 4 then alg.disj p q else if k = 5 then alg.next q else
  if k = 6 then alg.until p q else alg.release p q

def step (t : Token A) (s : List B) : List B :=
  match t with
  | .inl a => alg.atom a :: s
  | .inr k => if s.length < arity k then [alg.falsity]
      else operation alg k (s.tail.headD alg.falsity) (s.headD alg.falsity) :: s.drop (arity k)

def finish (s : List B) : B := if s.length = 1 then s.headD alg.falsity else alg.falsity

def run (c : Code A) : B := finish alg (c.foldl (fun s t => step alg t s) [])

theorem step_map (t : Token A) (s : List (LTL A)) :
    step alg t (s.map (formula alg)) = (evalToken t s).map (formula alg) := by
  cases t with
  | inl a => rfl
  | inr k =>
    fin_cases k <;> cases s with
    | nil => simp [step, arity, operation, evalToken, formula]
    | cons p s =>
      cases s <;> simp [step, arity, operation, evalToken, formula]

theorem run_correct (c : Code A) : run alg c = formula alg (decode c) := by
  have h (c : Code A) (s : List (LTL A)) :
      c.foldl (fun s t => step alg t s) (s.map (formula alg)) =
        (eval c s).map (formula alg) := by
    induction c generalizing s with
    | nil => rfl
    | cons t c ih => simpa only [List.foldl_cons, step_map, eval] using ih (evalToken t s)
  unfold run
  rw [show ([] : List B) = ([] : List (LTL A)).map (formula alg) from rfl, h]
  unfold decode
  generalize eval c [] = s
  cases s with
  | nil => rfl
  | cons p s => cases s <;> simp [finish, formula]

section Computability
variable [Primcodable A] [Primcodable B]

structure Effective : Prop where
  atom : Primrec alg.atom
  neg : Primrec alg.neg
  conj : Primrec₂ alg.conj
  disj : Primrec₂ alg.disj
  next : Primrec alg.next
  «until» : Primrec₂ alg.until
  «release» : Primrec₂ alg.release

theorem operation_primrec (he : Effective alg) {X : Type*} [Primcodable X]
    {k : X → Fin 8} {p q : X → B}
    (hk : Primrec k) (hp : Primrec p) (hq : Primrec q) :
    Primrec (fun x => operation alg (k x) (p x) (q x)) := by
  unfold operation
  repeat' first
    | apply Primrec.ite
    | exact Primrec.eq.comp hk (Primrec.const _)
    | exact Primrec.const _
    | exact he.neg.comp hq
    | exact he.next.comp hq
    | exact he.conj.comp hp hq
    | exact he.disj.comp hp hq
    | exact he.until.comp hp hq
    | exact he.release.comp hp hq

theorem headD_primrec (d : B) : Primrec (fun s : List B => s.headD d) :=
  (Primrec.option_getD.comp Primrec.list_head? (Primrec.const d)).of_eq
    (fun s => by cases s <;> rfl)

theorem step_primrec (he : Effective alg) : Primrec₂ (step alg) := by
  unfold step
  refine (Primrec.sumCasesOn
    (g := fun x a => alg.atom a :: x.2)
    (h := fun x k => if x.2.length < arity k then [alg.falsity] else
      operation alg k (x.2.tail.headD alg.falsity) (x.2.headD alg.falsity) :: x.2.drop (arity k))
    Primrec.fst ?_ ?_).of_eq ?_
  · exact (Primrec.list_cons.comp (he.atom.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)).to₂
  · have hk : Primrec (fun x : (Token A × List B) × Fin 8 => arity x.2) :=
      (Primrec.dom_finite arity).comp Primrec.snd
    exact (Primrec.ite
      (Primrec.nat_lt.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)) hk)
      (Primrec.const [alg.falsity])
      (Primrec.list_cons.comp
        (operation_primrec alg he Primrec.snd
          ((headD_primrec alg.falsity).comp (Primrec.list_tail.comp (Primrec.snd.comp Primrec.fst)))
          ((headD_primrec alg.falsity).comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.list_drop.comp hk (Primrec.snd.comp Primrec.fst)))).to₂
  · intro x
    cases x.1 <;> rfl

omit [Primcodable A] in
theorem finish_primrec : Primrec (finish alg) :=
  Primrec.ite (Primrec.eq.comp Primrec.list_length (Primrec.const 1))
    (headD_primrec alg.falsity) (Primrec.const alg.falsity)

theorem run_primrec (he : Effective alg) : Primrec (run alg) := by
  apply (finish_primrec alg).comp
  exact Primrec.list_foldl Primrec.id (Primrec.const [])
    ((step_primrec alg he).comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)).to₂

end Computability

section Families
variable {X : Type*} [Primcodable X] [Primcodable A] [Primcodable B]
variable (family : X → Algebra A B)

/-- Uniform effectiveness, including the input-dependent constants. -/
structure EffectiveFamily : Prop where
  truth : Primrec (fun x => (family x).truth)
  falsity : Primrec (fun x => (family x).falsity)
  atom : Primrec₂ (fun x a => (family x).atom a)
  neg : Primrec₂ (fun x p => (family x).neg p)
  conj : Primrec (fun x : X × B × B => (family x.1).conj x.2.1 x.2.2)
  disj : Primrec (fun x : X × B × B => (family x.1).disj x.2.1 x.2.2)
  next : Primrec₂ (fun x p => (family x).next p)
  «until» : Primrec (fun x : X × B × B => (family x.1).until x.2.1 x.2.2)
  «release» : Primrec (fun x : X × B × B => (family x.1).release x.2.1 x.2.2)

theorem family_operation_primrec (he : EffectiveFamily family)
    {Y : Type*} [Primcodable Y] {x : Y → X} {k : Y → Fin 8} {p q : Y → B}
    (hx : Primrec x) (hk : Primrec k) (hp : Primrec p) (hq : Primrec q) :
    Primrec (fun y => operation (family (x y)) (k y) (p y) (q y)) := by
  unfold operation
  repeat' first
    | apply Primrec.ite
    | exact Primrec.eq.comp hk (Primrec.const _)
    | exact he.truth.comp hx
    | exact he.falsity.comp hx
    | exact he.neg.comp hx hq
    | exact he.next.comp hx hq
    | exact he.conj.comp (hx.pair (hp.pair hq))
    | exact he.disj.comp (hx.pair (hp.pair hq))
    | exact he.until.comp (hx.pair (hp.pair hq))
    | exact he.release.comp (hx.pair (hp.pair hq))

theorem family_step_primrec (he : EffectiveFamily family) :
    Primrec (fun x : X × Token A × List B => step (family x.1) x.2.1 x.2.2) := by
  have hd : Primrec (fun x : B × List B => x.2.headD x.1) :=
    (Primrec.option_getD.comp (Primrec.list_head?.comp Primrec.snd) Primrec.fst).of_eq
      (fun x => by cases x.2 <;> rfl)
  let getX : (X × Token A × List B) × Fin 8 → X := fun x => x.1.1
  let getS : (X × Token A × List B) × Fin 8 → List B := fun x => x.1.2.2
  have hx : Primrec getX := Primrec.fst.comp Primrec.fst
  have hs : Primrec getS := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec (fun x : (X × Token A × List B) × Fin 8 => arity x.2) :=
    (Primrec.dom_finite arity).comp Primrec.snd
  unfold step
  refine (Primrec.sumCasesOn
    (g := fun x a => (family x.1).atom a :: x.2.2)
    (h := fun x k => if x.2.2.length < arity k then [(family x.1).falsity] else
      operation (family x.1) k (x.2.2.tail.headD (family x.1).falsity)
        (x.2.2.headD (family x.1).falsity) :: x.2.2.drop (arity k))
    (Primrec.fst.comp Primrec.snd) ?_ ?_).of_eq ?_
  · exact (Primrec.list_cons.comp
      (he.atom.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂
  · exact (Primrec.ite (Primrec.nat_lt.comp (Primrec.list_length.comp hs) hk)
      (Primrec.list_cons.comp (he.falsity.comp hx) (Primrec.const []))
      (Primrec.list_cons.comp
        (family_operation_primrec family he hx Primrec.snd
          (hd.comp ((he.falsity.comp hx).pair (Primrec.list_tail.comp hs)))
          (hd.comp ((he.falsity.comp hx).pair hs)))
        (Primrec.list_drop.comp hk hs))).to₂
  · intro x
    cases x.2.1 <;> rfl

/-- The algebra parameter varies with the encoded input, not just the formula. -/
theorem run_family_primrec (he : EffectiveFamily family) :
    Primrec₂ (fun x c => run (family x) c) := by
  have hf : Primrec (fun x : X × List B => finish (family x.1) x.2) := by
    unfold finish
    exact Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 1))
      ((Primrec.option_getD.comp (Primrec.list_head?.comp Primrec.snd)
        (he.falsity.comp Primrec.fst)).of_eq (fun x => by cases x.2 <;> rfl))
      (he.falsity.comp Primrec.fst)
  have hfold : Primrec (fun x : X × Code A =>
      x.2.foldl (fun s t => step (family x.1) t s) []) :=
    Primrec.list_foldl Primrec.snd (Primrec.const [])
      ((family_step_primrec family he).comp
        ((Primrec.fst.comp Primrec.fst).pair
          ((Primrec.snd.comp Primrec.snd).pair (Primrec.fst.comp Primrec.snd)))).to₂
  exact hf.comp (Primrec.fst.pair hfold)

end Families
end DistributedSynthesis.PostfixFold
