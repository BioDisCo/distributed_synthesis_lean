/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Formalizations.Lemma.LemFiniteLetterLTL
import Mathlib.Computability.Primrec.List

/-! # A concrete list encoding of LTL and primitive-recursive table expansion

Atoms are left tokens. Right tokens are the eight non-atomic LTL
constructors, in postfix order. Decoding is a total stack evaluation:
underflow resets the stack to false, and a final stack of size other than
one denotes false. The generated codes never underflow. No source-program
interpreter is present.
-/
namespace DistributedSynthesis.EncodedFiniteLTL
variable {A : Type*}
abbrev Token (A : Type*) := A ⊕ Fin 8
abbrev Code (A : Type*) := List (Token A)
def evalToken : Token A → List (LTL A) → List (LTL A)
  | .inl a,s => .atom a :: s
  | .inr k,s => match k.val,s with
    | 0,_ => .verum :: s
    | 1,_ => .falsum :: s
    | 2,p::s => .neg p :: s
    | 3,q::p::s => .conj p q :: s
    | 4,q::p::s => .disj p q :: s
    | 5,p::s => .next p :: s
    | 6,q::p::s => .until p q :: s
    | 7,q::p::s => .release p q :: s
    | _,_ => [.falsum]
def eval (c : Code A) (s : List (LTL A)) := c.foldl (fun s t ↦ evalToken t s) s
def decode (c : Code A) : LTL A := match eval c [] with
  | [p] => p
  | _ => .falsum
def Represents (c : Code A) (p : LTL A) : Prop := ∀ s, eval c s = p::s
theorem Represents.decode {c : Code A} {p : LTL A} (h : Represents c p) : EncodedFiniteLTL.decode c = p := by
  unfold EncodedFiniteLTL.decode
  rw [h []]
def atom (a : A) : Code A := [.inl a]
def truth : Code A := [.inr 0]
def falsity : Code A := [.inr 1]
def unary (k : Fin 8) (p : Code A) : Code A := p ++ [.inr k]
def binary (k : Fin 8) (p q : Code A) : Code A := p ++ q ++ [.inr k]
def always (p : Code A) : Code A := binary 7 falsity p
theorem atom_rep (a : A) : Represents (atom a) (.atom a) := fun _ ↦ rfl
theorem truth_rep : Represents (truth : Code A) .verum := fun _ ↦ rfl
theorem falsity_rep : Represents (falsity : Code A) .falsum := fun _ ↦ rfl
theorem unary_rep (k : Fin 8) (f : LTL A → LTL A)
    (hk : ∀ p s, evalToken (.inr k) (p::s) = f p::s)
    {c : Code A} {p : LTL A} (h : Represents c p) : Represents (unary k c) (f p) := by
  intro s
  simp only [unary,eval,List.foldl_append,List.foldl_cons,List.foldl_nil]
  exact (congrArg (evalToken (.inr k)) (h s)).trans (hk p s)
theorem binary_rep (k : Fin 8) (f : LTL A → LTL A → LTL A)
    (hk : ∀ p q s, evalToken (.inr k) (q::p::s) = f p q::s)
    {c d : Code A} {p q : LTL A} (hc : Represents c p) (hd : Represents d q) :
    Represents (binary k c d) (f p q) := by
  intro s
  change eval (c ++ d ++ [.inr k]) s = _
  simp only [eval,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change evalToken (.inr k) (eval d (eval c s)) = _
  rw [hc s,hd (p::s),hk]
theorem next_rep {c : Code A} {p : LTL A} (h : Represents c p) :
    Represents (unary 5 c) (.next p) := unary_rep 5 .next (fun _ _ ↦ rfl) h
theorem conj_rep {c d : Code A} {p q : LTL A} (hc : Represents c p) (hd : Represents d q) :
    Represents (binary 3 c d) (.conj p q) := binary_rep 3 .conj (fun _ _ _ ↦ rfl) hc hd
theorem disj_rep {c d : Code A} {p q : LTL A} (hc : Represents c p) (hd : Represents d q) :
    Represents (binary 4 c d) (.disj p q) := binary_rep 4 .disj (fun _ _ _ ↦ rfl) hc hd
theorem release_rep {c d : Code A} {p q : LTL A} (hc : Represents c p) (hd : Represents d q) :
    Represents (binary 7 c d) (.release p q) := binary_rep 7 .release (fun _ _ _ ↦ rfl) hc hd
theorem always_rep {c : Code A} {p : LTL A} (h : Represents c p) :
    Represents (always c) p.always := release_rep falsity_rep h

def disjunction (xs : List (Code A)) : Code A := xs.foldr (binary 4) falsity
def test (xs : List A) : Code A := disjunction (xs.map atom)
def relation (xs : List (A × A)) : Code A :=
  disjunction (xs.map fun ab ↦ binary 3 (atom ab.1) (unary 5 (atom ab.2)))
theorem disjunction_rep (xs : List (Code A)) (ps : List (LTL A))
    (h : List.Forall₂ Represents xs ps) :
    Represents (disjunction xs) (FiniteLetterLTL.disjunction ps) := by
  induction h with
  | nil => exact falsity_rep
  | cons h _ ih => exact disj_rep h ih
theorem test_rep (xs : List A) :
    Represents (test xs) (FiniteLetterLTL.disjunction (xs.map LTL.atom)) := by
  apply disjunction_rep
  induction xs with
  | nil => exact .nil
  | cons a xs ih => exact .cons (atom_rep a) ih
theorem relation_rep (xs : List (A × A)) :
    Represents (relation xs)
      (FiniteLetterLTL.disjunction (xs.map fun ab ↦ .conj (.atom ab.1) (.next (.atom ab.2)))) := by
  apply disjunction_rep
  induction xs with
  | nil => exact .nil
  | cons ab xs ih => exact .cons (conj_rep (atom_rep ab.1) (next_rep (atom_rep ab.2))) ih
theorem satisfies_test (w : OmegaWord A) (xs : List A) :
    LTL.Satisfies FiniteLetterLTL.interp w (decode (test xs)) ↔ w 0 ∈ xs := by
  rw [(test_rep xs).decode]
  simp [FiniteLetterLTL.satisfies_disjunction,LTL.Satisfies,FiniteLetterLTL.interp]
theorem satisfies_relation (w : OmegaWord A) (xs : List (A × A)) :
    LTL.Satisfies FiniteLetterLTL.interp w (decode (relation xs)) ↔ (w 0,w 1) ∈ xs := by
  rw [(relation_rep xs).decode]
  simp [FiniteLetterLTL.satisfies_disjunction,LTL.Satisfies,FiniteLetterLTL.interp,
    OmegaWord.drop,Prod.exists]

section Computability
variable [Primcodable A]
theorem atom_primrec : Primrec (atom : A → Code A) :=
  Primrec.list_cons.comp Primrec.sumInl (Primrec.const [])
theorem unary_primrec (k : Fin 8) : Primrec (unary k : Code A → Code A) :=
  Primrec.list_append.comp Primrec.id (Primrec.const ([.inr k] : Code A))
theorem binary_primrec (k : Fin 8) : Primrec₂ (binary k : Code A → Code A → Code A) :=
  Primrec.list_append.comp (Primrec.list_append.comp Primrec.fst Primrec.snd)
    (Primrec.const ([.inr k] : Code A))
theorem always_primrec : Primrec (always : Code A → Code A) :=
  (binary_primrec 7).comp (Primrec.const falsity) Primrec.id
theorem disjunction_primrec : Primrec (disjunction : List (Code A) → Code A) := by
  exact Primrec.list_foldr Primrec.id (Primrec.const falsity)
    ((binary_primrec 4).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
theorem test_primrec : Primrec (test : List A → Code A) :=
  disjunction_primrec.comp (Primrec.list_map Primrec.id (atom_primrec.comp Primrec.snd).to₂)
theorem relation_primrec : Primrec (relation : List (A × A) → Code A) :=
  disjunction_primrec.comp (Primrec.list_map Primrec.id
    ((binary_primrec 3).comp (atom_primrec.comp (Primrec.fst.comp Primrec.snd))
      ((unary_primrec 5).comp (atom_primrec.comp (Primrec.snd.comp Primrec.snd)))).to₂)
end Computability

abbrev Tables (A : Type*) :=
  List A × List A × List (A × A) × List A × List A × List A × List A
def assemble (t : Tables A) : Code A :=
  binary 3 (test t.1) (binary 3 (always (test t.2.1))
    (binary 3 (always (relation t.2.2.1))
      (binary 3 (binary 7 (test t.2.2.2.1) (test t.2.2.2.2.1))
        (binary 7 (test t.2.2.2.2.2.1) (test t.2.2.2.2.2.2)))))
def meaning (t : Tables A) : LTL A :=
  .conj (decode (test t.1)) (.conj (decode (test t.2.1)).always
    (.conj (decode (relation t.2.2.1)).always
      (.conj (.release (decode (test t.2.2.2.1)) (decode (test t.2.2.2.2.1)))
        (.release (decode (test t.2.2.2.2.2.1)) (decode (test t.2.2.2.2.2.2))))))
theorem assemble_rep (t : Tables A) : Represents (assemble t) (meaning t) := by
  have ht (xs : List A) : Represents (test xs) (decode (test xs)) := by
    rw [(test_rep xs).decode]; exact test_rep xs
  have hr (xs : List (A × A)) : Represents (relation xs) (decode (relation xs)) := by
    rw [(relation_rep xs).decode]; exact relation_rep xs
  exact conj_rep (ht _) (conj_rep (always_rep (ht _))
    (conj_rep (always_rep (hr _)) (conj_rep (release_rep (ht _) (ht _)) (release_rep (ht _) (ht _)))))
theorem assemble_primrec [Primcodable A] : Primrec (assemble : Tables A → Code A) :=
  (binary_primrec 3).comp (test_primrec.comp Primrec.fst)
    ((binary_primrec 3).comp (always_primrec.comp (test_primrec.comp (Primrec.fst.comp Primrec.snd)))
      ((binary_primrec 3).comp (always_primrec.comp (relation_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
        ((binary_primrec 3).comp
          ((binary_primrec 7).comp
            (test_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
            (test_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
          ((binary_primrec 7).comp
            (test_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
            (test_primrec.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))))))

theorem filter_primrec {X B : Type*} [Primcodable X] [Primcodable B]
    {xs : X → List B} {p : X → B → Bool} (hx : Primrec xs) (hp : Primrec₂ p) :
    Primrec (fun x ↦ (xs x).filter (p x)) := by
  have h := Primrec.listFilterMap hx
    (Primrec.cond hp (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂
  apply h.of_eq
  intro x
  induction xs x with
  | nil => rfl
  | cons b bs ih => cases hb : p x b <;> simp [hb,ih]

end DistributedSynthesis.EncodedFiniteLTL
