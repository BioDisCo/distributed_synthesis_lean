/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Copyright Dominique Larchey-Wendling (LORIA -- CNRS).
Lean adaptation of FRACTRAN.v at revision
11c41e0637f0c5219ad1c4c92d11609b7e072c31. See README.md.
-/
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.StateTransition

/-! # Regular FRACTRAN

A fraction (p,q) applies to x when q divides p*x, not merely when q divides x.
The first applicable fraction is selected. Denominator zero is excluded by
`Regular`; the executable semantics skips it outside this supported domain.
-/
namespace DistributedSynthesis.CounterMachine.FRACTRAN

abbrev Fraction := Nat × Nat
abbrev Program := List Fraction
def Regular (P : Program) : Prop := ∀ f ∈ P, f.2 ≠ 0
abbrev HaltingInput := Program × Nat

def applyFraction (f : Fraction) (x : Nat) : Option Nat :=
  if f.2 ≠ 0 ∧ f.2 ∣ f.1*x then some (f.1*x/f.2) else none

def step : Program → Nat → Option Nat
  | [],_ => none
  | f :: P,x => (applyFraction f x).or (step P x)

def Halts (d : HaltingInput) : Prop := (StateTransition.eval (step d.1) d.2).Dom
def RegularHalts (d : HaltingInput) : Prop := Regular d.1 ∧ Halts d

theorem applyFraction_eq_some {f : Fraction} {x y : Nat} (hq : f.2 ≠ 0)
    (h : f.2*y = f.1*x) : applyFraction f x = some y := by
  have hd : f.2 ∣ f.1*x := ⟨y,h.symm⟩
  simp [applyFraction,hq,hd,← h]

theorem applyFraction_eq_none {f : Fraction} {x : Nat} (h : ¬ f.2 ∣ f.1*x) :
    applyFraction f x = none := by simp [applyFraction,h]

theorem step_append (P Q : Program) (x : Nat) :
    step (P ++ Q) x = (step P x).or (step Q x) := by
  induction P with
  | nil => rfl
  | cons f P ih => simp only [List.cons_append,step,ih,Option.or_assoc]

theorem step_eq_none_iff (P : Program) (x : Nat) :
    step P x = none ↔ ∀ f ∈ P, applyFraction f x = none := by
  induction P with
  | nil => simp [step]
  | cons f P ih => simp [step,ih]

theorem regular_append (P Q : Program) : Regular (P ++ Q) ↔ Regular P ∧ Regular Q := by
  simp [Regular,List.mem_append,or_imp,forall_and]

/-- The upstream relational step rule, including its ordered failure premise. -/
inductive RelStep : Program → Nat → Nat → Prop
  | head {p q x y : Nat} {P : Program} : q*y = p*x → RelStep ((p,q) :: P) x y
  | tail {p q x y : Nat} {P : Program} :
      (¬ ∃ z, q*z = p*x) → RelStep P x y → RelStep ((p,q) :: P) x y

theorem applyFraction_eq_some_iff {f : Fraction} {x y : Nat} (hq : f.2 ≠ 0) :
    applyFraction f x = some y ↔ f.2*y = f.1*x := by
  constructor
  · intro h
    unfold applyFraction at h
    split_ifs at h with hd
    · have he : f.1*x/f.2 = y := Option.some.inj h
      rw [← he]
      exact Nat.mul_div_cancel' hd.2
  · exact applyFraction_eq_some hq

theorem step_eq_some_iff {P : Program} (hP : Regular P) (x y : Nat) :
    step P x = some y ↔ RelStep P x y := by
  induction P with
  | nil => constructor <;> intro h <;> cases h
  | cons f P ih =>
    obtain ⟨p,q⟩ := f
    have hq : q ≠ 0 := hP (p,q) (by simp)
    have ht : Regular P := fun f hf => hP f (by simp [hf])
    by_cases hd : q ∣ p*x
    · have he : q*(p*x/q) = p*x := Nat.mul_div_cancel' hd
      have ha : applyFraction (p,q) x = some (p*x/q) := applyFraction_eq_some hq he
      constructor
      · intro h
        have hy : p*x/q = y := by simpa [step,ha] using h
        exact RelStep.head (by simpa [hy] using he)
      · intro h
        cases h with
        | head h => simp [step,applyFraction_eq_some (f := (p,q)) hq h]
        | tail hn _ => exact False.elim (hn ⟨_,he⟩)
    · have hn : ¬ ∃ z, q*z = p*x := by
        rintro ⟨z,hz⟩
        exact hd ⟨z,hz.symm⟩
      have ha : applyFraction (p,q) x = none := applyFraction_eq_none hd
      constructor
      · intro h
        exact RelStep.tail hn ((ih ht).mp (by simpa [step,ha] using h))
      · intro h
        cases h with
        | head he => exact False.elim (hn ⟨y,he⟩)
        | tail _ hs => simpa [step,ha] using (ih ht).mpr hs

theorem halts_iff_relStep {P : Program} (hP : Regular P) (x : Nat) :
    Halts (P,x) ↔ ∃ y, Relation.ReflTransGen (RelStep P) x y ∧ ¬ ∃ z, RelStep P y z := by
  have he : (fun a b => b ∈ step P a) = RelStep P := by
    funext a b
    exact propext (by simpa using step_eq_some_iff hP a b)
  simp only [Halts,Part.dom_iff_mem,StateTransition.mem_eval,StateTransition.Reaches,he]
  congr! 2
  simp only [← step_eq_some_iff hP,Option.eq_none_iff_forall_not_mem,Option.mem_def,not_exists]

def runSteps (P : Program) : Nat → Nat → Option Nat
  | 0,x => some x
  | t+1,x => (step P x).bind (runSteps P t)

end DistributedSynthesis.CounterMachine.FRACTRAN
