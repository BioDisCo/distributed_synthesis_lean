/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemBlindLibraryParitySynthesis
import Mathlib.Tactic.DeriveFintype

/-!
# The finite scaling safety monitor

This is the literal finite DPA in SCALING-COUNTEREXAMPLE.md, not an oracle
for a row or a tree. Its state contains no unbounded counter or coordinate.
The end-to-end distributed realizability and non-finite-realizability
implications are proved in `LemScalingNoFiniteWinner`. The explicit LTL
extension is proved in `LemScalingLTL` and `LemScalingLTLWinner`.
-/

namespace DistributedSynthesis.ScalingSafety

structure Plan where
  weight : Fin 3
  child : Fin 3 → Fin 3
deriving DecidableEq, Fintype

def Plan.value (p : Plan) : Nat := p.weight.val + 2
def Plan.childValue (p : Plan) (d : Fin 3) : Nat := (p.child d).val + 2

structure Label where
  up : Bool
  carry : Fin 4
  left : Plan
  right : Plan
deriving DecidableEq, Fintype

def Label.multiplier (l : Label) : Nat := if l.up then 4 else 2

structure State where
  oneLeft : Bool
  leftBoundary : Bool
  rightBoundary : Bool
  previous : Option Plan
  good : Bool
deriving DecidableEq, Fintype

def digit (oneLeft : Bool) (g : Graph) : Fin 3 :=
  match g with
  | .both => 1
  | .right => if oneLeft then 0 else 2
  | .left => if oneLeft then 2 else 0

def step (s : State) (r : RoundRecord Unit Unit Graph Label Label) : State :=
  let d := digit s.oneLeft r.graph
  let oneLeft := if r.graph = .both then !s.oneLeft else s.oneLeft
  let lb := s.leftBoundary && decide (d = 0)
  let rb := s.rightBoundary && decide (d = 2)
  let l := if oneLeft then r.outputOne else r.outputTwo
  let right := if oneLeft then r.outputTwo else r.outputOne
  let p := l.right
  let valid := l.up = right.up ∧ p = right.left ∧
    p.childValue 0 + p.childValue 1 + p.childValue 2 + l.carry.val =
      l.multiplier * p.value + right.carry.val ∧
    (lb = true → l.carry.val = 0) ∧
    (rb = true → right.carry.val = 0) ∧
    (∀ old, s.previous = some old → p.value = old.childValue d)
  ⟨oneLeft, lb, rb, some p, s.good && decide valid⟩

def objective : DetParityAutomaton (RoundRecord Unit Unit Graph Label Label) where
  State := State
  stateFinite := inferInstance
  initial := ⟨true, true, true, none, true⟩
  step := step
  priority := fun s ↦ if s.good then 0 else 1

theorem step_stays_bad (s : State) (r : RoundRecord Unit Unit Graph Label Label)
    (h : s.good = false) : (step s r).good = false := by
  simp [step, h]

/-- The parity presentation accepts exactly the words with no failed check. -/
theorem accepts_iff_good (word : Nat → RoundRecord Unit Unit Graph Label Label) :
    objective.Accepts word ↔ ∀ n, (objective.run word n).good = true := by
  constructor
  · intro h n
    by_contra hn
    have hf : (objective.run word n).good = false := Bool.eq_false_iff.mpr hn
    have hpersist : ∀ k, (objective.run word (n + k)).good = false := by
      intro k
      induction k with
      | zero => simpa using hf
      | succ k ih =>
        rw [Nat.add_succ, objective.run_succ]
        exact step_stays_bad _ _ ih
    apply not_natSeqMinEvenParity_of_eventually_one _ n _ h
    intro k hk
    have hp := hpersist (k - n)
    rw [Nat.add_sub_of_le hk] at hp
    change (if (objective.run word k).good then 0 else 1) = 1
    simp [hp]
  · intro h
    change NatSeqMinEvenParity (fun n ↦ objective.priority (objective.run word n))
    refine ⟨0, ⟨0, rfl⟩, ?_, fun q _ ↦ Nat.zero_le q⟩
    intro n
    refine ⟨n, Nat.le_refl n, ?_⟩
    change (if (objective.run word n).good then 0 else 1) = 0
    simp [h n]

theorem label_multiplier_cases (l : Label) : l.multiplier = 2 ∨ l.multiplier = 4 := by
  cases h : l.up <;> simp [Label.multiplier, h]

theorem plan_value_bounds (p : Plan) : 2 ≤ p.value ∧ p.value ≤ 4 := by
  have := p.weight.isLt
  simp only [Plan.value]
  omega

theorem child_value_bounds (p : Plan) (d : Fin 3) :
    2 ≤ p.childValue d ∧ p.childValue d ≤ 4 := by
  have := (p.child d).isLt
  simp only [Plan.childValue]
  omega

theorem plan_card : Fintype.card Plan = 81 := by
  let e : Plan ≃ Fin 3 × (Fin 3 → Fin 3) :=
    ⟨fun p ↦ (p.weight,p.child), fun p ↦ ⟨p.1,p.2⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  rw [Fintype.card_congr e]
  norm_num

theorem label_card : Fintype.card Label = 52488 := by
  let e : Label ≃ Bool × Fin 4 × Plan × Plan :=
    ⟨fun l ↦ (l.up,l.carry,l.left,l.right), fun l ↦ ⟨l.1,l.2.1,l.2.2.1,l.2.2.2⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  rw [Fintype.card_congr e]
  norm_num [Fintype.card_prod, plan_card]

theorem state_card : Fintype.card State = 1312 := by
  let e : State ≃ Bool × Bool × Bool × Option Plan × Bool :=
    ⟨fun s ↦ (s.oneLeft,s.leftBoundary,s.rightBoundary,s.previous,s.good),
      fun s ↦ ⟨s.1,s.2.1,s.2.2.1,s.2.2.2.1,s.2.2.2.2⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  rw [Fintype.card_congr e]
  norm_num [Fintype.card_prod, Fintype.card_option, plan_card]

/-- A process can compute its geometric coordinate from its own view alone. -/
def coordinate : {p : Proc} → View Unit Unit p → Nat
  | _, .empty .one => 0
  | _, .empty .two => 1
  | _, .noRecv v _ => 3 * coordinate v
  | _, .recv v _ u _ => coordinate v + 2 * coordinate u

/-- The three children of an edge share their two new internal views.
This is where absence of acknowledgements enters the construction. -/
theorem children_share_views (v : View Unit Unit .one) (u : View Unit Unit .two) :
    (advanceViewsWithEnvironment (v,u) ⟨(),(),.right⟩).2 =
      (advanceViewsWithEnvironment (v,u) ⟨(),(),.both⟩).2 ∧
    (advanceViewsWithEnvironment (v,u) ⟨(),(),.both⟩).1 =
      (advanceViewsWithEnvironment (v,u) ⟨(),(),.left⟩).1 := by
  exact ⟨rfl, rfl⟩

theorem child_coordinates (v : View Unit Unit .one) (u : View Unit Unit .two)
    (j : Nat) (hv : coordinate v = j) (hu : coordinate u = j + 1) :
    (coordinate (advanceViewsWithEnvironment (v,u) ⟨(),(),.right⟩).1,
      coordinate (advanceViewsWithEnvironment (v,u) ⟨(),(),.right⟩).2) = (3*j,3*j+1) ∧
    (coordinate (advanceViewsWithEnvironment (v,u) ⟨(),(),.both⟩).2,
      coordinate (advanceViewsWithEnvironment (v,u) ⟨(),(),.both⟩).1) = (3*j+1,3*j+2) ∧
    (coordinate (advanceViewsWithEnvironment (v,u) ⟨(),(),.left⟩).1,
      coordinate (advanceViewsWithEnvironment (v,u) ⟨(),(),.left⟩).2) = (3*j+2,3*j+3) := by
  change (3 * coordinate v, coordinate u + 2 * coordinate v) = (3*j,3*j+1) ∧
    (coordinate u + 2 * coordinate v, coordinate v + 2 * coordinate u) = (3*j+1,3*j+2) ∧
    (coordinate v + 2 * coordinate u, 3 * coordinate u) = (3*j+2,3*j+3)
  simp only [hv, hu, Prod.mk.injEq]
  ring_nf
  simp

theorem child_coordinates_reverse (v : View Unit Unit .one) (u : View Unit Unit .two)
    (j : Nat) (hv : coordinate v = j + 1) (hu : coordinate u = j) :
    (coordinate (advanceViewsWithEnvironment (v,u) ⟨(),(),.left⟩).2,
      coordinate (advanceViewsWithEnvironment (v,u) ⟨(),(),.left⟩).1) = (3*j,3*j+1) ∧
    (coordinate (advanceViewsWithEnvironment (v,u) ⟨(),(),.both⟩).1,
      coordinate (advanceViewsWithEnvironment (v,u) ⟨(),(),.both⟩).2) = (3*j+1,3*j+2) ∧
    (coordinate (advanceViewsWithEnvironment (v,u) ⟨(),(),.right⟩).2,
      coordinate (advanceViewsWithEnvironment (v,u) ⟨(),(),.right⟩).1) = (3*j+2,3*j+3) := by
  change (3 * coordinate u, coordinate v + 2 * coordinate u) = (3*j,3*j+1) ∧
    (coordinate v + 2 * coordinate u, coordinate u + 2 * coordinate v) = (3*j+1,3*j+2) ∧
    (coordinate u + 2 * coordinate v, 3 * coordinate v) = (3*j+2,3*j+3)
  simp only [hv, hu, Prod.mk.injEq]
  ring_nf
  simp

end DistributedSynthesis.ScalingSafety
