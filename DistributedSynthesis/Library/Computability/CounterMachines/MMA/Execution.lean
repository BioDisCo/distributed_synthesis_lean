/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Executable support for the MMA model adapted from Dominique Larchey-Wendling.
The placement and Mathlib transition API are additions of this port.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MMA
import Mathlib.Computability.StateTransition

namespace DistributedSynthesis.CounterMachine.MMA

def inc {n : Nat} (r : Fin n) : Instr n := (r,none)
def dec {n : Nat} (r : Fin n) (j : Nat) : Instr n := (r,some j)
def step {n : Nat} (P : Program n) (x : Cfg n) : Option (Cfg n) :=
  (lookup P x.1).map (fun ρ => next ρ x)
abbrev Compute {n : Nat} (P : Program n) := StateTransition.Reaches (step P)
abbrev Progress {n : Nat} (P : Program n) := StateTransition.Reaches₁ (step P)

theorem step_iff {n : Nat} (P : Program n) (x y : Cfg n) : y ∈ step P x ↔ Step P x y := by
  simp [step,Step,Option.map_eq_some_iff,eq_comm]
theorem compute_iff {n : Nat} (P : Program n) (x y : Cfg n) : Compute P x y ↔ Reaches P x y := by
  have he : (fun a b => b ∈ step P a) = Step P := by funext a b; exact propext (step_iff P a b)
  simp only [Compute,StateTransition.Reaches,he,Reaches]
theorem terminates_iff_eval {n : Nat} (P : Program n) (x : Cfg n) :
    Terminates P x ↔ (StateTransition.eval (step P) x).Dom := by
  simp only [Terminates,Part.dom_iff_mem,StateTransition.mem_eval,compute_iff,stops_iff,
    step,Option.map_eq_none_iff]

def runSteps {n : Nat} (P : Program n) : Nat → Cfg n → Option (Cfg n)
  | 0,x => some x
  | t+1,x => (step P x).bind (runSteps P t)
theorem runSteps_compute {n : Nat} (P : Program n) (t : Nat) (x y : Cfg n)
    (h : runSteps P t x = some y) : Compute P x y := by
  induction t generalizing x with
  | zero => cases h; exact .refl
  | succ t ih =>
    cases hs : step P x with
    | none => simp [runSteps,hs] at h
    | some z => exact Relation.ReflTransGen.head (by simp [hs]) (ih z (by simpa [runSteps,hs] using h))
theorem runSteps_progress {n : Nat} (P : Program n) (t : Nat) (x y : Cfg n)
    (ht : 0 < t) (h : runSteps P t x = some y) : Progress P x y := by
  cases t with
  | zero => cases ht
  | succ t =>
    cases hs : step P x with
    | none => simp [runSteps,hs] at h
    | some z => exact Relation.TransGen.head' (by simp [hs]) (runSteps_compute P t z y (by simpa [runSteps,hs] using h))

def Placed {n : Nat} (P : Program n) (i : Nat) (code : Program n) : Prop :=
  ∀ j, j < code.length → lookup P (i+j) = code[j]?
theorem placed_self {n : Nat} (P : Program n) : Placed P 1 P := by
  intro j hj; simp [lookup]
theorem Placed.left {n : Nat} {P A B : Program n} {i : Nat}
    (h : Placed P i (A ++ B)) : Placed P i A := by
  intro j hj
  simpa [List.getElem?_append_left hj] using h j (by simp only [List.length_append]; omega)
theorem Placed.right {n : Nat} {P A B : Program n} {i : Nat}
    (h : Placed P i (A ++ B)) : Placed P (i+A.length) B := by
  intro j hj
  simpa [Nat.add_assoc,List.getElem?_append_right (show A.length ≤ A.length+j by omega)] using
    h (A.length+j) (by simp only [List.length_append]; omega)
theorem Placed.head {n : Nat} {P A : Program n} {ρ : Instr n} {i : Nat}
    (h : Placed P i (ρ :: A)) : lookup P i = some ρ := by simpa using h 0 (by simp)
theorem Placed.tail {n : Nat} {P A : Program n} {ρ : Instr n} {i : Nat}
    (h : Placed P i (ρ :: A)) : Placed P (i+1) A := by
  intro j hj
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h (j+1) (by simp; omega)

end DistributedSynthesis.CounterMachine.MMA
