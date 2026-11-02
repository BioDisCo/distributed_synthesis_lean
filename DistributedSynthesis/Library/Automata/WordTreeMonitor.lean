/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmDeterministicBlockAutomaton

/-! # A deterministic word automaton as a branchwise tree monitor -/
namespace DistributedSynthesis.WordTreeMonitor
variable {Branch Label : Type*} [Fintype Branch] [Fintype Label]
  (D : DetParityAutomaton (Label × Branch))

def monitor : DeterministicBlockMonitor Branch Label where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := D.State
  stateFinite := D.stateFinite
  initial := D.initial
  step q label branch := D.step q (label,branch)
  priority := D.priority
def word (tree : LabeledTree Branch Label) (branch : Nat → Branch) : OmegaWord (Label × Branch) :=
  fun t => (tree (branchNode branch t),branch t)

theorem control_eq_run (tree : LabeledTree Branch Label) (branch : Nat → Branch) (t : Nat) :
    (monitor D).control tree (branchNode branch t) = D.run (word tree branch) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (monitor D).control tree (branchNode branch t ++ [branch t]) = _
    rw [(monitor D).control_append,ih]
    rfl

theorem winning_iff (tree : LabeledTree Branch Label) :
    (monitor D).WinningTree tree ↔ ∀ branch, D.Accepts (word tree branch) := by
  change (∀ branch, NatSeqMinEvenParity (fun t =>
    (monitor D).priority ((monitor D).control tree (branchNode branch t)))) ↔
      ∀ branch, NatSeqMinEvenParity (fun t => D.priority (D.run (word tree branch) t))
  simp only [control_eq_run]
  rfl
end DistributedSynthesis.WordTreeMonitor
