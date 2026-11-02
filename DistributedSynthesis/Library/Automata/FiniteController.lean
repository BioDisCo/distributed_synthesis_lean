/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.TreeNonemptiness
import DistributedSynthesis.Library.Computability.FiniteOrders

namespace DistributedSynthesis.FiniteController
open DistributedSynthesis
open scoped DistributedSynthesis.FiniteOrders
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {Observation Move : Type} [Fintype Observation] [Fintype Move]
variable [LinearOrder Move]
variable (M : DeterministicBlockMonitor Observation Move) [LinearOrder M.State]

/-- The existing finite-orbit test checks every positional environment
response. Its completeness is the library's parity positionality theorem. -/
def Passes (policy : M.State → Move) : Prop :=
  ∀ directions : M.State → Observation,
    NatSeqMinEvenParity (fun n => M.priority ((TreeNonemptiness.policyStep M policy directions)^[n] M.initial))

instance passesDecidable (policy : M.State → Move) : Decidable (Passes M policy) := by
  letI (directions : M.State → Observation) :=
    FiniteOrbitParity.parityDecidable (TreeNonemptiness.policyStep M policy directions) M.initial M.priority
  unfold Passes
  infer_instance

def policies : Finset (M.State → Move) := Finset.univ.filter (Passes M)

/-- Return a concrete winning table, or none. The order only makes the
finite search deterministic; no winning strategy is input data. -/
def extract : Option (M.State → Move) :=
  if present : (policies M).Nonempty then some ((policies M).min' present) else none

theorem extract_sound (policy : M.State → Move) (found : extract M = some policy) : Passes M policy := by
  unfold extract at found
  split at found
  next present =>
    have eq := Option.some.inj found
    have mem := (policies M).min'_mem present
    rw [eq] at mem
    exact (Finset.mem_filter.mp mem).2
  next absent => simp at found

theorem extract_complete : (∃ policy, extract M = some policy) ↔ ∃ tree, M.WinningTree tree := by
  have equivalence : (policies M).Nonempty ↔ ∃ tree, M.WinningTree tree := by
    rw [Finset.nonempty_iff_ne_empty]
    have policyEq : (policies M ≠ ∅) ↔ ∃ policy, Passes M policy := by simp [policies]
    rw [policyEq]
    unfold Passes
    rw [← TreeNonemptiness.nonempty_iff M]
    exact exists_congr (fun tree => M.acceptsTree_iff_winningTree tree)
  rw [← equivalence]
  unfold extract
  split
  next present => simp only [Option.some.injEq,exists_eq',true_iff]; exact present
  next absent => simp [absent]

def tree (policy : M.State → Move) : LabeledTree Observation Move :=
  fun node => policy (ParityPrescription.stateAt M.initial M.step policy node)

theorem tree_control (policy : M.State → Move) (node : List Observation) :
    M.control (tree M policy) node = ParityPrescription.stateAt M.initial M.step policy node := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node o ih =>
    rw [M.control_append,ParityPrescription.stateAt_append,ih]
    rfl

theorem extracted_tree_wins (policy : M.State → Move) (found : extract M = some policy) :
    M.WinningTree (tree M policy) := by
  have all := (TreeNonemptiness.all_paths_iff M.initial (fun q d => M.step q (policy q) d) M.priority).mpr
    (extract_sound M policy found)
  intro branch
  simp only [tree_control]
  exact all (fun n => ParityPrescription.stateAt M.initial M.step policy (branchNode branch n)) branch rfl
    (fun n => ParityPrescription.stateAt_append M.initial M.step policy (branchNode branch n) (branch n))

end DistributedSynthesis.FiniteController
