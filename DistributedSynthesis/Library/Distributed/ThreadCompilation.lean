/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.ThreadComputable
import DistributedSynthesis.Library.Automata.PitermanComputable

/-! # Certified executable universal-thread compilation

The finite searches receive concrete decision procedures. The correctness
proof identifies the result with the canonical universal-thread monitor;
classical reasoning is confined to proofs, not the compiler's data.
-/

namespace DistributedSynthesis.ThreadCompilation

variable {RIn SIn ROut SOut : Type*}
variable (M : BlockRecordMonitor RIn SIn ROut SOut)
variable [Fintype RIn] [DecidableEq M.State]

/-- Determinize the bad-thread automaton and complement its parity condition. -/
def dpa : DetParityAutomaton (BlockRecordMonitor.ThreadLetter M) :=
  ((NondetBuchiAutomaton.Piterman.Computable.compilation
    (ThreadComputable.buchi M) (ThreadComputable.stepDecidable M)
    (ThreadComputable.acceptingDecidable M)).dpa).shiftPriority 1

theorem dpa_eq : dpa M = M.threadDPA := by
  change (NondetBuchiAutomaton.Piterman.Computable.automatonData
    (ThreadComputable.buchi M) (ThreadComputable.stepDecidable M)
    (ThreadComputable.acceptingDecidable M)).shiftPriority 1 = _
  rw [NondetBuchiAutomaton.Piterman.Computable.automatonData_eq]
  simp only [ThreadComputable.buchi_eq]
  unfold BlockRecordMonitor.threadDPA
    NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler
    NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompilation
    NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompilationOfCompleteness
  exact congrArg (fun d : DecidableEq M.threadBuchi.State =>
    (@NondetBuchiAutomaton.Piterman.CompactTreeData.automaton _ M.threadBuchi d).shiftPriority 1)
    (Subsingleton.elim _ _)

theorem accepts_iff (word : OmegaWord (BlockRecordMonitor.ThreadLetter M)) :
    (dpa M).Accepts word ↔ ∀ q : Nat → M.State,
      M.IsThread word q → NatSeqMinEvenParity (fun n => M.priority (q n)) := by
  rw [dpa_eq]
  exact M.threadDPA_accepts_iff word

variable [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

/-- Exhaustive enumeration of the two finite response tables. -/
@[reducible] def labelFintype : Fintype (NarrowedBlockLabel RIn SIn ROut SOut M.State) :=
  inferInstance

/-- Package the executable word automaton as a sender-branching tree monitor. -/
def monitor : DeterministicBlockMonitor SIn
    (NarrowedBlockLabel RIn SIn ROut SOut M.State) where
  branchFinite := inferInstance
  alphabetFinite := labelFintype M
  State := (dpa M).State
  stateFinite := (dpa M).stateFinite
  initial := (dpa M).initial
  step := fun state label branch => (dpa M).step state (label, branch)
  priority := (dpa M).priority

@[reducible] def stateDecidableEq : DecidableEq (monitor M).State :=
  NondetBuchiAutomaton.Piterman.Computable.stateDecidableEq (ThreadComputable.buchi M)

theorem monitor_eq : monitor M = M.threadBlockMonitor := by
  unfold monitor
  rw [dpa_eq]
  unfold BlockRecordMonitor.threadBlockMonitor
  have hfin : labelFintype M = (M.threadBlockMonitor).alphabetFinite :=
    Subsingleton.elim _ _
  rw [hfin]
  rfl

theorem winningTree_iff
    (tree : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State)) :
    (monitor M).WinningTree tree ↔ NarrowedAllThreadsWin M tree := by
  rw [monitor_eq]
  exact M.threadBlockMonitor_winningTree_iff tree

end DistributedSynthesis.ThreadCompilation
