/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedJournalStateCoding
import DistributedSynthesis.Library.Distributed.EncodedJournalMachineSteps

/-! # Exact outer journal transition simulation -/
namespace DistributedSynthesis.EncodedJournalTransitionsCorrect
open EncodedRoundObjectives EncodedOrdinaryThreads EncodedChainThreads EncodedJournalMachines
  EncodedJournalSubsets EncodedJournalStateCoding DetParityAutomaton
variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d
local instance : DecidableEq (A).State := inferInstanceAs (DecidableEq (Fin (stateCount d)))
local instance : Inhabited (Fin (inputOne d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (inputTwo d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (outputOne d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (outputTwo d)) := ⟨⟨0,Nat.succ_pos _⟩⟩

def branchCode : GlobalJournalBranch A → EncodedJournalTransitions.Branch
  | Sum.inl atom => (0,pairedIndex d atom)
  | Sum.inr (Sum.inl j) => (1,j.val)
  | Sum.inr (Sum.inr i) => (2,i.val)

theorem mem_atomEncode (s : Finset ((A).State × (A).State)) (a : (A).State × (A).State) :
    pairedIndex d a ∈ atomEncode d s ↔ a ∈ s := FiniteSetCodes.mem_encode (atomEquiv d) s a

theorem left_initial (b : (A).State) : ((EncodedOrdinaryCheckerAssembly.left d).start b).val = ordinaryInitial d b.val := rfl
theorem right_initial (b : (A).State) : ((EncodedOrdinaryCheckerAssembly.right d).start b).val = ordinaryInitial d b.val := rfl
theorem chain_initial (T : Finset (ChainThread A)) :
    ((EncodedChainCheckerAssembly.checker d).start T).2.val = chainInitial d := rfl
theorem chain_start_set (T : Finset (ChainThread A)) :
    ((EncodedChainCheckerAssembly.checker d).start T).1 = T := rfl
theorem chain_step_set (q : (EncodedChainCheckerAssembly.checker d).monitor.State)
    (l : EncodedCheckerLabels.ChainLabel d) (b : Fin (inputTwo d) ⊕ Fin (inputOne d)) :
    ((EncodedChainCheckerAssembly.checker d).monitor.step q l b).1 = q.1 := rfl
theorem chain_left_step (q : (EncodedChainCheckerAssembly.checker d).monitor.State)
    (c : EncodedJournalLabels.Code) (b : Fin (inputTwo d) ⊕ Fin (inputOne d)) :
    ((EncodedChainCheckerAssembly.checker d).monitor.step q (Sum.inl (label d c).revLeft) b).2.val =
      chainNext (EncodedChainMonitor.context d (chainEncode d q.1) true c b,q.2.val) :=
  EncodedJournalMachineSteps.chain_step d q c true b
theorem chain_right_step (q : (EncodedChainCheckerAssembly.checker d).monitor.State)
    (c : EncodedJournalLabels.Code) (b : Fin (inputTwo d) ⊕ Fin (inputOne d)) :
    ((EncodedChainCheckerAssembly.checker d).monitor.step q (Sum.inr (label d c).revRight) b).2.val =
      chainNext (EncodedChainMonitor.context d (chainEncode d q.1) false c b,q.2.val) :=
  EncodedJournalMachineSteps.chain_step d q c false b

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem step_correct (q : Semantic d) (c : EncodedJournalLabels.Code) (b : GlobalJournalBranch A) :
    EncodedJournalTransitions.step (d,encode d q,c,branchCode d b) =
      encode d ((EncodedJournalAssembly.compile d).step q (label d c) b) := by
  change _ = encode d (globalJournalStep A (EncodedOrdinaryCheckerAssembly.left d)
    (EncodedOrdinaryCheckerAssembly.right d) (EncodedChainCheckerAssembly.checker d) q (label d c) b)
  rcases q with a | ⟨q,T⟩ | ⟨q,T⟩ | ⟨q,T⟩ | ⟨q,T⟩ | u
  all_goals try cases u
  all_goals rcases b with a' | j | i
  all_goals simp only [EncodedJournalTransitions.step,EncodedJournalTransitions.closeSet,
    EncodedJournalTransitions.openNext,EncodedJournalTransitions.ordinaryNextState,
    EncodedJournalTransitions.reverseNext,EncodedJournalTransitions.chainNextState,
    EncodedJournalTransitions.handoff,EncodedJournalTransitions.ordinaryContext,
    EncodedJournalTransitions.chainContext,EncodedJournalTransitions.chainMonitorContext,
    EncodedJournalTransitions.objective,EncodedJournalTransitions.state,EncodedJournalTransitions.label,
    EncodedJournalTransitions.branch,EncodedJournalTransitions.side,EncodedJournalTransitions.mode,
    EncodedJournalTransitions.oldSide,branchCode,encode,globalJournalStep,
    Nat.reduceLT,Nat.reduceLeDiff,Nat.reduceEqDiff,Nat.reduceAdd,if_true,if_false,decide_true,decide_false]
  all_goals try simp only [EncodedJournalSubsets.both_correct,EncodedJournalSubsets.left_open,EncodedJournalSubsets.right_open,
    EncodedJournalSubsets.left_step,EncodedJournalSubsets.right_step,
    EncodedJournalSubsets.left_close,EncodedJournalSubsets.right_close,
    EncodedJournalSubsets.left_reverse,EncodedJournalSubsets.right_reverse,
    EncodedJournalSubsets.revLeft_close,EncodedJournalSubsets.revRight_close,
    EncodedJournalSubsets.revLeft_step,EncodedJournalSubsets.revRight_step,
    EncodedJournalSubsets.revLeft_reverse,EncodedJournalSubsets.revRight_reverse,
    mem_atomEncode,encode,EncodedJournalMachineSteps.left_step,EncodedJournalMachineSteps.right_step,
    left_initial,right_initial,chain_initial,chain_start_set,chain_step_set,chain_left_step,chain_right_step,
    pairedIndex_div]
  all_goals first | rfl | (split_ifs <;> first | contradiction | rfl)

theorem initial_correct : EncodedJournalTransitions.initial d = encode d (EncodedJournalAssembly.compile d).initial := rfl
end DistributedSynthesis.EncodedJournalTransitionsCorrect
