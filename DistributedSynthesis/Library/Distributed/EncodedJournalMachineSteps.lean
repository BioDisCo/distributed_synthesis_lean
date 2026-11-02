/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedJournalMachines
import DistributedSynthesis.Library.Distributed.EncodedJournalAssembly

/-! # Numeric checker steps agree with the assembled journal's steps

The equalities concern the complete ordered edge lists, not only the accepted
languages. Encoding a selected response label therefore leaves every later
deterministic checker state unchanged.
-/
namespace DistributedSynthesis.EncodedJournalMachineSteps
open EncodedRoundObjectives EncodedOrdinaryThreads EncodedChainThreads DetParityAutomaton
variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d
local instance : DecidableEq (A).State := inferInstanceAs (DecidableEq (Fin (stateCount d)))
local instance : Inhabited (Fin (inputOne d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (inputTwo d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (outputOne d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (outputTwo d)) := ⟨⟨0,Nat.succ_pos _⟩⟩

theorem left_edges_congr (c c' : EncodedJournalLabels.Code)
    (h : (label d c).leftNarrowed = (label d c').leftNarrowed) (j : Fin (inputTwo d)) :
    edges (d,false,c) j.val = edges (d,false,c') j.val := by
  unfold edges
  apply List.flatMap_congr
  intro q hq
  apply List.map_congr_left
  intro i hi
  let qm : (A).State × (A).State := finProdFinEquiv.symm ⟨q,List.mem_range.mp hq⟩
  have he : pairedIndex d qm = q := congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨q,List.mem_range.mp hq⟩)
  have hn := left_next d (A).initial c qm ⟨i,List.mem_range.mp hi⟩ j
  have hn' := left_next d (A).initial c' qm ⟨i,List.mem_range.mp hi⟩ j
  rw [he,h] at hn
  rw [he] at hn'
  exact congrArg (fun t => (q,t)) (hn.trans hn'.symm)

theorem right_edges_congr (c c' : EncodedJournalLabels.Code)
    (h : (label d c).rightNarrowed = (label d c').rightNarrowed) (i : Fin (inputOne d)) :
    edges (d,true,c) i.val = edges (d,true,c') i.val := by
  unfold edges
  apply List.flatMap_congr
  intro q hq
  apply List.map_congr_left
  intro j hj
  let qm : (A).State × (A).State := finProdFinEquiv.symm ⟨q,List.mem_range.mp hq⟩
  have he : pairedIndex d qm = q := congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨q,List.mem_range.mp hq⟩)
  have hn := right_next d (A).initial c qm ⟨j,List.mem_range.mp hj⟩ i
  have hn' := right_next d (A).initial c' qm ⟨j,List.mem_range.mp hj⟩ i
  rw [he,h] at hn
  rw [he] at hn'
  exact congrArg (fun t => (q,t)) (hn.trans hn'.symm)

theorem left_edges (c : EncodedJournalLabels.Code) (j : Fin (inputTwo d)) :
    EncodedOrdinaryCheckerAssembly.leftEdges d ((label d c).leftNarrowed,j) = edges (d,false,c) j.val :=
  left_edges_congr d _ c (EncodedCheckerLabels.left_decode d _) j
theorem right_edges (c : EncodedJournalLabels.Code) (i : Fin (inputOne d)) :
    EncodedOrdinaryCheckerAssembly.rightEdges d ((label d c).rightNarrowed,i) = edges (d,true,c) i.val :=
  right_edges_congr d _ c (EncodedCheckerLabels.right_decode d _) i

theorem left_step (q : (EncodedOrdinaryCheckerAssembly.left d).monitor.State)
    (c : EncodedJournalLabels.Code) (j : Fin (inputTwo d)) :
    ((EncodedOrdinaryCheckerAssembly.left d).monitor.step q (label d c).leftNarrowed j).val =
      EncodedJournalMachines.ordinaryNext ((d,false,c),q.val,j.val) := by
  change EncodedThreadStream.next (EncodedJournalMachines.ordinaryConfig d 0,
    EncodedOrdinaryCheckerAssembly.leftEdges d ((label d c).leftNarrowed,j),q.val) = _
  rw [left_edges]
  rfl
theorem right_step (q : (EncodedOrdinaryCheckerAssembly.right d).monitor.State)
    (c : EncodedJournalLabels.Code) (i : Fin (inputOne d)) :
    ((EncodedOrdinaryCheckerAssembly.right d).monitor.step q (label d c).rightNarrowed i).val =
      EncodedJournalMachines.ordinaryNext ((d,true,c),q.val,i.val) := by
  change EncodedThreadStream.next (EncodedJournalMachines.ordinaryConfig d 0,
    EncodedOrdinaryCheckerAssembly.rightEdges d ((label d c).rightNarrowed,i),q.val) = _
  rw [right_edges]
  rfl

theorem chain_edges_congr (T : List Nat) (mode mode' : Bool) (c c' : EncodedJournalLabels.Code)
    (h : semanticLabel d c mode = semanticLabel d c' mode') (b : Fin (inputTwo d) ⊕ Fin (inputOne d)) :
    EncodedChainMonitor.edges (EncodedChainMonitor.context d T mode c b) =
      EncodedChainMonitor.edges (EncodedChainMonitor.context d T mode' c' b) := by
  unfold EncodedChainMonitor.edges
  apply List.flatMap_congr
  intro q hq
  apply List.map_congr_left
  intro r hr
  obtain ⟨hi,hj,hg⟩ := (EncodedChainMonitor.mem_receivers d r).mp hr
  let st := (EncodedChainMonitor.monitorEquiv d).symm ⟨q,List.mem_range.mp hq⟩
  let guess := (chainEquiv d).symm ⟨r.2.2,hg⟩
  have hst : EncodedChainMonitor.stateCode d st = q := by
    rw [← EncodedChainMonitor.monitorEquiv_val]
    exact congrArg Fin.val ((EncodedChainMonitor.monitorEquiv d).apply_symm_apply ⟨q,List.mem_range.mp hq⟩)
  have hguess : chainIndex d guess = r.2.2 := by
    rw [← chainEquiv_val]
    exact congrArg Fin.val ((chainEquiv d).apply_symm_apply ⟨r.2.2,hg⟩)
  have hn := EncodedChainMonitor.step_correct d T mode c b st ⟨r.1,hi⟩ ⟨r.2.1,hj⟩ guess
  have hn' := EncodedChainMonitor.step_correct d T mode' c' b st ⟨r.1,hi⟩ ⟨r.2.1,hj⟩ guess
  rw [hst,hguess,h] at hn
  rw [hst,hguess] at hn'
  exact congrArg (fun t => (q,t)) (hn.trans hn'.symm)

theorem chain_edges (T : Finset (ChainThread A)) (c : EncodedJournalLabels.Code) (mode : Bool)
    (b : Fin (inputTwo d) ⊕ Fin (inputOne d)) :
    EncodedChainCheckerAssembly.baseEdges d T (semanticLabel d c mode,b) =
      EncodedChainMonitor.edges (EncodedChainMonitor.context d (EncodedChainCheckerAssembly.handoff d T) mode c b) :=
  chain_edges_congr d _ _ mode _ c (EncodedChainCheckerAssembly.label_decode d _) b

theorem chain_step (q : (EncodedChainCheckerAssembly.checker d).monitor.State)
    (c : EncodedJournalLabels.Code) (mode : Bool) (b : Fin (inputTwo d) ⊕ Fin (inputOne d)) :
    ((EncodedChainCheckerAssembly.checker d).monitor.step q (semanticLabel d c mode) b).2.val =
      EncodedJournalMachines.chainNext
        (EncodedChainMonitor.context d (EncodedChainCheckerAssembly.handoff d q.1) mode c b,q.2.val) := by
  change EncodedThreadStream.next (EncodedJournalMachines.chainConfig d,
    EncodedChainCheckerAssembly.baseEdges d q.1 (semanticLabel d c mode,b),q.2.val) = _
  rw [chain_edges]
  rfl
end DistributedSynthesis.EncodedJournalMachineSteps
