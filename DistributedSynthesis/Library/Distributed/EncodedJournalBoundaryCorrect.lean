/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedJournalBoundary
import DistributedSynthesis.Library.Distributed.EncodedChainThreadsCorrect

/-! # Exact boundary and handoff transition correspondence -/
namespace DistributedSynthesis.EncodedJournalBoundary
open EncodedRoundObjectives EncodedOrdinaryThreads EncodedChainThreads DetParityAutomaton
variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d

theorem advance_correct (update : Bool) (qm : (A).State × (A).State) (a : Letter d) :
    advance (d,update,pairedIndex d qm,EncodedNoDirect.letterCode a) =
      pairedIndex d ((A).step qm.1 a,
        bif update then (A).minPriorityState qm.2 ((A).step qm.1 a) else qm.2) := by
  unfold advance
  dsimp only
  rw [pairedIndex_div,pairedIndex_mod,objectiveStep_correct]
  cases update <;> simp only [Bool.cond_false,Bool.cond_true,Bool.false_eq_true,false_and,
    if_false,true_and,objectivePriority_correct,pairedIndex,minPriorityState]
  split_ifs <;> rfl

theorem closeRound_correct (side : Bool) (c : EncodedJournalLabels.Code)
    (qm : (A).State × (A).State) (i : Fin (inputOne d)) (j : Fin (inputTwo d)) :
    closeRound ((d,side,c),pairedIndex d qm,i.val,j.val) = EncodedNoDirect.letterCode
      (bothRoundRecord (i,j)
        (bif side then (label d c).rightClose qm (j,i) else (label d c).leftNarrowed.2 qm (i,j))
        (bif side then (label d c).rightNarrowed.2 qm (j,i) else (label d c).leftClose qm (i,j))) := by
  rcases qm with ⟨q,m⟩
  cases side <;> simp only [closeRound,field,inputIndex,swappedIndex,Bool.cond_false,Bool.cond_true,
    EncodedNoDirect.letterCode,bothRoundRecord,label,EncodedJournalLabels.left_close,
    EncodedJournalLabels.right_close,GlobalJournalLabel.leftNarrowed,GlobalJournalLabel.rightNarrowed,
    EncodedJournalLabels.left_receiver,EncodedJournalLabels.right_receiver,stateNumber_val,stateCount_card,
    pairedIndex,EncodedOrdinaryThreads.read] <;> rfl

theorem reverseRound_correct (side : Bool) (c : EncodedJournalLabels.Code)
    (qm : (A).State × (A).State) (i : Fin (inputOne d)) (j : Fin (inputTwo d)) :
    reverseRound ((d,side,c),pairedIndex d qm,i.val,j.val) = EncodedNoDirect.letterCode
      (bif side then leftRoundRecord (i,j) ((label d c).rightClose qm (j,i)) ((label d c).rightRev qm j)
        else rightRoundRecord (j,i) ((label d c).leftRev qm i) ((label d c).leftClose qm (i,j))) := by
  rcases qm with ⟨q,m⟩
  cases side <;> simp only [reverseRound,field,inputIndex,swappedIndex,Bool.cond_false,Bool.cond_true,
    EncodedNoDirect.letterCode,leftRoundRecord,rightRoundRecord,label,EncodedJournalLabels.left_close,
    EncodedJournalLabels.right_close,EncodedJournalLabels.left_reverse,EncodedJournalLabels.right_reverse,
    stateNumber_val,stateCount_card,pairedIndex,EncodedOrdinaryThreads.read] <;> rfl

theorem bothRound_correct (side : Bool) (c : EncodedJournalLabels.Code)
    (qm : (A).State × (A).State) (i : Fin (inputOne d)) (j : Fin (inputTwo d)) :
    bothRound ((d,side,c),pairedIndex d qm,i.val,j.val) = EncodedNoDirect.letterCode
      (bothRoundRecord (i,j) ((label d c).leftNarrowed.2 qm (i,j)) ((label d c).rightNarrowed.2 qm (j,i))) := by
  rcases qm with ⟨q,m⟩
  simp only [bothRound,field,inputIndex,swappedIndex,EncodedNoDirect.letterCode,bothRoundRecord,label,
    GlobalJournalLabel.leftNarrowed,GlobalJournalLabel.rightNarrowed,EncodedJournalLabels.left_receiver,
    EncodedJournalLabels.right_receiver,stateNumber_val,stateCount_card,pairedIndex,EncodedOrdinaryThreads.read]
  rfl

theorem chainCloseRound_correct (mode : Bool) (c : EncodedJournalLabels.Code)
    (th : ChainThread A) (i : Fin (inputOne d)) (j : Fin (inputTwo d)) :
    chainCloseRound ((d,mode,c),chainIndex d th,i.val,j.val) = EncodedNoDirect.letterCode
      (bothRoundRecord (i,j)
        (bif mode then (label d c).revLeft.oneRecv th (i,j) else (label d c).revRight.oneRecv th (i,j))
        (bif mode then (label d c).revLeft.twoRecv th (i,j) else (label d c).revRight.twoRecv th (i,j))) := by
  cases mode <;> simp only [chainCloseRound,field,inputIndex,Bool.cond_false,Bool.cond_true,
    EncodedNoDirect.letterCode,bothRoundRecord,label,EncodedJournalLabels.revLeft_oneRecv,
    EncodedJournalLabels.revLeft_twoRecv,EncodedJournalLabels.revRight_oneRecv,EncodedJournalLabels.revRight_twoRecv,
    label_chainCode,EncodedOrdinaryThreads.read] <;> rfl

theorem close_correct (side : Bool) (c : EncodedJournalLabels.Code)
    (qm : (A).State × (A).State) (i : Fin (inputOne d)) (j : Fin (inputTwo d)) :
    close ((d,side,c),pairedIndex d qm,i.val,j.val) = pairedIndex d
      (bif side then rightThreadClose qm (label d c).rightNarrowed (label d c).rightClose j i
        else leftThreadClose qm (label d c).leftNarrowed (label d c).leftClose i j) := by
  unfold close
  rw [closeRound_correct]
  rw [advance_correct]
  cases side <;> rfl

theorem reverse_correct (side : Bool) (c : EncodedJournalLabels.Code)
    (qm : (A).State × (A).State) (i : Fin (inputOne d)) (j : Fin (inputTwo d)) :
    reverse ((d,side,c),pairedIndex d qm,i.val,j.val) = chainIndex d
      (bif side then rightThreadReverse qm (label d c).rightClose (label d c).rightRev j i
        else leftThreadReverse qm (label d c).leftClose (label d c).leftRev i j) := by
  unfold reverse
  rw [reverseRound_correct]
  rw [advance_correct]
  cases side <;> rfl

theorem both_correct (side : Bool) (c : EncodedJournalLabels.Code)
    (qm : (A).State × (A).State) (i : Fin (inputOne d)) (j : Fin (inputTwo d)) :
    both ((d,side,c),pairedIndex d qm,i.val,j.val) = pairedIndex d
      (bothThreadAtom qm (label d c).leftNarrowed (label d c).rightNarrowed i j) := by
  unfold both resetMove
  dsimp only
  rw [pairedIndex_div]
  change advance (d,false,pairedIndex d (qm.1,qm.1),
    bothRound ((d,side,c),pairedIndex d (qm.1,qm.1),i.val,j.val)) = _
  rw [bothRound_correct,advance_correct]
  rfl

theorem chainClose_correct (mode : Bool) (c : EncodedJournalLabels.Code)
    (th : ChainThread A) (i : Fin (inputOne d)) (j : Fin (inputTwo d)) :
    chainClose ((d,mode,c),chainIndex d th,i.val,j.val) = pairedIndex d
      (bif mode then revLeftThreadClose A th (label d c).revLeft i j
        else revRightThreadClose A th (label d c).revRight i j) := by
  unfold chainClose
  dsimp only
  rw [show chainIndex d th % (stateCount d * stateCount d) = pairedIndex d th.2 from current_index d th,
    chainCloseRound_correct,advance_correct]
  cases mode <;> rfl
end DistributedSynthesis.EncodedJournalBoundary
