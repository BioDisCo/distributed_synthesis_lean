/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedChainThreads
import DistributedSynthesis.Library.Distributed.EncodedOrdinaryThreadsCorrect

/-! # Exact numeric correspondence for composed chain threads -/
namespace DistributedSynthesis.EncodedChainThreads
open EncodedRoundObjectives EncodedOrdinaryThreads EncodedNoDirect DetParityAutomaton
variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d

def chainIndex (th : ChainThread A) := pairedIndex d th.2 + atomCount d*pairedIndex d th.1
def chainEquiv : ChainThread A ≃ Fin (chainCount d) :=
  (finProdFinEquiv.prodCongr finProdFinEquiv).trans finProdFinEquiv
theorem chainEquiv_val (th : ChainThread A) : (chainEquiv d th).val = chainIndex d th := rfl
theorem chainIndex_lt (th : ChainThread A) : chainIndex d th < chainCount d := (chainEquiv d th).isLt
theorem atomCount_pos : 0 < atomCount d := Nat.mul_pos (stateCount_pos d) (stateCount_pos d)
theorem entry_index (th : ChainThread A) : entry d (chainIndex d th) = pairedIndex d th.1 := by
  have h : pairedIndex d th.2 < atomCount d := pairedIndex_lt d th.2
  simp only [entry,chainIndex,Nat.add_mul_div_left _ _ (atomCount_pos d),
    Nat.div_eq_of_lt h,zero_add]
theorem current_index (th : ChainThread A) : current d (chainIndex d th) = pairedIndex d th.2 := by
  have h : pairedIndex d th.2 < atomCount d := pairedIndex_lt d th.2
  simp only [current,chainIndex,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt h]
theorem label_atomCode (qm : (A).State × (A).State) :
    EncodedJournalLabels.atomCode A (stateNumber d) qm = pairedIndex d qm := by
  simp only [EncodedJournalLabels.atomCode,stateNumber_val,stateCount_card,pairedIndex]
theorem label_chainCode (th : ChainThread A) :
    EncodedJournalLabels.chainCode A (stateNumber d) th = chainIndex d th := by
  simp only [EncodedJournalLabels.chainCode,label_atomCode,stateCount_card,chainIndex,atomCount]

def semanticRound (c : EncodedJournalLabels.Code) (mode side : Bool) (th : ChainThread A)
    (i : Fin (inputOne d)) (j : Fin (inputTwo d)) : Letter d :=
  bif side then rightRoundRecord (j,i)
    (bif mode then (label d c).revLeft.oneSend th i else (label d c).revRight.oneSend th.1 i)
    (bif mode then (label d c).revLeft.twoRecv th (i,j) else (label d c).revRight.twoRecv th (i,j))
  else leftRoundRecord (i,j)
    (bif mode then (label d c).revLeft.oneRecv th (i,j) else (label d c).revRight.oneRecv th (i,j))
    (bif mode then (label d c).revLeft.twoSend th.1 j else (label d c).revRight.twoSend th j)

theorem roundCode_correct (c : EncodedJournalLabels.Code) (mode side : Bool) (th : ChainThread A)
    (i : Fin (inputOne d)) (j : Fin (inputTwo d)) :
    roundCode ((d,mode,side,c),chainIndex d th,i.val,j.val) =
      letterCode (semanticRound d c mode side th i j) := by
  cases mode <;> cases side <;>
    simp only [roundCode,outOne,outTwo,oneIndex,twoIndex,inputIndex,fieldBase,
      Bool.cond_true,Bool.cond_false,entry_index,semanticRound,label,letterCode,leftRoundRecord,rightRoundRecord,
      graphCode,EncodedJournalLabels.revLeft_oneRecv,EncodedJournalLabels.revLeft_oneSend,
      EncodedJournalLabels.revLeft_twoRecv,EncodedJournalLabels.revLeft_twoSend,
      EncodedJournalLabels.revRight_oneRecv,EncodedJournalLabels.revRight_oneSend,
      EncodedJournalLabels.revRight_twoRecv,EncodedJournalLabels.revRight_twoSend,
      label_atomCode,label_chainCode,EncodedOrdinaryThreads.read]
    <;> rfl

def semanticLabel (c : EncodedJournalLabels.Code) (mode : Bool) :
    ChainLabel (Fin (inputOne d)) (Fin (inputTwo d)) (Fin (outputOne d)) (Fin (outputTwo d)) ((A).State × (A).State) :=
  bif mode then Sum.inl (label d c).revLeft else Sum.inr (label d c).revRight
def semanticBranch (side : Bool) (i : Fin (inputOne d)) (j : Fin (inputTwo d)) :
    Fin (inputTwo d) ⊕ Fin (inputOne d) := bif side then Sum.inr i else Sum.inl j

theorem next_correct (c : EncodedJournalLabels.Code) (mode side : Bool) (th : ChainThread A)
    (i : Fin (inputOne d)) (j : Fin (inputTwo d)) :
    next ((d,mode,side,c),chainIndex d th,i.val,j.val) =
      chainIndex d (chainThreadStep A th (semanticLabel d c mode) (semanticBranch d side i j) (i,j)) := by
  have hq : nextObjective ((d,mode,side,c),chainIndex d th,i.val,j.val) =
      ((A).step th.2.1 (semanticRound d c mode side th i j)).val := by
    unfold nextObjective
    rw [current_index,pairedIndex_div,roundCode_correct,objectiveStep_correct]
  simp only [next,nextAtom,hq,current_index,pairedIndex_mod,objectivePriority_correct,entry_index]
  cases mode <;> cases side <;>
    simp only [semanticRound,semanticLabel,semanticBranch,chainThreadStep,
      revLeftThreadStep,revLeftThreadReverse,revRightThreadStep,revRightThreadReverse,
      chainIndex,pairedIndex,minPriorityState,Bool.cond_true,Bool.cond_false]
    <;> split_ifs <;> first | contradiction | rfl
end DistributedSynthesis.EncodedChainThreads
