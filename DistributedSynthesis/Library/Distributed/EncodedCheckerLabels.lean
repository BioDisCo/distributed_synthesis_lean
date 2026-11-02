/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedOrdinaryThreadsCorrect

/-! # Embedding checker labels in the complete journal label alphabet
Unused response fields are filled with output zero. The projections actually
read by the selected checker are preserved exactly.
-/
namespace DistributedSynthesis.EncodedCheckerLabels
open EncodedRoundObjectives EncodedOrdinaryThreads DetParityAutomaton
variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d
local instance : Inhabited (Fin (outputOne d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (outputTwo d)) := ⟨⟨0,Nat.succ_pos _⟩⟩

abbrev LeftLabel := NarrowedBlockLabel (Fin (inputOne d)) (Fin (inputTwo d))
  (Fin (outputOne d)) (Fin (outputTwo d)) ((A).State × (A).State)
abbrev RightLabel := NarrowedBlockLabel (Fin (inputTwo d)) (Fin (inputOne d))
  (Fin (outputTwo d)) (Fin (outputOne d)) ((A).State × (A).State)
abbrev ChainLabel := DetParityAutomaton.ChainLabel (Fin (inputOne d)) (Fin (inputTwo d))
  (Fin (outputOne d)) (Fin (outputTwo d)) ((A).State × (A).State)

def leftLift (l : LeftLabel d) : GlobalJournalLabel A := (l,default,default,default,default,default,default,default)
def rightLift (l : RightLabel d) : GlobalJournalLabel A := (default,default,default,l,default,default,default,default)
def chainLift (l : ChainLabel d) : GlobalJournalLabel A :=
  match l with
  | Sum.inl l => (default,default,default,default,default,default,l,default)
  | Sum.inr l => (default,default,default,default,default,default,default,l)
def chainMode : ChainLabel d → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false
def left (l : LeftLabel d) := EncodedJournalLabels.encode A (stateNumber d) (leftLift d l)
def right (l : RightLabel d) := EncodedJournalLabels.encode A (stateNumber d) (rightLift d l)
def chain (l : ChainLabel d) := EncodedJournalLabels.encode A (stateNumber d) (chainLift d l)

theorem left_decode (l : LeftLabel d) : (label d (left d l)).leftNarrowed = l := by
  simp only [label,left,EncodedJournalLabels.decode_encode,leftLift,GlobalJournalLabel.leftNarrowed]
theorem right_decode (l : RightLabel d) : (label d (right d l)).rightNarrowed = l := by
  simp only [label,right,EncodedJournalLabels.decode_encode,rightLift,GlobalJournalLabel.rightNarrowed]
end DistributedSynthesis.EncodedCheckerLabels
