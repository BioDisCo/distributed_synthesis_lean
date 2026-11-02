/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedCheckerLabels
import DistributedSynthesis.Library.Distributed.EncodedThreadStream
import DistributedSynthesis.Library.Distributed.ThreadWordMonitor

/-! # Ordinary journal checkers on a common numeric state carrier

The boundary changes only the initial state. In particular, a checker started
at a new boundary uses exactly the same numbering as every later step.
-/
namespace DistributedSynthesis.EncodedOrdinaryCheckerAssembly
open EncodedRoundObjectives EncodedOrdinaryThreads DetParityAutomaton
variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d
local instance : DecidableEq (A).State := inferInstanceAs (DecidableEq (Fin (stateCount d)))
local instance (b : (A).State) : DecidableEq ((A).leftBlockMonitor b).State :=
  inferInstanceAs (DecidableEq (Fin (stateCount d) × Fin (stateCount d)))
local instance (b : (A).State) : DecidableEq ((A).rightBlockMonitor b).State :=
  inferInstanceAs (DecidableEq (Fin (stateCount d) × Fin (stateCount d)))

def config (boundary : Nat) : EncodedThreadStream.Config :=
  (stateCount d * stateCount d, initial d boundary, priorities d)
def leftEdges (a : EncodedCheckerLabels.LeftLabel d × Fin (inputTwo d)) :=
  edges (d,false,EncodedCheckerLabels.left d a.1) a.2.val
def rightEdges (a : EncodedCheckerLabels.RightLabel d × Fin (inputOne d)) :=
  edges (d,true,EncodedCheckerLabels.right d a.1) a.2.val
def leftDPA (b : (A).State) := EncodedThreadStream.automaton (config d b.val) (leftEdges d)
def rightDPA (b : (A).State) := EncodedThreadStream.automaton (config d b.val) (rightEdges d)

theorem left_edges_correct (b : (A).State) (q t : (A).State × (A).State)
    (a : EncodedCheckerLabels.LeftLabel d × Fin (inputTwo d)) :
    ((pairNumber d q).val,(pairNumber d t).val) ∈ leftEdges d a ↔
      ∃ i : Fin (inputOne d), t = ((A).leftBlockMonitor b).step q
        (narrowedRecord ((A).leftBlockMonitor b) a.1 q (i,a.2)) := by
  simpa only [leftEdges,pairNumber_val,EncodedCheckerLabels.left_decode] using
    left_edges d b (EncodedCheckerLabels.left d a.1) q t a.2
theorem right_edges_correct (b : (A).State) (q t : (A).State × (A).State)
    (a : EncodedCheckerLabels.RightLabel d × Fin (inputOne d)) :
    ((pairNumber d q).val,(pairNumber d t).val) ∈ rightEdges d a ↔
      ∃ j : Fin (inputTwo d), t = ((A).rightBlockMonitor b).step q
        (narrowedRecord ((A).rightBlockMonitor b) a.1 q (j,a.2)) := by
  simpa only [rightEdges,pairNumber_val,EncodedCheckerLabels.right_decode] using
    right_edges d b (EncodedCheckerLabels.right d a.1) q t a.2

theorem left_config (b : (A).State) :
    (Fintype.card ((A).leftBlockMonitor b).State,
      (pairNumber d ((A).leftBlockMonitor b).initial).val, priorities d) = config d b.val := by
  change (Fintype.card ((A).State × (A).State),_,_) = _
  rw [pairNumber_val,Fintype.card_prod,stateCount_card]
  rfl
theorem right_config (b : (A).State) :
    (Fintype.card ((A).rightBlockMonitor b).State,
      (pairNumber d ((A).rightBlockMonitor b).initial).val, priorities d) = config d b.val := by
  change (Fintype.card ((A).State × (A).State),_,_) = _
  rw [pairNumber_val,Fintype.card_prod,stateCount_card]
  rfl

theorem left_accepts_iff (b : (A).State)
    (word : OmegaWord (BlockRecordMonitor.ThreadLetter ((A).leftBlockMonitor b))) :
    (leftDPA d b).Accepts word ↔ ∀ q, ((A).leftBlockMonitor b).IsThread word q →
      NatSeqMinEvenParity (fun t => ((A).leftBlockMonitor b).priority (q t)) := by
  have h := EncodedThreadStream.accepts_iff ((A).leftBlockMonitor b) (pairNumber d) (priorities d)
    (priorities_getD d) (left_priorities d b) (leftEdges d) id
    (fun q a t => left_edges_correct d b q t a) word
  exact (Iff.of_eq (congrArg (fun c =>
    (EncodedThreadStream.automaton c (leftEdges d)).Accepts word) (left_config d b))).symm.trans h
theorem right_accepts_iff (b : (A).State)
    (word : OmegaWord (BlockRecordMonitor.ThreadLetter ((A).rightBlockMonitor b))) :
    (rightDPA d b).Accepts word ↔ ∀ q, ((A).rightBlockMonitor b).IsThread word q →
      NatSeqMinEvenParity (fun t => ((A).rightBlockMonitor b).priority (q t)) := by
  have h := EncodedThreadStream.accepts_iff ((A).rightBlockMonitor b) (pairNumber d) (priorities d)
    (priorities_getD d) (right_priorities d b) (rightEdges d) id
    (fun q a t => right_edges_correct d b q t a) word
  exact (Iff.of_eq (congrArg (fun c =>
    (EncodedThreadStream.automaton c (rightEdges d)).Accepts word) (right_config d b))).symm.trans h

def left : LeftThreadChecker A where
  monitor := WordTreeMonitor.monitor (leftDPA d (A).initial)
  start b := (leftDPA d b).initial
  winning_iff b tree := ThreadWordMonitor.winning_iff ((A).leftBlockMonitor b)
    (leftDPA d b) (left_accepts_iff d b) tree
def right : RightThreadChecker A where
  monitor := WordTreeMonitor.monitor (rightDPA d (A).initial)
  start b := (rightDPA d b).initial
  winning_iff b tree := ThreadWordMonitor.winning_iff ((A).rightBlockMonitor b)
    (rightDPA d b) (right_accepts_iff d b) tree

end DistributedSynthesis.EncodedOrdinaryCheckerAssembly
