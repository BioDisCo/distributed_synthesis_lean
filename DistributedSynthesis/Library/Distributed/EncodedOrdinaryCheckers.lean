/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedOrdinaryCompiler
import DistributedSynthesis.Library.Distributed.EncodedThreadCompiler

/-! # Complete numeric ordinary deterministic thread checkers -/
namespace DistributedSynthesis.EncodedOrdinaryCheckers
set_option maxHeartbeats 800000
open EncodedRoundObjectives EncodedOrdinaryThreads EncodedOrdinaryCompiler DetParityAutomaton
def compile (x : Input) := EncodedThreadCompiler.compile (threadInput x)
theorem compile_primrec : Primrec compile := EncodedThreadCompiler.compile_primrec.comp threadInput_primrec

@[irreducible] def rowLetter (x : Input) (a : Fin (baseRows x).length) : EncodedJournalLabels.Code × Nat :=
  (alphabet x)[a.val]'(by simpa only [baseRows,List.length_map] using a.isLt)
theorem sender_lt (x : Input) (a : Fin (baseRows x).length) :
    (rowLetter x a).2 < senderCount (x.1,x.2.1,[]) := by
  apply ((mem_alphabet x _).mp ?_).2
  unfold rowLetter
  exact List.getElem_mem _
theorem row_lookup (x : Input) (a : Fin (baseRows x).length) :
    (baseRows x)[a.val]?.getD [] = edges (x.1,x.2.1,(rowLetter x a).1) (rowLetter x a).2 := by
  unfold rowLetter
  rw [List.getElem?_eq_getElem a.isLt,Option.getD_some]
  unfold baseRows
  exact List.getElem_map _

variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d
local instance (b : (A).State) : DecidableEq ((A).leftBlockMonitor b).State :=
  inferInstanceAs (DecidableEq (Fin (stateCount d) × Fin (stateCount d)))
local instance (b : (A).State) : DecidableEq ((A).rightBlockMonitor b).State :=
  inferInstanceAs (DecidableEq (Fin (stateCount d) × Fin (stateCount d)))

def leftLetter (b : (A).State) (a : Fin (baseRows (d,false,b.val)).length) :
    BlockRecordMonitor.ThreadLetter ((A).leftBlockMonitor b) :=
  ((label d (rowLetter (d,false,b.val) a).1).leftNarrowed,
    ⟨(rowLetter (d,false,b.val) a).2,sender_lt (d,false,b.val) a⟩)
def rightLetter (b : (A).State) (a : Fin (baseRows (d,true,b.val)).length) :
    BlockRecordMonitor.ThreadLetter ((A).rightBlockMonitor b) :=
  ((label d (rowLetter (d,true,b.val) a).1).rightNarrowed,
    ⟨(rowLetter (d,true,b.val) a).2,sender_lt (d,true,b.val) a⟩)

theorem left_sourceData (b : (A).State) :
    EncodedThreadCompiler.sourceData ((A).leftBlockMonitor b) (pairNumber d)
      (priorities d) (baseRows (d,false,b.val)) = threadInput (d,false,b.val) := by
  unfold EncodedThreadCompiler.sourceData threadInput
  change (Fintype.card ((A).State × (A).State),_,_,_) = _
  rw [Fintype.card_prod,stateCount_card]
  rfl
theorem right_sourceData (b : (A).State) :
    EncodedThreadCompiler.sourceData ((A).rightBlockMonitor b) (pairNumber d)
      (priorities d) (baseRows (d,true,b.val)) = threadInput (d,true,b.val) := by
  unfold EncodedThreadCompiler.sourceData threadInput
  change (Fintype.card ((A).State × (A).State),_,_,_) = _
  rw [Fintype.card_prod,stateCount_card]
  rfl

theorem left_row (b : (A).State) (q t : (A).State × (A).State)
    (a : Fin (baseRows (d,false,b.val)).length) :
    ((pairNumber d q).val,(pairNumber d t).val) ∈ (baseRows (d,false,b.val))[a.val]?.getD [] ↔
      ∃ i : Fin (inputOne d), t = ((A).leftBlockMonitor b).step q
        (narrowedRecord ((A).leftBlockMonitor b) (leftLetter d b a).1 q (i,(leftLetter d b a).2)) := by
  rw [row_lookup,pairNumber_val,pairNumber_val]
  exact left_edges d b (rowLetter (d,false,b.val) a).1 q t (leftLetter d b a).2
theorem right_row (b : (A).State) (q t : (A).State × (A).State)
    (a : Fin (baseRows (d,true,b.val)).length) :
    ((pairNumber d q).val,(pairNumber d t).val) ∈ (baseRows (d,true,b.val))[a.val]?.getD [] ↔
      ∃ j : Fin (inputTwo d), t = ((A).rightBlockMonitor b).step q
        (narrowedRecord ((A).rightBlockMonitor b) (rightLetter d b a).1 q (j,(rightLetter d b a).2)) := by
  rw [row_lookup,pairNumber_val,pairNumber_val]
  exact right_edges d b (rowLetter (d,true,b.val) a).1 q t (rightLetter d b a).2

theorem left_accepts_iff (b : (A).State) (word : OmegaWord (Fin (baseRows (d,false,b.val)).length)) :
    (EncodedThreadCompiler.automaton (threadInput (d,false,b.val))).Accepts word ↔
      ∀ q : Nat → ((A).leftBlockMonitor b).State,
        ((A).leftBlockMonitor b).IsThread (OmegaWord.map (leftLetter d b) word) q →
          NatSeqMinEvenParity (fun n => ((A).leftBlockMonitor b).priority (q n)) := by
  have h := EncodedThreadCompiler.accepts_iff ((A).leftBlockMonitor b) (pairNumber d) (priorities d)
    (priorities_getD d) (left_priorities d b) (baseRows (d,false,b.val)) (leftLetter d b)
    (fun q a t => left_row d b q t a) word
  have hc := left_sourceData d b
  exact (EncodedThreadCompiler.config_accepts_congr (priorities d) (baseRows (d,false,b.val))
    (congrArg Prod.fst hc) (congrArg (fun x => x.2.1) hc) word).symm.trans h
theorem right_accepts_iff (b : (A).State) (word : OmegaWord (Fin (baseRows (d,true,b.val)).length)) :
    (EncodedThreadCompiler.automaton (threadInput (d,true,b.val))).Accepts word ↔
      ∀ q : Nat → ((A).rightBlockMonitor b).State,
        ((A).rightBlockMonitor b).IsThread (OmegaWord.map (rightLetter d b) word) q →
          NatSeqMinEvenParity (fun n => ((A).rightBlockMonitor b).priority (q n)) := by
  have h := EncodedThreadCompiler.accepts_iff ((A).rightBlockMonitor b) (pairNumber d) (priorities d)
    (priorities_getD d) (right_priorities d b) (baseRows (d,true,b.val)) (rightLetter d b)
    (fun q a t => right_row d b q t a) word
  have hc := right_sourceData d b
  exact (EncodedThreadCompiler.config_accepts_congr (priorities d) (baseRows (d,true,b.val))
    (congrArg Prod.fst hc) (congrArg (fun x => x.2.1) hc) word).symm.trans h
end DistributedSynthesis.EncodedOrdinaryCheckers
