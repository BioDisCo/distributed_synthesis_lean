/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedChainThreads

/-! # Numeric boundary and handoff rounds of the journal

Inputs here are always in process order `(inputOne,inputTwo)`, even in right
rounds. Closing a block preserves its accumulated minimum; a reversal updates
the minimum and starts a chain whose entry and current atoms coincide.
-/
namespace DistributedSynthesis.EncodedJournalBoundary
open EncodedRoundObjectives EncodedOrdinaryThreads
abbrev Move := EncodedOrdinaryThreads.Move

def inputIndex (x : Move) := x.2.2.2 + inputTwo x.1.1 * x.2.2.1 +
  (inputOne x.1.1 * inputTwo x.1.1) * x.2.1
def swappedIndex (x : Move) := x.2.2.1 + inputOne x.1.1 * x.2.2.2 +
  (inputTwo x.1.1 * inputOne x.1.1) * x.2.1
def field (x : Move) (f i : Nat) := read x.1.2.2 f i
def closeRound (x : Move) : EncodedNoDirect.LetterCode :=
  (x.2.2.1,x.2.2.2,2,
    (bif x.1.2.1 then field x 6 (swappedIndex x) else field x 1 (inputIndex x)) % outputOne x.1.1,
    (bif x.1.2.1 then field x 5 (swappedIndex x) else field x 2 (inputIndex x)) % outputTwo x.1.1)
def reverseRound (x : Move) : EncodedNoDirect.LetterCode :=
  (x.2.2.1,x.2.2.2,(bif x.1.2.1 then 0 else 1),
    (bif x.1.2.1 then field x 6 (swappedIndex x)
      else field x 3 (x.2.2.1 + inputOne x.1.1 * x.2.1)) % outputOne x.1.1,
    (bif x.1.2.1 then field x 7 (x.2.2.2 + inputTwo x.1.1 * x.2.1)
      else field x 2 (inputIndex x)) % outputTwo x.1.1)
def bothRound (x : Move) : EncodedNoDirect.LetterCode :=
  (x.2.2.1,x.2.2.2,2,field x 1 (inputIndex x) % outputOne x.1.1,
    field x 5 (swappedIndex x) % outputTwo x.1.1)
def chainCloseRound (x : Move) : EncodedNoDirect.LetterCode :=
  (x.2.2.1,x.2.2.2,2,
    field x (bif x.1.2.1 then 8 else 12) (inputIndex x) % outputOne x.1.1,
    field x (bif x.1.2.1 then 11 else 15) (inputIndex x) % outputTwo x.1.1)

def advance (x : Data × Bool × Nat × EncodedNoDirect.LetterCode) :=
  let n := stateCount x.1
  let q := objectiveStep x.1 (x.2.2.1 / n) x.2.2.2
  let m := x.2.2.1 % n
  let m' := if x.2.1 = true ∧ objectivePriority x.1 q < objectivePriority x.1 m then q else m
  m' + n*q
def close (x : Move) := advance (x.1.1,false,x.2.1,closeRound x)
def reverse (x : Move) :=
  let a := advance (x.1.1,true,x.2.1,reverseRound x)
  a + (stateCount x.1.1 * stateCount x.1.1)*a
def resetMove (x : Move) : Move :=
  (x.1,initial x.1.1 (x.2.1 / stateCount x.1.1),x.2.2)
def both (x : Move) := advance (x.1.1,false,(resetMove x).2.1,bothRound (resetMove x))
def chainClose (x : Move) :=
  advance (x.1.1,false,x.2.1 % (stateCount x.1.1 * stateCount x.1.1),chainCloseRound x)

private theorem hd : Primrec (fun x : Move => x.1.1) := Primrec.fst.comp Primrec.fst
private theorem hs : Primrec (fun x : Move => x.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
private theorem hq : Primrec (fun x : Move => x.2.1) := Primrec.fst.comp Primrec.snd
private theorem hi : Primrec (fun x : Move => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem hj : Primrec (fun x : Move => x.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
theorem inputIndex_primrec : Primrec inputIndex :=
  Primrec.nat_add.comp (Primrec.nat_add.comp hj (Primrec.nat_mul.comp (inputTwo_primrec.comp hd) hi))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (inputOne_primrec.comp hd) (inputTwo_primrec.comp hd)) hq)
theorem swappedIndex_primrec : Primrec swappedIndex :=
  Primrec.nat_add.comp (Primrec.nat_add.comp hi (Primrec.nat_mul.comp (inputOne_primrec.comp hd) hj))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (inputTwo_primrec.comp hd) (inputOne_primrec.comp hd)) hq)
private theorem field_comp {f i : Move → Nat} (hf : Primrec f) (hi : Primrec i) :
    Primrec (fun x => field x (f x) (i x)) := by
  have hc : Primrec (fun x : Move => x.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  exact (Primrec.list_getD 0).comp ((Primrec.list_getD []).comp hc hf) hi
theorem closeRound_primrec : Primrec closeRound :=
  hi.pair (hj.pair ((Primrec.const 2).pair
    ((Primrec.nat_mod.comp (Primrec.cond hs (field_comp (Primrec.const 6) swappedIndex_primrec)
      (field_comp (Primrec.const 1) inputIndex_primrec)) (outputOne_primrec.comp hd)).pair
    (Primrec.nat_mod.comp (Primrec.cond hs (field_comp (Primrec.const 5) swappedIndex_primrec)
      (field_comp (Primrec.const 2) inputIndex_primrec)) (outputTwo_primrec.comp hd)))))
theorem reverseRound_primrec : Primrec reverseRound :=
  hi.pair (hj.pair ((Primrec.cond hs (Primrec.const 0) (Primrec.const 1)).pair
    ((Primrec.nat_mod.comp (Primrec.cond hs (field_comp (Primrec.const 6) swappedIndex_primrec)
      (field_comp (Primrec.const 3) (Primrec.nat_add.comp hi (Primrec.nat_mul.comp (inputOne_primrec.comp hd) hq))))
      (outputOne_primrec.comp hd)).pair
    (Primrec.nat_mod.comp (Primrec.cond hs
      (field_comp (Primrec.const 7) (Primrec.nat_add.comp hj (Primrec.nat_mul.comp (inputTwo_primrec.comp hd) hq)))
      (field_comp (Primrec.const 2) inputIndex_primrec)) (outputTwo_primrec.comp hd)))))
theorem bothRound_primrec : Primrec bothRound :=
  hi.pair (hj.pair ((Primrec.const 2).pair
    ((Primrec.nat_mod.comp (field_comp (Primrec.const 1) inputIndex_primrec) (outputOne_primrec.comp hd)).pair
    (Primrec.nat_mod.comp (field_comp (Primrec.const 5) swappedIndex_primrec) (outputTwo_primrec.comp hd)))))
theorem chainCloseRound_primrec : Primrec chainCloseRound :=
  hi.pair (hj.pair ((Primrec.const 2).pair
    ((Primrec.nat_mod.comp (field_comp (Primrec.cond hs (Primrec.const 8) (Primrec.const 12)) inputIndex_primrec)
      (outputOne_primrec.comp hd)).pair
    (Primrec.nat_mod.comp (field_comp (Primrec.cond hs (Primrec.const 11) (Primrec.const 15)) inputIndex_primrec)
      (outputTwo_primrec.comp hd)))))
theorem advance_primrec : Primrec advance := by
  let X := Data × Bool × Nat × EncodedNoDirect.LetterCode
  have hn : Primrec (fun x : X => stateCount x.1) := stateCount_primrec.comp Primrec.fst
  have hq : Primrec (fun x : X => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hnxt := objectiveStep_comp Primrec.fst (Primrec.nat_div.comp hq hn)
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hm := Primrec.nat_mod.comp hq hn
  exact Primrec.nat_add.comp (Primrec.ite
    ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true)).and
      (Primrec.nat_lt.comp (objectivePriority_primrec.comp Primrec.fst hnxt)
        (objectivePriority_primrec.comp Primrec.fst hm))) hnxt hm)
    (Primrec.nat_mul.comp hn hnxt)
theorem close_primrec : Primrec close :=
  advance_primrec.comp (hd.pair ((Primrec.const false).pair (hq.pair closeRound_primrec)))
theorem reverse_primrec : Primrec reverse := by
  have ha := advance_primrec.comp (hd.pair ((Primrec.const true).pair (hq.pair reverseRound_primrec)))
  exact Primrec.nat_add.comp ha (Primrec.nat_mul.comp
    (Primrec.nat_mul.comp (stateCount_primrec.comp hd) (stateCount_primrec.comp hd)) ha)
theorem resetMove_primrec : Primrec resetMove := Primrec.fst.pair
  ((initial_primrec.comp hd (Primrec.nat_div.comp hq (stateCount_primrec.comp hd))).pair
    (Primrec.snd.comp Primrec.snd))
theorem both_primrec : Primrec both := advance_primrec.comp (hd.pair ((Primrec.const false).pair
  ((hq.comp resetMove_primrec).pair (bothRound_primrec.comp resetMove_primrec))))
theorem chainClose_primrec : Primrec chainClose := advance_primrec.comp (hd.pair ((Primrec.const false).pair
  ((Primrec.nat_mod.comp hq (Primrec.nat_mul.comp (stateCount_primrec.comp hd) (stateCount_primrec.comp hd))).pair
    chainCloseRound_primrec)))
end DistributedSynthesis.EncodedJournalBoundary
