/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedOrdinaryThreads

/-! # Numeric composed-thread transitions

A chain stores its entry atom and current atom. `mode = true` selects a
reversed-left label; `side = true` selects a right round. The entry is reset
exactly on a re-reversal, while the running minimum is retained across it.
-/
namespace DistributedSynthesis.EncodedChainThreads
open EncodedRoundObjectives EncodedNoDirect
abbrev Context := Data × Bool × Bool × EncodedJournalLabels.Code
abbrev Move := Context × Nat × Nat × Nat

def atomCount (d : Data) := stateCount d * stateCount d
def chainCount (d : Data) := atomCount d * atomCount d
def entry (d : Data) (th : Nat) := th / atomCount d
def current (d : Data) (th : Nat) := th % atomCount d
def fieldBase (c : Context) : Nat := bif c.2.1 then 8 else 12
def inputIndex (x : Move) := x.2.2.2 + inputTwo x.1.1 * x.2.2.1 +
  (inputOne x.1.1 * inputTwo x.1.1)*x.2.1
def oneIndex (x : Move) :=
  bif x.1.2.2.1 then x.2.2.1 + inputOne x.1.1 *
    (bif x.1.2.1 then x.2.1 else entry x.1.1 x.2.1)
  else inputIndex x
def twoIndex (x : Move) :=
  bif x.1.2.2.1 then inputIndex x
  else x.2.2.2 + inputTwo x.1.1 *
    (bif x.1.2.1 then entry x.1.1 x.2.1 else x.2.1)
def outOne (x : Move) := EncodedOrdinaryThreads.read x.1.2.2.2
  (fieldBase x.1 + (bif x.1.2.2.1 then 1 else 0)) (oneIndex x) % outputOne x.1.1
def outTwo (x : Move) := EncodedOrdinaryThreads.read x.1.2.2.2
  (fieldBase x.1 + (bif x.1.2.2.1 then 3 else 2)) (twoIndex x) % outputTwo x.1.1
def roundCode (x : Move) : LetterCode :=
  (x.2.2.1,x.2.2.2,(bif x.1.2.2.1 then 1 else 0),outOne x,outTwo x)
def nextObjective (x : Move) :=
  objectiveStep x.1.1 (current x.1.1 x.2.1 / stateCount x.1.1) (roundCode x)
def nextAtom (x : Move) :=
  let q := nextObjective x
  let m := current x.1.1 x.2.1 % stateCount x.1.1
  (if objectivePriority x.1.1 q < objectivePriority x.1.1 m then q else m) + stateCount x.1.1*q
def next (x : Move) := nextAtom x + atomCount x.1.1 *
  (if x.1.2.1 = x.1.2.2.1 then nextAtom x else entry x.1.1 x.2.1)

theorem atomCount_primrec : Primrec atomCount := Primrec.nat_mul.comp stateCount_primrec stateCount_primrec
theorem chainCount_primrec : Primrec chainCount := Primrec.nat_mul.comp atomCount_primrec atomCount_primrec
theorem entry_primrec : Primrec₂ entry :=
  Primrec.nat_div.comp Primrec.snd (atomCount_primrec.comp Primrec.fst)
theorem current_primrec : Primrec₂ current :=
  Primrec.nat_mod.comp Primrec.snd (atomCount_primrec.comp Primrec.fst)
theorem fieldBase_primrec : Primrec fieldBase :=
  Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.const 8) (Primrec.const 12)

private theorem d_pr : Primrec (fun x : Move => x.1.1) := Primrec.fst.comp Primrec.fst
private theorem mode_pr : Primrec (fun x : Move => x.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
private theorem side_pr : Primrec (fun x : Move => x.1.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
private theorem code_pr : Primrec (fun x : Move => x.1.2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
private theorem th_pr : Primrec (fun x : Move => x.2.1) := Primrec.fst.comp Primrec.snd
private theorem i_pr : Primrec (fun x : Move => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem j_pr : Primrec (fun x : Move => x.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

theorem inputIndex_primrec : Primrec inputIndex :=
  Primrec.nat_add.comp (Primrec.nat_add.comp j_pr (Primrec.nat_mul.comp (inputTwo_primrec.comp d_pr) i_pr))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (inputOne_primrec.comp d_pr) (inputTwo_primrec.comp d_pr)) th_pr)
theorem oneIndex_primrec : Primrec oneIndex :=
  Primrec.cond side_pr (Primrec.nat_add.comp i_pr (Primrec.nat_mul.comp (inputOne_primrec.comp d_pr)
    (Primrec.cond mode_pr th_pr (entry_primrec.comp d_pr th_pr)))) inputIndex_primrec
theorem twoIndex_primrec : Primrec twoIndex :=
  Primrec.cond side_pr inputIndex_primrec (Primrec.nat_add.comp j_pr (Primrec.nat_mul.comp
    (inputTwo_primrec.comp d_pr) (Primrec.cond mode_pr (entry_primrec.comp d_pr th_pr) th_pr)))
theorem outOne_primrec : Primrec outOne :=
  Primrec.nat_mod.comp ((Primrec.list_getD 0).comp ((Primrec.list_getD []).comp code_pr
    (Primrec.nat_add.comp (fieldBase_primrec.comp Primrec.fst)
      (Primrec.cond side_pr (Primrec.const 1) (Primrec.const 0)))) oneIndex_primrec)
    (outputOne_primrec.comp d_pr)
theorem outTwo_primrec : Primrec outTwo :=
  Primrec.nat_mod.comp ((Primrec.list_getD 0).comp ((Primrec.list_getD []).comp code_pr
    (Primrec.nat_add.comp (fieldBase_primrec.comp Primrec.fst)
      (Primrec.cond side_pr (Primrec.const 3) (Primrec.const 2)))) twoIndex_primrec)
    (outputTwo_primrec.comp d_pr)
theorem roundCode_primrec : Primrec roundCode :=
  i_pr.pair (j_pr.pair ((Primrec.cond side_pr (Primrec.const 1) (Primrec.const 0)).pair
    (outOne_primrec.pair outTwo_primrec)))
theorem nextObjective_primrec : Primrec nextObjective :=
  objectiveStep_comp d_pr (Primrec.nat_div.comp (current_primrec.comp d_pr th_pr)
    (stateCount_primrec.comp d_pr)) roundCode_primrec
theorem nextAtom_primrec : Primrec nextAtom := by
  have hm := Primrec.nat_mod.comp (current_primrec.comp d_pr th_pr) (stateCount_primrec.comp d_pr)
  exact Primrec.nat_add.comp (Primrec.ite
    (Primrec.nat_lt.comp (objectivePriority_primrec.comp d_pr nextObjective_primrec)
      (objectivePriority_primrec.comp d_pr hm)) nextObjective_primrec hm)
    (Primrec.nat_mul.comp (stateCount_primrec.comp d_pr) nextObjective_primrec)
theorem next_primrec : Primrec next :=
  Primrec.nat_add.comp nextAtom_primrec (Primrec.nat_mul.comp (atomCount_primrec.comp d_pr)
    (Primrec.ite (Primrec.eq.comp mode_pr side_pr) nextAtom_primrec (entry_primrec.comp d_pr th_pr)))
end DistributedSynthesis.EncodedChainThreads
