/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedRoundObjectives
import DistributedSynthesis.Library.Distributed.EncodedJournalLabels
import DistributedSynthesis.Library.Distributed.EncodedThreadBuchi

/-! # Numeric ordinary left/right journal threads
An ordinary state stores the current objective state and the state recording
the block minimum, numbered as `minimum + stateCount * current`. Each edge
selects a receiver input; the sender input and journal label are fixed.
The numeric objective is arbitrary, including reversal-forgiving companions.
-/
namespace DistributedSynthesis.EncodedOrdinaryThreads
open EncodedNoDirect EncodedRoundObjectives
set_option synthInstance.maxSize 2048

abbrev Context := Data × Bool × EncodedJournalLabels.Code
def receiverCount (x : Context) := bif x.2.1 then inputTwo x.1 else inputOne x.1
def senderCount (x : Context) := bif x.2.1 then inputOne x.1 else inputTwo x.1
def receiverOutputs (x : Context) := bif x.2.1 then outputTwo x.1 else outputOne x.1
def senderOutputs (x : Context) := bif x.2.1 then outputOne x.1 else outputTwo x.1
def offset (x : Context) : Nat := bif x.2.1 then 4 else 0
def read (c : EncodedJournalLabels.Code) (field index : Nat) := (c.getD field []).getD index 0
abbrev Move := Context × Nat × Nat × Nat
def senderOutput (x : Move) := read x.1.2.2 (offset x.1) x.2.2.2 % senderOutputs x.1
def receiverOutput (x : Move) :=
  read x.1.2.2 (offset x.1 + 1)
    (x.2.2.2 + senderCount x.1 * x.2.2.1 + (receiverCount x.1 * senderCount x.1) * x.2.1) % receiverOutputs x.1
def roundCode (x : Move) : LetterCode :=
  bif x.1.2.1 then (x.2.2.2, x.2.2.1, 1, senderOutput x, receiverOutput x)
  else (x.2.2.1, x.2.2.2, 0, receiverOutput x, senderOutput x)
def nextObjective (x : Move) := objectiveStep x.1.1 (x.2.1 / stateCount x.1.1) (roundCode x)
def next (x : Move) : Nat :=
  let q := nextObjective x
  let m := x.2.1 % stateCount x.1.1
  let minimum := if objectivePriority x.1.1 q < objectivePriority x.1.1 m then q else m
  minimum + stateCount x.1.1 * q
def priorities (d : Data) : List Nat :=
  (List.range (stateCount d * stateCount d)).map (fun q => objectivePriority d (q / stateCount d))
def initial (d : Data) (boundary : Nat) := boundary + stateCount d * boundary
def edges (x : Context) (sender : Nat) : EncodedThreadBuchi.Edges :=
  (List.range (stateCount x.1 * stateCount x.1)).flatMap (fun q =>
    (List.range (receiverCount x)).map (fun r => (q, next (x, q, r, sender))))

private theorem d_primrec : Primrec (fun x : Context => x.1) := Primrec.fst
private theorem side_primrec : Primrec (fun x : Context => x.2.1) := Primrec.fst.comp Primrec.snd
theorem receiverCount_primrec : Primrec receiverCount :=
  Primrec.cond side_primrec (inputTwo_primrec.comp d_primrec) (inputOne_primrec.comp d_primrec)
theorem senderCount_primrec : Primrec senderCount :=
  Primrec.cond side_primrec (inputOne_primrec.comp d_primrec) (inputTwo_primrec.comp d_primrec)
theorem receiverOutputs_primrec : Primrec receiverOutputs :=
  Primrec.cond side_primrec (outputTwo_primrec.comp d_primrec) (outputOne_primrec.comp d_primrec)
theorem senderOutputs_primrec : Primrec senderOutputs :=
  Primrec.cond side_primrec (outputOne_primrec.comp d_primrec) (outputTwo_primrec.comp d_primrec)
theorem offset_primrec : Primrec offset := Primrec.cond side_primrec (Primrec.const 4) (Primrec.const 0)
theorem read_primrec : Primrec (fun x : EncodedJournalLabels.Code × Nat × Nat => read x.1 x.2.1 x.2.2) :=
  (Primrec.list_getD 0).comp ((Primrec.list_getD []).comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)
private theorem read_comp {X : Type*} [Primcodable X]
    {c : X → EncodedJournalLabels.Code} {f i : X → Nat}
    (hc : Primrec c) (hf : Primrec f) (hi : Primrec i) :
    Primrec (fun x => read (c x) (f x) (i x)) :=
  (Primrec.list_getD 0).comp ((Primrec.list_getD []).comp hc hf) hi
private theorem ctx_primrec : Primrec (fun x : Move => x.1) := Primrec.fst
private theorem q_primrec : Primrec (fun x : Move => x.2.1) := Primrec.fst.comp Primrec.snd
private theorem r_primrec : Primrec (fun x : Move => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem s_primrec : Primrec (fun x : Move => x.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
private theorem code_primrec : Primrec (fun x : Move => x.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
theorem senderOutput_primrec : Primrec senderOutput :=
  Primrec.nat_mod.comp (read_comp code_primrec
    (offset_primrec.comp ctx_primrec) s_primrec) (senderOutputs_primrec.comp ctx_primrec)
theorem receiverOutput_primrec : Primrec receiverOutput := by
  have hi := Primrec.nat_add.comp
    (Primrec.nat_add.comp s_primrec (Primrec.nat_mul.comp (senderCount_primrec.comp ctx_primrec) r_primrec))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (receiverCount_primrec.comp ctx_primrec)
      (senderCount_primrec.comp ctx_primrec)) q_primrec)
  exact Primrec.nat_mod.comp (read_comp code_primrec
    (Primrec.succ.comp (offset_primrec.comp ctx_primrec)) hi) (receiverOutputs_primrec.comp ctx_primrec)
theorem roundCode_primrec : Primrec roundCode :=
  Primrec.cond (side_primrec.comp ctx_primrec)
    (s_primrec.pair (r_primrec.pair ((Primrec.const 1).pair (senderOutput_primrec.pair receiverOutput_primrec))))
    (r_primrec.pair (s_primrec.pair ((Primrec.const 0).pair (receiverOutput_primrec.pair senderOutput_primrec))))
theorem nextObjective_primrec : Primrec nextObjective :=
  objectiveStep_comp (d_primrec.comp ctx_primrec)
    (Primrec.nat_div.comp q_primrec (stateCount_primrec.comp (d_primrec.comp ctx_primrec))) roundCode_primrec
theorem next_primrec : Primrec next := by
  have hd := d_primrec.comp ctx_primrec
  have hn := stateCount_primrec.comp hd
  have hm := Primrec.nat_mod.comp q_primrec hn
  exact Primrec.nat_add.comp
    (Primrec.ite (Primrec.nat_lt.comp (objectivePriority_primrec.comp hd nextObjective_primrec)
      (objectivePriority_primrec.comp hd hm)) nextObjective_primrec hm)
    (Primrec.nat_mul.comp hn nextObjective_primrec)
theorem priorities_primrec : Primrec priorities :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp stateCount_primrec stateCount_primrec))
    (objectivePriority_primrec.comp Primrec.fst
      (Primrec.nat_div.comp Primrec.snd (stateCount_primrec.comp Primrec.fst))).to₂
theorem initial_primrec : Primrec₂ initial :=
  Primrec.nat_add.comp Primrec.snd (Primrec.nat_mul.comp (stateCount_primrec.comp Primrec.fst) Primrec.snd)
theorem edges_primrec : Primrec₂ edges := by
  have hn : Primrec (fun x : Context × Nat => stateCount x.1.1) :=
    stateCount_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hmove : Primrec (fun y : ((Context × Nat) × Nat) × Nat =>
      (y.1.1.1, y.1.2, y.2, y.1.1.2)) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp Primrec.fst).pair
        (Primrec.snd.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
  have he : Primrec (fun y : ((Context × Nat) × Nat) × Nat =>
      (y.1.2, next (y.1.1.1, y.1.2, y.2, y.1.1.2))) :=
    (Primrec.snd.comp Primrec.fst).pair (Primrec.comp next_primrec hmove)
  have hr : Primrec (fun y : (Context × Nat) × Nat => List.range (receiverCount y.1.1)) :=
    Primrec.list_range.comp (receiverCount_primrec.comp (Primrec.fst.comp Primrec.fst))
  exact Primrec.list_flatMap (Primrec.list_range.comp (Primrec.nat_mul.comp hn hn))
    (Primrec.list_map hr he.to₂).to₂

end DistributedSynthesis.EncodedOrdinaryThreads
