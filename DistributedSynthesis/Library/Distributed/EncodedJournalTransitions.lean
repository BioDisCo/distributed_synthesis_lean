/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedJournalMachines
import DistributedSynthesis.Library.Distributed.EncodedJournalSubsets

/-! # Numeric outer journal transitions

State fields: mode, checker/atom index, current thread set, retained handoff set.
Modes 0--5 are boundary, left, right, reversed-left, reversed-right, and sink.
Branch fields: kind (0 boundary, 1 left, 2 right) and atom/sender index.
The handoff set is retained only by reversed states and is never confused with
the evolving current thread set. A first reversal initializes but does not
advance the chain checker.
-/
namespace DistributedSynthesis.EncodedJournalTransitions
open EncodedRoundObjectives EncodedJournalMachines
abbrev State := Nat × Nat × List Nat × List Nat
abbrev Branch := Nat × Nat
abbrev Move := Data × State × EncodedJournalLabels.Code × Branch
def sink : State := (5,0,[],[])
def objective (x : Move) := x.1
def state (x : Move) := x.2.1
def label (x : Move) := x.2.2.1
def branch (x : Move) := x.2.2.2
def side (x : Move) := decide ((branch x).1 = 2)
def mode (x : Move) := decide ((state x).1 = 3)
def oldSide (x : Move) := decide ((state x).1 = 2)
def ordinaryContext (x : Move) : EncodedOrdinaryThreads.Context := (objective x,side x,label x)
def chainContext (x : Move) : EncodedChainThreads.Context := (objective x,mode x,side x,label x)
def chainMonitorContext (x : Move) : EncodedChainMonitor.Context :=
  ((objective x,(state x).2.2.2),(mode x,side x,label x,(branch x).2))
def closeSet (x : Move) : List Nat :=
  if (state x).1 = 0 then EncodedJournalSubsets.both ((objective x,false,label x),(state x).2.1)
  else if (state x).1 = 1 then EncodedJournalSubsets.close ((objective x,false,label x),(state x).2.2.1,0)
  else if (state x).1 = 2 then EncodedJournalSubsets.close ((objective x,true,label x),(state x).2.2.1,0)
  else EncodedJournalSubsets.chainClose ((objective x,mode x,label x),(state x).2.2.1,0)
def openNext (x : Move) : State :=
  ((branch x).1,
    ordinaryNext (ordinaryContext x,ordinaryInitial (objective x) ((state x).2.1 / stateCount (objective x)),(branch x).2),
    EncodedJournalSubsets.openBlock (ordinaryContext x,(state x).2.1,(branch x).2),[])
def ordinaryNextState (x : Move) : State :=
  ((branch x).1,ordinaryNext (ordinaryContext x,(state x).2.1,(branch x).2),
    EncodedJournalSubsets.step (ordinaryContext x,(state x).2.2.1,(branch x).2),[])
def handoff (x : Move) := EncodedJournalSubsets.reverse
  ((objective x,oldSide x,label x),(state x).2.2.1,(branch x).2)
def reverseNext (x : Move) : State :=
  ((branch x).1+2,chainInitial (objective x),handoff x,handoff x)
def chainNextState (x : Move) : State :=
  ((branch x).1+2,chainNext (chainMonitorContext x,(state x).2.1),
    EncodedJournalSubsets.chainStep (chainContext x,(state x).2.2.1,(branch x).2),(state x).2.2.2)
def step (x : Move) : State :=
  if 5 ≤ (state x).1 then sink
  else if (branch x).1 = 0 then
    if (branch x).2 ∈ closeSet x then (0,(branch x).2,[],[]) else sink
  else if (state x).1 = 0 then openNext x
  else if (state x).1 = (branch x).1 then ordinaryNextState x
  else if (state x).1 < 3 then reverseNext x
  else chainNextState x
def initial (d : Data) : State :=
  (0,EncodedOrdinaryThreads.initial d (EncodedParityTables.initial d.2 % stateCount d),[],[])
def maximum (xs : List Nat) := xs.foldr max 0
def shift (d : Data) := 2 * (maximum ((List.range (stateCount d)).map (objectivePriority d)) + 1)
def priority (d : Data) (q : State) :=
  if q.1 = 0 then objectivePriority d (q.2.1 % stateCount d)
  else if q.1 < 3 then EncodedThreadStream.priority (ordinaryConfig d 0) q.2.1 + shift d
  else if q.1 < 5 then EncodedThreadStream.priority (chainConfig d) q.2.1 + shift d
  else shift d

theorem objective_primrec : Primrec objective := Primrec.fst
theorem state_primrec : Primrec state := Primrec.fst.comp Primrec.snd
theorem label_primrec : Primrec label := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem branch_primrec : Primrec branch := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
private theorem tag_pr : Primrec (fun x : Move => (state x).1) := Primrec.fst.comp state_primrec
private theorem q_pr : Primrec (fun x : Move => (state x).2.1) := Primrec.fst.comp (Primrec.snd.comp state_primrec)
private theorem set_pr : Primrec (fun x : Move => (state x).2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp state_primrec))
private theorem hand_pr : Primrec (fun x : Move => (state x).2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp state_primrec))
private theorem kind_pr : Primrec (fun x : Move => (branch x).1) := Primrec.fst.comp branch_primrec
private theorem input_pr : Primrec (fun x : Move => (branch x).2) := Primrec.snd.comp branch_primrec
theorem side_primrec : Primrec side := (Primrec.eq.comp kind_pr (Primrec.const 2)).decide
theorem mode_primrec : Primrec mode := (Primrec.eq.comp tag_pr (Primrec.const 3)).decide
theorem oldSide_primrec : Primrec oldSide := (Primrec.eq.comp tag_pr (Primrec.const 2)).decide
theorem ordinaryContext_primrec : Primrec ordinaryContext := objective_primrec.pair (side_primrec.pair label_primrec)
theorem chainContext_primrec : Primrec chainContext := objective_primrec.pair (mode_primrec.pair (side_primrec.pair label_primrec))
theorem chainMonitorContext_primrec : Primrec chainMonitorContext := (objective_primrec.pair hand_pr).pair
  (mode_primrec.pair (side_primrec.pair (label_primrec.pair input_pr)))
theorem closeSet_primrec : Primrec closeSet := Primrec.ite (Primrec.eq.comp tag_pr (Primrec.const 0))
  (EncodedJournalSubsets.both_primrec.comp ((objective_primrec.pair ((Primrec.const false).pair label_primrec)).pair q_pr))
  (Primrec.ite (Primrec.eq.comp tag_pr (Primrec.const 1))
    (EncodedJournalSubsets.close_primrec.comp ((objective_primrec.pair ((Primrec.const false).pair label_primrec)).pair
      (set_pr.pair (Primrec.const 0))))
    (Primrec.ite (Primrec.eq.comp tag_pr (Primrec.const 2))
      (EncodedJournalSubsets.close_primrec.comp ((objective_primrec.pair ((Primrec.const true).pair label_primrec)).pair
        (set_pr.pair (Primrec.const 0))))
      (EncodedJournalSubsets.chainClose_primrec.comp ((objective_primrec.pair (mode_primrec.pair label_primrec)).pair
        (set_pr.pair (Primrec.const 0))))))
theorem openNext_primrec : Primrec openNext := kind_pr.pair
  ((ordinaryNext_primrec.comp (ordinaryContext_primrec.pair
    ((ordinaryInitial_primrec.comp objective_primrec
      (Primrec.nat_div.comp q_pr (stateCount_primrec.comp objective_primrec))).pair input_pr))).pair
    ((EncodedJournalSubsets.openBlock_primrec.comp (ordinaryContext_primrec.pair (q_pr.pair input_pr))).pair (Primrec.const [])))
theorem ordinaryNextState_primrec : Primrec ordinaryNextState := kind_pr.pair
  ((ordinaryNext_primrec.comp (ordinaryContext_primrec.pair (q_pr.pair input_pr))).pair
    ((EncodedJournalSubsets.step_primrec.comp (ordinaryContext_primrec.pair (set_pr.pair input_pr))).pair (Primrec.const [])))
theorem handoff_primrec : Primrec handoff := EncodedJournalSubsets.reverse_primrec.comp
  ((objective_primrec.pair (oldSide_primrec.pair label_primrec)).pair (set_pr.pair input_pr))
theorem reverseNext_primrec : Primrec reverseNext := (Primrec.nat_add.comp kind_pr (Primrec.const 2)).pair
  ((chainInitial_primrec.comp objective_primrec).pair (handoff_primrec.pair handoff_primrec))
theorem chainNextState_primrec : Primrec chainNextState := (Primrec.nat_add.comp kind_pr (Primrec.const 2)).pair
  ((chainNext_primrec.comp (chainMonitorContext_primrec.pair q_pr)).pair
    ((EncodedJournalSubsets.chainStep_primrec.comp (chainContext_primrec.pair (set_pr.pair input_pr))).pair hand_pr))
theorem step_primrec : Primrec step := by
  have hm : PrimrecRel (fun (xs : List Nat) q => q ∈ xs) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  exact Primrec.ite (Primrec.nat_le.comp (Primrec.const 5) tag_pr) (Primrec.const sink)
    (Primrec.ite (Primrec.eq.comp kind_pr (Primrec.const 0))
      (Primrec.ite (hm.comp closeSet_primrec input_pr)
        ((Primrec.const 0).pair (input_pr.pair ((Primrec.const []).pair (Primrec.const [])))) (Primrec.const sink))
      (Primrec.ite (Primrec.eq.comp tag_pr (Primrec.const 0)) openNext_primrec
        (Primrec.ite (Primrec.eq.comp tag_pr kind_pr) ordinaryNextState_primrec
          (Primrec.ite (Primrec.nat_lt.comp tag_pr (Primrec.const 3)) reverseNext_primrec chainNextState_primrec))))
theorem initial_primrec : Primrec initial := (Primrec.const 0).pair
  ((EncodedOrdinaryThreads.initial_primrec.comp Primrec.id
    (Primrec.nat_mod.comp (EncodedParityTables.initial_primrec.comp Primrec.snd) stateCount_primrec)).pair
    ((Primrec.const []).pair (Primrec.const [])))
theorem maximum_primrec : Primrec maximum := Primrec.list_foldr Primrec.id (Primrec.const 0)
  (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
theorem shift_primrec : Primrec shift := Primrec.nat_mul.comp (Primrec.const 2)
  (Primrec.succ.comp (maximum_primrec.comp (Primrec.list_map (Primrec.list_range.comp stateCount_primrec)
    (objectivePriority_primrec.comp Primrec.fst Primrec.snd).to₂)))
theorem priority_primrec : Primrec₂ priority := by
  have ht : Primrec (fun x : Data × State => x.2.1) := Primrec.fst.comp Primrec.snd
  have hq : Primrec (fun x : Data × State => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0))
    (objectivePriority_primrec.comp Primrec.fst (Primrec.nat_mod.comp hq (stateCount_primrec.comp Primrec.fst)))
    (Primrec.ite (Primrec.nat_lt.comp ht (Primrec.const 3))
      (Primrec.nat_add.comp (EncodedThreadStream.priority_primrec.comp
        (ordinaryConfig_primrec.comp Primrec.fst (Primrec.const 0)) hq) (shift_primrec.comp Primrec.fst))
      (Primrec.ite (Primrec.nat_lt.comp ht (Primrec.const 5))
        (Primrec.nat_add.comp (EncodedThreadStream.priority_primrec.comp (chainConfig_primrec.comp Primrec.fst) hq)
          (shift_primrec.comp Primrec.fst)) (shift_primrec.comp Primrec.fst)))
end DistributedSynthesis.EncodedJournalTransitions
