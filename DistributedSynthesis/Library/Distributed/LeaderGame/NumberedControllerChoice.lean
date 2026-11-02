/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedSuccessorEdges

/-! Decode a legal finite move once on its carried literal source family.
The chosen controller serves every future target component of that phase. -/
namespace Characterisation
open DistributedSynthesis

section
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable [DecidableEq objective.State] (rank : objective.State → Fin (C+1))
variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
variable (past : Fin header.1.val → EnvHistory I₁ I₂)
variable (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))

def NumberedRightController (σ : StrategyPair I₁ I₂ O₁ O₂) : Prop :=
  ∃ table : NumberedRightTable M objective rank header permitted,
    NarrowedAllThreadsWin (numberedRightGuard M objective rank header permitted table.1)
      table.2.toTransitionRationalTree.labeledTree ∧
    let tree := narrowedInducedTree (numberedRightGuard M objective rank header permitted table.1)
      table.2.toTransitionRationalTree.labeledTree
    let receiver := receiverOfTree tree
    let leader := senderOfTree tree
    (∀ node i, closingPlanOfStrategy σ (rollingSourceHistory past node i) (d+1) =
      receiverClosingBank table.1 receiver node i) ∧
    (∀ node r i,
      σ.one (currentView .one (rollingSourceHistory past (node++[r]) i)) =
        leader (senderWord node) r.2 (shapeLeaderGroup header.2.1 .one i) ∧
      σ.two (currentView .two (rollingSourceHistory past (node++[r]) i)) = (receiver node r).1 i) ∧
    ∀ i (env : Nat → I₂ × I₁), objective.AcceptsFrom (header.2.2 i).1.2
      (continuationTrace (strategyContinuationPolicy σ past) i
        (fun n => ((env n).2,(env n).1,.right)))

def NumberedLeftController (σ : StrategyPair I₁ I₂ O₁ O₂) : Prop :=
  ∃ table : NumberedLeftTable M objective rank header permitted,
    NarrowedAllThreadsWin (numberedLeftGuard M objective rank header permitted table.1)
      table.2.toTransitionRationalTree.labeledTree ∧
    let tree := narrowedInducedTree (numberedLeftGuard M objective rank header permitted table.1)
      table.2.toTransitionRationalTree.labeledTree
    let receiver := receiverOfTree tree
    let leader := senderOfTree tree
    (∀ node i, closingPlanOfStrategy σ (leftSourceHistory past node i) (d+1) =
      exchangePlan (receiverClosingBank table.1 receiver node i)) ∧
    (∀ node r i,
      σ.one (currentView .one (leftSourceHistory past (node++[r]) i)) = (receiver node r).1 i ∧
      σ.two (currentView .two (leftSourceHistory past (node++[r]) i)) =
        leader (senderWord node) r.2 (shapeLeaderGroup header.2.1 .two i)) ∧
    ∀ i (env : Nat → I₁ × I₂), objective.AcceptsFrom (header.2.2 i).1.2
      (continuationTrace (strategyContinuationPolicy σ past) i
        (fun n => ((env n).1,(env n).2,.left)))

def NumberedController (p : Proc) (σ : StrategyPair I₁ I₂ O₁ O₂) : Prop :=
  match p with
  | .one => NumberedRightController M objective rank header past permitted σ
  | .two => NumberedLeftController M objective rank header past permitted σ

theorem numberedController_exists (p : Proc)
    (legal : numberedLeaderLegal M objective rank header (p,permitted) = true)
    (shape : RepresentsInputShape past header.2.1) (a : Nat) (depth : ∀ i, List.length (past i) = a) :
    ∃ σ, NumberedController M objective rank header past permitted p σ := by
  cases p with
  | one =>
    have localLegal : numberedRightLegal M objective rank header permitted = true := by
      simp only [numberedLeaderLegal,Bool.and_eq_true] at legal
      exact legal.2
    obtain ⟨table,accepted⟩ := (numberedRightLegal_iff_table M objective rank header permitted).mp localLegal
    obtain ⟨σ,plans,outputs,endless⟩ := numberedRightTable_readback M objective rank header permitted table accepted
      past shape a depth
    exact ⟨σ,table,accepted,plans,outputs,endless⟩
  | two =>
    have localLegal : numberedLeftLegal M objective rank header permitted = true := by
      simp only [numberedLeaderLegal,Bool.and_eq_true] at legal
      exact legal.2
    obtain ⟨table,accepted⟩ := (numberedLeftLegal_iff_table M objective rank header permitted).mp localLegal
    obtain ⟨σ,plans,outputs,endless⟩ := numberedLeftTable_readback M objective rank header permitted table accepted
      past shape a depth
    exact ⟨σ,table,accepted,plans,outputs,endless⟩

noncomputable def chooseNumberedController (p : Proc) : StrategyPair I₁ I₂ O₁ O₂ := by
  classical
  exact if possible : ∃ σ, NumberedController M objective rank header past permitted p σ
    then possible.choose else ⟨fun _ => default,fun _ => default⟩

theorem chooseNumberedController_spec (p : Proc)
    (legal : numberedLeaderLegal M objective rank header (p,permitted) = true)
    (shape : RepresentsInputShape past header.2.1) (a : Nat) (depth : ∀ i, List.length (past i) = a) :
    NumberedController M objective rank header past permitted p
      (chooseNumberedController M objective rank header past permitted p) := by
  have possible := numberedController_exists M objective rank header past permitted p legal shape a depth
  rw [chooseNumberedController,dif_pos possible]
  exact possible.choose_spec

variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (small : ∀ k : EnvHistory I₁ I₂, P (History.graphSequence k) → leaderBoundary P d k = true →
  Nat.card (InputHistoryComponent P k) ≤ B)

include closed recognizes recent bounded small in
theorem numberedController_actual_successor
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) (a : Nat)
    (phase : ConsecutiveLeaderBoundaries P d h a)
    (e : Fin header.1.val ≃ InputHistoryComponent P (h.take a))
    (numbering : ∀ i, (e i).val = past i)
    (shape : RepresentsInputShape past header.2.1)
    (graphs : ∀ i, GraphRootRep P M (History.graphSequence (past i)) (header.2.2 i).1.1)
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (controller : NumberedController M objective rank header past permitted
      (componentLeader P d (History.graphSequence (h.take a))) σ) :
    ∃ outcome nextPast, outcome ∈ permitted ∧
      NumberedSuccessorRep M objective rank P header past σ (boundaryOrigin P h) outcome nextPast := by
  have families : (fun i => (e i).val) = past := funext numbering
  cases selected : componentLeader P d (History.graphSequence (h.take a)) with
  | one =>
    rw [selected] at controller
    obtain ⟨table,accepted,plans,outputs,_⟩ := controller
    have result := numberedRightTable_actual_successor M objective rank P closed recognizes recent bounded small
      header permitted table accepted h live a phase e (by rw [families]; exact shape)
      (by intro i; rw [numbering]; exact graphs i) selected σ
    dsimp only at result
    rw [families] at result
    exact result plans outputs
  | two =>
    rw [selected] at controller
    obtain ⟨table,accepted,plans,outputs,_⟩ := controller
    have result := numberedLeftTable_actual_successor M objective rank P closed recognizes recent bounded small
      header permitted table accepted h live a phase e (by rw [families]; exact shape)
      (by intro i; rw [numbering]; exact graphs i) selected σ
    dsimp only at result
    rw [families] at result
    exact result plans outputs

end
end Characterisation
