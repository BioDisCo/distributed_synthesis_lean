/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeaderMoves

/-! The original strategy supplies a legal member of the fixed numbered
local alphabet and original witnesses for all its advertised outcomes.
The witnesses are collected before compression and are kept jointly. -/
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

noncomputable abbrev numberedPhaseRun
    (bank : ClosingPlanBank (Fin header.1.val) I₁ I₂ O₁ O₂ d)
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput (Fin header.1.val) I₁ I₂ O₁ O₂ d))
    (leader : SenderBlockStrategy I₁ (ShapeLeaderGroup header.2.1 .one → O₁))
    (env : Nat → I₂ × I₁) (n : Nat) :=
  phaseMemoryRun (((fun i => (header.2.2 i).1.1),(fun _ => true),
    (fun i => resetLeaderMinimum objective (header.2.2 i))),bank,true)
    (jointGraphLeaderNext (shapeLeaderGroup header.2.1 .one) M
      (leaderAnnotationStep (d:=d) (K:=K) M objective rank) (fun st => chooseGraphRootNext M st .right))
    (pairPlay receiver leader env) n

set_option maxHeartbeats 800000 in
set_option linter.constructorNameAsVariable false in
/-- The same finite numbered local game works at every actual physical
depth. Its permitted outcomes have original common-branch witnesses, while
its accepted table can be decoded on any realization of the same header. -/
theorem numbered_right_of_strategy
    (past : Fin header.1.val → EnvHistory I₁ I₂)
    (rep : RepresentsInputShape past header.2.1)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (winning : ContinuationWins objective.AcceptsFrom (fun i => (header.2.2 i).1.2)
      (strategyContinuationPolicy σ past)) :
    ∃ base : ShapeLeaderGroup header.2.1 .one → View I₁ I₂ .one,
      Function.Injective base ∧
      (∀ h, currentView .one (past h) = base (shapeLeaderGroup header.2.1 .one h)) ∧
      ∃ permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective),
        numberedRightLegal M objective rank header permitted = true ∧
        ∀ outcome, outcome ∈ permitted → ∃ env n,
          outcome ∈ jointGraphLeaderCollect M (leaderAnnotationStep (d:=d) (K:=K) M objective rank)
            header.2.1 (numberedLeaderSlot objective header) (fun q => q.2 ())
            (numberedPhaseRun M objective rank header (rollingOriginalBank σ past d [])
              (rollingOriginalReceiver σ past d) (jointOriginalLeader σ base) env n)
            (pairPlay (rollingOriginalReceiver σ past d) (jointOriginalLeader σ base) env n) := by
  obtain ⟨base,distinct,same⟩ := shapeLeaderGroup_views past header.2.1 rep .one
  let group := shapeLeaderGroup header.2.1 .one
  let physical := jointPhaseObjective objective (fun i => (header.2.2 i).1.2) group
  let bank := rollingOriginalBank σ past d []
  let source := fun i => (header.2.2 i).1.1
  let initial := fun i => resetLeaderMinimum objective (header.2.2 i)
  let start : GraphLeaderMemory (Fin header.1.val) GQ
      (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) I₁ I₂ O₁ O₂ d K :=
    ((source,(fun _ => true),initial),bank,true)
  let next := jointGraphLeaderNext (d:=d) (K:=K) group M (leaderAnnotationStep (d:=d) (K:=K) M objective rank)
    (fun st => chooseGraphRootNext M st .right)
  let collect := jointGraphLeaderCollect (G:=ShapeLeaderGroup header.2.1 .one) (d:=d) (K:=K) M
    (leaderAnnotationStep (d:=d) (K:=K) M objective rank) header.2.1 (numberedLeaderSlot objective header) (fun q => q.2 ())
  obtain ⟨permitted,table,accepted,witnesses,_,_,_,_⟩ :=
    finite_joint_leader_phase_witnesses physical header.2.1 group start next collect
      σ past rep L depth base distinct same
      (jointPhaseObjective_original_wins objective (fun i => (header.2.2 i).1.2) group
        σ past base same winning d)
  refine ⟨base,distinct,same,permitted,?_,witnesses⟩
  apply (numberedRightLegal_correct M objective rank header permitted).mpr
  exact ⟨bank,(finiteRootMemberController (fun _ : Unit =>
    numberedRightGuard M objective rank header permitted bank) table.toTransitionRationalTree ()).labeledTree,accepted⟩

/-- A globally winning physical strategy meets the numbered extraction
premise at every family carrying its actual incoming objective states. -/
theorem numbered_right_of_global_strategy
    (past : Fin header.1.val → EnvHistory I₁ I₂)
    (rep : RepresentsInputShape past header.2.1)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (winning : ∀ env, objective.Accepts (fun n => recordContinuationLetter (execution σ env n)))
    (incoming : ∀ h, (header.2.2 h).1.2 = strategyHistoryLabel σ
      (fun q input output => objective.step q (input,output)) objective.initial (past h)) :
    ∃ permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective),
      numberedRightLegal M objective rank header permitted = true := by
  have residual := continuationWins_at_histories objective σ winning past
  have labels := funext incoming
  rw [← labels] at residual
  obtain ⟨_,_,_,permitted,legal,_⟩ := numbered_right_of_strategy M objective rank header past rep L depth σ residual
  exact ⟨permitted,legal⟩

end
end Characterisation
