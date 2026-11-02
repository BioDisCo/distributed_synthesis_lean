/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeftLeader

/-! Original winning strategies supply legal leftward moves, with one
original branch witnessing every advertised whole outcome. The collector
uses the original graph language and original boundary rule throughout. -/
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

noncomputable abbrev numberedLeftPhaseRun
    (bank : ClosingPlanBank (Fin header.1.val) I₂ I₁ O₂ O₁ d)
    (receiver : ReceiverBlockStrategy I₁ I₂ (RollingReceiverOutput (Fin header.1.val) I₂ I₁ O₂ O₁ d))
    (leader : SenderBlockStrategy I₂ (ShapeLeaderGroup header.2.1 .two → O₂))
    (env : Nat → I₁ × I₂) (n : Nat) :=
  phaseMemoryRun (((fun i => (header.2.2 i).1.1),(fun _ => true),
    (fun i => resetLeaderMinimum objective (header.2.2 i))),bank,true)
    (numberedLeftNext M objective rank header) (pairPlay receiver leader env) n

set_option maxHeartbeats 800000 in
set_option linter.constructorNameAsVariable false in
theorem numbered_left_of_strategy
    (past : Fin header.1.val → EnvHistory I₁ I₂)
    (rep : RepresentsInputShape past header.2.1)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (winning : ContinuationWins objective.AcceptsFrom (fun i => (header.2.2 i).1.2)
      (strategyContinuationPolicy σ past)) :
    ∃ base : ShapeLeaderGroup header.2.1 .two → View I₂ I₁ .one,
      Function.Injective base ∧
      (∀ h, currentView .one (exchangeHistory (past h)) = base (shapeLeaderGroup header.2.1 .two h)) ∧
      ∃ permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective),
        numberedLeftLegal M objective rank header permitted = true ∧
        ∀ outcome, outcome ∈ permitted → ∃ env n,
          outcome ∈ numberedLeftCollect M objective rank header
            (numberedLeftPhaseRun M objective rank header
              (rollingOriginalBank (exchangeStrategy σ) (exchangeHistory ∘ past) d [])
              (rollingOriginalReceiver (exchangeStrategy σ) (exchangeHistory ∘ past) d)
              (jointOriginalLeader (exchangeStrategy σ) base) env n)
            (pairPlay (rollingOriginalReceiver (exchangeStrategy σ) (exchangeHistory ∘ past) d)
              (jointOriginalLeader (exchangeStrategy σ) base) env n) := by
  have exchangedShape := exchangeShape_exact past header.2.1 rep
  obtain ⟨base,distinct,same⟩ := shapeLeaderGroup_views (exchangeHistory ∘ past)
    (exchangeShape header.2.1) exchangedShape .one
  let group := shapeLeaderGroup header.2.1 .two
  let physical := jointPhaseObjective (objective.comap exchangeLetter) (fun i => (header.2.2 i).1.2) group
  let bank := rollingOriginalBank (exchangeStrategy σ) (exchangeHistory ∘ past) d []
  let start : NumberedLeftMemory objective header :=
    (((fun i => (header.2.2 i).1.1),(fun _ => true),
      (fun i => resetLeaderMinimum objective (header.2.2 i))),bank,true)
  have residual := exchange_continuation_wins objective (fun i => (header.2.2 i).1.2) σ past winning
  obtain ⟨permitted,table,accepted,witnesses,_,_,_,_⟩ :=
    finite_joint_leader_phase_witnesses physical (exchangeShape header.2.1) group start
      (numberedLeftNext M objective rank header) (numberedLeftCollect M objective rank header)
      (exchangeStrategy σ) (exchangeHistory ∘ past) exchangedShape L
      (fun h => (exchangeHistory_length _).trans (depth h)) base distinct same
      (jointPhaseObjective_original_wins (objective.comap exchangeLetter) (fun i => (header.2.2 i).1.2)
        group (exchangeStrategy σ) (exchangeHistory ∘ past) base same residual d)
  refine ⟨base,distinct,same,permitted,?_,witnesses⟩
  apply (numberedLeftLegal_correct M objective rank header permitted).mpr
  exact ⟨bank,(finiteRootMemberController (fun _ : Unit =>
    numberedLeftGuard M objective rank header permitted bank) table.toTransitionRationalTree ()).labeledTree,accepted⟩

end
end Characterisation
