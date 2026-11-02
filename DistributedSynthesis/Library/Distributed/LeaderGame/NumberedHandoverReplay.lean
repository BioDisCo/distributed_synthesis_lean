/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.LeaderLabelReplay

/-! Every target label in a numbered handover is the replay of the same
phase controller from its numbered predecessor. The replay covers the whole
one-way prefix and the closing window, with no bound on the prefix length. -/
namespace Characterisation
open DistributedSynthesis

section
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable (rank : objective.State → Fin (C+1))
variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
variable (P : List Graph → Prop) (past : Fin header.1.val → EnvHistory I₁ I₂)
variable (σ : StrategyPair I₁ I₂ O₁ O₂)

theorem numberedRight_handover_labels
    (bank : ClosingPlanBank (Fin header.1.val) I₁ I₂ O₁ O₂ d)
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput (Fin header.1.val) I₁ I₂ O₁ O₂ d))
    (leader : SenderBlockStrategy I₁ (ShapeLeaderGroup header.2.1 .one → O₁))
    (plans : ∀ node h, closingPlanOfStrategy σ (rollingSourceHistory past node h) (d+1) =
      receiverClosingBank bank receiver node h)
    (outputs : ∀ node r h,
      σ.one (currentView .one (rollingSourceHistory past (node++[r]) h)) =
        leader (senderWord node) r.2 (shapeLeaderGroup header.2.1 .one h) ∧
      σ.two (currentView .two (rollingSourceHistory past (node++[r]) h)) = (receiver node r).1 h)
    (env : Nat → I₂ × I₁) (n : Nat) :
    let state := numberedPhaseRun M objective rank header bank receiver leader env n
    ∀ (t : Nat) (bound : t ≤ d+1)
      (root : ClosingLayer (ActiveClosingRoots state.1.2.1) I₁ I₂ t)
      (move : ClosingBoundaryCertificate (ActiveClosingRoots state.1.2.1) I₁ I₂ O₁ O₂
        (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) B (d+1) t),
      ClosingOfferRealizes P (rollingSourceHistory past (branchNode env n) ∘ Subtype.val)
        (leaderAnnotationStep M objective rank) (state.1.2.2 ∘ Subtype.val)
        (restrictClosingPolicy Subtype.val (closingPolicyOfBank state.2.1)) bound root move →
      ∀ i : Fin move.1.val,
        let parent := (closingLayerRoot t (move.2.2.1 i)).val
        move.2.2.2.2 i = strategyContinuationLabel σ (leaderAnnotationStep M objective rank)
          (resetLeaderMinimum objective (header.2.2 parent)) (past parent)
          (rightInputHistory (branchNode env n) ++ closingSuffix t (move.2.2.1 i)) := by
  dsimp only
  intro t bound root move realizes i
  let state := numberedPhaseRun M objective rank header bank receiver leader env n
  have banks : state.2.1 = receiverClosingBank bank receiver (branchNode env n) := by
    dsimp only [state,numberedPhaseRun]
    rw [jointGraphLeaderMemory_run]
    rw [jointLeaderMemory_run]
  have implements := closingPolicyOfBank_implements σ (rollingSourceHistory past (branchNode env n))
    state.2.1 (fun h => (plans _ h).trans (congrFun banks h).symm)
  have restricted := restrictClosingPolicy_implements σ _ _ implements
    (Subtype.val : ActiveClosingRoots state.1.2.1 → Fin header.1.val)
  exact closingOffer_carried_labels P σ (past ∘ Subtype.val)
    (fun _ => rightInputHistory (branchNode env n)) (leaderAnnotationStep M objective rank)
    (fun h => resetLeaderMinimum objective (header.2.2 h.val)) (state.1.2.2 ∘ Subtype.val)
    (fun h => numberedPhaseRun_labels M objective rank header past σ bank receiver leader outputs env n h.val)
    _ restricted bound root move realizes i

theorem numberedLeft_handover_labels
    (bank : ClosingPlanBank (Fin header.1.val) I₂ I₁ O₂ O₁ d)
    (receiver : ReceiverBlockStrategy I₁ I₂ (RollingReceiverOutput (Fin header.1.val) I₂ I₁ O₂ O₁ d))
    (leader : SenderBlockStrategy I₂ (ShapeLeaderGroup header.2.1 .two → O₂))
    (plans : ∀ node h, closingPlanOfStrategy σ (leftSourceHistory past node h) (d+1) =
      exchangePlan (receiverClosingBank bank receiver node h))
    (outputs : ∀ node r h,
      σ.one (currentView .one (leftSourceHistory past (node++[r]) h)) = (receiver node r).1 h ∧
      σ.two (currentView .two (leftSourceHistory past (node++[r]) h)) =
        leader (senderWord node) r.2 (shapeLeaderGroup header.2.1 .two h))
    (env : Nat → I₁ × I₂) (n : Nat) :
    let state := numberedLeftPhaseRun M objective rank header bank receiver leader env n
    ∀ (t : Nat) (bound : t ≤ d+1)
      (root : ClosingLayer (ActiveClosingRoots state.1.2.1) I₁ I₂ t)
      (move : ClosingBoundaryCertificate (ActiveClosingRoots state.1.2.1) I₁ I₂ O₁ O₂
        (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) B (d+1) t),
      ClosingOfferRealizes P (leftSourceHistory past (branchNode env n) ∘ Subtype.val)
        (leaderAnnotationStep M objective rank) (state.1.2.2 ∘ Subtype.val)
        (restrictClosingPolicy Subtype.val (closingPolicyOfBank (fun h => exchangePlan (state.2.1 h))))
        bound root move →
      ∀ i : Fin move.1.val,
        let parent := (closingLayerRoot t (move.2.2.1 i)).val
        move.2.2.2.2 i = strategyContinuationLabel σ (leaderAnnotationStep M objective rank)
          (resetLeaderMinimum objective (header.2.2 parent)) (past parent)
          (leftInputHistory (branchNode env n) ++ closingSuffix t (move.2.2.1 i)) := by
  dsimp only
  intro t bound root move realizes i
  let state := numberedLeftPhaseRun M objective rank header bank receiver leader env n
  have banks := (numberedLeftPhaseRun_fields M objective rank header bank receiver leader env n).2.1
  have implements := closingPolicyOfBank_implements σ (leftSourceHistory past (branchNode env n))
    (fun h => exchangePlan (state.2.1 h))
    (fun h => (plans _ h).trans (congrArg exchangePlan (congrFun banks h)).symm)
  have restricted := restrictClosingPolicy_implements σ _ _ implements
    (Subtype.val : ActiveClosingRoots state.1.2.1 → Fin header.1.val)
  exact closingOffer_carried_labels P σ (past ∘ Subtype.val)
    (fun _ => leftInputHistory (branchNode env n)) (leaderAnnotationStep M objective rank)
    (fun h => resetLeaderMinimum objective (header.2.2 h.val)) (state.1.2.2 ∘ Subtype.val)
    (fun h => numberedLeftPhaseRun_labels M objective rank header past σ bank receiver leader outputs env n h.val)
    _ restricted bound root move realizes i

end
end Characterisation
