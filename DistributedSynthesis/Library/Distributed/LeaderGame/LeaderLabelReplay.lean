/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedRightHandover
import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeftHandover
import DistributedSynthesis.Library.Distributed.LeaderPhases.PhaseMonitorComposition

/-! Replay every numbered annotation from its own incoming boundary label.
The controller is evaluated on full physical histories. No outputs preceding
the current phase are used to reconstruct the incoming label. -/
namespace Characterisation
open DistributedSynthesis

theorem strategyContinuationLabel_append {I₁ I₂ O₁ O₂ Q : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (q : Q) (root word : EnvHistory I₁ I₂)
    (r : RoundRecord I₁ I₂ Graph Unit Unit) :
    strategyContinuationLabel σ step q root (word++[r]) =
      step (strategyContinuationLabel σ step q root word) (r.inputOne,r.inputTwo,r.graph)
        (σ.one (currentView .one (root++word++[r])),
         σ.two (currentView .two (root++word++[r]))) := by
  simp only [strategyContinuationLabel,List.foldl_append,List.foldl_cons,List.foldl_nil,
    strategyLabelStep,strategyLabelStep_history]

theorem strategyContinuationLabel_append_words {I₁ I₂ O₁ O₂ Q : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (q : Q) (root word rest : EnvHistory I₁ I₂) :
    strategyContinuationLabel σ step q root (word++rest) =
      strategyContinuationLabel σ step
        (strategyContinuationLabel σ step q root word) (root++word) rest := by
  have state : word.foldl (strategyLabelStep σ step) (root,q) =
      (root++word,strategyContinuationLabel σ step q root word) :=
    Prod.ext (strategyLabelStep_history σ step root q word) rfl
  unfold strategyContinuationLabel
  rw [List.foldl_append,state]

def closingSuffix {H I₁ I₂ : Type} (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    EnvHistory I₁ I₂ := closingLayerHistory (fun _ : H => []) n s

theorem closingLayerHistory_suffix {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    closingLayerHistory past n s = past (closingLayerRoot n s) ++ closingSuffix n s := by
  induction n with
  | zero => simp [closingLayerHistory,closingLayerRoot,closingSuffix]
  | succ n ih =>
    change closingLayerHistory past n s.1 ++ [_] =
      past (closingLayerRoot n s.1) ++ (closingSuffix n s.1 ++ [_])
    rw [ih,List.append_assoc]

theorem closingLayerLabels_continuation {H I₁ I₂ O₁ O₂ Q : Type} {D : Nat}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (implements : ∀ t s, out t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s))))
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) :
    closingLayerLabels step initial out n bound s =
      strategyContinuationLabel σ step (initial (closingLayerRoot n s))
        (past (closingLayerRoot n s)) (closingSuffix n s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [closingLayerLabels]
    rw [ih,implements]
    change step _ s.2 _ = strategyContinuationLabel σ step _ _
      (closingSuffix n s.1 ++ [⟨s.2.1,s.2.2.1,s.2.2.2,(),()⟩])
    rw [strategyContinuationLabel_append]
    congr 2 <;> simp only [closingLayerRoot,← closingLayerHistory_suffix,
      closingLayerHistory,scenarioHistory]

theorem closingOffer_continuation_labels {H I₁ I₂ O₁ O₂ Q : Type} {B D n : Nat}
    (P : List Graph → Prop) (σ : StrategyPair I₁ I₂ O₁ O₂)
    (past : H → EnvHistory I₁ I₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (implements : ∀ t s, out t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s))))
    (bound : n ≤ D) (root : ClosingLayer H I₁ I₂ n)
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n)
    (realizes : ClosingOfferRealizes P past step initial out bound root move) (i : Fin move.1.val) :
    move.2.2.2.2 i = strategyContinuationLabel σ step
      (initial (closingLayerRoot n (move.2.2.1 i)))
      (past (closingLayerRoot n (move.2.2.1 i))) (closingSuffix n (move.2.2.1 i)) := by
  rw [realizes.2.2.2.1 i,← closingLayerLabels_replay]
  exact closingLayerLabels_continuation σ past step initial out implements n bound _

section Numbered
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable (rank : objective.State → Fin (C+1))
variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
variable (past : Fin header.1.val → EnvHistory I₁ I₂)
variable (σ : StrategyPair I₁ I₂ O₁ O₂)

theorem numberedPhaseRun_labels
    (bank : ClosingPlanBank (Fin header.1.val) I₁ I₂ O₁ O₂ d)
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput (Fin header.1.val) I₁ I₂ O₁ O₂ d))
    (leader : SenderBlockStrategy I₁ (ShapeLeaderGroup header.2.1 .one → O₁))
    (outputs : ∀ node r h,
      σ.one (currentView .one (rollingSourceHistory past (node++[r]) h)) =
        leader (senderWord node) r.2 (shapeLeaderGroup header.2.1 .one h) ∧
      σ.two (currentView .two (rollingSourceHistory past (node++[r]) h)) = (receiver node r).1 h)
    (env : Nat → I₂ × I₁) (n : Nat) (h : Fin header.1.val) :
    (numberedPhaseRun M objective rank header bank receiver leader env n).1.2.2 h =
      strategyContinuationLabel σ (leaderAnnotationStep M objective rank)
        (resetLeaderMinimum objective (header.2.2 h)) (past h) (rightInputHistory (branchNode env n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change leaderAnnotationStep M objective rank
      ((numberedPhaseRun M objective rank header bank receiver leader env n).1.2.2 h)
      ((env n).2,(env n).1,.right)
      (leader (senderWord (branchNode env n)) (env n).2 (shapeLeaderGroup header.2.1 .one h),
       (receiver (branchNode env n) (env n)).1 h) = _
    rw [ih]
    simp only [branchNode,rightInputHistory,List.map_append,List.map_singleton]
    rw [strategyContinuationLabel_append]
    have out := outputs (branchNode env n) (env n) h
    simpa only [rollingSourceHistory,rightInputHistory,List.map_append,List.map_singleton,
      List.append_assoc] using congrArg
      (leaderAnnotationStep M objective rank
        (strategyContinuationLabel σ (leaderAnnotationStep M objective rank)
          (resetLeaderMinimum objective (header.2.2 h)) (past h)
          (rightInputHistory (branchNode env n))) ((env n).2,(env n).1,.right))
      (congrArg₂ Prod.mk out.1 out.2).symm

theorem numberedLeftPhaseRun_labels
    (bank : ClosingPlanBank (Fin header.1.val) I₂ I₁ O₂ O₁ d)
    (receiver : ReceiverBlockStrategy I₁ I₂ (RollingReceiverOutput (Fin header.1.val) I₂ I₁ O₂ O₁ d))
    (leader : SenderBlockStrategy I₂ (ShapeLeaderGroup header.2.1 .two → O₂))
    (outputs : ∀ node r h,
      σ.one (currentView .one (leftSourceHistory past (node++[r]) h)) = (receiver node r).1 h ∧
      σ.two (currentView .two (leftSourceHistory past (node++[r]) h)) =
        leader (senderWord node) r.2 (shapeLeaderGroup header.2.1 .two h))
    (env : Nat → I₁ × I₂) (n : Nat) (h : Fin header.1.val) :
    (numberedLeftPhaseRun M objective rank header bank receiver leader env n).1.2.2 h =
      strategyContinuationLabel σ (leaderAnnotationStep M objective rank)
        (resetLeaderMinimum objective (header.2.2 h)) (past h) (leftInputHistory (branchNode env n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change leaderAnnotationStep M objective rank
      ((numberedLeftPhaseRun M objective rank header bank receiver leader env n).1.2.2 h)
      ((env n).1,(env n).2,.left)
      ((receiver (branchNode env n) (env n)).1 h,
       leader (senderWord (branchNode env n)) (env n).2 (shapeLeaderGroup header.2.1 .two h)) = _
    rw [ih]
    simp only [branchNode,leftInputHistory,List.map_append,List.map_singleton]
    rw [strategyContinuationLabel_append]
    have out := outputs (branchNode env n) (env n) h
    simpa only [leftSourceHistory,leftInputHistory,List.map_append,List.map_singleton,
      List.append_assoc] using congrArg
      (leaderAnnotationStep M objective rank
        (strategyContinuationLabel σ (leaderAnnotationStep M objective rank)
          (resetLeaderMinimum objective (header.2.2 h)) (past h)
          (leftInputHistory (branchNode env n))) ((env n).1,(env n).2,.left))
      (congrArg₂ Prod.mk out.1 out.2).symm

end Numbered

theorem closingOffer_carried_labels {H I₁ I₂ O₁ O₂ Q : Type} {B D n : Nat}
    (P : List Graph → Prop) (σ : StrategyPair I₁ I₂ O₁ O₂)
    (past word : H → EnvHistory I₁ I₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (start initial : H → Q)
    (incoming : ∀ h, initial h = strategyContinuationLabel σ step (start h) (past h) (word h))
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (implements : ∀ t s, out t s =
      (σ.one (currentView .one (closingLayerHistory (fun h => past h ++ word h) (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory (fun h => past h ++ word h) (t.val+1) s))))
    (bound : n ≤ D) (root : ClosingLayer H I₁ I₂ n)
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n)
    (realizes : ClosingOfferRealizes P (fun h => past h ++ word h) step initial out bound root move)
    (i : Fin move.1.val) :
    move.2.2.2.2 i = strategyContinuationLabel σ step
      (start (closingLayerRoot n (move.2.2.1 i)))
      (past (closingLayerRoot n (move.2.2.1 i)))
      (word (closingLayerRoot n (move.2.2.1 i)) ++ closingSuffix n (move.2.2.1 i)) := by
  rw [closingOffer_continuation_labels P σ _ step initial out implements bound root move realizes i,
    incoming,← strategyContinuationLabel_append_words]

theorem restrictClosingPolicy_implements {H J I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (implements : ∀ t s, out t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s))))
    (f : J → H) :
    ∀ t s, restrictClosingPolicy f out t s =
      (σ.one (currentView .one (closingLayerHistory (past ∘ f) (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory (past ∘ f) (t.val+1) s))) := by
  intro t s
  simpa only [restrictClosingPolicy,closingLayerHistory_map] using implements t (mapClosingLayer f _ s)

end Characterisation
