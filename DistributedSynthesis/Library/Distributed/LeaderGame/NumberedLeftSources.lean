/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeftExtraction

/-! The leftward table's finite graph states and activity bits describe
actual histories under the original graph language and boundary selector. -/
namespace Characterisation
open DistributedSynthesis

theorem leftSourceHistory_snoc {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂)
    (node : List (I₁ × I₂)) (r : I₁ × I₂) (h : H) :
    leftSourceHistory past (node++[r]) h = leftSourceHistory past node h ++ [⟨r.1,r.2,.left,(),()⟩] := by
  simp only [leftSourceHistory,leftInputHistory,List.map_append,List.map_singleton,List.append_assoc]

theorem leftSourceHistory_take {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (node : List (I₁ × I₂)) (h : H) (n : Nat) :
    (leftSourceHistory past node h).take (L+n) = leftSourceHistory past (node.take n) h := by
  unfold leftSourceHistory
  rw [List.take_append,List.take_of_length_le (by rw [depth]; omega),depth,Nat.add_sub_cancel_left]
  simp only [leftInputHistory,List.map_take]

theorem continuationScenario_left_history {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (h : H) (env : Nat → I₁ × I₂) (n : Nat) :
    closingLayerHistory past n (continuationScenario h (fun i => ((env i).1,(env i).2,Graph.left)) n) =
      leftSourceHistory past (branchNode env n) h := by
  induction n with
  | zero => simp [continuationScenario,closingLayerHistory,leftSourceHistory,leftInputHistory,branchNode]
  | succ n ih =>
    change closingLayerHistory past n
      (continuationScenario h (fun i => ((env i).1,(env i).2,Graph.left)) n) ++ [_] = _
    rw [ih,branchNode,leftSourceHistory_snoc]
    rfl

theorem leftLeaderShape_exact {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂)
    (shape : InputShape H) (rep : RepresentsInputShape past shape) (node : List (I₁ × I₂)) :
    RepresentsInputShape (leftSourceHistory past node)
      (exchangeShape (jointLeaderShape (exchangeShape shape) (decide (node = [])))) := by
  have first := jointLeaderShape_exact (exchangeHistory ∘ past) (exchangeShape shape)
    (exchangeShape_exact past shape rep) node
  have second := exchangeShape_exact (rollingSourceHistory (exchangeHistory ∘ past) node) _ first
  have histories : exchangeHistory ∘ rollingSourceHistory (exchangeHistory ∘ past) node =
      leftSourceHistory past node := by
    funext h
    rw [Function.comp_apply,← exchange_leftSourceHistory,exchangeHistory_twice]
  rwa [histories] at second

section
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable (rank : objective.State → Fin (C+1))
variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
variable (bank : ClosingPlanBank (Fin header.1.val) I₂ I₁ O₂ O₁ d)
variable (receiver : ReceiverBlockStrategy I₁ I₂ (RollingReceiverOutput (Fin header.1.val) I₂ I₁ O₂ O₁ d))
variable (leader : SenderBlockStrategy I₂ (ShapeLeaderGroup header.2.1 .two → O₂))
variable (env : Nat → I₁ × I₂)

theorem numberedLeftPhaseRun_graphs (n : Nat) (h : Fin header.1.val) :
    (numberedLeftPhaseRun M objective rank header bank receiver leader env n).1.1 h =
      closingGraphRun M (fun i => (header.2.2 i).1.1) n
        (continuationScenario h (fun i => ((env i).1,(env i).2,Graph.left)) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change chooseGraphRootNext M
      ((numberedLeftPhaseRun M objective rank header bank receiver leader env n).1.1 h) .left = _
    rw [ih]
    rfl

theorem numberedLeftPhaseRun_fields (n : Nat) :
    let state := numberedLeftPhaseRun M objective rank header bank receiver leader env
    (state n).1.2.1 = rootActivityRun (fun i h => graphRootStop M ((state i).1.1 h) .left) n ∧
    (state n).2.1 = receiverClosingBank bank receiver (branchNode env n) ∧
    (state n).2.2 = decide (n = 0) := by
  dsimp only
  induction n with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    refine ⟨?_,?_,rfl⟩
    · change rootActivityNext
        ((numberedLeftPhaseRun M objective rank header bank receiver leader env n).1.2.1) _ = _
      rw [ih.1]
      rfl
    · rw [branchNode,receiverClosingBank_snoc]
      rfl

variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (past : Fin header.1.val → EnvHistory I₁ I₂) (a : Nat) (depth : ∀ h, List.length (past h) = a)
variable (graphs : ∀ h, GraphRootRep P M (History.graphSequence (past h)) (header.2.2 h).1.1)

include closed recognizes bounded depth graphs in
theorem numberedLeftPhaseRun_sources (n : Nat) :
    let state := numberedLeftPhaseRun M objective rank header bank receiver leader env n
    (∀ h, GraphRootRep P M (History.graphSequence (leftSourceHistory past (branchNode env n) h))
      (state.1.1 h)) ∧
    SourceActivityOnLive P d a (a+n) (leftSourceHistory past (branchNode env n)) state.1.2.1 ∧
    state.2.1 = receiverClosingBank bank receiver (branchNode env n) ∧
    state.2.2 = decide (n = 0) := by
  let state := numberedLeftPhaseRun M objective rank header bank receiver leader env
  have represented : ∀ i h, GraphRootRep P M
      (History.graphSequence (leftSourceHistory past (branchNode env i) h)) ((state i).1.1 h) := by
    intro i h
    rw [numberedLeftPhaseRun_graphs]
    have result := closingGraphRun_rep M P closed recognizes bounded past
      (fun j => (header.2.2 j).1.1) graphs i
      (continuationScenario h (fun j => ((env j).1,(env j).2,Graph.left)) i)
    rwa [continuationScenario_left_history] at result
  have fields := numberedLeftPhaseRun_fields M objective rank header bank receiver leader env n
  refine ⟨represented n,?_,fields.2⟩
  rw [fields.1]
  apply rootActivityRun_history_on_live P closed d a (fun i => leftSourceHistory past (branchNode env i))
    (fun i j le h => by rw [leftSourceHistory_take past a depth,take_branchNode env i j le])
  intro i h live
  have next : leftSourceHistory past (branchNode env (i+1)) h =
      leftSourceHistory past (branchNode env i) h ++ [⟨(env i).1,(env i).2,.left,(),()⟩] := by
    rw [branchNode,leftSourceHistory_snoc]
  have result := graphRootStop_exact_on_live M P closed recognizes _ ((state i).1.1 h) (represented i h)
    ⟨(env i).1,(env i).2,.left,(),()⟩ (by rwa [← next])
  rwa [← next] at result

end
end Characterisation
