/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.JointGraphLeaderCollector

/-! Current source and objective invariants for the jointly compressed
phase. Group entries are projected to actual outputs at their physical
rounds; the collector does not select independent objective labels. -/
namespace Characterisation
open DistributedSynthesis

theorem jointGraphLeaderMemory_rolling_sources
    {H G GQ Q I₁ I₂ O₁ O₂ : Type} {d K : Nat}
    [Fintype GQ] [DecidableEq GQ]
    (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
    (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
    (past : H → EnvHistory I₁ I₂) (a : Nat) (depth : ∀ h, List.length (past h) = a)
    (source : H → GraphRootState GQ d K)
    (sourceExact : ∀ h, GraphRootRep P M (History.graphSequence (past h)) (source h))
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (group : H → G) (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ d)
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d))
    (leader : SenderBlockStrategy I₁ (G → O₁)) (env : Nat → I₂ × I₁) (n : Nat) :
    let state := phaseMemoryRun ((source,(fun _ => true),initial),bank,true)
      (jointGraphLeaderNext group M step (fun st => chooseGraphRootNext M st .right))
      (pairPlay receiver leader env) n
    (∀ h, GraphRootRep P M (History.graphSequence (rollingSourceHistory past (branchNode env n) h))
      (state.1.1 h)) ∧
    SourceActivityOnLive P d a (a+n) (rollingSourceHistory past (branchNode env n)) state.1.2.1 ∧
    state.2.1 = receiverClosingBank bank receiver (branchNode env n) ∧
    state.2.2 = decide (n = 0) := by
  let play := pairPlay receiver leader env
  let history i := rollingSourceHistory past (branchNode env i)
  let round i := jointGraphRound (play i)
  have extension : ∀ i h, history (i+1) h = history i h ++ [round i h] := by
    intro i h
    change rollingSourceHistory past (branchNode env i ++ [env i]) h = _
    rw [rollingSourceHistory_snoc]
    rfl
  have prefixes : ∀ i j, i ≤ j → ∀ h, (history j h).take (a+i) = history i h := by
    intro i j le h
    change (rollingSourceHistory past (branchNode env j) h).take (a+i) = _
    rw [rollingSourceHistory_take past a depth, take_branchNode env i j le]
  have start : ∀ h, GraphRootRep P M (History.graphSequence (history 0 h)) (source h) := by
    intro h
    simpa only [history, rollingSourceHistory, rightInputHistory, branchNode,
      List.map_nil, List.append_nil] using sourceExact h
  have rightward : ∀ i h, (round i h).graph = .right := fun _ _ => rfl
  dsimp only
  rw [jointGraphLeaderMemory_run]
  refine ⟨?_, ?_, ?_, rfl⟩
  · exact graphLeaderBankRun_rep M P closed recognizes bounded history round extension rightward source start n
  · exact graphLeaderBankRun_activity M P closed recognizes bounded a history prefixes round extension rightward source start n
  · exact congrArg Prod.fst (jointLeaderMemory_run bank receiver leader env n)

theorem jointGraphLeaderMemory_rolling_labels
    {H G GQ Q I₁ I₂ O₁ O₂ : Type} {d K : Nat}
    (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
    (advance : GraphRootState GQ d K → GraphRootState GQ d K)
    (past : H → EnvHistory I₁ I₂) (source : H → GraphRootState GQ d K)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (initial : H → Q)
    (group : H → G) (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ d)
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d))
    (leader : SenderBlockStrategy I₁ (G → O₁)) (σ : StrategyPair I₁ I₂ O₁ O₂)
    (implements : ∀ node r h,
      σ.one (currentView .one (rollingSourceHistory past (node++[r]) h)) =
        leader (senderWord node) r.2 (group h) ∧
      σ.two (currentView .two (rollingSourceHistory past (node++[r]) h)) = (receiver node r).1 h)
    (start : ∀ h, initial h = strategyHistoryLabel σ step q₀ (past h))
    (env : Nat → I₂ × I₁) (n : Nat) (h : H) :
    (phaseMemoryRun ((source,(fun _ => true),initial),bank,true)
      (jointGraphLeaderNext group M step advance) (pairPlay receiver leader env) n).1.2.2 h =
      strategyHistoryLabel σ step q₀ (rollingSourceHistory past (branchNode env n) h) := by
  induction n with
  | zero =>
    simpa only [phaseMemoryRun, rollingSourceHistory, rightInputHistory, branchNode,
      List.map_nil, List.append_nil] using start h
  | succ n ih =>
    change step
      ((phaseMemoryRun ((source,(fun _ => true),initial),bank,true)
        (jointGraphLeaderNext group M step advance) (pairPlay receiver leader env) n).1.2.2 h)
      ((env n).2,(env n).1,.right)
      (leader (senderWord (branchNode env n)) (env n).2 (group h),
        (receiver (branchNode env n) (env n)).1 h) = _
    rw [ih, branchNode, rollingSourceHistory_snoc, strategyHistoryLabel_append]
    have outputs := implements (branchNode env n) (env n) h
    rw [rollingSourceHistory_snoc] at outputs
    rw [outputs.1, outputs.2]

end Characterisation
