/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RollingLeaderTables

/-! Extract rolling promises from an arbitrary local strategy. Receiver
inputs are available only to the receiver restriction. The leader restriction
reuses the checked own-input strategy tree. This proves that the rolling
checks impose no extra restriction on such one-way strategy restrictions. -/
namespace Characterisation
open DistributedSynthesis

def rightInputHistory {I₁ I₂ : Type} (node : List (I₂ × I₁)) : EnvHistory I₁ I₂ :=
  node.map (fun r => ⟨r.2,r.1,.right,(),()⟩)

def rollingSourceHistory {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂)
    (node : List (I₂ × I₁)) (h : H) : EnvHistory I₁ I₂ := past h ++ rightInputHistory node

theorem rollingSourceHistory_snoc {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂)
    (node : List (I₂ × I₁)) (r : I₂ × I₁) (h : H) :
    rollingSourceHistory past (node ++ [r]) h =
      rollingSourceHistory past node h ++ [⟨r.2,r.1,.right,(),()⟩] := by
  simp [rollingSourceHistory,rightInputHistory,List.append_assoc]

def rollingOriginalReceiver {H I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂) (D : Nat) :
    ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) :=
  fun node r =>
    (fun h => σ.two (currentView .two (rollingSourceHistory past (node ++ [r]) h)),
      fun h => closingPlanOfStrategy σ (rollingSourceHistory past (node ++ [r]) h) (D+1))

def rollingOriginalLeader {I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (base : View I₁ I₂ .one) :
    SenderBlockStrategy I₁ O₁ :=
  fun word input => leaderStrategyTree σ.one base (word.map PSum.inl) (PSum.inl input)

theorem rollingOriginalLeader_correct {H I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (base : View I₁ I₂ .one) (same : ∀ h, currentView .one (past h) = base)
    (node : List (I₂ × I₁)) (r : I₂ × I₁) (h : H) :
    rollingOriginalLeader σ base (senderWord node) r.2 =
      σ.one (currentView .one (rollingSourceHistory past (node ++ [r]) h)) := by
  have outgoing : ∀ s ∈ rightInputHistory node, s.graph = leaderOutgoingGraph .one := by
    intro s member
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp member
    rfl
  have correct := leaderStrategyTree_correct .one σ.one (past h) (rightInputHistory node)
    ⟨r.2,r.1,.right,(),()⟩ outgoing rfl
  rw [same h] at correct
  simpa [rollingOriginalLeader,rollingSourceHistory,rightInputHistory,inputWord,
    RoundRecord.input,senderWord,List.map_map,List.append_assoc] using correct

def rollingOriginalBank {H I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂) (D : Nat)
    (node : List (I₂ × I₁)) : ClosingPlanBank H I₁ I₂ O₁ O₂ D :=
  fun h => closingPlanOfStrategy σ (rollingSourceHistory past node h) (D+1)

theorem closingPlanOfStrategy_first {I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : EnvHistory I₁ I₂) (D : Nat)
    (r : I₁ × I₂ × Graph) :
    closingPlanEntry (closingPlanOfStrategy σ past (D+1)) (fun _ => r) ⟨0,by omega⟩ =
      (σ.one (currentView .one (past ++ [⟨r.1,r.2.1,r.2.2,(),()⟩])),
       σ.two (currentView .two (past ++ [⟨r.1,r.2.1,r.2.2,(),()⟩]))) := by
  simp [closingPlanEntry,closingPlanOfStrategy,windowHistory,List.ofFn_succ]

/-- Each concrete finite input history supplies a legal replenishment,
including agreement with the leader's single output at every hidden root. -/
theorem rollingOriginal_step_check {H I₁ I₂ O₁ O₂ : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂] [DecidableEq O₁] [DecidableEq O₂]
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂) (D : Nat)
    (base : View I₁ I₂ .one) (same : ∀ h, currentView .one (past h) = base)
    (node : List (I₂ × I₁)) (r : I₂ × I₁) :
    rollingLeaderCheck (rollingOriginalBank σ past D node)
      (r,rollingOriginalReceiver σ past D node r,rollingOriginalLeader σ base (senderWord node) r.2) = true := by
  simp only [rollingLeaderCheck,decide_eq_true_eq]
  intro h
  constructor
  · simpa only [rollingOriginalBank,rollingOriginalReceiver,rollingSourceHistory_snoc] using
      rollingClosingOverlap_ofStrategy (D:=D) σ (rollingSourceHistory past node h) (r.2,r.1,.right)
  · rw [rollingOriginalLeader_correct σ past base same node r h]
    simpa only [rollingOriginalBank,rollingOriginalReceiver,rollingSourceHistory_snoc] using
      closingPlanOfStrategy_first σ (rollingSourceHistory past node h) D (r.2,r.1,.right)

theorem rollingOriginal_memory {H I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂) (D : Nat)
    (base : View I₁ I₂ .one) (env : Nat → I₂ × I₁) (n : Nat) :
    phaseMemoryRun (rollingOriginalBank σ past D []) rollingLeaderNext
      (pairPlay (rollingOriginalReceiver σ past D) (rollingOriginalLeader σ base) env) n =
        rollingOriginalBank σ past D (branchNode env n) := by
  cases n with
  | zero => rfl
  | succ n => rfl

/-- The finite overlap checks hold on every receiver-input thread of an
arbitrary original strategy, with no finite-memory assumption on that strategy. -/
theorem rollingOriginal_checks {H I₁ I₂ O₁ O₂ : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂] [DecidableEq O₁] [DecidableEq O₂]
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂) (D : Nat)
    (base : View I₁ I₂ .one) (same : ∀ h, currentView .one (past h) = base)
    (env : Nat → I₂ × I₁) (n : Nat) :
    rollingLeaderCheck
      (phaseMemoryRun (rollingOriginalBank σ past D []) rollingLeaderNext
        (pairPlay (rollingOriginalReceiver σ past D) (rollingOriginalLeader σ base) env) n)
      (pairPlay (rollingOriginalReceiver σ past D) (rollingOriginalLeader σ base) env n) = true := by
  rw [rollingOriginal_memory]
  exact rollingOriginal_step_check σ past D base same (branchNode env n) (env n)

end Characterisation
