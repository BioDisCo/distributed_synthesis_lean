/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.JointLeaderReadback
import DistributedSynthesis.Library.Distributed.LeaderPhases.OfferPreservingCompression

/-! Narrow a whole boundary family in one tree. Leader outputs are indexed
by observable initial groups; receiver outputs and closing plans cover all
roots jointly. The source observation matrix changes after the first round. -/
namespace Characterisation
open DistributedSynthesis

def jointLeaderNext {H G I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (_ : ClosingPlanBank H I₁ I₂ O₁ O₂ D × Bool)
    (letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) (G → O₁)) :
    ClosingPlanBank H I₁ I₂ O₁ O₂ D × Bool := (letter.2.1.2,false)

section
variable {H G I₁ I₂ O₁ O₂ : Type} {D : Nat}
variable [Fintype H] [DecidableEq H] [Fintype G] [DecidableEq G]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (group : H → G) (shape : InputShape H)

def jointLeaderCheck (state : ClosingPlanBank H I₁ I₂ O₁ O₂ D × Bool)
    (letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) (G → O₁)) : Bool :=
  decide (ClosingBankCoherent (jointLeaderShape shape state.2) state.1 ∧
    ClosingBankCoherent (rightRefinedShape shape) letter.2.1.2 ∧
    ∀ h, RollingClosingOverlap (state.1 h) (letter.2.1.2 h) (letter.1.2,letter.1.1,.right) ∧
      closingPlanEntry (state.1 h) (fun _ => (letter.1.2,letter.1.1,.right)) ⟨0,by omega⟩ =
        (letter.2.2 (group h),letter.2.1.1 h))

variable (M : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H → O₂) (G → O₁))
variable (initial : ClosingPlanBank H I₁ I₂ O₁ O₂ D)

def jointLeaderMonitor : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁
    (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) (G → O₁) :=
  leaderMemoryMonitor M Prod.fst (initial,true) jointLeaderNext (jointLeaderCheck group shape)

omit [Fintype G] [DecidableEq G] in
theorem jointLeaderMonitor_wins_iff
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) (G → O₁)) :
    (jointLeaderMonitor group shape M initial).WinsPlay play ↔
      M.WinsPlay (phasePhysicalPlay Prod.fst play) ∧
      ∀ n, jointLeaderCheck group shape (phaseMemoryRun (initial,true) jointLeaderNext play n) (play n) = true := by
  exact leaderMemoryMonitor_wins_iff M Prod.fst (initial,true) jointLeaderNext (jointLeaderCheck group shape) play

omit [Fintype H] [DecidableEq H] [Fintype G] [DecidableEq G] [Fintype I₁] [Fintype I₂]
    [Fintype O₁] [Fintype O₂] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem jointLeaderMemory_run
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D))
    (leader : SenderBlockStrategy I₁ (G → O₁)) (env : Nat → I₂ × I₁) (n : Nat) :
    phaseMemoryRun (initial,true) jointLeaderNext (pairPlay receiver leader env) n =
      (receiverClosingBank initial receiver (branchNode env n),decide (n = 0)) := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [branchNode,receiverClosingBank_snoc]
    rfl

variable [Inhabited I₁] [Inhabited I₂] [Nonempty O₁] [Nonempty O₂]

omit [Nonempty O₁] [Nonempty O₂] [Fintype G] [DecidableEq G] in
theorem jointLeaderMonitor_checked_step
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D))
    (leader : SenderBlockStrategy I₁ (G → O₁))
    (wins : ∀ env, (jointLeaderMonitor group shape M initial).WinsPlay (pairPlay receiver leader env))
    (node : List (I₂ × I₁)) (r : I₂ × I₁) :
    ClosingBankCoherent (jointLeaderShape shape (decide (node = []))) (receiverClosingBank initial receiver node) ∧
    ∀ h, RollingClosingOverlap (receiverClosingBank initial receiver node h)
      (receiverClosingBank initial receiver (node++[r]) h) (r.2,r.1,.right) ∧
      closingPlanEntry (receiverClosingBank initial receiver node h) (fun _ => (r.2,r.1,.right)) ⟨0,by omega⟩ =
        (leader (senderWord node) r.2 (group h),(receiver node r).1 h) := by
  obtain ⟨env,old,fresh⟩ := rollingBranch_realizes_step node r
  have checks := ((jointLeaderMonitor_wins_iff group shape M initial _).mp (wins env)).2 node.length
  rw [jointLeaderMemory_run,old] at checks
  have letter : pairPlay receiver leader env node.length = (r,receiver node r,leader (senderWord node) r.2) := by
    simp only [pairPlay,treePlay,treeOfPair,blockLabelApply,old,fresh]
  rw [letter] at checks
  have empty : (node.length = 0) = (node = []) := propext List.length_eq_zero_iff
  simp only [jointLeaderCheck,decide_eq_true_eq,empty] at checks
  exact ⟨checks.1,by simpa only [receiverClosingBank_snoc] using checks.2.2⟩

omit [Fintype G] [DecidableEq G] in
/-- One actual strategy implements the entire jointly compressed family.
The leader projects the vector to its observable initial group. -/
theorem jointLeaderMonitor_readback
    (past : H → EnvHistory I₁ I₂) (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (groupExact : ∀ h k, group h = group k ↔ currentView .one (past h) = currentView .one (past k))
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D))
    (leader : SenderBlockStrategy I₁ (G → O₁))
    (wins : ∀ env, (jointLeaderMonitor group shape M initial).WinsPlay (pairPlay receiver leader env)) :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      (∀ node h, closingPlanOfStrategy σ (rollingSourceHistory past node h) (D+1) =
        receiverClosingBank initial receiver node h) ∧
      ∀ node r h,
        σ.one (currentView .one (rollingSourceHistory past (node++[r]) h)) = leader (senderWord node) r.2 (group h) ∧
        σ.two (currentView .two (rollingSourceHistory past (node++[r]) h)) = (receiver node r).1 h := by
  have checks := jointLeaderMonitor_checked_step group shape M initial receiver leader wins
  obtain ⟨σ,plans⟩ := jointLeaderBanks_phase_plans past shape rep L depth group groupExact
    (receiverClosingBank initial receiver) leader (fun node r h => ((checks node r).2 h).1)
    (fun node => (checks node default).1)
    (fun node r h => congrArg Prod.fst ((checks node r).2 h).2)
  refine ⟨σ,plans,?_⟩
  intro node r h
  have outputs := ((checks node r).2 h).2
  rw [← plans node h,closingPlanOfStrategy_first] at outputs
  rw [rollingSourceHistory_snoc]
  exact ⟨congrArg Prod.fst outputs,congrArg Prod.snd outputs⟩

end
end Characterisation
