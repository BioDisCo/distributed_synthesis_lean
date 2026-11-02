/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.JointLeaderMonitor

/-! Every original strategy supplies the joint monitor's rolling checks.
The monitor adds no assumption of a common leader view across distinct
initial groups. The same original strategy supplies all groups' banks. -/
namespace Characterisation
open DistributedSynthesis

def jointOriginalLeader {G I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (base : G → View I₁ I₂ .one) : SenderBlockStrategy I₁ (G → O₁) :=
  fun word input g => rollingOriginalLeader σ (base g) word input

theorem receiverClosingBank_original {H I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂) (D : Nat) (node : List (I₂ × I₁)) :
    receiverClosingBank (rollingOriginalBank σ past D []) (rollingOriginalReceiver σ past D) node =
      rollingOriginalBank σ past D node := by
  cases node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node r => rw [receiverClosingBank_snoc]; rfl

section
variable {H G I₁ I₂ O₁ O₂ : Type} {D : Nat}
variable [Fintype H] [DecidableEq H] [Fintype G] [DecidableEq G]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
variable (shape : InputShape H) (rep : RepresentsInputShape past shape)
variable (group : H → G) (base : G → View I₁ I₂ .one)
variable (same : ∀ h, currentView .one (past h) = base (group h))

include rep same in
omit [DecidableEq H] [Fintype G] [DecidableEq G] [Fintype O₁] [Fintype O₂] in
theorem jointOriginal_step_check (node : List (I₂ × I₁)) (r : I₂ × I₁) :
    jointLeaderCheck group shape (rollingOriginalBank σ past D node,decide (node = []))
      (r,rollingOriginalReceiver σ past D node r,jointOriginalLeader σ base (senderWord node) r.2) = true := by
  simp only [jointLeaderCheck,decide_eq_true_eq]
  refine ⟨closingBankOfStrategy_coherent σ _ _ (jointLeaderShape_exact past shape rep node),?_,?_⟩
  · have exactShape := jointLeaderShape_exact past shape rep (node++[r])
    have coherent := closingBankOfStrategy_coherent (D:=D) σ _ _ exactShape
    simpa [jointLeaderShape,rollingOriginalReceiver,rollingOriginalBank] using coherent
  · intro h
    constructor
    · simpa only [rollingOriginalBank,rollingOriginalReceiver,rollingSourceHistory_snoc] using
        rollingClosingOverlap_ofStrategy (D:=D) σ (rollingSourceHistory past node h) (r.2,r.1,.right)
    · have leaderEq := rollingOriginalLeader_correct σ (fun _ : Unit => past h) (base (group h))
        (fun _ => same h) node r ()
      change closingPlanEntry (closingPlanOfStrategy σ (rollingSourceHistory past node h) (D+1))
          (fun _ => (r.2,r.1,.right)) ⟨0,by omega⟩ = _
      rw [closingPlanOfStrategy_first]
      change (_,_) = (rollingOriginalLeader σ (base (group h)) (senderWord node) r.2,_)
      rw [leaderEq,rollingSourceHistory_snoc]
      simp [rollingOriginalReceiver,rollingSourceHistory,rightInputHistory,List.append_assoc]

include rep same in
omit [Fintype G] [DecidableEq G] in
theorem jointOriginal_monitor_wins
    (M : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H → O₂) (G → O₁))
    (physical : ∀ env, M.WinsPlay (phasePhysicalPlay Prod.fst
      (pairPlay (rollingOriginalReceiver σ past D) (jointOriginalLeader σ base) env))) :
    ∀ env, (jointLeaderMonitor group shape M (rollingOriginalBank σ past D [])).WinsPlay
      (pairPlay (rollingOriginalReceiver σ past D) (jointOriginalLeader σ base) env) := by
  intro env
  apply (jointLeaderMonitor_wins_iff group shape M _ _).mpr
  refine ⟨physical env,?_⟩
  intro n
  rw [jointLeaderMemory_run,receiverClosingBank_original]
  have nodeEmpty : (branchNode env n = []) ↔ n = 0 := by
    rw [← List.length_eq_zero_iff]
    have length : (branchNode env n).length = n := by
      induction n with
      | zero => rfl
      | succ n ih => simp [branchNode,ih]
    rw [length]
  have result := jointOriginal_step_check σ past shape rep group base same (D:=D) (branchNode env n) (env n)
  simpa only [pairPlay,treePlay,treeOfPair,blockLabelApply,propext nodeEmpty] using result

end
end Characterisation
