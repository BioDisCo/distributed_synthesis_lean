/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedExecutionSoundness

/-! The original strategy supplies precisely the plan and output equations
used in numbered handover replay. Both directions reuse the existing
rightward extraction and role exchange. -/
namespace Characterisation
open DistributedSynthesis

theorem originalRight_readback {H G I₁ I₂ O₁ O₂ : Type} (D : Nat)
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (group : H → G) (base : G → View I₁ I₂ .one)
    (same : ∀ h, currentView .one (past h) = base (group h)) :
    (∀ node h, closingPlanOfStrategy σ (rollingSourceHistory past node h) (D+1) =
      receiverClosingBank (rollingOriginalBank σ past D []) (rollingOriginalReceiver σ past D) node h) ∧
    ∀ node r h,
      σ.one (currentView .one (rollingSourceHistory past (node++[r]) h)) =
        jointOriginalLeader σ base (senderWord node) r.2 (group h) ∧
      σ.two (currentView .two (rollingSourceHistory past (node++[r]) h)) =
        (rollingOriginalReceiver σ past D node r).1 h := by
  constructor
  · intro node h
    rw [receiverClosingBank_original]
    rfl
  · intro node r h
    exact ⟨(rollingOriginalLeader_correct σ (fun _ : Unit => past h) (base (group h))
      (fun _ => same h) node r ()).symm,rfl⟩

theorem originalLeft_readback {H G I₁ I₂ O₁ O₂ : Type} (D : Nat)
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (group : H → G) (base : G → View I₂ I₁ .one)
    (same : ∀ h, currentView .one (exchangeHistory (past h)) = base (group h)) :
    (∀ node h, closingPlanOfStrategy σ (leftSourceHistory past node h) (D+1) =
      exchangePlan (receiverClosingBank
        (rollingOriginalBank (exchangeStrategy σ) (exchangeHistory ∘ past) D [])
        (rollingOriginalReceiver (exchangeStrategy σ) (exchangeHistory ∘ past) D) node h)) ∧
    ∀ node r h,
      σ.one (currentView .one (leftSourceHistory past (node++[r]) h)) =
        (rollingOriginalReceiver (exchangeStrategy σ) (exchangeHistory ∘ past) D node r).1 h ∧
      σ.two (currentView .two (leftSourceHistory past (node++[r]) h)) =
        jointOriginalLeader (exchangeStrategy σ) base (senderWord node) r.2 (group h) := by
  have original := originalRight_readback D (exchangeStrategy σ) (exchangeHistory ∘ past) group base same
  have involution : exchangeStrategy (exchangeStrategy σ) = σ := by
    cases σ
    simp only [exchangeStrategy]
    congr 1
    · funext v
      exact congrArg _ (exchangeView_twice_one v)
    · funext v
      exact congrArg _ (exchangeView_twice_two v)
  simpa only [involution] using exchange_left_readback past group
    (rollingOriginalBank (exchangeStrategy σ) (exchangeHistory ∘ past) D [])
    (rollingOriginalReceiver (exchangeStrategy σ) (exchangeHistory ∘ past) D)
    (jointOriginalLeader (exchangeStrategy σ) base) (exchangeStrategy σ) original.1 original.2

end Characterisation
