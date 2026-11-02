/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderGroupReadback

/-! Select finite phase tables for every initial leader-view group and
implement them jointly. The common original strategy supplies the initial
promises needed to couple the groups. No phase endpoint is supplied to
either process, and every table is evaluated at its physical round. -/
namespace Characterisation
open DistributedSynthesis

theorem ImplementsLeaderPhase.of_same_plans {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    {σ τ : StrategyPair I₁ I₂ O₁ O₂} {past : H → EnvHistory I₁ I₂}
    {initial : ClosingPlanBank H I₁ I₂ O₁ O₂ D}
    {receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D)}
    {leader : SenderBlockStrategy I₁ O₁}
    (impl : ImplementsLeaderPhase σ past initial receiver leader)
    (plans : ∀ node h, closingPlanOfStrategy τ (rollingSourceHistory past node h) (D+1) =
      closingPlanOfStrategy σ (rollingSourceHistory past node h) (D+1)) :
    ImplementsLeaderPhase τ past initial receiver leader := by
  refine ⟨fun node h => (plans node h).trans (impl.1 node h),?_⟩
  intro node r h
  have output := congrArg
    (fun plan => closingPlanEntry plan (fun _ => (r.2,r.1,Graph.right)) ⟨0,by omega⟩)
    (plans node h)
  dsimp only at output
  rw [closingPlanOfStrategy_first,closingPlanOfStrategy_first,
    ← rollingSourceHistory_snoc] at output
  exact ⟨(congrArg Prod.fst output).trans (impl.2 node r h).1,
    (congrArg Prod.snd output).trans (impl.2 node r h).2⟩

section Groups
variable {G I₁ I₂ O₁ O₂ : Type} {H : G → Type} {D : Nat}
variable [∀ g, Fintype (H g)] [∀ g, DecidableEq (H g)]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (M : ∀ g, BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H g → O₂) O₁)
variable (shape : ∀ g, InputShape (H g))

/-- Joint choices still range over a finite alphabet. Its definition
depends on the finite group interfaces and monitors, not on phase length. -/
theorem finite_leader_group_moves [Fintype G] [Nonempty I₁] :
    Finite (∀ g, CoherentLeaderPhaseMove (D:=D) (M g) (shape g)) := by
  infer_instance

variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]

/-- Compress all groups of one boundary together. The leader's initial
view identifies its group; the receiver may initially confuse groups.
One common initial bank resolves precisely that remaining ambiguity. -/
theorem finite_implementable_leader_groups
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : ∀ g, H g → EnvHistory I₁ I₂)
    (rep : ∀ g, RepresentsInputShape (past g) (shape g))
    (L : Nat) (depth : ∀ g h, List.length (past g h) = L)
    (base : G → View I₁ I₂ .one) (distinct : Function.Injective base)
    (same : ∀ g h, currentView .one (past g h) = base g)
    (physical : ∀ g env, (M g).WinsPlay (phasePhysicalPlay Prod.fst
      (pairPlay (rollingOriginalReceiver σ (past g) D) (rollingOriginalLeader σ (base g)) env))) :
    ∃ move : ∀ g, CoherentLeaderPhaseMove (D:=D) (M g) (shape g),
      ∃ τ : StrategyPair I₁ I₂ O₁ O₂, ∀ g,
        (move g).1 = rollingOriginalBank σ (past g) D [] ∧
        ImplementsLeaderPhase τ (past g) (move g).1
          (coherentMoveReceiver (M g) (shape g) (move g))
          (coherentMoveLeader (M g) (shape g) (move g)) ∧
        ∀ env, (M g).WinsPlay (phasePhysicalPlay Prod.fst
          (pairPlay (coherentMoveReceiver (M g) (shape g) (move g))
            (coherentMoveLeader (M g) (shape g) (move g)) env)) := by
  classical
  have each := fun g => finite_implementable_leader_phase (M g) (shape g) σ (past g)
    (rep g) L (depth g) (base g) (same g) (physical g)
  choose move initial _ strategies implementations winning using each
  let roots : (Σ g, H g) → EnvHistory I₁ I₂ := fun s => past s.1 s.2
  have observable : ∀ s t : Σ g, H g,
      currentView .one (roots s) = currentView .one (roots t) → s.1 = t.1 := by
    intro s t eq
    exact distinct ((same s.1 s.2).symm.trans (eq.trans (same t.1 t.2)))
  have initialPlans : ∀ s : Σ g, H g,
      closingPlanOfStrategy (strategies s.1) (roots s) (D+1) =
        closingPlanOfStrategy σ (roots s) (D+1) := by
    intro s
    have plans := (implementations s.1).1 [] s.2
    simpa only [receiverClosingBank,List.getLast?_nil,initial,
      rollingOriginalBank,rollingSourceHistory,rightInputHistory,List.map_nil,List.append_nil,roots]
      using plans
  obtain ⟨τ,plans⟩ := leader_groups_phase_readback roots L (fun s => depth s.1 s.2)
    Sigma.fst observable σ strategies initialPlans
  refine ⟨move,τ,fun g => ⟨initial g,?_,winning g⟩⟩
  exact (implementations g).of_same_plans (fun node h => plans node ⟨g,h⟩)

end Groups
end Characterisation
