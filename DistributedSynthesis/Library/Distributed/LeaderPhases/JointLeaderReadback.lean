/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.JointLeaderShape

/-! One joint phase tree can prescribe a vector of leader responses, indexed
by the leader's observable initial group. Readback still yields one actual
strategy, preserving the complete bank and all physical input positions. -/
namespace Characterisation
open DistributedSynthesis

theorem closingBankCoherent_restrict_to_shape {H J I₁ I₂ O₁ O₂ : Type} {D : Nat}
    [DecidableEq I₁] [DecidableEq I₂] [Nonempty O₁] [Nonempty O₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H) (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D) (coherent : ClosingBankCoherent shape bank)
    (f : J → H) (other : InputShape J) (otherRep : RepresentsInputShape (past ∘ f) other) :
    ClosingBankCoherent other (bank ∘ f) := by
  obtain ⟨σ,correct⟩ := closingBankCoherent_local past shape rep L depth bank coherent
  have plans : ∀ h, closingPlanOfStrategy σ (past h) (D+1) = bank h := by
    intro h
    funext s
    exact Prod.ext (correct h s).1 (correct h s).2
  have result := closingBankOfStrategy_coherent (D:=D) σ (past ∘ f) other otherRep
  simpa only [Function.comp_apply,plans] using result

/-- All groups are read back together. The joint coherence check uses the
initial shape at depth zero and its receiver refinement at later cuts. -/
theorem jointLeaderBanks_phase_plans {H G I₁ I₂ O₁ O₂ : Type} {D : Nat}
    [Inhabited I₁] [Inhabited I₂] [DecidableEq I₁] [DecidableEq I₂]
    [Nonempty O₁] [Nonempty O₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H) (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (group : H → G) (groupExact : ∀ h k, group h = group k ↔ currentView .one (past h) = currentView .one (past k))
    (banks : List (I₂ × I₁) → ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (leader : SenderBlockStrategy I₁ (G → O₁))
    (overlap : ∀ node r h, RollingClosingOverlap (banks node h) (banks (node++[r]) h) (r.2,r.1,.right))
    (coherent : ∀ node, ClosingBankCoherent (jointLeaderShape shape (decide (node = []))) (banks node))
    (first : ∀ node (r : I₂ × I₁) h,
      (closingPlanEntry (banks node h) (fun _ => (r.2,r.1,.right)) ⟨0,by omega⟩).1 =
        leader (senderWord node) r.2 (group h)) :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ node h,
      closingPlanOfStrategy σ (rollingSourceHistory past node h) (D+1) = banks node h := by
  classical
  have each : ∀ g, ∃ τ : StrategyPair I₁ I₂ O₁ O₂, ∀ node (h : {h : H // group h = g}),
      closingPlanOfStrategy τ (rollingSourceHistory past node h.val) (D+1) = banks node h.val := by
    intro g
    let f : {h : H // group h = g} → H := Subtype.val
    let subshape := restrictInputShape shape f
    have subrep := restrictInputShape_exact past shape rep f
    have same : ∀ h k : {h : H // group h = g}, currentView .one (past (f h)) = currentView .one (past (f k)) :=
      fun h k => (groupExact _ _).mp (h.property.trans k.property.symm)
    apply rollingBanks_phase_plans (past ∘ f) subshape subrep L (fun h => depth (f h)) same
      (fun node => banks node ∘ f) (fun word input => leader word input g)
      (fun node r h => overlap node r (f h))
    · intro node
      exact closingBankCoherent_restrict_to_shape (rollingSourceHistory past node)
        (jointLeaderShape shape (decide (node = []))) (jointLeaderShape_exact past shape rep node)
        (L+node.length) (fun h => by rw [rollingSourceHistory_length,depth]) (banks node) (coherent node)
        f subshape (rollingSourceHistory_shape (past ∘ f) subshape subrep same node)
    · intro node r h
      simpa only [f,h.property] using first node r h.val
  choose strategies implementations using each
  have zero : ClosingBankCoherent shape (banks []) := by simpa [jointLeaderShape] using coherent []
  obtain ⟨initialStrategy,initialCorrect⟩ := closingBankCoherent_local past shape rep L depth (banks []) zero
  have initialPlans : ∀ h, closingPlanOfStrategy (strategies (group h)) (past h) (D+1) =
      closingPlanOfStrategy initialStrategy (past h) (D+1) := by
    intro h
    have impl := implementations (group h) [] ⟨h,rfl⟩
    simp only [rollingSourceHistory,rightInputHistory,List.map_nil,List.append_nil] at impl
    rw [impl]
    funext s
    exact (Prod.ext (initialCorrect h s).1 (initialCorrect h s).2).symm
  obtain ⟨σ,plans⟩ := leader_groups_phase_readback past L depth group
    (fun h k same => (groupExact h k).mpr same) initialStrategy strategies initialPlans
  exact ⟨σ,fun node h => (plans node h).trans (implementations (group h) node ⟨h,rfl⟩)⟩

end Characterisation
