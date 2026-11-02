/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ComponentEquivalence
import DistributedSynthesis.Formalizations.ComponentGames.Representatives

/- The bounded-game invariant in the paper: q_n=q_f, the played rule is the
pullback of f, and the replacement fixes its image. -/
namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
variable (σ : StrategyPair I₁ I₂ O₁ O₂)

structure Faithful (m : Move I₁ I₂ O₁ O₂ Q D) : Prop where
  states : ∀ h, m.source.state h = strategyHistoryLabel σ step q₀ h.val
  rule : m.rule = restrictClosingPolicy m.replacement (algorithmRule σ m.source)
  idempotent : ∀ h, m.replacement (m.replacement h) = m.replacement h
  checks : ReplacementChecks m.source.shape M
    (fun h => M.eval (History.graphSequence h.val)) step m.source.state m.rule m.replacement

theorem faithful_replay (m : Move I₁ I₂ O₁ O₂ Q D) (faithful : Faithful M step q₀ σ m)
    (n : Nat) (within : n ≤ D) (e : ClosingLayer m.source.Root I₁ I₂ n) :
    closingLayerLabels step m.source.state m.rule n within e =
      strategyHistoryLabel σ step q₀
        (closingLayerHistory m.source.past n (mapClosingLayer m.replacement n e)) := by
  have start : m.source.state ∘ m.replacement = m.source.state := by
    funext h
    exact (faithful.checks.2 ⟨0,by omega⟩ h).2.symm
  rw [faithful.rule]
  have replay := closingLayerLabels_restrict m.replacement step m.source.state
    (algorithmRule σ m.source) n within e
  rw [start] at replay
  rw [replay]
  exact closingLayerLabels_strategyHistory σ m.source.past step q₀ m.source.state
    faithful.states (algorithmRule σ m.source) (fun _ _ => rfl) n within _

theorem retained_fixed (m : Move I₁ I₂ O₁ O₂ Q D)
    (idem : ∀ h, m.replacement (m.replacement h) = m.replacement h)
    (h : m.source.Root) (inside : h ∈ retained m) : m.replacement h = h := by
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp inside
  exact idem a

theorem faithful_retained_replay (m : Move I₁ I₂ O₁ O₂ Q D) (faithful : Faithful M step q₀ σ m)
    (n : Nat) (within : n ≤ D) (e : ClosingLayer m.source.Root I₁ I₂ n)
    (inside : closingLayerRoot n e ∈ retained m) :
    closingLayerLabels step m.source.state m.rule n within e =
      strategyHistoryLabel σ step q₀ (closingLayerHistory m.source.past n e) := by
  rw [faithful_replay M step q₀ σ m faithful n within e,
    scenarioWord_history,scenarioWord_history,closingLayerRoot_map,scenarioWord_map,
    retained_fixed m faithful.idempotent _ inside]

theorem faithful_next_states (m : Move I₁ I₂ O₁ O₂ Q D) (faithful : Faithful M step q₀ σ m)
    (P : Position I₁ I₂ Q D) (next : Next M step m P) :
    ∀ h : P.Root, P.state h = strategyHistoryLabel σ step q₀ h.val := by
  intro h
  obtain ⟨_,K,component,histories,labels⟩ := next
  have mem : h.val ∈ K.image m.source.history := by rw [← histories]; exact h.property
  obtain ⟨e,he,history⟩ := Finset.mem_image.mp mem
  have alive := component_member_live M m K component e he
  simp only [extensionLive,decide_eq_true_eq] at alive
  exact (labels h e he history.symm).trans
    ((faithful_retained_replay M step q₀ σ m faithful D (Nat.le_refl _) e alive.1).trans
      (congrArg (strategyHistoryLabel σ step q₀) history))

theorem faithful_stateAt (m : Move I₁ I₂ O₁ O₂ Q D) (faithful : Faithful M step q₀ σ m)
    (h : m.source.Root) (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D) (t : Nat) :
    stateAt step m h w t = strategyHistoryLabel σ step q₀ ((m.replacement h).val ++ w.val.take t) := by
  unfold stateAt
  rw [faithful_replay M step q₀ σ m faithful, mapClosingLayer_wordScenario,wordScenario_history]
  rfl

/-- On the participating roots of a previous component, the key's old rule
is f itself. Equal keys therefore preserve f's entire preceding block. -/
theorem faithful_key_replay (m : Move I₁ I₂ O₁ O₂ Q D) (faithful : Faithful M step q₀ σ m)
    (K : Finset m.source.End) (component : IsComponent M m K)
    (a b : participatingRoots m K) (same : componentKey M m K a = componentKey M m K b)
    (u : EnvHistory I₁ I₂) (within : List.length u ≤ D) :
    strategyHistoryLabel σ step q₀ (a.val.val ++ u) =
      strategyHistoryLabel σ step q₀ (b.val.val ++ u) := by
  have kept (i : participatingRoots m K) : i.val ∈ retained m := by
    obtain ⟨e,inside,eq⟩ := Finset.mem_image.mp i.property
    have alive := component_member_live M m K component e inside
    simp only [extensionLive,decide_eq_true_eq] at alive
    exact eq ▸ alive.1
  let w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) (List.length u) := ⟨u,rfl⟩
  have replay := policyCode_replay step m.source.state m.rule a.val b.val
    (congrArg BlockType.objectiveState same) (congrArg BlockType.rule same)
    (List.length u) within (wordScenario a.val w) (wordScenario_root _ _)
  rw [mapClosingLayer_wordScenario] at replay
  rw [faithful_retained_replay M step q₀ σ m faithful _ within _
      (by simpa only [wordScenario_root] using kept a),
    faithful_retained_replay M step q₀ σ m faithful _ within _
      (by simpa only [wordScenario_root] using kept b),wordScenario_history,wordScenario_history] at replay
  exact replay
end
end Characterisation.ComponentGames.HistoryGame
