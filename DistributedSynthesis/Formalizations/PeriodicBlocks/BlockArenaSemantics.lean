/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockScenarios

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis

section
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (move : BlockMove I₁ I₂ O₁ O₂ G Q B D)
variable (past : BlockSlots B → EnvHistory I₁ I₂)
variable (shape : RepresentsInputShape past move.source.shape)

include shape in
omit [Fintype I₁] [Fintype I₂] in
theorem blockEndShape_exact :
    RepresentsInputShape (closingLayerHistory past D) (blockEndShape move) :=
  closingLayerShape_exact past move.source.shape shape D

theorem blockComponent_self (e : BlockEnd I₁ I₂ B D) :
    blockComponent M move e e = blockEndLive M move e := by
  simp [blockComponent, closingComponentMask, SimpleGraph.Reachable.refl]

theorem blockComponent_eq_of_views (e f : BlockEnd I₁ I₂ B D)
    (liveE : blockEndLive M move e = true) (liveF : blockEndLive M move f = true)
    (p : Proc) (same : blockEndShape move p e f = true) :
    blockComponent M move e = blockComponent M move f := by
  let graph := closingObservationGraph (blockEndShape move) (blockEndLive M move)
  have reach : graph.Reachable e f := by
    by_cases eq : e = f
    · subst f; exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ⟨eq,liveE,liveF,p,Or.inl same⟩
  funext t
  apply Bool.eq_iff_iff.mpr
  simp only [blockComponent, closingComponentMask, Bool.and_eq_true, decide_eq_true_eq]
  exact and_congr_right (fun _ => ⟨fun r => reach.symm.trans r, fun r => reach.trans r⟩)

include shape in
theorem blockComponent_connected (P : List Graph → Prop)
    (graphExact : ∀ e, blockEndLive M move e = true ↔
      P (History.graphSequence (closingLayerHistory past D e)))
    (e f : BlockEnd I₁ I₂ B D) (inside : blockComponent M move e f = true) :
    InputConnected P (closingLayerHistory past D e) (closingLayerHistory past D f) := by
  have decoded : blockEndLive M move f = true ∧
      (closingObservationGraph (blockEndShape move) (blockEndLive M move)).Reachable e f := by
    simpa only [blockComponent, closingComponentMask, Bool.and_eq_true, decide_eq_true_eq] using inside
  have path := ((closingObservationGraph (blockEndShape move) (blockEndLive M move)).reachable_iff_reflTransGen e f).mp decoded.2
  exact Relation.ReflTransGen.lift (closingLayerHistory past D)
    (fun _ _ edge => closing_graph_adjacent_sound P _ _ (blockEndShape_exact move past shape)
      _ graphExact edge) path

include shape in
omit [Fintype I₁] [Fintype I₂] [DecidablePred (· ∈ M.accept)] in
theorem blockResponse_preserves_views (mask : ComponentMask I₁ I₂ B D)
    (valid : ResponseValid M step move mask) (e f : BlockEnd I₁ I₂ B D)
    (insideE : mask e = true) (insideF : mask f = true) (p : Proc)
    (same : currentView p (closingLayerHistory past D e) =
      currentView p (closingLayerHistory past D f)) :
    currentView p (closingLayerHistory past D ((move.response mask).keep ((move.response mask).fold e))) =
      currentView p (closingLayerHistory past D ((move.response mask).keep ((move.response mask).fold f))) :=
  (blockEndShape_exact move past shape p _ _).mp
    (valid.2.1 p e f insideE insideF ((blockEndShape_exact move past shape p e f).mpr same))

include shape in
omit [Fintype I₁] [Fintype I₂] [DecidablePred (· ∈ M.accept)] in
theorem blockTarget_shape (mask : ComponentMask I₁ I₂ B D) :
    RepresentsInputShape (closingLayerHistory past D ∘ (move.response mask).keep)
      (blockTarget M step move mask).shape :=
  restrictInputShape_exact _ _ (blockEndShape_exact move past shape) _

omit [Fintype I₁] [Fintype I₂] [DecidablePred (· ∈ M.accept)] in
theorem blockTarget_graph (mask : ComponentMask I₁ I₂ B D)
    (graphExact : ∀ i, move.source.graph i = M.eval (History.graphSequence (past i))) (j : BlockSlots B) :
    (blockTarget M step move mask).graph j =
      M.eval (History.graphSequence (closingLayerHistory past D ((move.response mask).keep j))) :=
  closingLayerLabels_recognizer M past move.source.graph graphExact move.policy D (Nat.le_refl _) _

def blockStateAt (e : BlockEnd I₁ I₂ B D) (k : Nat) : Q :=
  let u := scenarioWord D e
  let pref : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) (min k D) :=
    ⟨u.val.take k, by simp [u.property]⟩
  closingLayerLabels step move.source.objective move.policy (min k D) (Nat.min_le_right _ _)
    (wordScenario (closingLayerRoot D e) pref)

def blockColor (χ : Q → Nat) (e : BlockEnd I₁ I₂ B D) : Nat :=
  rangeMin (fun k => χ (blockStateAt step move e k)) 0 (D-1)

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem blockColor_le (χ : Q → Nat) (e : BlockEnd I₁ I₂ B D) :
    blockColor step move χ e ≤ χ (move.source.objective (closingLayerRoot D e)) := by
  exact rangeMin_le _ 0 (D-1) 0 (Nat.zero_le _)

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem blockStateAt_strategy (σ : StrategyPair I₁ I₂ O₁ O₂) (q₀ : Q)
    (source : ∀ i, move.source.objective i = strategyHistoryLabel σ step q₀ (past i))
    (outputs : ∀ t s, move.policy t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s))))
    (e : BlockEnd I₁ I₂ B D) (k : Nat) :
    blockStateAt step move e k =
      strategyHistoryLabel σ step q₀ (past (closingLayerRoot D e) ++ (scenarioWord D e).val.take k) := by
  unfold blockStateAt
  rw [closingLayerLabels_strategyHistory σ past step q₀ _ source _ outputs, wordScenario_history]

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem blockColor_strategy (σ : StrategyPair I₁ I₂ O₁ O₂) (q₀ : Q)
    (source : ∀ i, move.source.objective i = strategyHistoryLabel σ step q₀ (past i))
    (outputs : ∀ t s, move.policy t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s))))
    (χ : Q → Nat) (e : BlockEnd I₁ I₂ B D) :
    blockColor step move χ e =
      blockMinimum (fun h => χ (strategyHistoryLabel σ step q₀ h))
        (past (closingLayerRoot D e)) (scenarioWord D e).val := by
  simp only [blockColor, blockMinimum, (scenarioWord D e).property,
    blockStateAt_strategy step move past σ q₀ source outputs]

end
end Characterisation.PeriodicBlocks
