/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockStrategy

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis

/-- Replay needs output agreement only along the chosen root's live
continuations, not on the other roots of the finite family. -/
theorem closingLayerLabels_oneRoot {H I₁ I₂ O₁ O₂ Q : Type} {D : Nat}
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
    (h : EnvHistory I₁ I₂) (i : H) (initial : H → Q)
    (source : initial i = strategyHistoryLabel σ step q₀ h)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (outputs : ∀ t s, closingLayerRoot (t.val+1) s = i →
      P (History.graphSequence (closingLayerHistory (fun _ : H => h) (t.val+1) s)) →
      out t s =
        (σ.one (currentView .one (closingLayerHistory (fun _ : H => h) (t.val+1) s)),
         σ.two (currentView .two (closingLayerHistory (fun _ : H => h) (t.val+1) s))))
    (n : Nat) (within : n ≤ D) (s : ClosingLayer H I₁ I₂ n)
    (root : closingLayerRoot n s = i)
    (live : P (History.graphSequence (closingLayerHistory (fun _ : H => h) n s))) :
    closingLayerLabels step initial out n within s =
      strategyHistoryLabel σ step q₀ (closingLayerHistory (fun _ : H => h) n s) := by
  induction n with
  | zero =>
    change s = i at root
    change initial s = strategyHistoryLabel σ step q₀ h
    rw [root]
    exact source
  | succ n ih =>
    have parentLive : P (History.graphSequence (closingLayerHistory (fun _ : H => h) n s.1)) := by
      apply closed _ [s.2.2.2]
      simpa only [closingLayerHistory,scenarioHistory,History.graphSequence,List.map_append,
        List.map_cons,List.map_nil] using live
    dsimp only [closingLayerLabels]
    rw [ih (by omega) s.1 root parentLive,outputs ⟨n,by omega⟩ s root live]
    simpa only [closingLayerHistory,scenarioHistory] using
      (strategyHistoryLabel_append σ step q₀ (closingLayerHistory (fun _ : H => h) n s.1)
        ⟨s.2.1,s.2.2.1,s.2.2.2,(),()⟩).symm

section
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq G] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
variable (tree : LabeledTree (BlockOutcome I₁ I₂ G Q B D) (BlockMove I₁ I₂ O₁ O₂ G Q B D))
variable (legal : SupportedMovesValid (blockOffers M step) (initialBlockOutcome M q₀ B D)
  (fun outcome move => BlockMoveValid M step outcome.target move) tree)
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (σ : StrategyPair I₁ I₂ O₁ O₂)
variable (implements : ∀ x : BlockPosition I₁ I₂ D, P (History.graphSequence (positionHistory x)) →
  (σ.one (currentView .one (positionHistory x)),σ.two (currentView .two (positionHistory x))) =
    positionOutput M step tree x)

include closed implements in
omit [DecidableEq G] [DecidableEq Q] in
theorem blockMachine_layer_replay (words : List (BlockInput I₁ I₂ D))
    (source : (tree (blockMachine M step tree words).1).source.objective (blockMachine M step tree words).2 =
      strategyHistoryLabel σ step q₀ (blockHistory words))
    (n : Nat) (within : n ≤ D) (s : ClosingLayer (BlockSlots B) I₁ I₂ n)
    (root : closingLayerRoot n s = (blockMachine M step tree words).2)
    (live : P (History.graphSequence (blockHistory words ++ (scenarioWord n s).val))) :
    closingLayerLabels step (tree (blockMachine M step tree words).1).source.objective
      (tree (blockMachine M step tree words).1).policy n within s =
      strategyHistoryLabel σ step q₀ (blockHistory words ++ (scenarioWord n s).val) := by
  rw [← scenarioWord_history (fun _ : BlockSlots B => blockHistory words) n s] at live ⊢
  apply closingLayerLabels_oneRoot P closed σ step q₀ (blockHistory words) _ _ source _ _ n within s root live
  intro t e rootEq alive
  have correct := implements (words,⟨t,scenarioWord (t.val+1) e⟩)
    (by simpa only [positionHistory,scenarioWord_history] using alive)
  simp only [positionHistory,positionOutput] at correct
  rw [← rootEq,wordScenario_scenarioWord] at correct
  simpa only [scenarioWord_history] using correct.symm

include legal closed recognizes implements in
theorem blockMachine_objective (words : List (BlockInput I₁ I₂ D))
    (live : P (History.graphSequence (blockHistory words))) :
    (tree (blockMachine M step tree words).1).source.objective (blockMachine M step tree words).2 =
      strategyHistoryLabel σ step q₀ (blockHistory words) := by
  induction words using List.reverseRecOn with
  | nil =>
    have source := (legal [] (publicSupport_nil _ _)).1
    change (tree []).source = initialBlockBoundary M q₀ B at source
    simp only [blockMachine_nil,blockHistory_nil,source]
    rfl
  | append_singleton words u ih =>
    have parentLive : P (History.graphSequence (blockHistory words)) := by
      apply closed _ (History.graphSequence u.val)
      simpa only [blockHistory_append,History.graphSequence,List.map_append] using live
    let state := blockMachine M step tree words
    let move := tree state.1
    let e := wordScenario state.2 u
    let outcome := actualBlockOutcome M step move e
    have supported := (blockMachine_supported M step tree q₀ legal P closed recognizes words parentLive).1
    have endLive := blockMachine_endpoint_live M step tree q₀ legal P closed recognizes words u live
    have kept := ((legal state.1 supported).2.2 e endLive).2.2 e
      ((blockComponent_self M move e).trans endLive)
    have replay := blockMachine_layer_replay M step q₀ tree P closed σ implements words (ih parentLive)
      D (Nat.le_refl _) e (wordScenario_root _ _) (by simpa only [e,scenarioWord_wordScenario,blockHistory_append] using live)
    have newSupported := (blockMachine_supported M step tree q₀ legal P closed recognizes (words++[u]) live).1
    have newSource := (legal _ newSupported).1
    rw [blockMachine_append] at newSource ⊢
    change (tree (state.1++[outcome])).source = _ at newSource
    have last : (observableAt (initialBlockOutcome M q₀ B D) (state.1++[outcome])).target = outcome.target := by
      simp [observableAt]
    rw [last] at newSource
    change (tree (state.1++[outcome])).source.objective ((move.response outcome.component).fold e) = _
    rw [newSource]
    change blockEndObjective step move ((move.response outcome.component).keep ((move.response outcome.component).fold e)) = _
    exact kept.2.trans (by simpa only [blockHistory_append,e,scenarioWord_wordScenario] using replay)

include legal closed recognizes implements in
theorem blockMachine_color (words : List (BlockInput I₁ I₂ D)) (u : BlockInput I₁ I₂ D)
    (live : P (History.graphSequence (blockHistory (words++[u])))) (χ : Q → Nat) :
    blockColor step (tree (blockMachine M step tree words).1) χ
        (wordScenario (blockMachine M step tree words).2 u) =
      blockMinimum (fun h => χ (strategyHistoryLabel σ step q₀ h)) (blockHistory words) u.val := by
  have parentLive : P (History.graphSequence (blockHistory words)) := by
    apply closed _ (History.graphSequence u.val)
    simpa only [blockHistory_append,History.graphSequence,List.map_append] using live
  have source := blockMachine_objective M step q₀ tree legal P closed recognizes σ implements words parentLive
  unfold blockColor blockMinimum
  rw [u.property]
  apply rangeMin_congr
  intro k _
  simp only [Nat.zero_add]
  congr 1
  unfold blockStateAt
  simp only [wordScenario_root,scenarioWord_wordScenario,Nat.zero_add]
  let pref : BlockInput I₁ I₂ (min k D) := ⟨u.val.take k,by simp [u.property]⟩
  have livePref : P (History.graphSequence (blockHistory words ++ pref.val)) := by
    apply closed _ (History.graphSequence (u.val.drop k))
    simpa only [pref,History.graphSequence,← List.map_append,List.append_assoc,List.take_append_drop,
      blockHistory_append] using live
  have replay := blockMachine_layer_replay M step q₀ tree P closed σ implements words source
    (min k D) (Nat.min_le_right _ _) (wordScenario (blockMachine M step tree words).2 pref)
    (wordScenario_root _ _) (by simpa only [scenarioWord_wordScenario] using livePref)
  simpa only [pref,scenarioWord_wordScenario,Nat.zero_add] using replay

end
end Characterisation.PeriodicBlocks
