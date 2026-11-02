/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ComponentCoverage

/- Replay of the single distributed algorithm constructed from all finite
play prescriptions, followed by the paper's fixed-block parity argument. -/
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
variable (tree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D))
variable (legal : SupportedMovesValid (offers M step) (Position.initial q₀) (Legal M step .component) tree)
variable (closed : PrefixClosed (fun g => M.eval g ∈ M.accept))
variable (σ : StrategyPair I₁ I₂ O₁ O₂)
variable (implements : ∀ x : Prescription M step tree,
  (σ.one (currentView .one (prescribedHistory M step tree x)),
   σ.two (currentView .two (prescribedHistory M step tree x))) = prescribedOutput M step tree x)

include closed implements in
theorem controller_layer_replay (node : List (Position I₁ I₂ Q D))
    (supported : publicSupport (offers M step) tree node = true)
    (states : ∀ h, (tree node).source.state h = strategyHistoryLabel σ step q₀ h.val)
    (n : Nat) (within : n ≤ D) (e : ClosingLayer (tree node).source.Root I₁ I₂ n)
    (live : M.eval (History.graphSequence (closingLayerHistory (tree node).source.past n e)) ∈ M.accept) :
    closingLayerLabels step (tree node).source.state (tree node).rule n within e =
      strategyHistoryLabel σ step q₀ (closingLayerHistory (tree node).source.past n e) := by
  let a := closingLayerRoot n e
  have hist (k : Nat) (s : ClosingLayer (tree node).source.Root I₁ I₂ k)
      (root : closingLayerRoot k s = a) :
      closingLayerHistory (tree node).source.past k s =
        closingLayerHistory (fun _ : (tree node).source.Root => a.val) k s := by
    rw [scenarioWord_history,scenarioWord_history,root]; rfl
  rw [hist n e rfl] at live ⊢
  apply closingLayerLabels_oneRoot (fun g => M.eval g ∈ M.accept) closed σ step q₀ a.val a
    (tree node).source.state (states a) (tree node).rule _ n within e rfl live
  intro t s root alive
  have eq := hist (t.val+1) s root
  have actualLive : M.eval (History.graphSequence (closingLayerHistory (tree node).source.past (t.val+1) s)) ∈ M.accept := by
    rw [eq]; exact alive
  have outputs := implements ⟨node,supported,t,s,actualLive⟩
  change (σ.one (currentView .one (closingLayerHistory (tree node).source.past (t.val+1) s)),
    σ.two (currentView .two (closingLayerHistory (tree node).source.past (t.val+1) s))) = (tree node).rule t s at outputs
  rw [eq] at outputs
  exact outputs.symm

include legal closed implements in
theorem controller_states (node : List (Position I₁ I₂ Q D))
    (supported : publicSupport (offers M step) tree node = true)
    (h : (tree node).source.Root) :
    (tree node).source.state h = strategyHistoryLabel σ step q₀ h.val := by
  induction node using List.reverseRecOn with
  | nil =>
    have source := (legal [] supported).1
    change (tree []).source = Position.initial q₀ at source
    revert h
    rw [source]
    intro h
    have empty : h.val = [] := Finset.mem_singleton.mp h.property
    change q₀ = _
    rw [empty]; rfl
  | append_singleton node P ih =>
    have both : publicSupport (offers M step) tree node = true ∧ offers M step (tree node) P = true := by
      simpa only [publicSupport_append,Bool.and_eq_true] using supported
    have next : Next M step (tree node) P := of_decide_eq_true both.2
    have source : (tree (node ++ [P])).source = P := by simpa [observableAt] using (legal _ supported).1
    revert h
    rw [source]
    intro h
    obtain ⟨_,K,component,histories,labels⟩ := next
    have mem : h.val ∈ K.image (tree node).source.history := by rw [← histories]; exact h.property
    obtain ⟨e,he,history⟩ := Finset.mem_image.mp mem
    have alive := component_member_live M (tree node) K component e he
    simp only [extensionLive,decide_eq_true_eq] at alive
    have replay := controller_layer_replay M step q₀ tree closed σ implements node both.1
      (ih both.1) D (Nat.le_refl _) e alive.2
    exact (labels h e he history.symm).trans (replay.trans (congrArg (strategyHistoryLabel σ step q₀) history))

include legal closed implements in
theorem controller_stateAt (node : List (Position I₁ I₂ Q D))
    (supported : publicSupport (offers M step) tree node = true)
    (h : (tree node).source.Root)
    (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D)
    (live : M.eval (History.graphSequence (h.val ++ w.val)) ∈ M.accept) (t : Nat) :
    stateAt step (tree node) h w t = strategyHistoryLabel σ step q₀ (h.val ++ w.val.take t) := by
  let u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) (min t D) := ⟨w.val.take t,by simp [w.property]⟩
  have alive : M.eval (History.graphSequence (h.val ++ u.val)) ∈ M.accept := by
    apply closed _ (History.graphSequence (w.val.drop t))
    simpa only [u,History.graphSequence,← List.map_append,List.append_assoc,List.take_append_drop] using live
  have replay := controller_layer_replay M step q₀ tree closed σ implements node supported
    (controller_states M step q₀ tree legal closed σ implements node supported)
    (min t D) (Nat.min_le_right _ _) (wordScenario h u)
    (by simpa only [wordScenario_history,Position.past] using alive)
  simpa only [stateAt,wordScenario_history,Position.past,u] using replay

include closed in
/-- Forward direction of the paper's Component-game proof. The output
algorithm comes from all live prescriptions, not a new decision procedure. -/
theorem component_winning_algorithm [Nonempty O₁] [Nonempty O₂] (positive : 0 < D) (χ : Q → Nat)
    (winning : Winning M step .component q₀ χ tree) :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      ∀ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
        (∀ n, M.eval (History.graphSequence (branchNode word n)) ∈ M.accept) →
        NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))) := by
  obtain ⟨σ,implements⟩ := component_controller_strategy M step tree q₀ winning.1
  refine ⟨σ,fun word live => ?_⟩
  obtain ⟨branch,supported,run,histories,words⟩ := component_word_run M step tree q₀ winning.1 word live
  have parity := winning.2 branch supported run
  let score n := χ (strategyHistoryLabel σ step q₀ (branchNode word n))
  have minima : ∀ n, rangeMin
      (fun t => χ (stateAt step (tree (branchNode branch n)) (run.history n) (run.word n) t))
      0 (D-1) = cutBlockMin score (fun k => k*D) n := by
    intro n
    have full : (run.history n).val ++ (run.word n).val = branchNode word ((n+1)*D) := by
      rw [histories n,words n,Nat.add_mul,Nat.one_mul]
      exact prefix_append_segment word (n*D) D
    have alive : M.eval (History.graphSequence ((run.history n).val ++ (run.word n).val)) ∈ M.accept := by
      rw [full]; exact live _
    unfold cutBlockMin
    have span : (n+1)*D - n*D - 1 = D-1 := by simp [Nat.add_mul]
    rw [span]
    apply rangeMin_congr
    intro t within
    simp only [Nat.zero_add]
    rw [controller_stateAt M step q₀ tree winning.1 closed σ implements _ (supported n) _ _ alive,
      histories n,words n,eventBlock_take word D n t (by omega),prefix_append_segment]
  rw [funext minima] at parity
  exact (natSeqMinEvenParity_cutBlockMin score
    (fun _ _ h => Nat.mul_lt_mul_of_pos_right h positive) (by simp)).mp parity
end
end Characterisation.ComponentGames.HistoryGame
