/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.TreePrescriptions
import DistributedSynthesis.Formalizations.ComponentTrees.AlgorithmBlocks

/-! Replaying the single distributed strategy chosen from all live local
prescriptions. Every block state is reconstructed, not only its priority.
-/
namespace Characterisation.ComponentTrees.UncompressedTree
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames.HistoryGame
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable {B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D)}
variable {M : Recognizer Graph G} [DecidablePred (· ∈ M.accept)]
variable (tree : UncompressedTree B M) (valid : tree.Valid)
variable (closed : PrefixClosed (fun g => M.eval g ∈ M.accept))
variable (σ : StrategyPair I₁ I₂ O₁ O₂)
variable (implements : ∀ x : tree.Prescription,
  (σ.one (currentView .one (tree.prescribedHistory x)),
   σ.two (currentView .two (tree.prescribedHistory x))) = tree.prescribedOutput x)

include closed implements in
theorem trace_replay (node : List (Position I₁ I₂ B.State D))
    (supported : publicSupport UncompressedNode.offers tree node = true)
    (n : Nat) (within : n ≤ D) (e : ClosingLayer (tree node).position.Root I₁ I₂ n)
    (live : M.eval (History.graphSequence (closingLayerHistory (tree node).position.past n e)) ∈ M.accept) :
    closingLayerTrace (tree node).rule n within e =
      closingLayerTrace (strategyPolicy σ (tree node).position.past) n within e := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have parent : M.eval (History.graphSequence (closingLayerHistory (tree node).position.past n e.1)) ∈ M.accept := by
      apply closed _ [e.2.2.2]
      simpa only [closingLayerHistory, scenarioHistory, History.graphSequence, List.map_append, List.map_singleton] using live
    have out := implements ⟨node, supported, ⟨n, by omega⟩, e, live⟩
    simp only [closingLayerTrace, ih (by omega) e.1 parent]
    exact congrArg (fun o => _ ++ [(e.2, o)]) out.symm

include closed implements in
theorem block_replay (node : List (Position I₁ I₂ B.State D))
    (supported : publicSupport UncompressedNode.offers tree node = true)
    (a : (tree node).position.Root) (u : BlockInput I₁ I₂ D)
    (live : M.eval (History.graphSequence (a.val ++ u.val)) ∈ M.accept) :
    ruleBlock (tree node).rule (wordScenario a u) = strategyBlock σ a.val u := by
  change ruleBlock (tree node).rule (wordScenario a u) = strategyBlock σ ((tree node).position.past a) u
  rw [← strategyBlock_at σ (tree node).position.past a u]
  apply Subtype.ext
  exact trace_replay tree closed σ implements node supported D (Nat.le_refl _) _
    (by simpa only [wordScenario_history, Position.past] using live)

include valid closed implements in
theorem states_replay (positive : 0 < D) (node : List (Position I₁ I₂ B.State D))
    (supported : publicSupport UncompressedNode.offers tree node = true)
    (h : (tree node).position.Root) :
    (tree node).position.state h = strategyState σ B (historyBlocks D h.val) := by
  induction node using List.reverseRecOn with
  | nil =>
    have source := valid [] supported
    change (tree []).position = Position.initial B.initial at source
    revert h
    rw [source]
    intro h
    have empty : h.val = [] := Finset.mem_singleton.mp h.property
    change B.initial = _
    rw [empty, show ([] : EnvHistory I₁ I₂) = blockHistory ([] : List (BlockInput I₁ I₂ D)) from rfl,
      historyBlocks_blockHistory positive, strategyState_nil]
  | append_singleton node P ih =>
    have both : publicSupport UncompressedNode.offers tree node = true ∧
        UncompressedNode.offers (tree node) P = true := by
      simpa only [publicSupport_append, Bool.and_eq_true] using supported
    have next : (tree node).Successor P := of_decide_eq_true both.2
    have source : (tree (node ++ [P])).position = P := by simpa [observableAt] using valid _ supported
    revert h
    rw [source]
    intro h
    obtain ⟨C, component, _, histories, labels⟩ := next
    have member : h.val ∈ C.image (tree node).position.history := by
      change h.val ∈ C.image (tree node).move.source.history
      rw [← histories]
      exact h.property
    obtain ⟨e, he, eh⟩ := Finset.mem_image.mp member
    let a := closingLayerRoot D e
    let u := scenarioWord D e
    have history : h.val = a.val ++ u.val := eh.symm.trans (scenarioWord_history (tree node).position.past D e)
    have alive : M.eval (History.graphSequence (a.val ++ u.val)) ∈ M.accept := by
      rw [← history, ← eh]
      exact component_alive M (tree node).move C component ⟨e, he⟩
    have output := block_replay tree closed σ implements node both.1 a u alive
    have scenario : wordScenario a u = e := wordScenario_scenarioWord D e
    rw [scenario] at output
    rw [labels h ⟨e, he⟩ eh.symm]
    change B.step ((tree node).position.state a) (ruleBlock (tree node).rule e) = _
    rw [ih both.1 a, output, history,
      historyBlocks_append positive (tree node).position.phase a.val ((tree node).position.lengths _ a.property) u,
      strategyState_append,
      blockHistory_historyBlocks (tree node).position.phase a.val ((tree node).position.lengths _ a.property)]

include valid closed implements in
theorem accepts_strategy_blocks (positive : 0 < D) (accepting : tree.Accepting)
    (A : Set (Nat → Graph)) (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (word : Nat → BlockInput I₁ I₂ D)
    (live : ∀ n, M.eval (History.graphSequence (blockHistory (branchNode word n))) ∈ M.accept) :
    NatSeqMinEvenParity (fun n => B.priority (strategyState σ B (branchNode word n))) := by
  obtain ⟨branch, support, run, histories, _⟩ := tree.live_word_run valid A recognizes word live
  have labels n := states_replay tree valid closed σ implements positive _ (support n) (run.history n)
  simp only [histories, historyBlocks_blockHistory positive] at labels
  simpa only [labels] using accepting.2 branch support run

end
end Characterisation.ComponentTrees.UncompressedTree
