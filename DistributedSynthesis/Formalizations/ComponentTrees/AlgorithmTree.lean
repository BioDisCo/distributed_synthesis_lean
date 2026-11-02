/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.TreeReplay

/-! Label every vertex by the given distributed algorithm, as in the
forward uncompressed-tree equivalence. Unsupported addresses use the root.
-/
namespace Characterisation.ComponentTrees.AlgorithmTree
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames.HistoryGame
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (σ : StrategyPair I₁ I₂ O₁ O₂)

def node (P : Position I₁ I₂ B.State D) (valid : PositionValid B M P) : UncompressedNode B M :=
  ⟨P, valid, strategyPolicy σ P.past, strategyPolicy_coherent σ P.past⟩

variable (initialLive : M.eval [] ∈ M.accept)
def tree : UncompressedTree B M := fun address =>
  let P := observableAt (Position.initial B.initial) address
  if valid : PositionValid B M P then node B M σ P valid
  else node B M σ (Position.initial B.initial) (initial_position_valid B M initialLive)

theorem position_of_valid (address : List (Position I₁ I₂ B.State D))
    (valid : PositionValid B M (observableAt (Position.initial B.initial) address)) :
    (tree B M σ initialLive address).position = observableAt (Position.initial B.initial) address := by
  simp only [tree, dif_pos valid, node]

theorem tree_valid : (tree B M σ initialLive).Valid := by
  intro address supported
  cases address using List.reverseRecOn with
  | nil => exact position_of_valid B M σ initialLive [] (initial_position_valid B M initialLive)
  | append_singleton address P =>
    have both : publicSupport UncompressedNode.offers (tree B M σ initialLive) address = true ∧
        UncompressedNode.offers (tree B M σ initialLive address) P = true := by
      simpa only [publicSupport_append, Bool.and_eq_true] using supported
    have next : (tree B M σ initialLive address).Successor P := of_decide_eq_true both.2
    apply position_of_valid
    simpa only [observableAt, List.getLast?_concat, Option.getD_some] using
      ComponentSuccessor.valid B M next (tree B M σ initialLive address).valid

/-- The given strategy supplies every node's output, including nonlive views. -/
theorem implements : ∀ x : (tree B M σ initialLive).Prescription,
    (σ.one (currentView .one ((tree B M σ initialLive).prescribedHistory x)),
     σ.two (currentView .two ((tree B M σ initialLive).prescribedHistory x))) =
      (tree B M σ initialLive).prescribedOutput x := by
  have outputs address : ∀ (t : Fin D) (e : ClosingLayer (tree B M σ initialLive address).position.Root I₁ I₂ (t.val+1)),
      (σ.one (currentView .one (closingLayerHistory (tree B M σ initialLive address).position.past (t.val+1) e)),
       σ.two (currentView .two (closingLayerHistory (tree B M σ initialLive address).position.past (t.val+1) e))) =
         (tree B M σ initialLive address).rule t e := by
    have form : ∃ P, ∃ v : PositionValid B M P, tree B M σ initialLive address = node B M σ P v := by
      unfold tree
      dsimp only
      split
      · rename_i v
        exact ⟨_, v, rfl⟩
      · exact ⟨_, initial_position_valid B M initialLive, rfl⟩
    obtain ⟨P, v, eq⟩ := form
    rw [eq]
    intro t e
    rfl
  exact fun x => outputs x.node x.time x.scenario

theorem run_histories (branch : Nat → Position I₁ I₂ B.State D) (run : (tree B M σ initialLive).Run branch) :
    ∀ n, (run.history n).val = blockHistory (branchNode run.word n) := by
  intro n
  induction n with
  | zero => exact run.initial
  | succ n ih =>
    have next := run.next n
    change (run.history (n+1)).val = (run.history n).val ++ (run.word n).val at next
    rw [next, ih]
    exact (blockHistory_append (branchNode run.word n) (run.word n)).symm

include initialLive in
theorem tree_accepting (positive : 0 < D)
    (closed : PrefixClosed (fun g => M.eval g ∈ M.accept))
    (winning : ∀ word : Nat → BlockInput I₁ I₂ D,
      (∀ n, M.eval (History.graphSequence (blockHistory (branchNode word n))) ∈ M.accept) →
      NatSeqMinEvenParity (fun n => B.priority (strategyState σ B (branchNode word n)))) :
    (tree B M σ initialLive).Accepting := by
  refine ⟨tree_valid B M σ initialLive, ?_⟩
  intro branch supported run
  have histories := run_histories B M σ initialLive branch run
  have live n := (tree B M σ initialLive (branchNode branch n)).valid.1 (run.history n)
  simp only [histories] at live
  have accepted := winning run.word live
  have labels n := (tree B M σ initialLive).states_replay (tree_valid B M σ initialLive)
    closed σ (implements B M σ initialLive) positive _ (supported n) (run.history n)
  simp only [histories, historyBlocks_blockHistory positive] at labels
  simpa only [labels] using accepted

end
end Characterisation.ComponentTrees.AlgorithmTree
