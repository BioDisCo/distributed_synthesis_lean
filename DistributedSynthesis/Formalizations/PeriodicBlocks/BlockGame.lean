/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockArenaSemantics

/-! The finite periodic-block game. Environment chooses an ending component.
The hidden thread carries one source slot and the exact minimum priority of
the last block. All compatible threads must satisfy parity. -/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
set_option maxSynthPendingDepth 16

section
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D K : Nat}
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [DecidableEq G] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (χ : Q → Nat)

def BlockEdge (old : HandoverCode B K)
    (move : BlockMove I₁ I₂ O₁ O₂ G Q B D) (outcome : BlockOutcome I₁ I₂ G Q B D)
    (next : HandoverCode B K) : Prop :=
  blockOffers M step move outcome = true ∧ ∃ e : BlockEnd I₁ I₂ B D,
    outcome.component e = true ∧ closingLayerRoot D e = old.1 ∧
    (move.response outcome.component).fold e = next.1 ∧
    blockColor step move χ e = next.2.val

instance blockEdge_decidable (old : HandoverCode B K)
    (move : BlockMove I₁ I₂ O₁ O₂ G Q B D) (outcome : BlockOutcome I₁ I₂ G Q B D)
    (next : HandoverCode B K) : Decidable (BlockEdge M step χ old move outcome next) := by
  unfold BlockEdge
  infer_instance

noncomputable def blockGame (initial : BlockOutcome I₁ I₂ G Q B D) (code : HandoverCode B K) :=
  supportedPublicTreeMonitor
    (hiddenCodeContinuitySystem (handoverPriorityDPA B K) code (BlockEdge M step χ)).universalRunDPA
    (blockOffers M step) initial (fun outcome move => BlockMoveValid M step outcome.target move)

variable [Inhabited (BlockOutcome I₁ I₂ G Q B D)]

theorem blockGame_winning_iff (initial : BlockOutcome I₁ I₂ G Q B D) (code : HandoverCode B K)
    (tree : LabeledTree (BlockOutcome I₁ I₂ G Q B D) (BlockMove I₁ I₂ O₁ O₂ G Q B D)) :
    (blockGame M step χ initial code).WinningTree tree ↔
      SupportedMovesValid (blockOffers M step) initial
        (fun outcome move => BlockMoveValid M step outcome.target move) tree ∧
      ∀ branch : Nat → BlockOutcome I₁ I₂ G Q B D,
        ∀ thread : HiddenCodeContinuityThread code (BlockEdge M step χ) (observableThreadWord tree branch),
          NatSeqMinEvenParity (fun n => (thread.code (n+1)).2.val) := by
  rw [blockGame, supportedPublicTreeMonitor_winning_iff]
  constructor
  · rintro ⟨legal,accepted⟩
    refine ⟨legal,fun branch thread => ?_⟩
    have supported := publicSupport_branch_of_offered (blockOffers M step) tree branch
      (fun n => (thread.edge n).1)
    have acceptedThread := (hiddenCodeContinuitySystem_universalRunDPA_accepts_iff
      (handoverPriorityDPA B K) code (BlockEdge M step χ) (observableThreadWord tree branch)).mp
      (accepted branch supported) thread
    exact (handoverPriorityDPA_accepts_iff _).mp acceptedThread
  · rintro ⟨legal,progress⟩
    refine ⟨legal,fun branch _ => ?_⟩
    apply (hiddenCodeContinuitySystem_universalRunDPA_accepts_iff
      (handoverPriorityDPA B K) code (BlockEdge M step χ) (observableThreadWord tree branch)).mpr
    intro thread
    exact (handoverPriorityDPA_accepts_iff _).mpr (progress branch thread)

/-- The game has finite states, directions, and moves. Consequently every
winning public strategy has a finite transition table. -/
theorem blockGame_finite_controller (initial : BlockOutcome I₁ I₂ G Q B D) (code : HandoverCode B K)
    (tree : LabeledTree (BlockOutcome I₁ I₂ G Q B D) (BlockMove I₁ I₂ O₁ O₂ G Q B D))
    (winning : (blockGame M step χ initial code).WinningTree tree) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
      (blockGame M step χ initial code).toRunAutomaton,
      (blockGame M step χ initial code).WinningTree table.toTransitionRationalTree.labeledTree := by
  let game := blockGame M step χ initial code
  obtain ⟨table, accepted⟩ := game.toRunAutomaton.exists_stateControlledTreeTable_accepted
    ⟨tree, (game.acceptsTree_iff_winningTree tree).mpr winning⟩
  exact ⟨table, (game.acceptsTree_iff_winningTree _).mp accepted⟩

end
end Characterisation.PeriodicBlocks
