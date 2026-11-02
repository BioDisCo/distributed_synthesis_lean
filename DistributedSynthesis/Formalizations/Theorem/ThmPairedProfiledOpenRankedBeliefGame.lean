/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemDiagonalPairTreeRationalization

/-!
# The finite ranked-belief game for open profiled roots

The observable-thread monitor already contains the finite belief/obligation
state needed at an open root: the current public class, the universal hidden
thread bundle, and the sticky legality bit.  Its parity-tree emptiness game is
therefore the finite ranked-belief arena for this construction.

This file records the exact equivalence, rather than introducing another
certificate interface.  Winning the finite game is equivalent to the
existence of *some* public-class-measurable winning move tree, and hence to a
finite state-controlled winning table.  The canonical realization tree is
only one sufficient witness; it is not built into the game.

The remaining unconditional lifting question is consequently sharp: a raw
exact-view distributed winner must induce a winner of this finite game.  No
canonical-representative choice occurs in the statements below.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- The concrete finite ranked-belief arena.  Its Even positions are monitor
states and its Odd positions choose one public successor class. -/
abbrev profiledOpenSemanticRankedBeliefGame
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initial : ProfiledOpenSemanticObservation A strategy hwin basis) :=
  RunParityTreeAutomaton.emptinessGame
    (profiledOpenSemanticTreeMonitor A strategy hwin basis initial).toRunAutomaton

/-- Even wins the finite arena from the monitor's genuine initial state. -/
def ProfiledOpenSemanticRankedBeliefWinning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initial : ProfiledOpenSemanticObservation A strategy hwin basis) : Prop :=
  some (Sum.inl
      (profiledOpenSemanticTreeMonitor A strategy hwin basis initial).initial) ∈
    (profiledOpenSemanticRankedBeliefGame A strategy hwin basis initial).PositionalWinningRegion
      ParityPlayer.even

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Exact game semantics: the initial ranked-belief position is winning iff
there exists a public-class-measurable tree satisfying legality and every
coherent hidden-root parity obligation. -/
theorem profiledOpenSemanticRankedBeliefWinning_iff_exists_winningTree
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initial : ProfiledOpenSemanticObservation A strategy hwin basis) :
    ProfiledOpenSemanticRankedBeliefWinning A strategy hwin basis initial ↔
      ∃ tree : LabeledTree
          (ProfiledOpenSemanticObservation A strategy hwin basis)
          (ProfiledOpenRepresentableMove A),
        (profiledOpenSemanticTreeMonitor A strategy hwin basis initial).WinningTree
          tree := by
  let M := profiledOpenSemanticTreeMonitor A strategy hwin basis initial
  constructor
  · rintro ⟨sigma, hsigma⟩
    let tree := RunParityTreeAutomaton.extractedTree M.toRunAutomaton sigma
      (ProfiledOpenRepresentableMove.sink)
    refine ⟨tree.labeledTree, ?_⟩
    apply (M.acceptsTree_iff_winningTree tree.labeledTree).mp
    exact RunParityTreeAutomaton.acceptsTree_extractedTree M.toRunAutomaton
      sigma ProfiledOpenRepresentableMove.sink hsigma
  · rintro ⟨tree, htree⟩
    have haccepts : ∃ tree, M.toRunAutomaton.acceptsTree tree :=
      ⟨tree, (M.acceptsTree_iff_winningTree tree).mpr htree⟩
    simpa [ProfiledOpenSemanticRankedBeliefWinning,
      profiledOpenSemanticRankedBeliefGame, M] using
      M.toRunAutomaton.exists_evenPositionalStrategy_of_accepts haccepts

/-- A global-parity proof for the canonical realization tree is sufficient
for the ranked-belief arena, but the arena itself does not require that
canonical tree. -/
theorem profiledOpenSemanticRankedBeliefWinning_of_globalParity
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initial : ProfiledOpenSemanticObservation A strategy hwin basis)
    (hparity : ProfiledOpenSemanticGlobalParity A strategy hwin basis initial) :
    ProfiledOpenSemanticRankedBeliefWinning A strategy hwin basis initial := by
  rw [profiledOpenSemanticRankedBeliefWinning_iff_exists_winningTree]
  exact ⟨profiledOpenSemanticMoveTree A strategy hwin basis initial,
    (profiledOpenSemanticMoveTree_winning_iff_globalParity A strategy hwin
      basis initial).2 hparity⟩

/-- Positional determinacy turns a winning ranked-belief position directly
into the finite public table consumed by the readback layer. -/
theorem exists_finite_profiledOpenSemanticTable_of_rankedBeliefWinning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initial : ProfiledOpenSemanticObservation A strategy hwin basis)
    (hranked :
      ProfiledOpenSemanticRankedBeliefWinning A strategy hwin basis initial) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (profiledOpenSemanticTreeMonitor A strategy hwin basis initial).toRunAutomaton,
      (profiledOpenSemanticTreeMonitor A strategy hwin basis initial).WinningTree
        table.toTransitionRationalTree.labeledTree := by
  rw [profiledOpenSemanticRankedBeliefWinning_iff_exists_winningTree] at hranked
  rcases hranked with ⟨tree, htree⟩
  exact exists_stateControlled_observableThreadTree_of_winning
    (profiledOpenSemanticThreadSystem A strategy hwin basis initial) initial
    (fun observation move =>
      ProfiledOpenObservableMoveValid A observation.public move)
    tree htree

/-- The ranked-belief route also closes the diagonal/shared-origin gate: the
square is taken only after the one public tree has been rationalized. -/
theorem exists_finite_profiledOpenSemanticTable_with_sharedOrigin_of_rankedBeliefWinning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initial : ProfiledOpenSemanticObservation A strategy hwin basis)
    (hranked :
      ProfiledOpenSemanticRankedBeliefWinning A strategy hwin basis initial) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (profiledOpenSemanticTreeMonitor A strategy hwin basis initial).toRunAutomaton,
      (profiledOpenSemanticTreeMonitor A strategy hwin basis initial).WinningTree
          table.toTransitionRationalTree.labeledTree ∧
        RationalPairTreeHasSharedOrigin
          table.toTransitionRationalTree.selfProduct := by
  rcases exists_finite_profiledOpenSemanticTable_of_rankedBeliefWinning A
      strategy hwin basis initial hranked with ⟨table, htable⟩
  exact ⟨table, htable,
    TransitionRationalTree.selfProduct_hasSharedOrigin
      table.toTransitionRationalTree⟩

end

end

end DetParityAutomaton

end DistributedSynthesis
