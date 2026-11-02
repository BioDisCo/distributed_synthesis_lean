/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteSemanticThreadLifting
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedHiddenCodeContinuity

/-!
# One-origin lifting for the hidden indexed-code thread

The public staged controller carries only finite family data.  Its hidden
continuity monitor consequently admits a code edge only after the concrete
model proves that edge liftable from the *current* correlated semantic state.
This file turns that local lifting operation into the whole-branch
`ProfiledOpenIndexedHiddenFiniteTagLift` required by the controller
extraction theorem.

This is the anti-mosaic adapter: it recursively uses the semantic state
reached at the preceding level.  It never chooses unrelated witnesses for
successive code edges, and it exposes no leader, orientation, or current
graph bit to either process.
-/

namespace DistributedSynthesis

universe i u v x y s f m

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable {FamilyCode : Type f} {FamilyMove : Type m}

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

/-- The exact local model obligation.  Starting from any current correlated
semantic representative, every advertised hidden code edge chooses a finite
direction tag whose literal semantic child has the advertised next code. -/
abbrev ProfiledOpenIndexedHiddenSemanticEdgeLifter
    (ExactEdge : ProfiledOpenIndexedExactFamilyEdge A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove)) :=
  SemanticEdgeLifter
    (profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin basis)
    (fun state => state.code A strategy hwin basis)
    ExactEdge

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A local semantic edge lifter recursively supplies the single finite-tag
branch witnessing every persistent hidden code thread. -/
theorem profiledOpenIndexedHiddenFiniteTagLift_of_semanticEdgeLifter
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (ExactEdge : ProfiledOpenIndexedExactFamilyEdge A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove))
    (lifter : ProfiledOpenIndexedHiddenSemanticEdgeLifter A strategy hwin
      basis ExactEdge)
    (tree : LabeledTree FamilyCode FamilyMove) :
    ProfiledOpenIndexedHiddenFiniteTagLift A strategy hwin basis initial
      ExactEdge tree := by
  intro branch thread
  let finiteBranch := lifter.liftedBranch
    (profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin basis)
    (fun state => state.code A strategy hwin basis) ExactEdge initial
    (observableThreadWord tree branch) thread
  refine ⟨finiteBranch, ?_⟩
  have hword := SemanticEdgeLifter.childDescriptorWord_eq
    (lifter := lifter) (initial := initial)
    (word := observableThreadWord tree branch) (thread := thread)
  simpa only [SourceFreeBeliefSemanticTree.childCodeWord,
    SourceFreeBeliefSemanticTree.stateAt] using hword

variable [Fintype FamilyCode] [Fintype FamilyMove] [Inhabited FamilyCode]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- End-to-end finite public controller extraction, with the dangerous
whole-thread lifting premise reduced to one recursively composable local
model operation. -/
theorem exists_profiledOpenIndexedHiddenCodeFamilyController_of_semanticEdgeLifter
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (ExactEdge : ProfiledOpenIndexedExactFamilyEdge A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove))
    (lifter : ProfiledOpenIndexedHiddenSemanticEdgeLifter A strategy hwin
      basis ExactEdge)
    (initialFamily : FamilyCode)
    (Valid : FamilyCode → FamilyMove → Prop) [DecidableRel Valid]
    (tree : LabeledTree FamilyCode FamilyMove)
    (hvalid : ObservableMovesValid initialFamily Valid tree) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (profiledOpenIndexedHiddenCodeTreeMonitor A
          (initial.code A strategy hwin basis) ExactEdge initialFamily Valid
            |>.toRunAutomaton),
      (profiledOpenIndexedHiddenCodeTreeMonitor A
        (initial.code A strategy hwin basis) ExactEdge initialFamily Valid).WinningTree
          table.toTransitionRationalTree.labeledTree := by
  apply exists_profiledOpenIndexedHiddenCodeFamilyController_of_finiteTagLift
    A strategy hwin basis initial ExactEdge initialFamily Valid tree hvalid
  exact profiledOpenIndexedHiddenFiniteTagLift_of_semanticEdgeLifter A
    strategy hwin basis initial ExactEdge lifter tree

end

end DetParityAutomaton

end DistributedSynthesis
