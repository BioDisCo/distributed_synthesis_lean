/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingMove
import DistributedSynthesis.Formalizations.Lemma.LemObservableThreadTreeRationalization

/-!
# Central rationalization over finite physical rounds

The old outer automata used `PairedEntryDirection`, whose fields contain
arbitrary strict-history lists.  Applying a rational-run theorem to that
presentation therefore required an unproved basis for an infinite branch
type.

Here the branch type is the actual current `EnvironmentRound`, and the move
type is the finite sibling-table alphabet constructed in the preceding file.
History is the tree node before extraction and the extracted finite control
afterwards.  The checked state-controlled tree theorem therefore applies
directly; no `RationalRunBasis` hypothesis occurs anywhere in this module.

This is deliberately only a **central proof-side** rationalization.
`EnvironmentRound` contains the graph and both current inputs, so an arbitrary
tree on its histories may select a move using information unavailable to
either process.  In particular, the finite table extracted here is not by
itself a distributed controller and must not be fed directly to readback.

The central semantic premise is named
`ProfiledRawJointPhysicalSiblingCoherentAssignment`: one physical-round tree
whose moves satisfy a proof-side node law and whose every coherent hidden
thread has the required parity.  The local common/strict lambda switch is not
part of that boundary: each move already contains one controller independent
of the hidden member.  The remaining distributed boundary is stronger: the
selection and installation of successive moves must factor through the
graph-blind local `noRecv`/`recv` maps of
`ProfiledRawJointLeaderFreeKernel` (or equivalently supply an honest
`FiniteGlobalRoundMachine.LocalPresentation`).
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Hidden-thread systems consumed by the finite physical-round tree. -/
abbrev ProfiledRawJointPhysicalSiblingThreadSystem :=
  FiniteThreadSystem
    (ProfiledRawJointPhysicalSiblingMove A ×
      ProfiledRawJointPhysicalBranch (In₁ := In₁) (In₂ := In₂))

noncomputable instance : Inhabited
    (ProfiledRawJointPhysicalBranch (In₁ := In₁) (In₂ := In₂)) :=
  ⟨{ inputOne := default, inputTwo := default, graph := .both }⟩

/-- The exact *central* premise after finite physical presentation.

`tree node` may inspect the complete physical-round history, including the
graph and both inputs.  `Valid` is only a node predicate; it does not imply
that the choice factors through either process's local view.  `S` checks all
proof-side coherent roots. -/
def ProfiledRawJointPhysicalSiblingCoherentAssignment
    (S : ProfiledRawJointPhysicalSiblingThreadSystem A)
    (initialRound : ProfiledRawJointPhysicalBranch
      (In₁ := In₁) (In₂ := In₂))
    (Valid : ProfiledRawJointPhysicalBranch
        (In₁ := In₁) (In₂ := In₂) →
      ProfiledRawJointPhysicalSiblingMove A → Prop)
    (tree : LabeledTree
      (ProfiledRawJointPhysicalBranch (In₁ := In₁) (In₂ := In₂))
      (ProfiledRawJointPhysicalSiblingMove A)) : Prop :=
  ObservableMovesValid initialRound Valid tree ∧
    ∀ branch : Nat → ProfiledRawJointPhysicalBranch
        (In₁ := In₁) (In₂ := In₂),
      S.universalRunDPA.Accepts (observableThreadWord tree branch)

/-- A coherent physical assignment wins the ordinary finite-branch monitor.
This is just the exact semantic characterization, exposed here to prevent the
old arbitrary-direction basis from reappearing in downstream code. -/
theorem profiledRawJointPhysicalSiblingTree_winning
    (S : ProfiledRawJointPhysicalSiblingThreadSystem A)
    (initialRound : ProfiledRawJointPhysicalBranch
      (In₁ := In₁) (In₂ := In₂))
    (Valid : ProfiledRawJointPhysicalBranch
        (In₁ := In₁) (In₂ := In₂) →
      ProfiledRawJointPhysicalSiblingMove A → Prop)
    [DecidableRel Valid]
    (tree : LabeledTree
      (ProfiledRawJointPhysicalBranch (In₁ := In₁) (In₂ := In₂))
      (ProfiledRawJointPhysicalSiblingMove A))
    (hcoherent : ProfiledRawJointPhysicalSiblingCoherentAssignment A S
      initialRound Valid tree) :
    (observableThreadTreeMonitor S initialRound Valid).WinningTree tree := by
  exact observableThreadTreeMonitor_winning_of S initialRound Valid tree
    hcoherent.1 hcoherent.2

/-- **Unconditional finite-direction rationalization.**

The conclusion is a literal finite state-controlled table over current
environment rounds.  There is no `RationalRunBasis` argument: finiteness of
the physical branch and sibling move types lets the checked parity-tree
emptiness construction apply immediately. -/
theorem exists_stateControlled_profiledRawJointPhysicalSiblingTree
    (S : ProfiledRawJointPhysicalSiblingThreadSystem A)
    (initialRound : ProfiledRawJointPhysicalBranch
      (In₁ := In₁) (In₂ := In₂))
    (Valid : ProfiledRawJointPhysicalBranch
        (In₁ := In₁) (In₂ := In₂) →
      ProfiledRawJointPhysicalSiblingMove A → Prop)
    [DecidableRel Valid]
    (tree : LabeledTree
      (ProfiledRawJointPhysicalBranch (In₁ := In₁) (In₂ := In₂))
      (ProfiledRawJointPhysicalSiblingMove A))
    (hcoherent : ProfiledRawJointPhysicalSiblingCoherentAssignment A S
      initialRound Valid tree) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (observableThreadTreeMonitor S initialRound Valid).toRunAutomaton,
      (observableThreadTreeMonitor S initialRound Valid).WinningTree
        table.toTransitionRationalTree.labeledTree := by
  exact exists_stateControlled_observableThreadTree_of_winning S initialRound
    Valid tree
    (profiledRawJointPhysicalSiblingTree_winning A S initialRound Valid tree
      hcoherent)

/-- The extracted table still satisfies the proof-side node validity law and
universal coherent-thread parity.  No distributed factorization follows from
this theorem. -/
theorem stateControlled_profiledRawJointPhysicalSiblingTree_spec
    (S : ProfiledRawJointPhysicalSiblingThreadSystem A)
    (initialRound : ProfiledRawJointPhysicalBranch
      (In₁ := In₁) (In₂ := In₂))
    (Valid : ProfiledRawJointPhysicalBranch
        (In₁ := In₁) (In₂ := In₂) →
      ProfiledRawJointPhysicalSiblingMove A → Prop)
    [DecidableRel Valid]
    (table : RunParityTreeAutomaton.StateControlledTreeTable
      (observableThreadTreeMonitor S initialRound Valid).toRunAutomaton)
    (hwin : (observableThreadTreeMonitor S initialRound Valid).WinningTree
      table.toTransitionRationalTree.labeledTree) :
    ProfiledRawJointPhysicalSiblingCoherentAssignment A S initialRound Valid
      table.toTransitionRationalTree.labeledTree := by
  exact (observableThreadTreeMonitor_winning_iff S initialRound Valid
    table.toTransitionRationalTree.labeledTree).mp hwin

/-- Existential package form for central coherence.  This proposition contains no local-presentation field. -/
def ProfiledRawJointPhysicalSiblingGlobalCoherence
    (S : ProfiledRawJointPhysicalSiblingThreadSystem A)
    (initialRound : ProfiledRawJointPhysicalBranch
      (In₁ := In₁) (In₂ := In₂))
    (Valid : ProfiledRawJointPhysicalBranch
        (In₁ := In₁) (In₂ := In₂) →
      ProfiledRawJointPhysicalSiblingMove A → Prop) : Prop :=
  ∃ tree, ProfiledRawJointPhysicalSiblingCoherentAssignment A S
    initialRound Valid tree

/-- The global-coherence package alone yields a finite **central tree table**.
It does not yield a `FinitePairedPhysicalController`: downstream work must
also construct the leader-free local transition/factorization data. -/
theorem exists_stateControlled_profiledRawJointPhysicalSiblingTree_of_globalCoherence
    (S : ProfiledRawJointPhysicalSiblingThreadSystem A)
    (initialRound : ProfiledRawJointPhysicalBranch
      (In₁ := In₁) (In₂ := In₂))
    (Valid : ProfiledRawJointPhysicalBranch
        (In₁ := In₁) (In₂ := In₂) →
      ProfiledRawJointPhysicalSiblingMove A → Prop)
    [DecidableRel Valid]
    (hglobal : ProfiledRawJointPhysicalSiblingGlobalCoherence A S
      initialRound Valid) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (observableThreadTreeMonitor S initialRound Valid).toRunAutomaton,
      (observableThreadTreeMonitor S initialRound Valid).WinningTree
        table.toTransitionRationalTree.labeledTree := by
  rcases hglobal with ⟨tree, htree⟩
  exact exists_stateControlled_profiledRawJointPhysicalSiblingTree A S
    initialRound Valid tree htree

end

end DetParityAutomaton

end DistributedSynthesis
