/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyReindexing

/-!
# Provenance-preserving descriptor-family extraction

A history-dependent semantic construction may need a table law stronger than
the finite law exposed by its eventual move alphabet.  Running the rational
extraction once under the strong law and then extracting again under the weak
law would lose the semantic provenance carried by the first table.

This module packages the safe order.  We extract once under every
descriptor-indexed strong law, reinterpret the *same* finite controller under
the weak laws, and retain the strong law as a proof field.  Thus a raw
history-dependent accepting run may use the provenance to follow an exact
semantic thread; a later input-free rationalization sees only the finite weak
move.  No descriptor, orientation, or selected root is added to the sender
control.
-/

namespace DistributedSynthesis

universe i u v x y w

section

variable {Descriptor : Type i}
variable (Root : Descriptor → Type i)
variable {RIn : Type u} {SIn : Type v}
variable {ROut : Type x} {SOut : Type y}
variable
  (M : ∀ descriptor, Root descriptor →
    BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
variable
  (Strong Weak : ∀ descriptor,
    (((Root descriptor × RIn) × SIn) → ROut) → Prop)

variable [Fintype Descriptor] [DecidableEq Descriptor]
variable [∀ descriptor, Fintype (Root descriptor)]
variable [∀ descriptor, DecidableEq (Root descriptor)]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

/-- A finite move exposed through `Weak`, together with the stronger semantic
table law on its literal underlying labeled tree.  The provenance proof is
not part of the runtime controller state. -/
noncomputable abbrev FiniteDescriptorFamilyProvenanceMove :=
  { move : FiniteDescriptorFamilyAllowedMove Root M Weak //
    NarrowedTablesAllowed
      (finiteRootFamilyMonitor (descriptorRootUnionMonitor Root M))
      (DescriptorRootUnionAllowed Root Strong)
      move.1.toTransitionRationalTree.labeledTree }

noncomputable instance :
    Fintype (FiniteDescriptorFamilyProvenanceMove Root M Strong Weak) := by
  classical
  infer_instance

/-- Extract once under `Strong`, then forget only the predicate carried by
the table type.  The weak move and the retained strong certificate refer to
definitionally the same controller, transitions, and labels. -/
noncomputable def finiteDescriptorFamilyProvenanceMoveOfStrategies
    [Inhabited (Sigma Root)] [Inhabited RIn] [Inhabited SIn]
    [Inhabited ROut]
    (himp : ∀ descriptor responses,
      Strong descriptor responses → Weak descriptor responses)
    (defaultTable : (((Sigma Root) × RIn) × SIn) → ROut)
    (hdefault : DescriptorRootUnionAllowed Root Strong defaultTable)
    (receiver : ∀ _ : Sigma Root,
      ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ member env,
      (descriptorRootUnionMonitor Root M member).WinsPlay
        (pairPlay (receiver member) sender env))
    (hstrong : ∀ past,
      DescriptorRootUnionAllowed Root Strong
        ((finiteRootFamilyReceiver receiver) past)) :
    FiniteDescriptorFamilyProvenanceMove Root M Strong Weak := by
  classical
  let unionMonitor :=
    finiteRootFamilyMonitor (descriptorRootUnionMonitor Root M)
  let StrongUnion := DescriptorRootUnionAllowed Root Strong
  let WeakUnion := DescriptorRootUnionAllowed Root Weak
  let strongMove := finiteDescriptorFamilyAllowedMoveOfStrategies Root M Strong
    defaultTable hdefault receiver sender hwin hstrong
  have hunionImp : ∀ responses, StrongUnion responses →
      WeakUnion responses := by
    intro responses hresponses descriptor
    exact himp descriptor _ (hresponses descriptor)
  let weakTable : LocallyConsistentNarrowedTable unionMonitor WeakUnion :=
    strongMove.1.weaken unionMonitor StrongUnion WeakUnion
  have hweakWins : NarrowedAllThreadsWin unionMonitor
      weakTable.toTransitionRationalTree.labeledTree := by
    exact LocallyConsistentNarrowedTable.weaken_wins unionMonitor StrongUnion
      WeakUnion strongMove.1 strongMove.2.1
  have hweakAllowed : NarrowedTablesAllowed unionMonitor WeakUnion
      weakTable.toTransitionRationalTree.labeledTree := by
    exact LocallyConsistentNarrowedTable.weaken_allowed unionMonitor StrongUnion
      WeakUnion hunionImp strongMove.1 strongMove.2.2
  let weakMove : FiniteDescriptorFamilyAllowedMove Root M Weak :=
    ⟨weakTable, hweakWins, hweakAllowed⟩
  refine ⟨weakMove, ?_⟩
  simpa [weakMove, weakTable] using strongMove.2.2

omit [DecidableEq RIn] in
/-- The retained union provenance restricts to every descriptor projection
without another rationalization. -/
theorem FiniteDescriptorFamilyProvenanceMove.controllerFor_strongAllowed
    (move : FiniteDescriptorFamilyProvenanceMove Root M Strong Weak)
    (descriptor : Descriptor) :
    NarrowedTablesAllowed (finiteRootFamilyMonitor (M descriptor))
      (Strong descriptor)
      (move.1.controllerFor Root M Weak descriptor).labeledTree := by
  intro word state
  have hunion := move.2 word
    (reindexFiniteRootFamilyState (descriptorRootUnionMonitor Root M)
      (fun root : Root descriptor ↦ Sigma.mk descriptor root) state)
  have hdescriptor := hunion descriptor
  simpa only [FiniteDescriptorFamilyAllowedMove.controllerFor,
    DescriptorRootUnionAllowed,
    TransitionRationalTree.labeledTree,
    reindexFiniteRootFamilyController_controlAt] using hdescriptor

/-- Forgetting the proof-only provenance returns the finite weak move used by
the outer history automaton. -/
noncomputable def FiniteDescriptorFamilyProvenanceMove.toWeakMove
    (move : FiniteDescriptorFamilyProvenanceMove Root M Strong Weak) :
    FiniteDescriptorFamilyAllowedMove Root M Weak :=
  move.1

end

end DistributedSynthesis
