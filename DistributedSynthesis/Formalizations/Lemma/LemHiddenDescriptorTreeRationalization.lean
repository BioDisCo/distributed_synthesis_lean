/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemHiddenDescriptorContinuityBundle
import DistributedSynthesis.Formalizations.Lemma.LemObservableThreadTreeRationalization

/-!
# Observable-tree rationalization for full hidden descriptors

`hiddenDescriptorContinuitySystem` checks one word whose letters contain a
public family move, Nature's finite direction, and the next public family.
This file couples that word monitor to an observable move tree.  The branch
observation is the pair `(direction, nextFamily)`; the move is still chosen at
the parent, before either component of that observation is read.

This is the full-descriptor analogue of `hiddenCodeContinuityTreeMonitor`.
In particular it preserves the hidden move identity and code-DPA control
across the whole branch, so the rationalized tree cannot reselect an unrelated
semantic root at every level.
-/

namespace DistributedSynthesis

universe u v m b f x

section

variable {Code : Type u} {MoveIdentity : Type v}
variable {FamilyMove : Type m} {Direction : Type b} {FamilyCode : Type f}
variable (D : DetParityAutomaton.{u, x} Code)
variable [Fintype Code] [Fintype MoveIdentity]
variable [Fintype FamilyMove] [Fintype Direction] [Fintype FamilyCode]
variable [Inhabited Direction] [Inhabited FamilyCode]

/-- Nature's finite observation after one staged family move. -/
abbrev HiddenDescriptorTreeObservation := Direction × FamilyCode

/-- The observable tree monitor for a persistent full hidden descriptor.

The dummy direction in the initial observation is ignored by `Valid`.  At
every non-root node the observation is literally the incoming finite
direction and next-family pair. -/
noncomputable def hiddenDescriptorContinuityTreeMonitor
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (initialFamily : FamilyCode)
    (Valid : FamilyCode → FamilyMove → Prop) [DecidableRel Valid] :=
  observableThreadTreeMonitor
    (hiddenDescriptorContinuitySystem D initialDescriptor ExactEdge)
    ((default : Direction), initialFamily)
    (fun observation move => Valid observation.2 move)

/-- Exact winning condition of the observable full-descriptor tree. -/
theorem hiddenDescriptorContinuityTreeMonitor_winning_iff
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (hinitialControl : initialDescriptor.control = D.initial)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (initialFamily : FamilyCode)
    (Valid : FamilyCode → FamilyMove → Prop) [DecidableRel Valid]
    (tree : LabeledTree
      (HiddenDescriptorTreeObservation
        (Direction := Direction) (FamilyCode := FamilyCode)) FamilyMove) :
    (hiddenDescriptorContinuityTreeMonitor D initialDescriptor ExactEdge
        initialFamily Valid).WinningTree tree ↔
      ObservableMovesValid ((default : Direction), initialFamily)
          (fun observation move => Valid observation.2 move) tree ∧
        ∀ branch : Nat →
            HiddenDescriptorTreeObservation
              (Direction := Direction) (FamilyCode := FamilyCode),
          ∀ thread : HiddenDescriptorContinuityThread D initialDescriptor
              ExactEdge (observableThreadWord tree branch),
            D.Accepts thread.childCodeWord := by
  rw [hiddenDescriptorContinuityTreeMonitor,
    observableThreadTreeMonitor_winning_iff]
  constructor
  · rintro ⟨hvalid, hbundle⟩
    refine ⟨hvalid, ?_⟩
    intro branch
    exact (hiddenDescriptorContinuitySystem_universalRunDPA_accepts_iff
      D initialDescriptor hinitialControl ExactEdge
      (observableThreadWord tree branch)).mp (hbundle branch)
  · rintro ⟨hvalid, hthreads⟩
    refine ⟨hvalid, ?_⟩
    intro branch
    exact (hiddenDescriptorContinuitySystem_universalRunDPA_accepts_iff
      D initialDescriptor hinitialControl ExactEdge
      (observableThreadWord tree branch)).mpr (hthreads branch)

/-- A history-dependent observable tree with legal moves and accepting full
descriptor threads admits one finite state-controlled replacement tree. -/
theorem exists_stateControlled_hiddenDescriptorContinuityTree
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (hinitialControl : initialDescriptor.control = D.initial)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (initialFamily : FamilyCode)
    (Valid : FamilyCode → FamilyMove → Prop) [DecidableRel Valid]
    (tree : LabeledTree
      (HiddenDescriptorTreeObservation
        (Direction := Direction) (FamilyCode := FamilyCode)) FamilyMove)
    (hvalid : ObservableMovesValid ((default : Direction), initialFamily)
      (fun observation move => Valid observation.2 move) tree)
    (hthreads : ∀ branch : Nat →
        HiddenDescriptorTreeObservation
          (Direction := Direction) (FamilyCode := FamilyCode),
      ∀ thread : HiddenDescriptorContinuityThread D initialDescriptor
          ExactEdge (observableThreadWord tree branch),
        D.Accepts thread.childCodeWord) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (hiddenDescriptorContinuityTreeMonitor D initialDescriptor ExactEdge
          initialFamily Valid).toRunAutomaton,
      (hiddenDescriptorContinuityTreeMonitor D initialDescriptor ExactEdge
        initialFamily Valid).WinningTree
          table.toTransitionRationalTree.labeledTree := by
  apply exists_stateControlled_observableThreadTree_of_winning
    (hiddenDescriptorContinuitySystem D initialDescriptor ExactEdge)
    ((default : Direction), initialFamily)
    (fun observation move => Valid observation.2 move) tree
  exact (hiddenDescriptorContinuityTreeMonitor_winning_iff D
    initialDescriptor hinitialControl ExactEdge initialFamily Valid tree).mpr
      ⟨hvalid, hthreads⟩

end

end DistributedSynthesis
