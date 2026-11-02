/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemHiddenDescriptorFamilyTotality
import DistributedSynthesis.Formalizations.Lemma.LemHiddenDescriptorTreeRationalization

/-!
# Family-aware lifting of hidden-descriptor threads

The first hidden-descriptor lifting interface asks an exact edge to determine
the literal semantic child from the hidden descriptor alone.  That is stronger
than the staged family construction needs: the finite move is checked at the
current public family, and that family is precisely the finite local-view
fibre which makes the move sound.

This file records the weaker, faithful interface.  Starting with the correct
initial family, a valid exact edge must produce both the literal semantic
child descriptor and its public child family.  Induction then keeps the
semantic state, hidden descriptor, and public family synchronized.  A false
advertised family cannot support an infinite exact thread, while a coherent
thread lifts to one semantic branch.

The family is proof-side public control.  No process is given a lane,
orientation, strict-leader flag, or selected descriptor member.
-/

namespace DistributedSynthesis

universe u v m b f x y

section

variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable {FamilyMove : Type m} {Direction : Type b} {Family : Type f}
variable {Semantic : Type y}
variable [Fintype Code] [Fintype MoveIdentity]

/-- An exact edge may use the current public family through `Valid`.

Besides identifying the literal semantic child descriptor, it must identify
the child's advertised family.  This second equality is what lets the
induction use the next node's validity hypothesis without assuming that the
descriptor alone determines its exact local-view fibre. -/
structure FamilyAwareHiddenDescriptorEdgeLifter
    (semanticStep : Semantic → Direction → Semantic)
    (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (familyOf : Semantic → Family)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → Family →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : Family → FamilyMove → Prop) : Prop where
  lifts : ∀ state move direction nextFamily target,
    Valid (familyOf state) move →
    ExactEdge (semanticDescriptor state) move direction nextFamily target →
      semanticDescriptor (semanticStep state direction) = target ∧
        familyOf (semanticStep state direction) = nextFamily

/-- Literal semantic state reached after the public direction prefix of a
family word. -/
def familyAwareHiddenDescriptorSemanticAt
    (initial : Semantic)
    (semanticStep : Semantic → Direction → Semantic)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := Family)))
    (n : Nat) : Semantic :=
  (branchNode (fun k ↦ (word k).2.1) n).foldl semanticStep initial

@[simp] theorem familyAwareHiddenDescriptorSemanticAt_zero
    (initial : Semantic)
    (semanticStep : Semantic → Direction → Semantic)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := Family))) :
    familyAwareHiddenDescriptorSemanticAt initial semanticStep word 0 =
      initial :=
  rfl

@[simp] theorem familyAwareHiddenDescriptorSemanticAt_succ
    (initial : Semantic)
    (semanticStep : Semantic → Direction → Semantic)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := Family)))
    (n : Nat) :
    familyAwareHiddenDescriptorSemanticAt initial semanticStep word (n + 1) =
      semanticStep
        (familyAwareHiddenDescriptorSemanticAt initial semanticStep word n)
        (word n).2.1 := by
  simp [familyAwareHiddenDescriptorSemanticAt, branchNode]

/-- Current family of a word over an arbitrary family type. -/
def familyAwareHiddenDescriptorFamilyAt
    (initialFamily : Family)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := Family))) : Nat → Family
  | 0 => initialFamily
  | n + 1 => (word n).2.2

@[simp] theorem familyAwareHiddenDescriptorFamilyAt_zero
    (initialFamily : Family)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := Family))) :
    familyAwareHiddenDescriptorFamilyAt initialFamily word 0 = initialFamily :=
  rfl

@[simp] theorem familyAwareHiddenDescriptorFamilyAt_succ
    (initialFamily : Family)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := Family)))
    (n : Nat) :
    familyAwareHiddenDescriptorFamilyAt initialFamily word (n + 1) =
      (word n).2.2 :=
  rfl

namespace FamilyAwareHiddenDescriptorEdgeLifter

variable
  (semanticStep : Semantic → Direction → Semantic)
  (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
    (MoveIdentity := MoveIdentity))
  (familyOf : Semantic → Family)
  (ExactEdge : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    FamilyMove → Direction → Family →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
  (Valid : Family → FamilyMove → Prop)
  (lifter : FamilyAwareHiddenDescriptorEdgeLifter D semanticStep
    semanticDescriptor familyOf ExactEdge Valid)
  (initial : Semantic)
  (initialFamily : Family)
  (word : OmegaWord (HiddenDescriptorFamilyLetter
    (FamilyMove := FamilyMove) (Direction := Direction)
    (FamilyCode := Family)))
  (thread : HiddenDescriptorContinuityThread D
    (semanticDescriptor initial) ExactEdge word)
  (hinitialFamily : initialFamily = familyOf initial)
  (hvalid : ∀ n,
    Valid (familyAwareHiddenDescriptorFamilyAt initialFamily word n)
      (word n).1)

include lifter hinitialFamily hvalid

section
omit [Fintype Code] [Fintype MoveIdentity]

/-- The semantic state, hidden descriptor, and public family remain aligned
at every depth. -/
theorem descriptor_eq_and_family_eq : ∀ n,
    thread.descriptor n =
        semanticDescriptor
          (familyAwareHiddenDescriptorSemanticAt initial semanticStep word n) ∧
      familyAwareHiddenDescriptorFamilyAt initialFamily word n =
        familyOf
          (familyAwareHiddenDescriptorSemanticAt initial semanticStep word n) := by
  intro n
  induction n with
  | zero =>
      exact ⟨thread.initial, hinitialFamily⟩
  | succ n ih =>
      let state := familyAwareHiddenDescriptorSemanticAt initial semanticStep
        word n
      have hedge : ExactEdge (semanticDescriptor state) (word n).1
          (word n).2.1 (word n).2.2 (thread.descriptor (n + 1)) := by
        simpa only [state, ih.1] using thread.exactEdge n
      have hmove : Valid (familyOf state) (word n).1 := by
        rw [← ih.2]
        exact hvalid n
      have hlift := lifter.lifts state (word n).1 (word n).2.1
        (word n).2.2 (thread.descriptor (n + 1)) hmove hedge
      exact ⟨by simpa [state] using hlift.1.symm,
        by simpa [state] using hlift.2.symm⟩

/-- A family-valid exact thread is the child-descriptor word of one literal
semantic direction branch. -/
theorem childDescriptorWord_eq :
    (fun n ↦ thread.descriptor (n + 1)) = fun n ↦
      semanticDescriptor
        (familyAwareHiddenDescriptorSemanticAt initial semanticStep word
          (n + 1)) := by
  funext n
  exact (lifter.descriptor_eq_and_family_eq D semanticStep semanticDescriptor
    familyOf ExactEdge Valid initial initialFamily word thread hinitialFamily
    hvalid (n + 1)).1

/-- Code projection of the preceding one-origin equality. -/
theorem childCodeWord_eq :
    thread.childCodeWord = fun n ↦
      (semanticDescriptor
        (familyAwareHiddenDescriptorSemanticAt initial semanticStep word
          (n + 1))).code := by
  funext n
  have h := congrFun
    (lifter.childDescriptorWord_eq D semanticStep semanticDescriptor familyOf
      ExactEdge Valid initial initialFamily word thread hinitialFamily hvalid) n
  exact congrArg HiddenCodeControlDescriptor.code h

/-- Semantic branch parity transfers to every family-valid exact thread. -/
theorem thread_accepts
    (haccepts : ∀ branch : Nat → Direction,
      D.Accepts (fun n ↦
        (semanticDescriptor
          ((branchNode branch (n + 1)).foldl semanticStep initial)).code)) :
    D.Accepts thread.childCodeWord := by
  rw [lifter.childCodeWord_eq D semanticStep semanticDescriptor familyOf
    ExactEdge Valid initial initialFamily word thread hinitialFamily hvalid]
  exact haccepts (fun n ↦ (word n).2.1)

end

end FamilyAwareHiddenDescriptorEdgeLifter

/-! ## Observable-tree transfer -/

variable [Fintype FamilyMove] [Fintype Direction] [Fintype Family]
variable [Inhabited Direction] [Inhabited Family]

omit [Fintype FamilyMove] [Fintype Direction] [Fintype Family] [Inhabited Family] in
/-- Along an observable branch, the staged word's current family is exactly
the family component currently visible to the tree. -/
theorem familyAwareHiddenDescriptorFamilyAt_observableThreadWord
    (initialFamily : Family)
    (tree : LabeledTree
      (HiddenDescriptorTreeObservation
        (Direction := Direction) (FamilyCode := Family)) FamilyMove)
    (branch : Nat → HiddenDescriptorTreeObservation
      (Direction := Direction) (FamilyCode := Family)) : ∀ n,
    familyAwareHiddenDescriptorFamilyAt initialFamily
        (observableThreadWord tree branch) n =
      (observableAt ((default : Direction), initialFamily)
        (branchNode branch n)).2 := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
      simp [familyAwareHiddenDescriptorFamilyAt, observableThreadWord,
        observableAt, branchNode]

/-- A family-aware exact-edge lift is sufficient for winning the complete
observable hidden-descriptor tree monitor.  False family advertisements can
support no exact thread unless they are also the literal semantic child
family. -/
theorem familyAware_hiddenDescriptorContinuityTree_winning
    (semanticStep : Semantic → Direction → Semantic)
    (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (familyOf : Semantic → Family)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → Family →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : Family → FamilyMove → Prop) [DecidableRel Valid]
    (lifter : FamilyAwareHiddenDescriptorEdgeLifter D semanticStep
      semanticDescriptor familyOf ExactEdge Valid)
    (initial : Semantic)
    (initialFamily : Family)
    (hinitialFamily : initialFamily = familyOf initial)
    (hinitialControl : (semanticDescriptor initial).control = D.initial)
    (tree : LabeledTree
      (HiddenDescriptorTreeObservation
        (Direction := Direction) (FamilyCode := Family)) FamilyMove)
    (hvalid : ObservableMovesValid
      ((default : Direction), initialFamily)
      (fun observation move ↦ Valid observation.2 move) tree)
    (haccepts : ∀ branch : Nat → Direction,
      D.Accepts (fun n ↦
        (semanticDescriptor
          ((branchNode branch (n + 1)).foldl semanticStep initial)).code)) :
    (hiddenDescriptorContinuityTreeMonitor D (semanticDescriptor initial)
      ExactEdge initialFamily Valid).WinningTree tree := by
  apply (hiddenDescriptorContinuityTreeMonitor_winning_iff D
    (semanticDescriptor initial) hinitialControl ExactEdge initialFamily Valid
    tree).2
  refine ⟨hvalid, ?_⟩
  intro branch thread
  apply lifter.thread_accepts D semanticStep semanticDescriptor familyOf
    ExactEdge Valid initial initialFamily (observableThreadWord tree branch)
    thread hinitialFamily
  · intro n
    have hnode := hvalid (branchNode branch n)
    rw [familyAwareHiddenDescriptorFamilyAt_observableThreadWord
      initialFamily tree branch n]
    exact hnode
  · exact haccepts

/-- One-shot finite rationalization through the weaker family-aware lift. -/
theorem exists_stateControlled_familyAwareHiddenDescriptorContinuityTree
    (semanticStep : Semantic → Direction → Semantic)
    (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (familyOf : Semantic → Family)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → Family →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : Family → FamilyMove → Prop) [DecidableRel Valid]
    (lifter : FamilyAwareHiddenDescriptorEdgeLifter D semanticStep
      semanticDescriptor familyOf ExactEdge Valid)
    (initial : Semantic)
    (initialFamily : Family)
    (hinitialFamily : initialFamily = familyOf initial)
    (hinitialControl : (semanticDescriptor initial).control = D.initial)
    (tree : LabeledTree
      (HiddenDescriptorTreeObservation
        (Direction := Direction) (FamilyCode := Family)) FamilyMove)
    (hvalid : ObservableMovesValid
      ((default : Direction), initialFamily)
      (fun observation move ↦ Valid observation.2 move) tree)
    (haccepts : ∀ branch : Nat → Direction,
      D.Accepts (fun n ↦
        (semanticDescriptor
          ((branchNode branch (n + 1)).foldl semanticStep initial)).code)) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (hiddenDescriptorContinuityTreeMonitor D (semanticDescriptor initial)
          ExactEdge initialFamily Valid).toRunAutomaton,
      (hiddenDescriptorContinuityTreeMonitor D (semanticDescriptor initial)
        ExactEdge initialFamily Valid).WinningTree
          table.toTransitionRationalTree.labeledTree := by
  apply exists_stateControlled_hiddenDescriptorContinuityTree D
    (semanticDescriptor initial) hinitialControl ExactEdge initialFamily Valid
    tree hvalid
  intro branch thread
  apply lifter.thread_accepts D semanticStep semanticDescriptor familyOf
    ExactEdge Valid initial initialFamily (observableThreadWord tree branch)
    thread hinitialFamily
  · intro n
    have hnode := hvalid (branchNode branch n)
    rw [familyAwareHiddenDescriptorFamilyAt_observableThreadWord
      initialFamily tree branch n]
    exact hnode
  · exact haccepts

end

end DistributedSynthesis
