/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyNarrowing
import DistributedSynthesis.Formalizations.Lemma.LemLocallyConsistentStateControlled

/-!
# Reindexing one simultaneous finite-root controller

A controller obtained by narrowing one union of hidden roots must not be
rationalized again when it is read at a smaller source family.  This file
restricts such a controller along an arbitrary map `f : J → I`.  The finite
control, its transition, and the sender label are copied literally.  Only the
proof-side family tag used by the receiver table is mapped through `f`.

Consequently every projected member is the corresponding member of the
original union controller, and all subfamilies retain the very same sender
control and output.  No injectivity of `f` is required: duplicate finite roots
may deliberately share one union member.

A projection intentionally does not inhabit a descriptor-local
`LocallyConsistentNarrowedTable`.  That old type fixes its controller to the
state of the descriptor-local restricted automaton, whereas locality requires
the projection to retain the state of the one union restricted automaton.
There is no generic conversion between those state types; applying Rabin
extraction again would erase the sharing proved here.  The final section
therefore preserves descriptor-indexed complete-table laws in the union label
restriction and exposes projections through a foreign-control readback
interface.
-/

namespace DistributedSynthesis

universe i u v x y w

section

variable {I J : Type i}
variable {RIn : Type u} {SIn : Type v}
variable {ROut : Type x} {SOut : Type y}
variable (M : I → BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

/-! ## Mapping the proof-side family monitor state -/

/-- Map a state of a reindexed family monitor back to the union monitor.
The underlying member-monitor state is definitionally unchanged. -/
def reindexFiniteRootFamilyState
    (f : J → I) :
    FiniteRootFamilyState (fun index => M (f index)) →
      FiniteRootFamilyState M
  | .initial => .initial
  | .active index state => .active (f index) state
  | .sink => .sink

/-! ## Restricting the controller without another rationalization -/

/-- Restrict one simultaneous union controller to a (possibly
non-injectively) reindexed subfamily.  Its runtime control and sender side are
copied literally; only receiver-side monitor states and tagged receiver inputs
are embedded in the union family. -/
noncomputable def reindexFiniteRootFamilyController
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (f : J → I)
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State)) :
    TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (J × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor (fun index => M (f index))).State) where
  Control := family.Control
  controlFinite := family.controlFinite
  initial := family.initial
  step := family.step
  labelOf := fun control =>
    let label := family.labelOf control
    (label.1, fun state move =>
      label.2 (reindexFiniteRootFamilyState M f state)
        ((f move.1.1, move.1.2), move.2))

@[simp] theorem reindexFiniteRootFamilyController_controlAt
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (f : J → I)
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (word : List SIn) :
    (reindexFiniteRootFamilyController M f family).controlAt word =
      family.controlAt word := by
  induction word using List.reverseRecOn with
  | nil => rfl
  | append_singleton word input ih =>
      rw [TransitionRationalTree.controlAt_append,
        TransitionRationalTree.controlAt_append]
      simpa [reindexFiniteRootFamilyController] using
        congrArg (fun control => family.step control input) ih

/-- Reindexing does not change the sender label at any finite sender word. -/
@[simp] theorem reindexFiniteRootFamilyController_sender
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (f : J → I)
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (word : List SIn) :
    ((reindexFiniteRootFamilyController M f family).labeledTree word).1 =
      (family.labeledTree word).1 := by
  change
    (family.labelOf
      ((reindexFiniteRootFamilyController M f family).controlAt word)).1 =
      (family.labelOf (family.controlAt word)).1
  rw [reindexFiniteRootFamilyController_controlAt M f family word]

/-! ## Member projections commute with reindexing -/

/-- Projecting a reindexed family at `index` gives exactly the same labeled
tree as projecting the union family at `f index`. -/
theorem finiteRootMemberController_reindex_labeledTree
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (f : J → I)
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (index : J) :
    (finiteRootMemberController (fun j => M (f j))
        (reindexFiniteRootFamilyController M f family) index).labeledTree =
      (finiteRootMemberController M family (f index)).labeledTree := by
  funext word
  have hcontrol :
      (finiteRootMemberController (fun j => M (f j))
          (reindexFiniteRootFamilyController M f family) index).controlAt word =
        (finiteRootMemberController M family (f index)).controlAt word := by
    apply Prod.ext
    · rw [finiteRootMemberController_control_fst,
        finiteRootMemberController_control_fst]
      exact reindexFiniteRootFamilyController_controlAt M f family word
    · rfl
  change
    (finiteRootMemberController (fun j => M (f j))
        (reindexFiniteRootFamilyController M f family) index).labelOf
        ((finiteRootMemberController (fun j => M (f j))
          (reindexFiniteRootFamilyController M f family) index).controlAt
            word) =
      (finiteRootMemberController M family (f index)).labelOf
        ((finiteRootMemberController M family (f index)).controlAt word)
  rw [hcontrol]
  rcases hmemberControl :
      (finiteRootMemberController M family (f index)).controlAt word with
    ⟨control, selected⟩
  cases selected <;> rfl

/-- Every reindexed member inherits the all-thread guarantee of the original
union controller. -/
theorem finiteRootMemberController_reindex_allThreadsWin
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (f : J → I)
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (hfamily : NarrowedAllThreadsWin (finiteRootFamilyMonitor M)
      family.labeledTree)
    (index : J) :
    NarrowedAllThreadsWin (M (f index))
      (finiteRootMemberController (fun j => M (f j))
        (reindexFiniteRootFamilyController M f family) index).labeledTree := by
  rw [finiteRootMemberController_reindex_labeledTree M f family index]
  exact finiteRootMemberController_allThreadsWin M family hfamily (f index)

/-- Two arbitrary subfamilies of the same union controller still expose the
same sender output, even if they use unrelated reindexing maps. -/
theorem reindexFiniteRootFamilyController_sender_eq
    {K : Type i}
    [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (f : J → I) (g : K → I)
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (left right : List SIn) (hword : left = right) :
    ((reindexFiniteRootFamilyController M f family).labeledTree left).1 =
      ((reindexFiniteRootFamilyController M g family).labeledTree right).1 := by
  subst right
  rw [reindexFiniteRootFamilyController_sender M f family,
    reindexFiniteRootFamilyController_sender M g family]

end

/-! ## One finite move for a descriptor-indexed union of source roots -/

section DescriptorFamily

variable {Descriptor : Type i}
variable (Root : Descriptor → Type i)
variable {RIn : Type u} {SIn : Type v}
variable {ROut : Type x} {SOut : Type y}
variable
  (M : ∀ descriptor, Root descriptor →
    BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

variable [Fintype Descriptor] [DecidableEq Descriptor]
variable [∀ descriptor, Fintype (Root descriptor)]
variable [∀ descriptor, DecidableEq (Root descriptor)]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

/-- The disjoint union of every source root belonging to every finite
descriptor.  The descriptor is proof-side receiver information; it is never
an input of the shared sender controller. -/
noncomputable abbrev descriptorRootUnionMonitor :=
  fun member : Sigma Root => M member.1 member.2

/-- A single finite table for the whole descriptor/root union, bundled with
its universal-thread certificate.  This is the strengthened set-valued move:
individual descriptor moves are projections of this one object, not tables
chosen independently after rationalization. -/
noncomputable abbrev FiniteDescriptorFamilyMove :=
  { table : FiniteRootFamilyTable (descriptorRootUnionMonitor Root M) //
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor (descriptorRootUnionMonitor Root M))
      table.toTransitionRationalTree.labeledTree }

noncomputable instance : Fintype (FiniteDescriptorFamilyMove Root M) := by
  classical
  infer_instance

/-- Construct the strengthened move from one semantic sender shared by the
whole union and arbitrary descriptor/root-indexed receivers.  The universal
narrowing theorem is invoked exactly once. -/
noncomputable def finiteDescriptorFamilyMoveOfStrategies
    [Inhabited (Sigma Root)] [Inhabited RIn] [Inhabited SIn]
    [Inhabited ROut]
    (receiver : ∀ _ : Sigma Root,
      ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ member env,
      (descriptorRootUnionMonitor Root M member).WinsPlay
        (pairPlay (receiver member) sender env)) :
    FiniteDescriptorFamilyMove Root M := by
  let table := finiteRootFamilyTable (descriptorRootUnionMonitor Root M)
    receiver sender hwin
  refine ⟨table, ?_⟩
  exact finiteRootFamilyTable_wins (descriptorRootUnionMonitor Root M)
    receiver sender hwin

/-- Restrict the one union move to all roots belonging to one descriptor.
The returned controller is not rationalized again. -/
noncomputable def FiniteDescriptorFamilyMove.controllerFor
    (move : FiniteDescriptorFamilyMove Root M)
    (descriptor : Descriptor) :
    TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (Root descriptor × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor (M descriptor)).State) :=
  reindexFiniteRootFamilyController
    (descriptorRootUnionMonitor Root M)
    (fun root : Root descriptor => Sigma.mk descriptor root)
    move.1.toTransitionRationalTree

/-- Descriptor projection leaves the shared finite sender control unchanged.
In particular the descriptor is not a leader/orientation signal available to
that control. -/
theorem FiniteDescriptorFamilyMove.controllerFor_controlAt
    (move : FiniteDescriptorFamilyMove Root M)
    (descriptor : Descriptor) (word : List SIn) :
    (move.controllerFor Root M descriptor).controlAt word =
      move.1.toTransitionRationalTree.controlAt word := by
  exact reindexFiniteRootFamilyController_controlAt
    (descriptorRootUnionMonitor Root M)
    (fun root : Root descriptor => Sigma.mk descriptor root)
    move.1.toTransitionRationalTree word

/-- Every descriptor/root member inherits its monitor guarantee from the
single union certificate. -/
theorem FiniteDescriptorFamilyMove.member_allThreadsWin
    (move : FiniteDescriptorFamilyMove Root M)
    (descriptor : Descriptor) (root : Root descriptor) :
    NarrowedAllThreadsWin (M descriptor root)
      (finiteRootMemberController (M descriptor)
        (move.controllerFor Root M descriptor) root).labeledTree := by
  exact finiteRootMemberController_reindex_allThreadsWin
    (descriptorRootUnionMonitor Root M)
    (fun member : Root descriptor => Sigma.mk descriptor member)
    move.1.toTransitionRationalTree move.2 root

/-- The member controller read below one descriptor.  Its control is the
union controller control plus the ordinary one-shot family-root flag; neither
component contains the descriptor or root. -/
noncomputable def FiniteDescriptorFamilyMove.memberController
    (move : FiniteDescriptorFamilyMove Root M)
    (descriptor : Descriptor) (root : Root descriptor) :=
  finiteRootMemberController (M descriptor)
    (move.controllerFor Root M descriptor) root

/-- Member controllers projected from arbitrary descriptors carry exactly
the same runtime control after every sender word. -/
theorem FiniteDescriptorFamilyMove.memberController_controlAt_eq
    (move : FiniteDescriptorFamilyMove Root M)
    (left right : Descriptor) (leftRoot : Root left)
    (rightRoot : Root right) (word : List SIn) :
    (move.memberController Root M left leftRoot).controlAt word =
      (move.memberController Root M right rightRoot).controlAt word := by
  apply Prod.ext
  · simp only [FiniteDescriptorFamilyMove.memberController,
      finiteRootMemberController_control_fst]
    rw [move.controllerFor_controlAt Root M left word,
      move.controllerFor_controlAt Root M right word]
  · rfl

/-- Cross-descriptor member projections have identical sender outputs at
every sender word.  This is the operational coherence law that independent
per-descriptor rationalization could not provide. -/
theorem FiniteDescriptorFamilyMove.memberController_sender_eq
    (move : FiniteDescriptorFamilyMove Root M)
    (left right : Descriptor) (leftRoot : Root left)
    (rightRoot : Root right) (word : List SIn) :
    ((move.memberController Root M left leftRoot).labeledTree word).1 =
      ((move.memberController Root M right rightRoot).labeledTree word).1 := by
  change
    ((move.controllerFor Root M left).labelOf
      (((move.memberController Root M left leftRoot).controlAt word).1)).1 =
    ((move.controllerFor Root M right).labelOf
      (((move.memberController Root M right rightRoot).controlAt word).1)).1
  simp only [FiniteDescriptorFamilyMove.memberController,
    finiteRootMemberController_control_fst]
  rw [move.controllerFor_controlAt Root M left word,
    move.controllerFor_controlAt Root M right word]
  rfl

/-- Projected descriptors share the sender output at every common sender
word, even when their source-root types differ. -/
theorem FiniteDescriptorFamilyMove.sender_eq
    (move : FiniteDescriptorFamilyMove Root M)
    (left right : Descriptor) (word : List SIn) :
    ((move.controllerFor Root M left).labeledTree word).1 =
      ((move.controllerFor Root M right).labeledTree word).1 := by
  simp only [FiniteDescriptorFamilyMove.controllerFor]
  rw [reindexFiniteRootFamilyController_sender,
    reindexFiniteRootFamilyController_sender]

end DescriptorFamily

/-! ## Descriptor-indexed complete-table laws -/

section DescriptorFamilyAllowed

variable {Descriptor : Type i}
variable (Root : Descriptor → Type i)
variable {RIn : Type u} {SIn : Type v}
variable {ROut : Type x} {SOut : Type y}
variable
  (M : ∀ descriptor, Root descriptor →
    BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
variable
  (Allowed : ∀ descriptor,
    (((Root descriptor × RIn) × SIn) → ROut) → Prop)

variable [Fintype Descriptor] [DecidableEq Descriptor]
variable [∀ descriptor, Fintype (Root descriptor)]
variable [∀ descriptor, DecidableEq (Root descriptor)]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

/-- One complete-table predicate on the union receiver table.  Its
`descriptor` projection is exactly the table seen by that descriptor's
source roots. -/
def DescriptorRootUnionAllowed
    (responses : (((Sigma Root) × RIn) × SIn) → ROut) : Prop :=
  ∀ descriptor,
    Allowed descriptor (fun move =>
      responses
        ((Sigma.mk descriptor move.1.1, move.1.2), move.2))

noncomputable instance descriptorRootUnionAllowed_decidable :
    DecidablePred (DescriptorRootUnionAllowed Root Allowed) :=
  fun _ => Classical.propDecidable _

/-- The fixed finite move alphabet obtained by restricting labels with all
descriptor-indexed complete-table laws *before* state-controlled extraction.
The control is the union restricted automaton's state, so it remains shared
by every descriptor projection. -/
noncomputable abbrev FiniteDescriptorFamilyAllowedTable :=
  LocallyConsistentNarrowedTable
    (finiteRootFamilyMonitor (descriptorRootUnionMonitor Root M))
    (DescriptorRootUnionAllowed Root Allowed)

noncomputable instance :
    Fintype (FiniteDescriptorFamilyAllowedTable Root M Allowed) := by
  classical
  infer_instance

/-- A certified union table retaining both parity and every projected
complete-table law.  This—not an old per-source classified table—is the
finite outer move. -/
noncomputable abbrev FiniteDescriptorFamilyAllowedMove :=
  { table : FiniteDescriptorFamilyAllowedTable Root M Allowed //
    NarrowedAllThreadsWin
        (finiteRootFamilyMonitor (descriptorRootUnionMonitor Root M))
        table.toTransitionRationalTree.labeledTree ∧
      NarrowedTablesAllowed
        (finiteRootFamilyMonitor (descriptorRootUnionMonitor Root M))
        (DescriptorRootUnionAllowed Root Allowed)
        table.toTransitionRationalTree.labeledTree }

noncomputable instance :
    Fintype (FiniteDescriptorFamilyAllowedMove Root M Allowed) := by
  classical
  infer_instance

/-- Construct the law-preserving union move in one extraction.  The raw
union receiver must satisfy all descriptor laws at every past; the sender is
still one common semantic strategy. -/
noncomputable def finiteDescriptorFamilyAllowedMoveOfStrategies
    [Inhabited (Sigma Root)] [Inhabited RIn] [Inhabited SIn]
    [Inhabited ROut]
    (defaultTable : (((Sigma Root) × RIn) × SIn) → ROut)
    (hdefault : DescriptorRootUnionAllowed Root Allowed defaultTable)
    (receiver : ∀ _ : Sigma Root,
      ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ member env,
      (descriptorRootUnionMonitor Root M member).WinsPlay
        (pairPlay (receiver member) sender env))
    (hallowed : ∀ past,
      DescriptorRootUnionAllowed Root Allowed
        ((finiteRootFamilyReceiver receiver) past)) :
    FiniteDescriptorFamilyAllowedMove Root M Allowed := by
  let unionMonitor :=
    finiteRootFamilyMonitor (descriptorRootUnionMonitor Root M)
  let unionReceiver := finiteRootFamilyReceiver receiver
  have hunionWin : ∀ env,
      unionMonitor.WinsPlay (pairPlay unionReceiver sender env) :=
    finiteRootFamily_realizable (descriptorRootUnionMonitor Root M)
      receiver sender hwin
  let table := locallyConsistentTableOfStrategies unionMonitor
    (DescriptorRootUnionAllowed Root Allowed) defaultTable hdefault
    unionReceiver sender hunionWin hallowed
  refine ⟨table, ?_, ?_⟩
  · exact locallyConsistentTableOfStrategies_wins unionMonitor
      (DescriptorRootUnionAllowed Root Allowed) defaultTable hdefault
      unionReceiver sender hunionWin hallowed
  · exact locallyConsistentTableOfStrategies_allowed unionMonitor
      (DescriptorRootUnionAllowed Root Allowed) defaultTable hdefault
      unionReceiver sender hunionWin hallowed

/-- Restrict a law-preserving union move to one descriptor without changing
its control or labels. -/
noncomputable def FiniteDescriptorFamilyAllowedMove.controllerFor
    (move : FiniteDescriptorFamilyAllowedMove Root M Allowed)
    (descriptor : Descriptor) :
    TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (Root descriptor × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor (M descriptor)).State) :=
  reindexFiniteRootFamilyController
    (descriptorRootUnionMonitor Root M)
    (fun root : Root descriptor => Sigma.mk descriptor root)
    move.1.toTransitionRationalTree

section
omit [DecidableEq RIn]

/-- Every projected member retains its monitor language. -/
theorem FiniteDescriptorFamilyAllowedMove.member_allThreadsWin
    (move : FiniteDescriptorFamilyAllowedMove Root M Allowed)
    (descriptor : Descriptor) (root : Root descriptor) :
    NarrowedAllThreadsWin (M descriptor root)
      (finiteRootMemberController (M descriptor)
        (move.controllerFor Root M Allowed descriptor) root).labeledTree := by
  exact finiteRootMemberController_reindex_allThreadsWin
    (descriptorRootUnionMonitor Root M)
    (fun member : Root descriptor => Sigma.mk descriptor member)
    move.1.toTransitionRationalTree move.2.1 root

/-- The union table law restricts to the advertised law of every descriptor.
No second state-controlled extraction is used. -/
theorem FiniteDescriptorFamilyAllowedMove.controllerFor_allowed
    (move : FiniteDescriptorFamilyAllowedMove Root M Allowed)
    (descriptor : Descriptor) :
    NarrowedTablesAllowed (finiteRootFamilyMonitor (M descriptor))
      (Allowed descriptor)
      (move.controllerFor Root M Allowed descriptor).labeledTree := by
  intro word state
  have hunion := move.2.2 word
    (reindexFiniteRootFamilyState (descriptorRootUnionMonitor Root M)
      (fun root : Root descriptor => Sigma.mk descriptor root) state)
  have hdescriptor := hunion descriptor
  simpa only [FiniteDescriptorFamilyAllowedMove.controllerFor,
    DescriptorRootUnionAllowed,
    TransitionRationalTree.labeledTree,
    reindexFiniteRootFamilyController_controlAt] using hdescriptor

/-- Descriptor projections of a law-preserving union move still have one
literal sender table. -/
theorem FiniteDescriptorFamilyAllowedMove.sender_eq
    (move : FiniteDescriptorFamilyAllowedMove Root M Allowed)
    (left right : Descriptor) (word : List SIn) :
    ((move.controllerFor Root M Allowed left).labeledTree word).1 =
      ((move.controllerFor Root M Allowed right).labeledTree word).1 := by
  simp only [FiniteDescriptorFamilyAllowedMove.controllerFor]
  rw [reindexFiniteRootFamilyController_sender,
    reindexFiniteRootFamilyController_sender]

end

/-- Readback interface for one descriptor.  Its controller type is allowed
to remain the union automaton state; the finite move itself is the enclosing
`FiniteDescriptorFamilyAllowedMove`. -/
structure DescriptorFamilyProjectedController
    (descriptor : Descriptor)
    (move : FiniteDescriptorFamilyAllowedMove Root M Allowed) where
  controller : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
    (NarrowedBlockLabel (Root descriptor × RIn) SIn ROut SOut
      (finiteRootFamilyMonitor (M descriptor)).State)
  members_win : ∀ root,
    NarrowedAllThreadsWin (M descriptor root)
      (finiteRootMemberController (M descriptor) controller root).labeledTree
  tables_allowed : NarrowedTablesAllowed
    (finiteRootFamilyMonitor (M descriptor)) (Allowed descriptor)
    controller.labeledTree

/-- Canonical readback package of a descriptor projection. -/
noncomputable def FiniteDescriptorFamilyAllowedMove.projectionFor
    (move : FiniteDescriptorFamilyAllowedMove Root M Allowed)
    (descriptor : Descriptor) :
    DescriptorFamilyProjectedController Root M Allowed descriptor move where
  controller := move.controllerFor Root M Allowed descriptor
  members_win := move.member_allThreadsWin Root M Allowed descriptor
  tables_allowed := move.controllerFor_allowed Root M Allowed descriptor

end DescriptorFamilyAllowed

end DistributedSynthesis
