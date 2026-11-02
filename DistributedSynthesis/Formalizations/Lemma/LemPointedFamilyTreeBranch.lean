/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPointedSupportedSuccessor
import DistributedSynthesis.Formalizations.Lemma.LemHiddenDescriptorTreeRationalization

/-!
# Genuine pointed branches of an arbitrary valid public family tree

This is the minimal, monitor-independent branch follower used after a finite
public tree has been extracted for some other acceptance monitor.  It needs
only the literal public tree, nodewise move validity, pointed successor
totality, and one live initial descriptor.  In particular it does not ask for
a semantic state representing the whole public two-fibre family.

The descriptor retained by the cursor is a proof-side coupling coordinate.
It is not added to the public observation, and neither an orientation nor a
strict-leader bit is exposed to a process.
-/

namespace DistributedSynthesis

universe u v m b x

section


variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable {FamilyMove : Type m} {Direction : Type b}
variable [Fintype Code] [Fintype MoveIdentity]
variable [Fintype FamilyMove] [Fintype Direction] [Inhabited Direction]

variable
  (Represented : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
  (Live : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
  (ExactEdge : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
  (Valid : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
  (Supported : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
    FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)

/-- Minimal data required to follow a genuine descriptor-pointed branch of a
public family tree. -/
structure PointedFamilyTreeBranchPackage
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (initialFamily : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity)) where
  totality : PointedHiddenDescriptorFamilyTotality D Represented Live ExactEdge
    Valid Supported
  initialLive : Live initialDescriptor initialFamily
  tree : LabeledTree
    (HiddenDescriptorTreeObservation
      (Direction := Direction)
      (FamilyCode := HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity))) FamilyMove
  movesValid : ObservableMovesValid
    ((default : Direction), initialFamily)
    (fun observation move ↦ Valid observation.2 move) tree

end

section


variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable {FamilyMove : Type m} {Direction : Type b}
variable [Fintype Code] [Fintype MoveIdentity]
variable [Fintype FamilyMove] [Fintype Direction] [Inhabited Direction]

variable
  {Represented : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop}
  {Live : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop}
  {ExactEdge : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop}
  {Valid : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → FamilyMove → Prop}
  {Supported : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
    FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop}

variable [DecidableRel Valid]

namespace PointedFamilyTreeBranchPackage

variable
  (initialDescriptor : HiddenCodeControlDescriptor D
    (MoveIdentity := MoveIdentity))
  (initialFamily : HiddenDescriptorTwoFibreFamily D
    (MoveIdentity := MoveIdentity))
  (package : PointedFamilyTreeBranchPackage D Represented Live ExactEdge Valid
    Supported initialDescriptor initialFamily)

private abbrev Observation := HiddenDescriptorTreeObservation
  (Direction := Direction)
  (FamilyCode := HiddenDescriptorTwoFibreFamily D
    (MoveIdentity := MoveIdentity))

/-- One reached public node coupled to a genuine live descriptor. -/
structure Cursor where
  node : TreeNode
    (Observation D (MoveIdentity := MoveIdentity) (Direction := Direction))
  family : HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity)
  descriptor : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)
  /-- Literal finite-table label at this public node. -/
  treeLabel : FamilyMove
  treeLabel_eq : treeLabel = package.tree node
  family_eq : family =
    (observableAt ((default : Direction), initialFamily) node).2
  live : Live descriptor family

def initialCursor : package.Cursor D initialDescriptor initialFamily where
  node := []
  family := initialFamily
  descriptor := initialDescriptor
  treeLabel := package.tree []
  treeLabel_eq := rfl
  family_eq := rfl
  live := package.initialLive

noncomputable def Cursor.move
    (cursor : package.Cursor D initialDescriptor initialFamily) : FamilyMove :=
  package.tree cursor.node

omit [Fintype FamilyMove] [Fintype Direction] [DecidableRel Valid] in
theorem Cursor.move_valid
    (cursor : package.Cursor D initialDescriptor initialFamily) :
    Valid cursor.family
      (cursor.move D initialDescriptor initialFamily package) := by
  have hvalid := package.movesValid cursor.node
  rw [cursor.family_eq]
  exact hvalid

noncomputable def Cursor.query
    (cursor : package.Cursor D initialDescriptor initialFamily)
    (direction : Direction) :
    PointedSupportedSuccessorQuery D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction) where
  current := cursor.descriptor
  currentFamily := cursor.family
  move := cursor.move D initialDescriptor initialFamily package
  direction := direction

omit [Fintype FamilyMove] [Fintype Direction] [DecidableRel Valid] in
theorem Cursor.exists_answer
    (cursor : package.Cursor D initialDescriptor initialFamily)
    (direction : Direction) :
    ∃ answer,
      pointedSupportedSuccessor? D ExactEdge Supported
          (cursor.query D initialDescriptor initialFamily package direction) =
        some answer ∧
      PointedSupportedSuccessorGood D ExactEdge Supported
        (cursor.query D initialDescriptor initialFamily package direction)
        answer :=
  pointedSupportedSuccessor?_spec D Represented Live ExactEdge Valid Supported
    package.totality
    (cursor.query D initialDescriptor initialFamily package direction)
    cursor.live
    (cursor.move_valid D initialDescriptor initialFamily package)

noncomputable def Cursor.answer
    (cursor : package.Cursor D initialDescriptor initialFamily)
    (direction : Direction) :
    PointedSupportedSuccessorAnswer D (MoveIdentity := MoveIdentity) :=
  Classical.choose
    (cursor.exists_answer D initialDescriptor initialFamily package direction)

omit [Fintype FamilyMove] [Fintype Direction] [DecidableRel Valid] in
theorem Cursor.answer_spec
    (cursor : package.Cursor D initialDescriptor initialFamily)
    (direction : Direction) :
    PointedSupportedSuccessorGood D ExactEdge Supported
      (cursor.query D initialDescriptor initialFamily package direction)
      (cursor.answer D initialDescriptor initialFamily package direction) :=
  (Classical.choose_spec
    (cursor.exists_answer D initialDescriptor initialFamily package
      direction)).2

noncomputable def Cursor.step
    (cursor : package.Cursor D initialDescriptor initialFamily)
    (direction : Direction) :
    package.Cursor D initialDescriptor initialFamily := by
  let answer := cursor.answer D initialDescriptor initialFamily package direction
  have hgood := cursor.answer_spec D initialDescriptor initialFamily package
    direction
  refine
    { node := cursor.node ++ [(direction, answer.1)]
      family := answer.1
      descriptor := answer.2
      treeLabel := package.tree (cursor.node ++ [(direction, answer.1)])
      treeLabel_eq := rfl
      family_eq := ?_
      live := ?_ }
  · simp [observableAt]
  · exact package.totality.target_live cursor.descriptor cursor.family
      (cursor.move D initialDescriptor initialFamily package) direction
      answer.1 answer.2 cursor.live
      (cursor.move_valid D initialDescriptor initialFamily package)
      hgood.1 hgood.2.1

noncomputable def cursorAt (branch : Nat → Direction) : Nat →
    package.Cursor D initialDescriptor initialFamily
  | 0 => package.initialCursor D initialDescriptor initialFamily
  | n + 1 =>
      (cursorAt branch n).step D initialDescriptor initialFamily package
        (branch n)

noncomputable def observationBranch (branch : Nat → Direction) (n : Nat) :
    Observation D (MoveIdentity := MoveIdentity) (Direction := Direction) :=
  let cursor := package.cursorAt D initialDescriptor initialFamily branch n
  let answer := cursor.answer D initialDescriptor initialFamily package
    (branch n)
  (branch n, answer.1)

omit [Fintype FamilyMove] [Fintype Direction] [DecidableRel Valid] in
theorem cursorAt_node (branch : Nat → Direction) : ∀ n,
    (package.cursorAt D initialDescriptor initialFamily branch n).node =
      branchNode
        (package.observationBranch D initialDescriptor initialFamily branch) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        (package.cursorAt D initialDescriptor initialFamily branch n).node ++
            [package.observationBranch D initialDescriptor initialFamily
              branch n] = _
      rw [ih]
      rfl

noncomputable def word (branch : Nat → Direction) :
    OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity))) := fun n =>
  let cursor := package.cursorAt D initialDescriptor initialFamily branch n
  let answer := cursor.answer D initialDescriptor initialFamily package
    (branch n)
  (cursor.move D initialDescriptor initialFamily package,
    (branch n, answer.1))

omit [Fintype FamilyMove] [Fintype Direction] [DecidableRel Valid] in
theorem word_eq_observableThreadWord (branch : Nat → Direction) :
    package.word D initialDescriptor initialFamily branch =
      observableThreadWord package.tree
        (package.observationBranch D initialDescriptor initialFamily branch) := by
  funext n
  change
    (package.tree
        (package.cursorAt D initialDescriptor initialFamily branch n).node,
      package.observationBranch D initialDescriptor initialFamily branch n) =
      (package.tree
        (branchNode
          (package.observationBranch D initialDescriptor initialFamily branch) n),
       package.observationBranch D initialDescriptor initialFamily branch n)
  rw [package.cursorAt_node D initialDescriptor initialFamily branch n]

omit [Fintype FamilyMove] [Fintype Direction] [DecidableRel Valid] in
theorem familyAt_word_eq_cursor_family (branch : Nat → Direction) : ∀ n,
    hiddenDescriptorFamilyAt D initialFamily
        (package.word D initialDescriptor initialFamily branch) n =
      (package.cursorAt D initialDescriptor initialFamily branch n).family := by
  intro n
  cases n with
  | zero => rfl
  | succ n => rfl

noncomputable def admissible (branch : Nat → Direction) :
    PointedHiddenDescriptorFamilyWordAdmissible D Live ExactEdge Valid Supported
      initialDescriptor initialFamily
      (package.word D initialDescriptor initialFamily branch) where
  descriptor := fun n =>
    (package.cursorAt D initialDescriptor initialFamily branch n).descriptor
  initial := rfl
  live := by
    intro n
    rw [package.familyAt_word_eq_cursor_family D initialDescriptor
      initialFamily branch n]
    exact (package.cursorAt D initialDescriptor initialFamily branch n).live
  valid := by
    intro n
    rw [package.familyAt_word_eq_cursor_family D initialDescriptor
      initialFamily branch n]
    exact (package.cursorAt D initialDescriptor initialFamily branch n).move_valid
      D initialDescriptor initialFamily package
  supported := by
    intro n
    rw [package.familyAt_word_eq_cursor_family D initialDescriptor
      initialFamily branch n]
    exact ((package.cursorAt D initialDescriptor initialFamily branch n
      ).answer_spec D initialDescriptor initialFamily package (branch n)).1
  exactEdge := by
    intro n
    exact ((package.cursorAt D initialDescriptor initialFamily branch n
      ).answer_spec D initialDescriptor initialFamily package (branch n)).2.1
  controlStep := by
    intro n
    exact ((package.cursorAt D initialDescriptor initialFamily branch n
      ).answer_spec D initialDescriptor initialFamily package (branch n)).2.2

omit [Fintype FamilyMove] [Fintype Direction] [DecidableRel Valid] in
theorem continuityThread_nonempty (branch : Nat → Direction) :
    Nonempty
      (HiddenDescriptorContinuityThread D initialDescriptor ExactEdge
        (package.word D initialDescriptor initialFamily branch)) :=
  (package.admissible D initialDescriptor initialFamily branch
    ).nonempty_continuityThread D Live ExactEdge Valid Supported
      initialDescriptor initialFamily _

end PointedFamilyTreeBranchPackage

end


end DistributedSynthesis
