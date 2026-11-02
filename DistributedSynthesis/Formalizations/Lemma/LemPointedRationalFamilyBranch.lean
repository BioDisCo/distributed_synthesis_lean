/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPointedSupportedSuccessor
import DistributedSynthesis.Formalizations.Lemma.LemFamilyAwareGuardedHiddenDescriptorTreeAssembly

/-!
# A non-vacuous pointed branch through the extracted rational family tree

The pre-rationalization semantic tree may have a canonical exact thread, but
Rabin extraction is free to choose a different valid move.  Therefore that
old thread does not by itself rule out acceptance of the extracted tree via
the hidden monitor's even dead state.

This file closes the generic post-extraction gap.  Starting from a
state-controlled winning table and descriptor-pointed totality for *every*
valid move, it follows any external direction word.  At each step it reads
the move actually selected by the rational table, evaluates the finite
descriptor-to-answer plan, advertises the selected child family, and retains
the selected exact target descriptor.  The resulting public word is exactly
one branch of the extracted table, has a nonempty exact continuity thread,
and that thread is accepting by the table's universal winning condition.

The chosen descriptor is a proof-side coupling coordinate.  The concrete
model still has to show that a later joint full-view receive evaluates the
same finite plan at the actual descriptor; no descriptor, lane, orientation,
or strict-leader bit is added to either local observation.
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

variable [DecidableRel Valid]

/-- All data needed to follow a genuine pointed branch of one extracted
state-controlled table. -/
structure PointedRationalFamilyBranchPackage
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (initialFamily : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity)) where
  totality : PointedHiddenDescriptorFamilyTotality D Represented Live ExactEdge
    Valid Supported
  initialControl : initialDescriptor.control = D.initial
  initialLive : Live initialDescriptor initialFamily
  table : RunParityTreeAutomaton.StateControlledTreeTable
    (hiddenDescriptorContinuityTreeMonitor D initialDescriptor ExactEdge
      initialFamily Valid).toRunAutomaton
  winning : (hiddenDescriptorContinuityTreeMonitor D initialDescriptor
    ExactEdge initialFamily Valid).WinningTree
      table.toTransitionRationalTree.labeledTree

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

namespace PointedRationalFamilyBranchPackage

variable
  (initialDescriptor : HiddenCodeControlDescriptor D
    (MoveIdentity := MoveIdentity))
  (initialFamily : HiddenDescriptorTwoFibreFamily D
    (MoveIdentity := MoveIdentity))
  (package : PointedRationalFamilyBranchPackage D Represented Live ExactEdge
    Valid Supported initialDescriptor initialFamily)

private abbrev Observation := HiddenDescriptorTreeObservation
  (Direction := Direction)
  (FamilyCode := HiddenDescriptorTwoFibreFamily D
    (MoveIdentity := MoveIdentity))

/-- The extracted public family tree. -/
noncomputable def tree : LabeledTree
    (Observation D (MoveIdentity := MoveIdentity) (Direction := Direction))
    FamilyMove :=
  package.table.toTransitionRationalTree.labeledTree

/-- Every label actually selected by the extracted table is valid at the
family advertised at its node. -/
theorem tree_movesValid :
    ObservableMovesValid
      ((default : Direction), initialFamily)
      (fun observation move ↦ Valid observation.2 move)
      (package.tree D initialDescriptor initialFamily) :=
  ((hiddenDescriptorContinuityTreeMonitor_winning_iff D initialDescriptor
    package.initialControl ExactEdge initialFamily Valid
    (package.tree D initialDescriptor initialFamily)).mp package.winning).1

/-- Proof-side cursor coupling one reached table node with the actual pointed
descriptor and its advertised public family. -/
structure Cursor where
  node : TreeNode
    (Observation D (MoveIdentity := MoveIdentity) (Direction := Direction))
  family : HiddenDescriptorTwoFibreFamily D
    (MoveIdentity := MoveIdentity)
  descriptor : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)
  /-- The finite table state at this public node.  Besides making the cursor
  explicitly table-dependent, this records the controller coordinate that
  the next public observation advances. -/
  tableControl :
    (hiddenDescriptorContinuityTreeMonitor D initialDescriptor ExactEdge
      initialFamily Valid).toRunAutomaton.State
  tableControl_eq : tableControl =
    package.table.toTransitionRationalTree.controlAt node
  family_eq : family =
    (observableAt ((default : Direction), initialFamily) node).2
  live : Live descriptor family

/-- Root cursor. -/
noncomputable def initialCursor :
    package.Cursor D initialDescriptor initialFamily where
  node := []
  family := initialFamily
  descriptor := initialDescriptor
  tableControl := package.table.toTransitionRationalTree.initial
  tableControl_eq := rfl
  family_eq := rfl
  live := package.initialLive

/-- Move actually emitted by the rational table at a cursor. -/
noncomputable def Cursor.move
    (cursor : package.Cursor D initialDescriptor initialFamily) : FamilyMove :=
  package.tree D initialDescriptor initialFamily cursor.node

/-- The emitted move is valid at the cursor's literal family. -/
theorem Cursor.move_valid
    (cursor : package.Cursor D initialDescriptor initialFamily) :
    Valid cursor.family
      (cursor.move D initialDescriptor initialFamily package) := by
  have hvalid := package.tree_movesValid D initialDescriptor
    initialFamily cursor.node
  rw [cursor.family_eq]
  exact hvalid

/-- Finite pointed lookup made at the cursor and the next external direction. -/
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

/-- The selector returns a good answer at every reached cursor. -/
theorem Cursor.exists_answer
    (cursor : package.Cursor D initialDescriptor initialFamily)
    (direction : Direction) :
    ∃ answer,
      pointedSupportedSuccessor? D ExactEdge Supported
          (cursor.query D initialDescriptor initialFamily package
            direction) = some answer ∧
        PointedSupportedSuccessorGood D ExactEdge Supported
          (cursor.query D initialDescriptor initialFamily package
            direction) answer :=
  pointedSupportedSuccessor?_spec D Represented Live ExactEdge Valid Supported
    package.totality
    (cursor.query D initialDescriptor initialFamily package direction)
    cursor.live
    (cursor.move_valid D initialDescriptor initialFamily package)

/-- The answer carried by the fixed finite descriptor-to-answer plan. -/
noncomputable def Cursor.answer
    (cursor : package.Cursor D initialDescriptor initialFamily)
    (direction : Direction) :
    PointedSupportedSuccessorAnswer D (MoveIdentity := MoveIdentity) :=
  Classical.choose
    (cursor.exists_answer D initialDescriptor initialFamily package direction)

theorem Cursor.answer_spec
    (cursor : package.Cursor D initialDescriptor initialFamily)
    (direction : Direction) :
    pointedSupportedSuccessor? D ExactEdge Supported
        (cursor.query D initialDescriptor initialFamily package
          direction) =
        some (cursor.answer D initialDescriptor initialFamily package
          direction) ∧
      PointedSupportedSuccessorGood D ExactEdge Supported
        (cursor.query D initialDescriptor initialFamily package
          direction)
        (cursor.answer D initialDescriptor initialFamily package direction) :=
  Classical.choose_spec
    (cursor.exists_answer D initialDescriptor initialFamily package direction)

/-- Advance the table node along the selected public child family and retain
the exact target of the same pointed answer. -/
noncomputable def Cursor.step
    (cursor : package.Cursor D initialDescriptor initialFamily)
    (direction : Direction) :
    package.Cursor D initialDescriptor initialFamily := by
  let answer := cursor.answer D initialDescriptor initialFamily package direction
  have hgood := (cursor.answer_spec D initialDescriptor initialFamily package
    direction).2
  refine
    { node := cursor.node ++ [(direction, answer.1)]
      family := answer.1
      descriptor := answer.2
      tableControl := package.table.toTransitionRationalTree.controlAt
        (cursor.node ++ [(direction, answer.1)])
      tableControl_eq := rfl
      family_eq := ?_
      live := ?_ }
  · simp [observableAt]
  · exact package.totality.target_live cursor.descriptor cursor.family
      (cursor.move D initialDescriptor initialFamily package) direction
      answer.1 answer.2 cursor.live
      (cursor.move_valid D initialDescriptor initialFamily package)
      hgood.1 hgood.2.1

/-- Cursor reached after the first `n` external directions. -/
noncomputable def cursorAt (branch : Nat → Direction) : Nat →
    package.Cursor D initialDescriptor initialFamily
  | 0 => package.initialCursor D initialDescriptor initialFamily
  | n + 1 =>
      (cursorAt branch n).step D
        initialDescriptor initialFamily package (branch n)

/-- Public observation selected by the pointed plan at depth `n`. -/
noncomputable def observationBranch (branch : Nat → Direction) (n : Nat) :
    Observation D (MoveIdentity := MoveIdentity) (Direction := Direction) :=
  let cursor := package.cursorAt D initialDescriptor initialFamily branch n
  let answer := cursor.answer D initialDescriptor initialFamily package
    (branch n)
  (branch n, answer.1)

/-- The cursor node is exactly the prefix of the selected observation branch. -/
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

/-- Word generated by the actual rational-table move and the selected pointed
answer at every depth. -/
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

/-- The constructed word is literally one observation branch of the extracted
rational table. -/
theorem word_eq_observableThreadWord (branch : Nat → Direction) :
    package.word D initialDescriptor initialFamily branch =
      observableThreadWord
        (package.tree D initialDescriptor initialFamily)
        (package.observationBranch D initialDescriptor initialFamily branch) := by
  funext n
  change
    (package.tree D initialDescriptor initialFamily
        (package.cursorAt D initialDescriptor initialFamily branch n).node,
      package.observationBranch D initialDescriptor initialFamily branch n) =
      (package.tree D initialDescriptor initialFamily
        (branchNode
          (package.observationBranch D initialDescriptor initialFamily branch) n),
       package.observationBranch D initialDescriptor initialFamily branch n)
  rw [package.cursorAt_node D initialDescriptor initialFamily branch n]

/-- Current public family in the constructed word is the cursor family. -/
theorem familyAt_word_eq_cursor_family (branch : Nat → Direction) : ∀ n,
    hiddenDescriptorFamilyAt D initialFamily
        (package.word D initialDescriptor initialFamily branch) n =
      (package.cursorAt D initialDescriptor initialFamily branch n).family := by
  intro n
  cases n with
  | zero => rfl
  | succ n => rfl

/-- Complete pointed admissibility certificate for the branch selected through
the extracted table. -/
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
    exact ((package.cursorAt D initialDescriptor initialFamily branch n).answer_spec
      D initialDescriptor initialFamily package (branch n)).2.1
  exactEdge := by
    intro n
    exact ((package.cursorAt D initialDescriptor initialFamily branch n).answer_spec
      D initialDescriptor initialFamily package (branch n)).2.2.1
  controlStep := by
    intro n
    exact ((package.cursorAt D initialDescriptor initialFamily branch n).answer_spec
      D initialDescriptor initialFamily package (branch n)).2.2.2

/-- The extracted rational table now has a genuine exact thread on every
external direction word; dead-state acceptance cannot be the only witness. -/
theorem continuityThread_nonempty (branch : Nat → Direction) :
    Nonempty
      (HiddenDescriptorContinuityThread D initialDescriptor ExactEdge
        (package.word D initialDescriptor initialFamily branch)) :=
  (package.admissible D initialDescriptor initialFamily branch
    ).nonempty_continuityThread D Live
      ExactEdge Valid Supported initialDescriptor initialFamily _

/-- The selected genuine exact thread is accepting because it lies on one
literal branch of the extracted table's universal winning condition. -/
theorem continuityThread_accepts (branch : Nat → Direction) :
    D.Accepts
      ((package.admissible D initialDescriptor initialFamily branch
        ).toContinuityThread D Live
          ExactEdge Valid Supported initialDescriptor initialFamily _).childCodeWord := by
  have hall :=
    ((hiddenDescriptorContinuityTreeMonitor_winning_iff D initialDescriptor
      package.initialControl ExactEdge initialFamily Valid
      (package.tree D initialDescriptor initialFamily)).mp package.winning).2
      (package.observationBranch D initialDescriptor initialFamily branch)
  rw [← package.word_eq_observableThreadWord D initialDescriptor
    initialFamily branch] at hall
  exact hall
    ((package.admissible D initialDescriptor initialFamily branch
      ).toContinuityThread D Live
        ExactEdge Valid Supported initialDescriptor initialFamily _)

end PointedRationalFamilyBranchPackage

end

end DistributedSynthesis
