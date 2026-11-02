/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenClassifiedAutomaton
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRootFamilyLocalOverlay

/-!
# A package-free bidirectional open-family belief node

This is the two-shadow finite node that exists before the end-to-end
`PairedInitialProfiledRationalPackage` is assembled.  Its public code stores
both current open-root families, never one selected orientation.  A single
source-free move stores one right table and one left table.  Nature then
supplies both proof-side exit directions, and the two advertised successor
families are cross-swapped into the next bidirectional code.

The node-validity predicate is purely structural: the two move sources must
be exactly the two families in the code.  It contains no semantic
representability or pointed-history existence premise.  Universal block
parity and the classified table laws are separated into `ThreadValid`.

The local T1 law is unconditional for every well-shaped move.  Both hidden
members of either family use the same simultaneous table control, so their
blind output and next blind control are literally equal.  The remaining
model theorem is consequently semantic: a raw winning-strategy history must
produce `ThreadValid` labels at all reachable nodes and its literal child
history must follow the cross-swapped successor code coherently forever.
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

/-! ## Shared local controls for classified open tables -/

/-- The blind process-one control of one right open-family table. -/
abbrev ProfiledOpenRightClassifiedLocalControl
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source) :=
  FiniteRootFamilyLocalOverlay
    (fun member : {root // root ∈ source.1} =>
      profiledOpenRightClassifiedRootMonitor A member.1)
    table.toTransitionRationalTree

/-- Process-two mirror. -/
abbrev ProfiledOpenLeftClassifiedLocalControl
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source) :=
  FiniteRootFamilyLocalOverlay
    (fun member : {root // root ∈ source.1} =>
      profiledOpenLeftClassifiedRootMonitor A member.1)
    table.toTransitionRationalTree

/-- One hidden-member projection of a shared right table.  The second
component is deliberately the shared overlay successor, not a member-indexed
state. -/
def profiledOpenRightClassifiedLocalMemberStep
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (state : ProfiledOpenRightClassifiedLocalControl A source table)
    (member : {root // root ∈ source.1}) (input : In₁) :
    Out₁ × ProfiledOpenRightClassifiedLocalControl A source table :=
  let monitors := fun member : {root // root ∈ source.1} =>
    profiledOpenRightClassifiedRootMonitor A member.1
  let family := table.toTransitionRationalTree
  (((finiteRootMemberController monitors family member).labelOf
      (state.memberControl monitors family member)).1 input,
    state.step monitors family input)

/-- Left hidden-member projection. -/
def profiledOpenLeftClassifiedLocalMemberStep
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (state : ProfiledOpenLeftClassifiedLocalControl A source table)
    (member : {root // root ∈ source.1}) (input : In₂) :
    Out₂ × ProfiledOpenLeftClassifiedLocalControl A source table :=
  let monitors := fun member : {root // root ∈ source.1} =>
    profiledOpenLeftClassifiedRootMonitor A member.1
  let family := table.toTransitionRationalTree
  (((finiteRootMemberController monitors family member).labelOf
      (state.memberControl monitors family member)).1 input,
    state.step monitors family input)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Right local T1 holds at every shared control, not merely initially. -/
theorem profiledOpenRightClassifiedLocalMemberStep_eq
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (state : ProfiledOpenRightClassifiedLocalControl A source table)
    (left right : {root // root ∈ source.1}) (input : In₁) :
    profiledOpenRightClassifiedLocalMemberStep A source table state left input =
      profiledOpenRightClassifiedLocalMemberStep A source table state right
        input := by
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left local T1 mirror. -/
theorem profiledOpenLeftClassifiedLocalMemberStep_eq
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (state : ProfiledOpenLeftClassifiedLocalControl A source table)
    (left right : {root // root ∈ source.1}) (input : In₂) :
    profiledOpenLeftClassifiedLocalMemberStep A source table state left input =
      profiledOpenLeftClassifiedLocalMemberStep A source table state right
        input := by
  rfl

/-! ## Finite bidirectional node -/

/-- Both family shadows, with no selected one.  The first component is the
right-family lane and the second the left-family lane; both lanes are always
present at a node. -/
abbrev ProfiledOpenBiBeliefCode :=
  Finset (ProfiledOpenClassifiedAnchor A) ×
    Finset (ProfiledOpenClassifiedAnchor A)

/-- One label contains both classified family tables. -/
abbrev ProfiledOpenBiBeliefMove :=
  ProfiledOpenClassifiedMove A × ProfiledOpenClassifiedMove A

/-- Proof-side exits for both shadows.  These directions are resolutions of
the universal thread system; they are not observations available to either
process. -/
abbrev ProfiledOpenBiBeliefDirection :=
  ProfiledOpenClassifiedDirection A × ProfiledOpenClassifiedDirection A

noncomputable instance : Fintype (ProfiledOpenBiBeliefCode A) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledOpenBiBeliefMove A) := by
  classical
  infer_instance

/-- Structural source matching only.  The right lane must carry a right move
and the left lane a left move, with exactly the two root sets in the code. -/
def ProfiledOpenBiBeliefValid
    (code : ProfiledOpenBiBeliefCode A)
    (move : ProfiledOpenBiBeliefMove A) : Prop :=
  match move.1, move.2 with
  | .right rightSource _, .left leftSource _ =>
      profiledOpenRightClassifiedRoots A rightSource = code.1 ∧
        profiledOpenLeftClassifiedRoots A leftSource = code.2
  | _, _ => False

/-- The parity/table-law half, kept separate from structural validity.  The
classified validity predicates do not mention semantic representability. -/
def ProfiledOpenBiBeliefThreadValid
    (move : ProfiledOpenBiBeliefMove A) : Prop :=
  move.1.Valid A ∧ move.2.Valid A

/-- Total two-shadow successor.  The left table produces the next right
family and the right table produces the next left family. -/
noncomputable def profiledOpenBiBeliefNext
    (_code : ProfiledOpenBiBeliefCode A)
    (move : ProfiledOpenBiBeliefMove A)
    (direction : ProfiledOpenBiBeliefDirection A) :
    ProfiledOpenBiBeliefCode A :=
  ((move.2.successor A direction.2).2,
    (move.1.successor A direction.1).2)

/-! ## Package-free structural T1 -/

/-- Both family tables satisfy member-independent local behavior at every
shared local control. -/
def ProfiledOpenBiBeliefMove.StructuralT1
    (move : ProfiledOpenBiBeliefMove A) : Prop :=
  match move.1, move.2 with
  | .right rightSource rightTable, .left leftSource leftTable =>
      (∀ (state : ProfiledOpenRightClassifiedLocalControl A rightSource
            rightTable)
          (left right : {root // root ∈ rightSource.1}) (input : In₁),
        profiledOpenRightClassifiedLocalMemberStep A rightSource rightTable
            state left input =
          profiledOpenRightClassifiedLocalMemberStep A rightSource rightTable
            state right input) ∧
      (∀ (state : ProfiledOpenLeftClassifiedLocalControl A leftSource
            leftTable)
          (left right : {root // root ∈ leftSource.1}) (input : In₂),
        profiledOpenLeftClassifiedLocalMemberStep A leftSource leftTable
            state left input =
          profiledOpenLeftClassifiedLocalMemberStep A leftSource leftTable
            state right input)
  | _, _ => False

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Structural source matching is sufficient for local T1. -/
theorem profiledOpenBiBeliefMove_structuralT1_of_valid
    (code : ProfiledOpenBiBeliefCode A)
    (move : ProfiledOpenBiBeliefMove A)
    (hvalid : ProfiledOpenBiBeliefValid A code move) :
    move.StructuralT1 A := by
  rcases move with ⟨rightMove, leftMove⟩
  cases rightMove with
  | sink => simp [ProfiledOpenBiBeliefValid] at hvalid
  | left source table => simp [ProfiledOpenBiBeliefValid] at hvalid
  | right rightSource rightTable =>
      cases leftMove with
      | sink => simp [ProfiledOpenBiBeliefValid] at hvalid
      | right source table => simp [ProfiledOpenBiBeliefValid] at hvalid
      | left leftSource leftTable =>
          change
            (∀ state left right input,
              profiledOpenRightClassifiedLocalMemberStep A rightSource
                  rightTable state left input =
                profiledOpenRightClassifiedLocalMemberStep A rightSource
                  rightTable state right input) ∧
            (∀ state left right input,
              profiledOpenLeftClassifiedLocalMemberStep A leftSource
                  leftTable state left input =
                profiledOpenLeftClassifiedLocalMemberStep A leftSource
                  leftTable state right input)
          exact
            ⟨fun state left right input =>
                profiledOpenRightClassifiedLocalMemberStep_eq A rightSource
                  rightTable state left right input,
              fun state left right input =>
                profiledOpenLeftClassifiedLocalMemberStep_eq A leftSource
                  leftTable state left right input⟩

/-- The package-free T1 interface: no semantic premise occurs. -/
def ProfiledOpenBiBeliefT1
    (code : ProfiledOpenBiBeliefCode A)
    (move : ProfiledOpenBiBeliefMove A) : Prop :=
  ProfiledOpenBiBeliefValid A code move ∧ move.StructuralT1 A

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenBiBeliefT1_of_valid
    (code : ProfiledOpenBiBeliefCode A)
    (move : ProfiledOpenBiBeliefMove A)
    (hvalid : ProfiledOpenBiBeliefValid A code move) :
    ProfiledOpenBiBeliefT1 A code move :=
  ⟨hvalid, profiledOpenBiBeliefMove_structuralT1_of_valid A code move
    hvalid⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The cross-swap is definitionally visible for later thread proofs. -/
@[simp] theorem profiledOpenBiBeliefNext_right
    (code : ProfiledOpenBiBeliefCode A)
    (move : ProfiledOpenBiBeliefMove A)
    (direction : ProfiledOpenBiBeliefDirection A) :
    (profiledOpenBiBeliefNext A code move direction).1 =
      (move.2.successor A direction.2).2 :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenBiBeliefNext_left
    (code : ProfiledOpenBiBeliefCode A)
    (move : ProfiledOpenBiBeliefMove A)
    (direction : ProfiledOpenBiBeliefDirection A) :
    (profiledOpenBiBeliefNext A code move direction).2 =
      (move.1.successor A direction.1).2 :=
  rfl

end


end DetParityAutomaton

end DistributedSynthesis
