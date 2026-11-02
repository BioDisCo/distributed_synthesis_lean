/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeamTaggedExecutableKernel

/-!
# Exact finite stage retained by the right heterogeneous seam

The right heterogeneous table runs through the whole homogeneous left block.
Its blind endpoint therefore stays in the shared table carrier; it must not be
identified with the blind endpoint of the target policy, which belongs to the
opposite process.  The informed receiver instead refreshes one finite stage:
the exact dependent literal child, its entry row, and the ordinary right root
selected by that child.

At the subsequent reversal both local endpoints can construct the two halves
of one matched-right recurrent control from this stage.  The nonreceiver reads
its own stored stage, while the new receiver reads the delivered copy.  No
runtime map receives a graph, hierarchy side, leader bit, history, or view.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev TaggedChild (initial : CommonPoint A strategy)
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy hwin
    package

private abbrev ChildSource (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :=
  package.literalRightSeamTaggedChildSource A strategy hwin child

private abbrev ChildPolicy (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :=
  package.literalRightSeamTaggedChildPolicy A strategy hwin child

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Extensionality for a fixed right-policy macro.  The reachability and
active-lane fields are propositions, so the operational state and live slot
are the complete data. -/
private theorem unitRightPolicyMacro_ext
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    (left right : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
      policy)
    (hstate : left.state = right.state)
    (hslot : left.slot = right.slot) :
    left = right := by
  cases left with
  | mk leftState leftReach leftSlot leftActive =>
      cases right with
      | mk rightState rightReach rightSlot rightActive =>
          cases hstate
          cases hslot
          rfl

/-! ## Finite exact stage -/

/-- Exact right-policy root most recently emitted by the true table member.
The entry row is retained because it initializes the matching receiver and is
not reconstructible from the incidence code alone. -/
structure ProfiledRawJointGuardedCommonLiteralRightSeamStage
    (package : Package A strategy hwin initial) where
  child : TaggedChild A strategy hwin initial package
  row : PairedEntryRow
  root : ProfiledRawJointUnitRightPolicyMacro A strategy
    ((package.literalRightSeamTaggedChildSource A strategy hwin child).code A)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin child)

noncomputable instance literalRightSeamStageFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
        package) := by
  classical
  let Rep := Σ child : TaggedChild A strategy hwin initial package,
    PairedEntryRow ×
      ProfiledRawJointUnitRightPolicyMacro A strategy
        ((package.literalRightSeamTaggedChildSource A strategy hwin child).code
          A)
        (package.literalRightSeamTaggedChildPolicy A strategy hwin child)
  let equiv :
      ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
          package ≃ Rep := {
    toFun := fun stage ↦ ⟨stage.child, stage.row, stage.root⟩
    invFun := fun stage ↦ ⟨stage.1, stage.2.1, stage.2.2⟩
    left_inv := by intro stage; cases stage; rfl
    right_inv := by
      intro stage
      rcases stage with ⟨child, row, root⟩
      rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-! ## Total live-lane inspection -/

/-- Construct the ordinary right root of a tagged child whose right lane is
live.  This is the child-indexed form of the root constructor used at the
pinned semantic letter. -/
noncomputable def literalRightSeamRootOfLiveChild
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package)
    (slot : ProfiledRawRightSlot A)
    (hslot : child.2.1.family.right () = some slot) :
    ProfiledRawJointUnitRightPolicyMacro A strategy
      ((package.literalRightSeamTaggedChildSource A strategy hwin child).code
        A)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin child) := by
  let source := package.literalRightSeamTaggedChildSource A strategy hwin child
  let policy := package.literalRightSeamTaggedChildPolicy A strategy hwin child
  have hrootCode : (policy.run []).1 = source.code A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    have hrootChild : (policy.run []).1 = child.2.1 := by
      simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
    exact hrootChild.trans (package.literalRightSeamTaggedChildSource_code
      A strategy hwin child).symm
  exact {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := slot
    active_slot := by
      rw [hrootCode]
      rw [package.literalRightSeamTaggedChildSource_code A strategy hwin]
      exact hslot }

/-- Inspect a table-emitted child and retain its exact right root exactly when
the required right lane is live.  Reachable true-member records take the
`some` branch; `none` only totalizes malformed/off-invariant table data. -/
noncomputable def literalRightSeamStageOfChild
    (package : Package A strategy hwin initial)
    (row : PairedEntryRow)
    (child : TaggedChild A strategy hwin initial package) :
    Option
      (ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
        package) := by
  classical
  by_cases hlive : ∃ slot : ProfiledRawRightSlot A,
      child.2.1.family.right () = some slot
  · let slot := Classical.choose hlive
    let hslot := Classical.choose_spec hlive
    exact some ⟨child, row,
      package.literalRightSeamRootOfLiveChild A strategy hwin child slot
        hslot⟩
  · exact none

@[simp] theorem literalRightSeamStageOfChild_isSome_iff
    (package : Package A strategy hwin initial)
    (row : PairedEntryRow)
    (child : TaggedChild A strategy hwin initial package) :
    (package.literalRightSeamStageOfChild A strategy hwin row child).isSome =
        true ↔
      ∃ slot : ProfiledRawRightSlot A,
        child.2.1.family.right () = some slot := by
  classical
  simp [literalRightSeamStageOfChild]

theorem literalRightSeamStageOfChild_child
    (package : Package A strategy hwin initial)
    (row : PairedEntryRow)
    (child : TaggedChild A strategy hwin initial package)
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
      hwin package)
    (hstage : package.literalRightSeamStageOfChild A strategy hwin row child =
      some stage) :
    stage.child = child := by
  classical
  simp only [literalRightSeamStageOfChild] at hstage
  split at hstage
  · exact Option.some.inj hstage |>.symm ▸ rfl
  · contradiction

theorem literalRightSeamStageOfChild_row
    (package : Package A strategy hwin initial)
    (row : PairedEntryRow)
    (child : TaggedChild A strategy hwin initial package)
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
      hwin package)
    (hstage : package.literalRightSeamStageOfChild A strategy hwin row child =
      some stage) :
    stage.row = row := by
  classical
  simp only [literalRightSeamStageOfChild] at hstage
  split at hstage
  · exact congrArg
      (fun value :
          ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
            package ↦ value.row)
      (Option.some.inj hstage).symm
  · contradiction

/-- Change only the row at which a retained right-seam root is entered.  The
child and its root still record the source-row table lookup that produced the
stage. -/
noncomputable def literalRightSeamStageRetag
    (package : Package A strategy hwin initial)
    (entryRow : PairedEntryRow)
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
      hwin package) :
    ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
      package :=
  ⟨stage.child, entryRow, stage.root⟩

@[simp] theorem literalRightSeamStageRetag_child
    (package : Package A strategy hwin initial)
    (entryRow : PairedEntryRow)
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
      hwin package) :
    (package.literalRightSeamStageRetag A strategy hwin entryRow stage).child =
      stage.child :=
  rfl

@[simp] theorem literalRightSeamStageRetag_row
    (package : Package A strategy hwin initial)
    (entryRow : PairedEntryRow)
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
      hwin package) :
    (package.literalRightSeamStageRetag A strategy hwin entryRow stage).row =
      entryRow :=
  rfl

@[simp] theorem literalRightSeamStageRetag_root
    (package : Package A strategy hwin initial)
    (entryRow : PairedEntryRow)
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
      hwin package) :
    (package.literalRightSeamStageRetag A strategy hwin entryRow stage).root =
      stage.root :=
  rfl

/-- Inspecting a child is independent of the row except for the row stored in
the resulting stage.  This separates the source row used to select the child
from the fresh row used to enter that child. -/
theorem literalRightSeamStageOfChild_retag
    (package : Package A strategy hwin initial)
    (sourceRow entryRow : PairedEntryRow)
    (child : TaggedChild A strategy hwin initial package) :
    package.literalRightSeamStageOfChild A strategy hwin entryRow child =
      Option.map
        (package.literalRightSeamStageRetag A strategy hwin entryRow)
        (package.literalRightSeamStageOfChild A strategy hwin sourceRow
          child) := by
  classical
  by_cases hlive : ∃ slot : ProfiledRawRightSlot A,
      child.2.1.family.right () = some slot
  · simp [literalRightSeamStageOfChild, hlive, literalRightSeamStageRetag]
  · simp [literalRightSeamStageOfChild, hlive]

/-! ## Canonical pinned stage and exact activation -/

/-- Stage emitted by the semantic pinned letter. -/
noncomputable def literalRightSeamExactStage
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
      package :=
  ⟨package.literalRightSeamTaggedTarget A strategy hwin key row past input,
    row,
    package.literalRightSeamTaggedChildRootMacro A strategy hwin key row past
      input⟩

/-- Exact right stage whose child and root are selected from `sourceRow`, but
whose receiver starts in the fresh `entryRow`. -/
noncomputable def literalRightSeamExactStageAt
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (sourceRow entryRow : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
      package :=
  package.literalRightSeamStageRetag A strategy hwin entryRow
    (package.literalRightSeamExactStage A strategy hwin key sourceRow past
      input)

@[simp] theorem literalRightSeamExactStageAt_child
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (sourceRow entryRow : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (package.literalRightSeamExactStageAt A strategy hwin key sourceRow
      entryRow past input).child =
      package.literalRightSeamTaggedTarget A strategy hwin key sourceRow past
        input :=
  rfl

@[simp] theorem literalRightSeamExactStageAt_row
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (sourceRow entryRow : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (package.literalRightSeamExactStageAt A strategy hwin key sourceRow
      entryRow past input).row = entryRow :=
  rfl

@[simp] theorem literalRightSeamExactStageAt_root
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (sourceRow entryRow : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (package.literalRightSeamExactStageAt A strategy hwin key sourceRow
      entryRow past input).root =
      package.literalRightSeamTaggedChildRootMacro A strategy hwin key
        sourceRow past input :=
  rfl

@[simp] theorem literalRightSeamExactStage_child
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (package.literalRightSeamExactStage A strategy hwin key row past input
      ).child =
      package.literalRightSeamTaggedTarget A strategy hwin key row past input :=
  rfl

@[simp] theorem literalRightSeamExactStage_row
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (package.literalRightSeamExactStage A strategy hwin key row past input
      ).row = row :=
  rfl

@[simp] theorem literalRightSeamExactStage_root
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (package.literalRightSeamExactStage A strategy hwin key row past input
      ).root =
      package.literalRightSeamTaggedChildRootMacro A strategy hwin key row past
        input :=
  rfl

/-- Inspecting the exact semantic target never takes the totalizing `none`
branch: its root certificate supplies the live lane, and uniqueness of the
stored slot identifies the reconstructed root with the pinned root. -/
theorem literalRightSeamStageOfChild_exact
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    package.literalRightSeamStageOfChild A strategy hwin row
        (package.literalRightSeamTaggedTarget A strategy hwin key row past
          input) =
      some (package.literalRightSeamExactStage A strategy hwin key row past
        input) := by
  classical
  let child := package.literalRightSeamTaggedTarget A strategy hwin key row
    past input
  let root := package.literalRightSeamTaggedChildRootMacro A strategy hwin key
    row past input
  let policy := package.literalRightSeamTaggedChildPolicy A strategy hwin child
  have hrootCode : root.state.1 =
      (package.literalRightSeamTaggedChildSource A strategy hwin child).code A := by
    rw [package.literalRightSeamTaggedChildRootMacro_state A strategy hwin]
    have hrun := congrArg Prod.fst policy.accepts.1.1
    simpa [policy, sourceFreeBeliefCodeParityRunAutomaton] using hrun
  have hrootLive : child.2.1.family.right () = some root.slot := by
    have hstateFamily := congrArg
      (fun code : ProfiledRawJointIncidenceCode A (I := Unit) ↦
        code.family.right ()) hrootCode
    have hsourceLive :
        ((package.literalRightSeamTaggedChildSource A strategy hwin child).code
          A).family.right () = some root.slot :=
      hstateFamily.symm.trans root.active_slot
    have hsourceChild := congrArg
      (fun code : ProfiledRawJointIncidenceCode A (I := Unit) ↦
        code.family.right ())
      (package.literalRightSeamTaggedChildSource_code A strategy hwin child)
    exact hsourceChild.symm.trans hsourceLive
  simp only [literalRightSeamStageOfChild]
  split
  · rename_i hlive
    let slot := Classical.choose hlive
    have hslotLive : child.2.1.family.right () = some slot :=
      Classical.choose_spec hlive
    have hslot : slot = root.slot := Option.some.inj
      (hslotLive.symm.trans hrootLive)
    have hroot :
        package.literalRightSeamRootOfLiveChild A strategy hwin child slot
            hslotLive = root := by
      apply unitRightPolicyMacro_ext
      · rfl
      · exact hslot
    have hstage := congrArg
      (fun value ↦ some
        (ProfiledRawJointGuardedCommonLiteralRightSeamStage.mk child row
          value)) hroot
    simpa [child, root, literalRightSeamExactStage] using hstage
  · rename_i hlive
    exact False.elim (hlive ⟨root.slot, hrootLive⟩)

/-- The exact target selected in one row can be installed at a different,
fresh entry row without changing its child or certified root. -/
theorem literalRightSeamStageOfChild_exactAt
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (sourceRow entryRow : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    package.literalRightSeamStageOfChild A strategy hwin entryRow
        (package.literalRightSeamTaggedTarget A strategy hwin key sourceRow
          past input) =
      some (package.literalRightSeamExactStageAt A strategy hwin key sourceRow
        entryRow past input) := by
  rw [package.literalRightSeamStageOfChild_retag A strategy hwin sourceRow
    entryRow]
  rw [package.literalRightSeamStageOfChild_exact A strategy hwin]
  rfl

/-- Process-one owner installed at a reversal from the staged left block. -/
noncomputable def literalRightSeamStageInitialRightOwner
    (package : Package A strategy hwin initial)
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
      package) :
    ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightOwner A strategy
      hwin package stage.child :=
  initialProfiledRawJointUnitRightPolicyOwner A strategy
    (package.literalRightSeamTaggedChildSource A strategy hwin stage.child)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin stage.child)
    (package.literalRightSeamTaggedChildControllerBank A strategy hwin
      stage.child)
    stage.root

/-- Matching process-two receiver, reconstructed from a delivered copy of the
same finite stage. -/
noncomputable def literalRightSeamStageInitialRightReceiver
    (package : Package A strategy hwin initial)
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
      package) :
    ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightReceiver A strategy
      hwin package stage.child :=
  initialProfiledRawJointUnitRightPolicyReceiver A strategy
    (package.literalRightSeamTaggedChildSource A strategy hwin stage.child)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin stage.child)
    stage.root stage.row

/-- The stage alone reconstructs one exact matched-right pair. -/
noncomputable def literalRightSeamStageMatched
    (package : Package A strategy hwin initial)
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
      package) :
    ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
        package ×
      ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
        package :=
  (.rightOwner stage.child
      (package.literalRightSeamStageInitialRightOwner A strategy hwin stage),
    .rightReceiver stage.child
      (package.literalRightSeamStageInitialRightReceiver A strategy hwin
        stage))

/-- At the pinned semantic letter, activation from the retained stage is
definitionally the previously checked exact matched pair. -/
theorem literalRightSeamExactStage_matched
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    package.literalRightSeamStageMatched A strategy hwin
        (package.literalRightSeamExactStage A strategy hwin key row past
          input) =
      package.literalRightSeamTaggedMatched A strategy hwin key row past
        input :=
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
