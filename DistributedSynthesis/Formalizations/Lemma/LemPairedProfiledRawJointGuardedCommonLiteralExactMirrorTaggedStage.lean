/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactMirrorTaggedExecutableKernel

/-!
# Exact finite stage retained by the mirror heterogeneous seam

The mirror heterogeneous table runs through the whole homogeneous right
block.  Process one remains its blind sender, while process two refreshes the
exact dependent left-policy child, entry row, and ordinary left root emitted
by the true table member.

At the subsequent left reversal, process two uses the locally stored owner
half and process one reads the delivered stage to obtain the matching
receiver half.  No runtime map receives a graph, orientation, hierarchy side,
leader bit, history, or view.
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
  ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedChildCode A strategy hwin
    package

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Extensionality for a fixed left-policy macro.  Its remaining fields are
proofs once the finite state and active slot are fixed. -/
private theorem unitLeftPolicyMacro_ext
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    (left right : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
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

/-! ## Finite exact mirror stage -/

/-- Exact left-policy root most recently emitted by the mirror true member.
The row is retained because it initializes the matching left receiver. -/
structure ProfiledRawJointGuardedCommonLiteralLeftSeamStage
    (package : Package A strategy hwin initial) where
  child : TaggedChild A strategy hwin initial package
  row : PairedEntryRow
  root : ProfiledRawJointUnitLeftPolicyMacro A strategy
    ((package.literalLeftSeamTaggedChildSource A strategy hwin child).code A)
    (package.literalLeftSeamTaggedChildPolicy A strategy hwin child)

noncomputable instance literalLeftSeamStageFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
        package) := by
  classical
  let Rep := Σ child : TaggedChild A strategy hwin initial package,
    PairedEntryRow ×
      ProfiledRawJointUnitLeftPolicyMacro A strategy
        ((package.literalLeftSeamTaggedChildSource A strategy hwin child).code
          A)
        (package.literalLeftSeamTaggedChildPolicy A strategy hwin child)
  let equiv :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
          package ≃ Rep := {
    toFun := fun stage ↦ ⟨stage.child, stage.row, stage.root⟩
    invFun := fun stage ↦ ⟨stage.1, stage.2.1, stage.2.2⟩
    left_inv := by intro stage; cases stage; rfl
    right_inv := by
      intro stage
      rcases stage with ⟨child, row, root⟩
      rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-! ## Total live-left-lane inspection -/

/-- Construct the ordinary left root of a tagged child whose left lane is
live. -/
noncomputable def literalLeftSeamRootOfLiveChild
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package)
    (slot : ProfiledRawLeftSlot A)
    (hslot : child.2.1.family.left () = some slot) :
    ProfiledRawJointUnitLeftPolicyMacro A strategy
      ((package.literalLeftSeamTaggedChildSource A strategy hwin child).code A)
      (package.literalLeftSeamTaggedChildPolicy A strategy hwin child) := by
  let source := package.literalLeftSeamTaggedChildSource A strategy hwin child
  let policy := package.literalLeftSeamTaggedChildPolicy A strategy hwin child
  have hrootCode : (policy.run []).1 = source.code A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    have hrootChild : (policy.run []).1 = child.2.1 := by
      simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
    exact hrootChild.trans (package.literalLeftSeamTaggedChildSource_code
      A strategy hwin child).symm
  exact {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := slot
    active_slot := by
      rw [hrootCode]
      rw [package.literalLeftSeamTaggedChildSource_code A strategy hwin]
      exact hslot }

/-- Retain the exact left root iff the table-emitted child has a live left
lane.  `none` only totalizes malformed/off-invariant data. -/
noncomputable def literalLeftSeamStageOfChild
    (package : Package A strategy hwin initial)
    (row : PairedEntryRow)
    (child : TaggedChild A strategy hwin initial package) :
    Option
      (ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
        package) := by
  classical
  by_cases hlive : ∃ slot : ProfiledRawLeftSlot A,
      child.2.1.family.left () = some slot
  · let slot := Classical.choose hlive
    let hslot := Classical.choose_spec hlive
    exact some ⟨child, row,
      package.literalLeftSeamRootOfLiveChild A strategy hwin child slot hslot⟩
  · exact none

@[simp] theorem literalLeftSeamStageOfChild_isSome_iff
    (package : Package A strategy hwin initial)
    (row : PairedEntryRow)
    (child : TaggedChild A strategy hwin initial package) :
    (package.literalLeftSeamStageOfChild A strategy hwin row child).isSome =
        true ↔
      ∃ slot : ProfiledRawLeftSlot A,
        child.2.1.family.left () = some slot := by
  classical
  simp [literalLeftSeamStageOfChild]

theorem literalLeftSeamStageOfChild_child
    (package : Package A strategy hwin initial)
    (row : PairedEntryRow)
    (child : TaggedChild A strategy hwin initial package)
    (stage : ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
      package)
    (hstage : package.literalLeftSeamStageOfChild A strategy hwin row child =
      some stage) :
    stage.child = child := by
  classical
  simp only [literalLeftSeamStageOfChild] at hstage
  split at hstage
  · exact Option.some.inj hstage |>.symm ▸ rfl
  · contradiction

theorem literalLeftSeamStageOfChild_row
    (package : Package A strategy hwin initial)
    (row : PairedEntryRow)
    (child : TaggedChild A strategy hwin initial package)
    (stage : ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
      package)
    (hstage : package.literalLeftSeamStageOfChild A strategy hwin row child =
      some stage) :
    stage.row = row := by
  classical
  simp only [literalLeftSeamStageOfChild] at hstage
  split at hstage
  · exact congrArg
      (fun value :
          ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
            package ↦ value.row)
      (Option.some.inj hstage).symm
  · contradiction

/-- Change only the fresh entry row of a retained left-seam stage.  Its child
and root continue to record the source-row table lookup. -/
noncomputable def literalLeftSeamStageRetag
    (package : Package A strategy hwin initial)
    (entryRow : PairedEntryRow)
    (stage : ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
      package) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
      package :=
  ⟨stage.child, entryRow, stage.root⟩

@[simp] theorem literalLeftSeamStageRetag_child
    (package : Package A strategy hwin initial)
    (entryRow : PairedEntryRow)
    (stage : ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
      package) :
    (package.literalLeftSeamStageRetag A strategy hwin entryRow stage).child =
      stage.child :=
  rfl

@[simp] theorem literalLeftSeamStageRetag_row
    (package : Package A strategy hwin initial)
    (entryRow : PairedEntryRow)
    (stage : ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
      package) :
    (package.literalLeftSeamStageRetag A strategy hwin entryRow stage).row =
      entryRow :=
  rfl

@[simp] theorem literalLeftSeamStageRetag_root
    (package : Package A strategy hwin initial)
    (entryRow : PairedEntryRow)
    (stage : ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
      package) :
    (package.literalLeftSeamStageRetag A strategy hwin entryRow stage).root =
      stage.root :=
  rfl

/-- Child inspection changes with the row only through the retained entry-row
tag. -/
theorem literalLeftSeamStageOfChild_retag
    (package : Package A strategy hwin initial)
    (sourceRow entryRow : PairedEntryRow)
    (child : TaggedChild A strategy hwin initial package) :
    package.literalLeftSeamStageOfChild A strategy hwin entryRow child =
      Option.map
        (package.literalLeftSeamStageRetag A strategy hwin entryRow)
        (package.literalLeftSeamStageOfChild A strategy hwin sourceRow child) := by
  classical
  by_cases hlive : ∃ slot : ProfiledRawLeftSlot A,
      child.2.1.family.left () = some slot
  · simp [literalLeftSeamStageOfChild, hlive, literalLeftSeamStageRetag]
  · simp [literalLeftSeamStageOfChild, hlive]

/-! ## Canonical exact stage -/

/-- Stage emitted by one exact semantic mirror letter. -/
noncomputable def literalLeftSeamExactStage
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin package :=
  ⟨package.literalLeftSeamTaggedTarget A strategy hwin key row past input,
    row,
    package.literalLeftSeamTaggedChildRootMacro A strategy hwin key row past
      input⟩

/-- Exact mirror stage selected from `sourceRow` and entered at the fresh
`entryRow`. -/
noncomputable def literalLeftSeamExactStageAt
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (sourceRow entryRow : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin package :=
  package.literalLeftSeamStageRetag A strategy hwin entryRow
    (package.literalLeftSeamExactStage A strategy hwin key sourceRow past
      input)

@[simp] theorem literalLeftSeamExactStageAt_child
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (sourceRow entryRow : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (package.literalLeftSeamExactStageAt A strategy hwin key sourceRow
      entryRow past input).child =
      package.literalLeftSeamTaggedTarget A strategy hwin key sourceRow past
        input :=
  rfl

@[simp] theorem literalLeftSeamExactStageAt_row
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (sourceRow entryRow : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (package.literalLeftSeamExactStageAt A strategy hwin key sourceRow
      entryRow past input).row = entryRow :=
  rfl

@[simp] theorem literalLeftSeamExactStageAt_root
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (sourceRow entryRow : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (package.literalLeftSeamExactStageAt A strategy hwin key sourceRow
      entryRow past input).root =
      package.literalLeftSeamTaggedChildRootMacro A strategy hwin key sourceRow
        past input :=
  rfl

@[simp] theorem literalLeftSeamExactStage_child
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (package.literalLeftSeamExactStage A strategy hwin key row past input
      ).child =
      package.literalLeftSeamTaggedTarget A strategy hwin key row past input :=
  rfl

@[simp] theorem literalLeftSeamExactStage_row
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (package.literalLeftSeamExactStage A strategy hwin key row past input
      ).row = row :=
  rfl

@[simp] theorem literalLeftSeamExactStage_root
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (package.literalLeftSeamExactStage A strategy hwin key row past input
      ).root =
      package.literalLeftSeamTaggedChildRootMacro A strategy hwin key row past
        input :=
  rfl

/-- The exact semantic target always takes the live branch, and the
reconstructed root is the pinned root. -/
theorem literalLeftSeamStageOfChild_exact
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    package.literalLeftSeamStageOfChild A strategy hwin row
        (package.literalLeftSeamTaggedTarget A strategy hwin key row past
          input) =
      some (package.literalLeftSeamExactStage A strategy hwin key row past
        input) := by
  classical
  let child := package.literalLeftSeamTaggedTarget A strategy hwin key row
    past input
  let root := package.literalLeftSeamTaggedChildRootMacro A strategy hwin key
    row past input
  let policy := package.literalLeftSeamTaggedChildPolicy A strategy hwin child
  have hrootCode : root.state.1 =
      (package.literalLeftSeamTaggedChildSource A strategy hwin child).code A := by
    rw [package.literalLeftSeamTaggedChildRootMacro_state A strategy hwin]
    have hrun := congrArg Prod.fst policy.accepts.1.1
    simpa [policy, sourceFreeBeliefCodeParityRunAutomaton] using hrun
  have hrootLive : child.2.1.family.left () = some root.slot := by
    have hstateFamily := congrArg
      (fun code : ProfiledRawJointIncidenceCode A (I := Unit) ↦
        code.family.left ()) hrootCode
    have hsourceLive :
        ((package.literalLeftSeamTaggedChildSource A strategy hwin child).code
          A).family.left () = some root.slot :=
      hstateFamily.symm.trans root.active_slot
    have hsourceChild := congrArg
      (fun code : ProfiledRawJointIncidenceCode A (I := Unit) ↦
        code.family.left ())
      (package.literalLeftSeamTaggedChildSource_code A strategy hwin child)
    exact hsourceChild.symm.trans hsourceLive
  simp only [literalLeftSeamStageOfChild]
  split
  · rename_i hlive
    let slot := Classical.choose hlive
    have hslotLive : child.2.1.family.left () = some slot :=
      Classical.choose_spec hlive
    have hslot : slot = root.slot := Option.some.inj
      (hslotLive.symm.trans hrootLive)
    have hroot :
        package.literalLeftSeamRootOfLiveChild A strategy hwin child slot
            hslotLive = root := by
      apply unitLeftPolicyMacro_ext
      · rfl
      · exact hslot
    have hstage := congrArg
      (fun value ↦ some
        (ProfiledRawJointGuardedCommonLiteralLeftSeamStage.mk child row
          value)) hroot
    simpa [child, root, literalLeftSeamExactStage] using hstage
  · rename_i hlive
    exact False.elim (hlive ⟨root.slot, hrootLive⟩)

/-- The mirror target selected from one row can be installed at a fresh entry
row while retaining the selected child and root. -/
theorem literalLeftSeamStageOfChild_exactAt
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (sourceRow entryRow : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    package.literalLeftSeamStageOfChild A strategy hwin entryRow
        (package.literalLeftSeamTaggedTarget A strategy hwin key sourceRow past
          input) =
      some (package.literalLeftSeamExactStageAt A strategy hwin key sourceRow
        entryRow past input) := by
  rw [package.literalLeftSeamStageOfChild_retag A strategy hwin sourceRow
    entryRow]
  rw [package.literalLeftSeamStageOfChild_exact A strategy hwin]
  rfl

/-! ## Matched-left reconstruction -/

/-- Process-one receiver reconstructed from the delivered stage. -/
noncomputable def literalLeftSeamStageInitialLeftReceiver
    (package : Package A strategy hwin initial)
    (stage : ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
      package) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftReceiver A strategy
      hwin package stage.child :=
  initialProfiledRawJointUnitLeftPolicyReceiver A strategy
    (package.literalLeftSeamTaggedChildSource A strategy hwin stage.child)
    (package.literalLeftSeamTaggedChildPolicy A strategy hwin stage.child)
    stage.root stage.row

/-- Matching process-two owner reconstructed locally from the same stage. -/
noncomputable def literalLeftSeamStageInitialLeftOwner
    (package : Package A strategy hwin initial)
    (stage : ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
      package) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftOwner A strategy hwin
      package stage.child :=
  initialProfiledRawJointUnitLeftPolicyOwner A strategy
    (package.literalLeftSeamTaggedChildSource A strategy hwin stage.child)
    (package.literalLeftSeamTaggedChildPolicy A strategy hwin stage.child)
    (package.literalLeftSeamTaggedChildControllerBank A strategy hwin
      stage.child)
    stage.root

/-- The mirror stage reconstructs one exact matched-left pair. -/
noncomputable def literalLeftSeamStageMatched
    (package : Package A strategy hwin initial)
    (stage : ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
      package) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamOneControl A strategy hwin
        package ×
      ProfiledRawJointGuardedCommonLiteralLeftSeamTwoControl A strategy hwin
        package :=
  (.leftReceiver stage.child
      (package.literalLeftSeamStageInitialLeftReceiver A strategy hwin stage),
    .leftOwner stage.child
      (package.literalLeftSeamStageInitialLeftOwner A strategy hwin stage))

/-- At an exact semantic letter this is definitionally the checked
matched-left pair. -/
theorem literalLeftSeamExactStage_matched
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    package.literalLeftSeamStageMatched A strategy hwin
        (package.literalLeftSeamExactStage A strategy hwin key row past
          input) =
      package.literalLeftSeamTaggedMatched A strategy hwin key row past input :=
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
