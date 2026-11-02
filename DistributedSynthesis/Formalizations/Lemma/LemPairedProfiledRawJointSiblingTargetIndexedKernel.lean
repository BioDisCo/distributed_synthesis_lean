/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSiblingHiddenThreadContinuation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitFixedPolicyParity
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointIndexedPolicyLeaderFreeKernel

/-!
# One finite indexed recurrent family below the shared sibling relations

The pre-policy sibling construction has two finite target alphabets: targets
of a right/common--strict-left block and targets of its left mirror.  Every
such target already has an exact one-sided semantic representative and an
unconditional finite rational policy.  This file takes their disjoint union
and feeds it into the existing indexed leader-free recurrent kernel.

The sum tag records which checked target relation supplied the child.  It is
finite proof-side provenance, not a graph, orientation, strict-leader, or
hidden sibling observation.  Runtime transitions below a selected child use
only the local `recv`/`noRecv` signatures of the indexed kernel.
-/

namespace DistributedSynthesis

universe u v x y s i₁ i₂ e₁ e₂

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
  (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
  (direction : ProfiledRawJointFamilyDirection
    (I := Unit) (In₁ := In₁) (In₂ := In₂))

/-! ## Finite child key and its exact recurrent data -/

/-- All checked targets of the two shared sibling relations. -/
abbrev ProfiledRawJointSiblingTargetChildCode :=
  ProfiledRawJointRightSiblingChildCode A family direction ⊕
    ProfiledRawJointLeftSiblingChildCode A family direction

noncomputable instance profiledRawJointSiblingTargetChildCodeFintype :
    Fintype (ProfiledRawJointSiblingTargetChildCode A strategy family
      direction) := by
  classical
  infer_instance

noncomputable instance profiledRawJointSiblingTargetChildCodeDecidableEq :
    DecidableEq (ProfiledRawJointSiblingTargetChildCode A strategy family
      direction) :=
  Classical.decEq _

def profiledRawJointSiblingTargetChildOfRight
    (child : ProfiledRawJointRightSiblingChildCode A family direction) :
    ProfiledRawJointSiblingTargetChildCode A strategy family direction :=
  .inl child

def profiledRawJointSiblingTargetChildOfLeft
    (child : ProfiledRawJointLeftSiblingChildCode A family direction) :
    ProfiledRawJointSiblingTargetChildCode A strategy family direction :=
  .inr child

/-- Recover the exact one-sided source represented by a checked target. -/
noncomputable def profiledRawJointSiblingTargetChildSource
    (child : ProfiledRawJointSiblingTargetChildCode A strategy family
      direction) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) := by
  cases child with
  | inl right =>
      exact profiledRawJointRightSiblingChildSource A family direction right
  | inr left =>
      exact profiledRawJointLeftSiblingChildSource A family direction left

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

@[simp] theorem profiledRawJointSiblingTargetChildSource_right
    (child : ProfiledRawJointRightSiblingChildCode A family direction) :
    profiledRawJointSiblingTargetChildSource A strategy family direction
        (profiledRawJointSiblingTargetChildOfRight A strategy family direction
          child) =
      profiledRawJointRightSiblingChildSource A family direction child :=
  rfl

@[simp] theorem profiledRawJointSiblingTargetChildSource_left
    (child : ProfiledRawJointLeftSiblingChildCode A family direction) :
    profiledRawJointSiblingTargetChildSource A strategy family direction
        (profiledRawJointSiblingTargetChildOfLeft A strategy family direction
          child) =
      profiledRawJointLeftSiblingChildSource A family direction child :=
  rfl

/-- The source code is literally the finite target stored by the child key. -/
@[simp] theorem profiledRawJointSiblingTargetChildSource_code_right
    (child : ProfiledRawJointRightSiblingChildCode A family direction) :
    (profiledRawJointSiblingTargetChildSource A strategy family direction
      (profiledRawJointSiblingTargetChildOfRight A strategy family direction
        child)
      ).code A = child.1 := by
  exact profiledRawJointRightSiblingChildSource_code A family direction child

@[simp] theorem profiledRawJointSiblingTargetChildSource_code_left
    (child : ProfiledRawJointLeftSiblingChildCode A family direction) :
    (profiledRawJointSiblingTargetChildSource A strategy family direction
      (profiledRawJointSiblingTargetChildOfLeft A strategy family direction
        child)
      ).code A = child.1 := by
  exact profiledRawJointLeftSiblingChildSource_code A family direction child

end

include hwin in
/-- Select one fixed rational policy once for every finite child key. -/
noncomputable def profiledRawJointSiblingTargetChildPolicy
    (child : ProfiledRawJointSiblingTargetChildCode A strategy family
      direction) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointSiblingTargetChildSource A strategy family direction
        child).code A) := by
  cases child with
  | inl right =>
      simpa only [profiledRawJointSiblingTargetChildSource,
        profiledRawJointRightSiblingChildSource_code] using
        (profiledRawJointRightSiblingChildPolicy A hwin family direction right)
  | inr left =>
      simpa only [profiledRawJointSiblingTargetChildSource,
        profiledRawJointLeftSiblingChildSource_code] using
        (profiledRawJointLeftSiblingChildPolicy A hwin family direction left)

/-- The ordinary recurrent controller bank belonging to the selected child
policy. -/
noncomputable def profiledRawJointSiblingTargetChildControllerBank
    (child : ProfiledRawJointSiblingTargetChildCode A strategy family
      direction) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (profiledRawJointSiblingTargetChildSource A strategy family direction
        child)
      (profiledRawJointSiblingTargetChildPolicy A strategy hwin family
        direction child) :=
  profiledRawJointUnitPolicyControllerBank A strategy
    (profiledRawJointSiblingTargetChildSource A strategy family direction child)
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction
      child)

/-! ## Exact root installation at a checked physical close -/

include hwin in
/-- The selected child policy together with its literal root macro.  This is
finite recurrent data indexed by the checked target; the semantic source is
used only to prove the root equation. -/
structure ProfiledRawJointSiblingTargetChildRootPackage
    (child : ProfiledRawJointSiblingTargetChildCode A strategy family
      direction) where
  seed : ProfiledRawJointUnitFixedPolicyRoot A strategy
    ((profiledRawJointSiblingTargetChildSource A strategy family direction
      child).code A)
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction
      child)
  seed_state : ProfiledRawJointUnitFixedPolicyRoot.state A
      (profiledRawJointSiblingTargetChildPolicy A strategy hwin family
        direction child) seed =
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction
      child).run []

/-- Orientation-refined package produced by a right close.  Its root is a
left macro, so a local close transition can initialize the left-owner family
without inspecting a proof-side sum tag. -/
structure ProfiledRawJointRightSiblingTargetChildRootPackage
    (child : ProfiledRawJointRightSiblingChildCode A family direction) where
  seed : ProfiledRawJointUnitLeftPolicyMacro A strategy
    ((profiledRawJointSiblingTargetChildSource A strategy family direction
      (profiledRawJointSiblingTargetChildOfRight A strategy family direction
        child)).code A)
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction
      (profiledRawJointSiblingTargetChildOfRight A strategy family direction
        child))
  seed_state : seed.state =
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction
      (profiledRawJointSiblingTargetChildOfRight A strategy family direction
        child)).run []

/-- Orientation-refined mirror produced by a left close. -/
structure ProfiledRawJointLeftSiblingTargetChildRootPackage
    (child : ProfiledRawJointLeftSiblingChildCode A family direction) where
  seed : ProfiledRawJointUnitRightPolicyMacro A strategy
    ((profiledRawJointSiblingTargetChildSource A strategy family direction
      (profiledRawJointSiblingTargetChildOfLeft A strategy family direction
        child)).code A)
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction
      (profiledRawJointSiblingTargetChildOfLeft A strategy family direction
        child))
  seed_state : seed.state =
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction
      (profiledRawJointSiblingTargetChildOfLeft A strategy family direction
        child)).run []

section
omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂]

/-- A right close supplies the orientation-refined left root. -/
theorem
    nonempty_profiledRawJointRightSiblingTargetChildRootPackage_of_close
    (child : ProfiledRawJointRightSiblingChildCode A family direction)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A child.1) =
      pairedRightCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointRightSiblingTargetChildRootPackage A strategy hwin
        family direction child) := by
  classical
  let combined := profiledRawJointSiblingTargetChildOfRight A strategy family
    direction child
  let source := profiledRawJointSiblingTargetChildSource A strategy family
    direction combined
  let policy := profiledRawJointSiblingTargetChildPolicy A strategy hwin family
    direction combined
  have hrootCode : (policy.run []).1 = source.code A :=
    congrArg Prod.fst policy.accepts.1.1
  cases hslot : child.1.family.left () with
  | none =>
      simp [profiledRawJointUnitRightTargetProjection, hslot,
        erasePairedProfiledState, pairedRightCloseTarget] at hclose
  | some slot =>
      let seed : ProfiledRawJointUnitLeftPolicyMacro A strategy
          (source.code A) policy := {
        state := policy.run []
        reachable := ⟨[], rfl⟩
        slot := slot
        active_slot := by
          rw [hrootCode]
          simpa [source, combined] using hslot }
      exact ⟨⟨seed, rfl⟩⟩

/-- Left-close orientation-refined mirror. -/
theorem
    nonempty_profiledRawJointLeftSiblingTargetChildRootPackage_of_close
    (child : ProfiledRawJointLeftSiblingChildCode A family direction)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A child.1) =
      pairedLeftCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointLeftSiblingTargetChildRootPackage A strategy hwin family
        direction child) := by
  classical
  let combined := profiledRawJointSiblingTargetChildOfLeft A strategy family
    direction child
  let source := profiledRawJointSiblingTargetChildSource A strategy family
    direction combined
  let policy := profiledRawJointSiblingTargetChildPolicy A strategy hwin family
    direction combined
  have hrootCode : (policy.run []).1 = source.code A :=
    congrArg Prod.fst policy.accepts.1.1
  cases hslot : child.1.family.right () with
  | none =>
      simp [profiledRawJointUnitLeftTargetProjection, hslot,
        erasePairedProfiledState, pairedLeftCloseTarget] at hclose
  | some slot =>
      let seed : ProfiledRawJointUnitRightPolicyMacro A strategy
          (source.code A) policy := {
        state := policy.run []
        reachable := ⟨[], rfl⟩
        slot := slot
        active_slot := by
          rw [hrootCode]
          simpa [source, combined] using hslot }
      exact ⟨⟨seed, rfl⟩⟩

/-- A checked right close initializes the selected target policy at a literal
left root. -/
theorem nonempty_profiledRawJointSiblingTargetChildRootPackage_of_rightClose
    (child : ProfiledRawJointRightSiblingChildCode A family direction)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A child.1) =
      pairedRightCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointSiblingTargetChildRootPackage A strategy hwin family
        direction
        (profiledRawJointSiblingTargetChildOfRight A strategy family direction
          child)) := by
  classical
  let combined := profiledRawJointSiblingTargetChildOfRight A strategy family
    direction child
  let source := profiledRawJointSiblingTargetChildSource A strategy family
    direction combined
  let policy := profiledRawJointSiblingTargetChildPolicy A strategy hwin family
    direction combined
  have hrootCode : (policy.run []).1 = source.code A :=
    congrArg Prod.fst policy.accepts.1.1
  cases hslot : child.1.family.left () with
  | none =>
      simp [profiledRawJointUnitRightTargetProjection, hslot,
        erasePairedProfiledState, pairedRightCloseTarget] at hclose
  | some slot =>
      let seed : ProfiledRawJointUnitLeftPolicyMacro A strategy
          (source.code A) policy := {
        state := policy.run []
        reachable := ⟨[], rfl⟩
        slot := slot
        active_slot := by
          rw [hrootCode]
          simpa [source, combined] using hslot }
      exact ⟨⟨.inr seed, rfl⟩⟩

/-- Checked left-close mirror: initialize at a literal right root. -/
theorem nonempty_profiledRawJointSiblingTargetChildRootPackage_of_leftClose
    (child : ProfiledRawJointLeftSiblingChildCode A family direction)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A child.1) =
      pairedLeftCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointSiblingTargetChildRootPackage A strategy hwin family
        direction
        (profiledRawJointSiblingTargetChildOfLeft A strategy family direction
          child)) := by
  classical
  let combined := profiledRawJointSiblingTargetChildOfLeft A strategy family
    direction child
  let source := profiledRawJointSiblingTargetChildSource A strategy family
    direction combined
  let policy := profiledRawJointSiblingTargetChildPolicy A strategy hwin family
    direction combined
  have hrootCode : (policy.run []).1 = source.code A :=
    congrArg Prod.fst policy.accepts.1.1
  cases hslot : child.1.family.right () with
  | none =>
      simp [profiledRawJointUnitLeftTargetProjection, hslot,
        erasePairedProfiledState, pairedLeftCloseTarget] at hclose
  | some slot =>
      let seed : ProfiledRawJointUnitRightPolicyMacro A strategy
          (source.code A) policy := {
        state := policy.run []
        reachable := ⟨[], rfl⟩
        slot := slot
        active_slot := by
          rw [hrootCode]
          simpa [source, combined] using hslot }
      exact ⟨⟨.inl seed, rfl⟩⟩

end

/-! ## The local indexed recurrent kernel -/

abbrev ProfiledRawJointSiblingTargetRightOwner
    (child : ProfiledRawJointSiblingTargetChildCode A strategy family
      direction) :=
  ProfiledRawJointIndexedPolicyRightOwner A strategy
    (ProfiledRawJointSiblingTargetChildCode A strategy family direction)
    (profiledRawJointSiblingTargetChildSource A strategy family direction)
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction)
    (profiledRawJointSiblingTargetChildControllerBank A strategy hwin family
      direction) child

abbrev ProfiledRawJointSiblingTargetLeftReceiver
    (child : ProfiledRawJointSiblingTargetChildCode A strategy family
      direction) :=
  ProfiledRawJointIndexedPolicyLeftReceiver A strategy
    (ProfiledRawJointSiblingTargetChildCode A strategy family direction)
    (profiledRawJointSiblingTargetChildSource A strategy family direction)
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction)
    child

abbrev ProfiledRawJointSiblingTargetRightReceiver
    (child : ProfiledRawJointSiblingTargetChildCode A strategy family
      direction) :=
  ProfiledRawJointIndexedPolicyRightReceiver A strategy
    (ProfiledRawJointSiblingTargetChildCode A strategy family direction)
    (profiledRawJointSiblingTargetChildSource A strategy family direction)
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction)
    child

abbrev ProfiledRawJointSiblingTargetLeftOwner
    (child : ProfiledRawJointSiblingTargetChildCode A strategy family
      direction) :=
  ProfiledRawJointIndexedPolicyLeftOwner A strategy
    (ProfiledRawJointSiblingTargetChildCode A strategy family direction)
    (profiledRawJointSiblingTargetChildSource A strategy family direction)
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction)
    (profiledRawJointSiblingTargetChildControllerBank A strategy hwin family
      direction) child

namespace ProfiledRawJointRightSiblingTargetChildRootPackage

/-- Install the checked right close as the next left owner. -/
noncomputable def initialLeftOwner
    (child : ProfiledRawJointRightSiblingChildCode A family direction)
    (package : ProfiledRawJointRightSiblingTargetChildRootPackage A strategy
      hwin family direction child) :
    ProfiledRawJointSiblingTargetLeftOwner A strategy hwin family direction
      (profiledRawJointSiblingTargetChildOfRight A strategy family direction
        child) :=
  initialProfiledRawJointUnitLeftPolicyOwner A strategy
    (profiledRawJointSiblingTargetChildSource A strategy family direction
      (profiledRawJointSiblingTargetChildOfRight A strategy family direction
        child))
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction
      (profiledRawJointSiblingTargetChildOfRight A strategy family direction
        child))
    (profiledRawJointSiblingTargetChildControllerBank A strategy hwin family
      direction
      (profiledRawJointSiblingTargetChildOfRight A strategy family direction
        child)) package.seed

/-- Install the same checked target and row as the next left receiver. -/
noncomputable def initialLeftReceiver
    (child : ProfiledRawJointRightSiblingChildCode A family direction)
    (package : ProfiledRawJointRightSiblingTargetChildRootPackage A strategy
      hwin family direction child)
    (row : PairedEntryRow) :
    ProfiledRawJointSiblingTargetLeftReceiver A strategy hwin family direction
      (profiledRawJointSiblingTargetChildOfRight A strategy family direction
        child) :=
  initialProfiledRawJointUnitLeftPolicyReceiver A strategy
    (profiledRawJointSiblingTargetChildSource A strategy family direction
      (profiledRawJointSiblingTargetChildOfRight A strategy family direction
        child))
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction
      (profiledRawJointSiblingTargetChildOfRight A strategy family direction
        child)) package.seed row

end ProfiledRawJointRightSiblingTargetChildRootPackage

namespace ProfiledRawJointLeftSiblingTargetChildRootPackage

/-- Install a checked left close as the next right owner. -/
noncomputable def initialRightOwner
    (child : ProfiledRawJointLeftSiblingChildCode A family direction)
    (package : ProfiledRawJointLeftSiblingTargetChildRootPackage A strategy
      hwin family direction child) :
    ProfiledRawJointSiblingTargetRightOwner A strategy hwin family direction
      (profiledRawJointSiblingTargetChildOfLeft A strategy family direction
        child) :=
  initialProfiledRawJointUnitRightPolicyOwner A strategy
    (profiledRawJointSiblingTargetChildSource A strategy family direction
      (profiledRawJointSiblingTargetChildOfLeft A strategy family direction
        child))
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction
      (profiledRawJointSiblingTargetChildOfLeft A strategy family direction
        child))
    (profiledRawJointSiblingTargetChildControllerBank A strategy hwin family
      direction
      (profiledRawJointSiblingTargetChildOfLeft A strategy family direction
        child)) package.seed

/-- Install the same checked target and row as the next right receiver. -/
noncomputable def initialRightReceiver
    (child : ProfiledRawJointLeftSiblingChildCode A family direction)
    (package : ProfiledRawJointLeftSiblingTargetChildRootPackage A strategy
      hwin family direction child)
    (row : PairedEntryRow) :
    ProfiledRawJointSiblingTargetRightReceiver A strategy hwin family direction
      (profiledRawJointSiblingTargetChildOfLeft A strategy family direction
        child) :=
  initialProfiledRawJointUnitRightPolicyReceiver A strategy
    (profiledRawJointSiblingTargetChildSource A strategy family direction
      (profiledRawJointSiblingTargetChildOfLeft A strategy family direction
        child))
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction
      (profiledRawJointSiblingTargetChildOfLeft A strategy family direction
        child)) package.seed row

end ProfiledRawJointLeftSiblingTargetChildRootPackage

/-- The genuinely local finite-front seam above the sibling-target family. -/
abbrev ProfiledRawJointSiblingTargetExceptionalAdapter
    (InitialOne : Type i₁) (InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂) :=
  ProfiledRawJointIndexedPolicyExceptionalAdapter A strategy
    (ProfiledRawJointSiblingTargetChildCode A strategy family direction)
    (profiledRawJointSiblingTargetChildSource A strategy family direction)
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction)
    (profiledRawJointSiblingTargetChildControllerBank A strategy hwin family
      direction) InitialOne InitialTwo ExceptionalOne ExceptionalTwo

/-- Any local exceptional adapter now yields the complete recurrent kernel
for every checked sibling target. -/
noncomputable def profiledRawJointSiblingTargetLeaderFreeKernel
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointSiblingTargetExceptionalAdapter A strategy hwin
      family direction InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :
    ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂ InitialOne
      InitialTwo ExceptionalOne ExceptionalTwo
      (ProfiledRawJointSiblingTargetChildCode A strategy family direction)
      (ProfiledRawJointSiblingTargetRightOwner A strategy hwin family direction)
      (ProfiledRawJointSiblingTargetLeftReceiver A strategy hwin family
        direction)
      (ProfiledRawJointSiblingTargetRightReceiver A strategy hwin family
        direction)
      (ProfiledRawJointSiblingTargetLeftOwner A strategy hwin family direction) :=
  profiledRawJointIndexedPolicyLeaderFreeKernel A strategy
    (ProfiledRawJointSiblingTargetChildCode A strategy family direction)
    (profiledRawJointSiblingTargetChildSource A strategy family direction)
    (profiledRawJointSiblingTargetChildPolicy A strategy hwin family direction)
    (profiledRawJointSiblingTargetChildControllerBank A strategy hwin family
      direction) adapter

/-! ## Direct finite-move handoff into the indexed family -/

/-- Every target emitted by the canonical right sibling move is already a key
of the indexed family, has the advertised public code, and installs its fixed
policy at a literal recurrent root. -/
theorem profiledRawJointRightPhysicalSiblingMoveOf_targetIndexedRoot
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let move := profiledRawJointRightPhysicalSiblingMoveOf A hwin family
      direction semanticMember hmember
    let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    let target := (play n).2.1.target row
    ∃ child : ProfiledRawJointSiblingTargetChildCode A strategy family
        direction,
      (profiledRawJointSiblingTargetChildSource A strategy family direction
        child).code A = target ∧
      Nonempty
        (ProfiledRawJointSiblingTargetChildRootPackage A strategy hwin family
          direction child) := by
  dsimp only
  obtain ⟨hclose, htarget⟩ :=
    profiledRawJointRightPhysicalSiblingMoveOf_targetSafe_shared A hwin family
      direction semanticMember hmember member env n row
  let rightChild : ProfiledRawJointRightSiblingChildCode A family direction :=
    ⟨_, htarget⟩
  let child := profiledRawJointSiblingTargetChildOfRight A strategy family
    direction rightChild
  refine ⟨child, ?_, ?_⟩
  · exact profiledRawJointSiblingTargetChildSource_code_right A strategy family
      direction rightChild
  · exact
      nonempty_profiledRawJointSiblingTargetChildRootPackage_of_rightClose A
        strategy hwin family direction rightChild _ row _ hclose

/-- Left finite-move mirror. -/
theorem profiledRawJointLeftPhysicalSiblingMoveOf_targetIndexedRoot
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let move := profiledRawJointLeftPhysicalSiblingMoveOf A hwin family
      direction semanticMember hmember
    let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    let target := (play n).2.1.target row
    ∃ child : ProfiledRawJointSiblingTargetChildCode A strategy family
        direction,
      (profiledRawJointSiblingTargetChildSource A strategy family direction
        child).code A = target ∧
      Nonempty
        (ProfiledRawJointSiblingTargetChildRootPackage A strategy hwin family
          direction child) := by
  dsimp only
  obtain ⟨hclose, htarget⟩ :=
    profiledRawJointLeftPhysicalSiblingMoveOf_targetSafe_shared A hwin family
      direction semanticMember hmember member env n row
  let leftChild : ProfiledRawJointLeftSiblingChildCode A family direction :=
    ⟨_, htarget⟩
  let child := profiledRawJointSiblingTargetChildOfLeft A strategy family
    direction leftChild
  refine ⟨child, ?_, ?_⟩
  · exact profiledRawJointSiblingTargetChildSource_code_left A strategy family
      direction leftChild
  · exact
      nonempty_profiledRawJointSiblingTargetChildRootPackage_of_leftClose A
        strategy hwin family direction leftChild _ row _ hclose

end

end DetParityAutomaton

end DistributedSynthesis
