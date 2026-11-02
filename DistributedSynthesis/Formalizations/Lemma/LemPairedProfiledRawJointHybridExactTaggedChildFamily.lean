/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialPolicyBank
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointHybridExactRootGuard
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstPolicyRootHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyLeaderFreeKernel

/-!
# The finite exact tagged-child family below a hybrid common control

Every finite common control has two canonical exact guarded roots.  Their
literal children need not coincide, so the recurrent carrier uses a finite
tagged sum: an exact-right child or an exact-left child, each retaining the
common control that determines its dependent source and policy.

The tag is proof-side provenance.  It is not a graph, orientation, or leader
field.  Once a child is selected, its recovered one-sided policy and recurrent
controller bank stay fixed.
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

local notation "CommonControl" =>
  ProfiledRawJointHybridCommonControl A strategy hwin

local notation "Installed" => fun control : CommonControl ↦
  ProfiledRawJointHybridCommonInstalledMove.toCommonMoveData A
    (profiledRawJointHybridCommonControlInstalled A strategy hwin control)

/-! ## The two exact dependent child summands -/

/-- The semantic source selected by the canonical exact-right root at one
common control. -/
abbrev ProfiledRawJointHybridExactRightSelectedSource
    (control : CommonControl) :=
  profiledRawJointRootPinnedSelectedSource A strategy
    ((Installed control).world.oneSidedState A .right)
    (profiledRawJointHybridExactRightRootPredicate A (Installed control))
    (profiledRawJointHybridExactRightPolicy A hwin (Installed control))

/-- Exact-left mirror. -/
abbrev ProfiledRawJointHybridExactLeftSelectedSource
    (control : CommonControl) :=
  profiledRawJointRootPinnedSelectedSource A strategy
    ((Installed control).world.oneSidedState A .left)
    (profiledRawJointHybridExactLeftRootPredicate A (Installed control))
    (profiledRawJointHybridExactLeftPolicy A hwin (Installed control))

/-- A literal child of one canonical exact-right root, tagged by its common
control. -/
abbrev ProfiledRawJointHybridExactRightTaggedChild :=
  Σ control : CommonControl,
    ProfiledRawJointOneSidedLiteralChildCode A strategy
      (ProfiledRawJointHybridExactRightSelectedSource A strategy hwin control)

/-- Exact-left child summand. -/
abbrev ProfiledRawJointHybridExactLeftTaggedChild :=
  Σ control : CommonControl,
    ProfiledRawJointOneSidedLiteralChildCode A strategy
      (ProfiledRawJointHybridExactLeftSelectedSource A strategy hwin control)

/-- The finite heterogeneous child code used below all exact hybrid roots. -/
abbrev ProfiledRawJointHybridExactTaggedChildCode :=
  ProfiledRawJointHybridExactRightTaggedChild A strategy hwin ⊕
    ProfiledRawJointHybridExactLeftTaggedChild A strategy hwin

noncomputable instance profiledRawJointHybridExactTaggedChildCodeFintype :
    Fintype (ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) := by
  classical
  infer_instance

/-! ## Recovering the exact semantic source and fresh policy -/

/-- The literal semantic child represented by a tagged exact-root child. -/
noncomputable def profiledRawJointHybridExactTaggedChildSource
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  match child with
  | .inl child =>
      profiledRawJointOneSidedLiteralChildSource A strategy
        (ProfiledRawJointHybridExactRightSelectedSource A strategy hwin
          child.1) child.2
  | .inr child =>
      profiledRawJointOneSidedLiteralChildSource A strategy
        (ProfiledRawJointHybridExactLeftSelectedSource A strategy hwin
          child.1) child.2

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The recovered source has exactly the incidence code stored in its
corresponding child summand. -/
theorem profiledRawJointHybridExactTaggedChildSource_code
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    (profiledRawJointHybridExactTaggedChildSource A strategy hwin child).code
        A =
      match child with
      | .inl child => child.2.1
      | .inr child => child.2.1 := by
  cases child with
  | inl child =>
      exact profiledRawJointOneSidedLiteralChildSource_code A strategy
        (ProfiledRawJointHybridExactRightSelectedSource A strategy hwin
          child.1) child.2
  | inr child =>
      exact profiledRawJointOneSidedLiteralChildSource_code A strategy
        (ProfiledRawJointHybridExactLeftSelectedSource A strategy hwin
          child.1) child.2

/-- Recover the fresh fixed one-sided policy attached to the exact literal
child. -/
noncomputable def profiledRawJointHybridExactTaggedChildPolicy
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointHybridExactTaggedChildSource A strategy hwin child
        ).code A) := by
  cases child with
  | inl child =>
      let policy :=
        profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin
          ((Installed child.1).world.oneSidedState A .right)
          (profiledRawJointHybridExactRightRootPredicate A
            (Installed child.1))
          (profiledRawJointHybridExactRightPolicy A hwin
            (Installed child.1)) child.2
      simpa only [profiledRawJointHybridExactTaggedChildSource,
        profiledRawJointOneSidedLiteralChildSource_code] using policy
  | inr child =>
      let policy :=
        profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin
          ((Installed child.1).world.oneSidedState A .left)
          (profiledRawJointHybridExactLeftRootPredicate A
            (Installed child.1))
          (profiledRawJointHybridExactLeftPolicy A hwin
            (Installed child.1)) child.2
      simpa only [profiledRawJointHybridExactTaggedChildSource,
        profiledRawJointOneSidedLiteralChildSource_code] using policy

/-- Complete recurrent controller bank below the selected exact child. -/
noncomputable def profiledRawJointHybridExactTaggedChildControllerBank
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (profiledRawJointHybridExactTaggedChildSource A strategy hwin child)
      (profiledRawJointHybridExactTaggedChildPolicy A strategy hwin child) :=
  profiledRawJointUnitPolicyControllerBank A strategy
    (profiledRawJointHybridExactTaggedChildSource A strategy hwin child)
    (profiledRawJointHybridExactTaggedChildPolicy A strategy hwin child)

/-! ## The four finite dependent recurrent carrier families -/

abbrev ProfiledRawJointHybridExactTaggedRightOwner
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :=
  ProfiledRawJointUnitPolicyRightOwner A strategy
    (profiledRawJointHybridExactTaggedChildSource A strategy hwin child)
    (profiledRawJointHybridExactTaggedChildPolicy A strategy hwin child)
    (profiledRawJointHybridExactTaggedChildControllerBank A strategy hwin
      child) ()

abbrev ProfiledRawJointHybridExactTaggedLeftReceiver
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :=
  ProfiledRawJointUnitPolicyLeftReceiver A strategy
    (profiledRawJointHybridExactTaggedChildSource A strategy hwin child)
    (profiledRawJointHybridExactTaggedChildPolicy A strategy hwin child) ()

abbrev ProfiledRawJointHybridExactTaggedRightReceiver
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :=
  ProfiledRawJointUnitPolicyRightReceiver A strategy
    (profiledRawJointHybridExactTaggedChildSource A strategy hwin child)
    (profiledRawJointHybridExactTaggedChildPolicy A strategy hwin child) ()

abbrev ProfiledRawJointHybridExactTaggedLeftOwner
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :=
  ProfiledRawJointUnitPolicyLeftOwner A strategy
    (profiledRawJointHybridExactTaggedChildSource A strategy hwin child)
    (profiledRawJointHybridExactTaggedChildPolicy A strategy hwin child)
    (profiledRawJointHybridExactTaggedChildControllerBank A strategy hwin
      child) ()

noncomputable instance profiledRawJointHybridExactTaggedRightOwnerFintype
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    Fintype (ProfiledRawJointHybridExactTaggedRightOwner A strategy hwin
      child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridExactTaggedLeftReceiverFintype
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    Fintype (ProfiledRawJointHybridExactTaggedLeftReceiver A strategy hwin
      child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridExactTaggedRightReceiverFintype
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    Fintype (ProfiledRawJointHybridExactTaggedRightReceiver A strategy hwin
      child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridExactTaggedLeftOwnerFintype
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    Fintype (ProfiledRawJointHybridExactTaggedLeftOwner A strategy hwin
      child) := by
  classical
  infer_instance

/-! ## Concrete guarded-close roots in the tagged family -/

/-- Package the exact literal child emitted by one canonical right guarded
close in the right summand. -/
def profiledRawJointHybridExactRightTaggedTarget
    (control : CommonControl) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    ProfiledRawJointHybridExactTaggedChildCode A strategy hwin :=
  .inl ⟨control,
    profiledRawJointGuardedFirstRightTarget A strategy
      ((Installed control).world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A (Installed control))
      (profiledRawJointHybridExactRightPolicy A hwin (Installed control))
      row past input⟩

/-- Exact-left close mirror. -/
def profiledRawJointHybridExactLeftTaggedTarget
    (control : CommonControl) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    ProfiledRawJointHybridExactTaggedChildCode A strategy hwin :=
  .inr ⟨control,
    profiledRawJointGuardedFirstLeftTarget A strategy
      ((Installed control).world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A (Installed control))
      (profiledRawJointHybridExactLeftPolicy A hwin (Installed control))
      row past input⟩

/-- The exact right guarded close recovers the reachable left-policy root of
its tagged child. -/
noncomputable def profiledRawJointHybridExactRightTaggedChildRootMacro
    (control : CommonControl) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    let child := profiledRawJointHybridExactRightTaggedTarget A strategy hwin
      control row past input
    ProfiledRawJointUnitLeftPolicyMacro A strategy
      ((profiledRawJointHybridExactTaggedChildSource A strategy hwin child
        ).code A)
      (profiledRawJointHybridExactTaggedChildPolicy A strategy hwin child) := by
  let installed := Installed control
  let literal := profiledRawJointGuardedFirstRightTarget A strategy
    (installed.world.oneSidedState A .right)
    (profiledRawJointHybridExactRightRootPredicate A installed)
    (profiledRawJointHybridExactRightPolicy A hwin installed) row past input
  let child := profiledRawJointHybridExactRightTaggedTarget A strategy hwin
    control row past input
  let policy :=
    profiledRawJointHybridExactTaggedChildPolicy A strategy hwin child
  let activation := profiledRawJointHybridExactRightActivation A hwin installed
  let slot := profiledRawRightChildSlot A (installed.world.procOneSlot A)
    activation.lambda row past input
  have hliteral : literal.1.family.left () = some slot := by
    exact activation.target_active_slot row past input
  have hsource :
      (profiledRawJointHybridExactTaggedChildSource A strategy hwin child).code
          A = literal.1 := by
    exact profiledRawJointHybridExactTaggedChildSource_code A strategy hwin
      child
  have hrootCode :
      (policy.run []).1 =
        (profiledRawJointHybridExactTaggedChildSource A strategy hwin child
          ).code A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  exact {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := slot
    active_slot := by
      rw [hrootCode, hsource]
      exact hliteral }

/-- Left guarded close mirror, recovering a right-policy root. -/
noncomputable def profiledRawJointHybridExactLeftTaggedChildRootMacro
    (control : CommonControl) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let child := profiledRawJointHybridExactLeftTaggedTarget A strategy hwin
      control row past input
    ProfiledRawJointUnitRightPolicyMacro A strategy
      ((profiledRawJointHybridExactTaggedChildSource A strategy hwin child
        ).code A)
      (profiledRawJointHybridExactTaggedChildPolicy A strategy hwin child) := by
  let installed := Installed control
  let literal := profiledRawJointGuardedFirstLeftTarget A strategy
    (installed.world.oneSidedState A .left)
    (profiledRawJointHybridExactLeftRootPredicate A installed)
    (profiledRawJointHybridExactLeftPolicy A hwin installed) row past input
  let child := profiledRawJointHybridExactLeftTaggedTarget A strategy hwin
    control row past input
  let policy :=
    profiledRawJointHybridExactTaggedChildPolicy A strategy hwin child
  let activation := profiledRawJointHybridExactLeftActivation A hwin installed
  let slot := profiledRawLeftChildSlot A (installed.world.procTwoSlot A)
    activation.lambda row past input
  have hliteral : literal.1.family.right () = some slot := by
    exact activation.target_active_slot row past input
  have hsource :
      (profiledRawJointHybridExactTaggedChildSource A strategy hwin child).code
          A = literal.1 := by
    exact profiledRawJointHybridExactTaggedChildSource_code A strategy hwin
      child
  have hrootCode :
      (policy.run []).1 =
        (profiledRawJointHybridExactTaggedChildSource A strategy hwin child
          ).code A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  exact {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := slot
    active_slot := by
      rw [hrootCode, hsource]
      exact hliteral }

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointHybridExactRightTaggedChildRootMacro_state
    (control : CommonControl) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    (profiledRawJointHybridExactRightTaggedChildRootMacro A strategy hwin
      control row past input).state =
      (profiledRawJointHybridExactTaggedChildPolicy A strategy hwin
        (profiledRawJointHybridExactRightTaggedTarget A strategy hwin control
          row past input)).run [] :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointHybridExactLeftTaggedChildRootMacro_state
    (control : CommonControl) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    (profiledRawJointHybridExactLeftTaggedChildRootMacro A strategy hwin
      control row past input).state =
      (profiledRawJointHybridExactTaggedChildPolicy A strategy hwin
        (profiledRawJointHybridExactLeftTaggedTarget A strategy hwin control
          row past input)).run [] :=
  rfl

end


end DetParityAutomaton

end DistributedSynthesis
