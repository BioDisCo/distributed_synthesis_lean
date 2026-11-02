/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedInitialState
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyLeaderFreeKernel

/-!
# One fixed finite policy family for the initial immediate switch

The same one-sided recurrent policy must be reused at the two operational
entry shapes surrounding the physical root: an immediately strict root and a
first strict exit after a simultaneous root.  Selecting policies separately
at those two sites would create an unnecessary policy-equality obligation.

Here the finite tag is only the literal root input pair together with the
chosen live singleton lane.  It recovers one exact semantic source, one fresh
ordinary provenance policy, one complete recurrent controller bank, and the
canonical live root of that policy.  Both entry sites can therefore name this
same tag and obtain definitionally the same recurrent data.

The tag is proof-side construction provenance.  No transition is given a
graph, orientation, leader, or strict-leader signal.
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

/-! ## Finite tag and literal singleton source -/

/-- Left summand selects the process-one/right-live singleton; the right
summand selects the process-two/left-live singleton. -/
abbrev ProfiledRawJointHybridInitialImmediateSwitchSideTag := Unit ⊕ Unit

/-- The finite common index shared by both immediate-switch entry sites. -/
abbrev ProfiledRawJointHybridInitialImmediateSwitchTag :=
  (In₁ × In₂) × ProfiledRawJointHybridInitialImmediateSwitchSideTag

noncomputable instance
    profiledRawJointHybridInitialImmediateSwitchTagFintype :
    Fintype
      (ProfiledRawJointHybridInitialImmediateSwitchTag
        (In₁ := In₁) (In₂ := In₂)) := by
  classical
  infer_instance

/-- The literal common base determined by the tag's root input. -/
def profiledRawJointHybridInitialImmediateSwitchWorld
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointCommonBaseWorld A strategy :=
  profiledRawJointInitialCommonBaseWorld A strategy tag.1.1 tag.1.2

/-- Exact right-live or left-live singleton source recovered from the tag. -/
def profiledRawJointHybridInitialImmediateSwitchSource
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  match tag.2 with
  | .inl _ =>
      (profiledRawJointHybridInitialImmediateSwitchWorld A strategy tag
        ).oneSidedState A .right
  | .inr _ =>
      (profiledRawJointHybridInitialImmediateSwitchWorld A strategy tag
        ).oneSidedState A .left

/-- Constructor for the right-live shared tag. -/
def profiledRawJointHybridInitialImmediateSwitchRightTag
    (rootInput : In₁ × In₂) :
    ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂) :=
  (rootInput, .inl ())

/-- Constructor for the left-live shared tag. -/
def profiledRawJointHybridInitialImmediateSwitchLeftTag
    (rootInput : In₁ × In₂) :
    ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂) :=
  (rootInput, .inr ())

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointHybridInitialImmediateSwitchSource_right
    (rootInput : In₁ × In₂) :
    profiledRawJointHybridInitialImmediateSwitchSource A strategy
        (profiledRawJointHybridInitialImmediateSwitchRightTag rootInput) =
      (profiledRawJointInitialCommonBaseWorld A strategy rootInput.1
        rootInput.2).oneSidedState A .right :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointHybridInitialImmediateSwitchSource_left
    (rootInput : In₁ × In₂) :
    profiledRawJointHybridInitialImmediateSwitchSource A strategy
        (profiledRawJointHybridInitialImmediateSwitchLeftTag rootInput) =
      (profiledRawJointInitialCommonBaseWorld A strategy rootInput.1
        rootInput.2).oneSidedState A .left :=
  rfl

/-! ## One fixed policy and controller bank per tag -/

/-- Fresh ordinary policy selected once at the tag's literal singleton
source. -/
noncomputable def profiledRawJointHybridInitialImmediateSwitchPolicy
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointHybridInitialImmediateSwitchSource A strategy tag
        ).code A) :=
  Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin
      (profiledRawJointHybridInitialImmediateSwitchSource A strategy tag))

/-- Complete recurrent controller bank below the once-selected policy. -/
noncomputable def
    profiledRawJointHybridInitialImmediateSwitchControllerBank
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (profiledRawJointHybridInitialImmediateSwitchSource A strategy tag)
      (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin
        tag) :=
  profiledRawJointUnitPolicyControllerBank A strategy
    (profiledRawJointHybridInitialImmediateSwitchSource A strategy tag)
    (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin tag)

/-! ## Canonical live root -/

/-- The live root-macro type determined by the tag's singleton side. -/
abbrev ProfiledRawJointHybridInitialImmediateSwitchRootMacro
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :=
  match tag.2 with
  | .inl _ =>
      ProfiledRawJointUnitRightPolicyMacro A strategy
        ((profiledRawJointHybridInitialImmediateSwitchSource A strategy tag
          ).code A)
        (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin
          tag)
  | .inr _ =>
      ProfiledRawJointUnitLeftPolicyMacro A strategy
        ((profiledRawJointHybridInitialImmediateSwitchSource A strategy tag
          ).code A)
        (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin
          tag)

/-- Canonical live recurrent root of the tag's fixed policy. -/
noncomputable def profiledRawJointHybridInitialImmediateSwitchRoot
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridInitialImmediateSwitchRootMacro A strategy hwin
      tag := by
  let source :=
    profiledRawJointHybridInitialImmediateSwitchSource A strategy tag
  let policy :=
    profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin tag
  have hrootCode : (policy.run []).1 = source.code A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  rcases tag with ⟨rootInput, side⟩
  cases side with
  | inl empty =>
      cases empty
      exact {
        state := policy.run []
        reachable := ⟨[], rfl⟩
        slot := (profiledRawJointInitialCommonBaseWorld A strategy
          rootInput.1 rootInput.2).procOneSlot A
        active_slot := by
          rw [hrootCode]
          rfl }
  | inr empty =>
      cases empty
      exact {
        state := policy.run []
        reachable := ⟨[], rfl⟩
        slot := (profiledRawJointInitialCommonBaseWorld A strategy
          rootInput.1 rootInput.2).procTwoSlot A
        active_slot := by
          rw [hrootCode]
          rfl }

noncomputable instance
    profiledRawJointHybridInitialImmediateSwitchRootMacroFintype
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    Fintype
      (ProfiledRawJointHybridInitialImmediateSwitchRootMacro A strategy hwin
        tag) := by
  classical
  rcases tag with ⟨rootInput, side⟩
  cases side with
  | inl empty => cases empty; infer_instance
  | inr empty => cases empty; infer_instance

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridInitialImmediateSwitchRoot_right
    (rootInput : In₁ × In₂) :
    profiledRawJointHybridInitialImmediateSwitchRoot A strategy hwin
        (profiledRawJointHybridInitialImmediateSwitchRightTag rootInput) =
      {
        state :=
          (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin
            (profiledRawJointHybridInitialImmediateSwitchRightTag rootInput)
            ).run []
        reachable := ⟨[], rfl⟩
        slot := (profiledRawJointInitialCommonBaseWorld A strategy
          rootInput.1 rootInput.2).procOneSlot A
        active_slot := by
          have hroot := congrArg Prod.fst
            (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin
              (profiledRawJointHybridInitialImmediateSwitchRightTag rootInput)
              ).accepts.1.1
          have hrootCode := by
            simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
          rw [hrootCode]
          rfl } := by
  rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridInitialImmediateSwitchRoot_left
    (rootInput : In₁ × In₂) :
    profiledRawJointHybridInitialImmediateSwitchRoot A strategy hwin
        (profiledRawJointHybridInitialImmediateSwitchLeftTag rootInput) =
      {
        state :=
          (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin
            (profiledRawJointHybridInitialImmediateSwitchLeftTag rootInput)
            ).run []
        reachable := ⟨[], rfl⟩
        slot := (profiledRawJointInitialCommonBaseWorld A strategy
          rootInput.1 rootInput.2).procTwoSlot A
        active_slot := by
          have hroot := congrArg Prod.fst
            (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin
              (profiledRawJointHybridInitialImmediateSwitchLeftTag rootInput)
              ).accepts.1.1
          have hrootCode := by
            simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
          rw [hrootCode]
          rfl } := by
  rfl

/-! ## The four finite dependent recurrent families -/

abbrev ProfiledRawJointHybridInitialImmediateSwitchRightOwner
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :=
  ProfiledRawJointUnitPolicyRightOwner A strategy
    (profiledRawJointHybridInitialImmediateSwitchSource A strategy tag)
    (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin tag)
    (profiledRawJointHybridInitialImmediateSwitchControllerBank A strategy hwin
      tag) ()

abbrev ProfiledRawJointHybridInitialImmediateSwitchLeftReceiver
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :=
  ProfiledRawJointUnitPolicyLeftReceiver A strategy
    (profiledRawJointHybridInitialImmediateSwitchSource A strategy tag)
    (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin tag) ()

abbrev ProfiledRawJointHybridInitialImmediateSwitchRightReceiver
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :=
  ProfiledRawJointUnitPolicyRightReceiver A strategy
    (profiledRawJointHybridInitialImmediateSwitchSource A strategy tag)
    (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin tag) ()

abbrev ProfiledRawJointHybridInitialImmediateSwitchLeftOwner
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :=
  ProfiledRawJointUnitPolicyLeftOwner A strategy
    (profiledRawJointHybridInitialImmediateSwitchSource A strategy tag)
    (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin tag)
    (profiledRawJointHybridInitialImmediateSwitchControllerBank A strategy hwin
      tag) ()

noncomputable instance
    profiledRawJointHybridInitialImmediateSwitchRightOwnerFintype
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    Fintype
      (ProfiledRawJointHybridInitialImmediateSwitchRightOwner A strategy hwin
        tag) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridInitialImmediateSwitchLeftReceiverFintype
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    Fintype
      (ProfiledRawJointHybridInitialImmediateSwitchLeftReceiver A strategy hwin
        tag) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridInitialImmediateSwitchRightReceiverFintype
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    Fintype
      (ProfiledRawJointHybridInitialImmediateSwitchRightReceiver A strategy
        hwin tag) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridInitialImmediateSwitchLeftOwnerFintype
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    Fintype
      (ProfiledRawJointHybridInitialImmediateSwitchLeftOwner A strategy hwin
        tag) := by
  classical
  infer_instance

/-! ## Direct initialization at the two live tags -/

/-- Initialize the process-one owner at the canonical right-live root. -/
noncomputable def
    initialProfiledRawJointHybridInitialImmediateSwitchRightOwner
    (rootInput : In₁ × In₂) :
    ProfiledRawJointHybridInitialImmediateSwitchRightOwner A strategy hwin
      (profiledRawJointHybridInitialImmediateSwitchRightTag rootInput) :=
  let tag := profiledRawJointHybridInitialImmediateSwitchRightTag rootInput
  initialProfiledRawJointUnitRightPolicyOwner A strategy
    (profiledRawJointHybridInitialImmediateSwitchSource A strategy tag)
    (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin tag)
    (profiledRawJointHybridInitialImmediateSwitchControllerBank A strategy hwin
      tag)
    (profiledRawJointHybridInitialImmediateSwitchRoot A strategy hwin tag)

/-- Initialize its process-two receiver mirror at an entry row. -/
noncomputable def
    initialProfiledRawJointHybridInitialImmediateSwitchRightReceiver
    (rootInput : In₁ × In₂) (row : PairedEntryRow) :
    ProfiledRawJointHybridInitialImmediateSwitchRightReceiver A strategy hwin
      (profiledRawJointHybridInitialImmediateSwitchRightTag rootInput) :=
  let tag := profiledRawJointHybridInitialImmediateSwitchRightTag rootInput
  initialProfiledRawJointUnitRightPolicyReceiver A strategy
    (profiledRawJointHybridInitialImmediateSwitchSource A strategy tag)
    (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin tag)
    (profiledRawJointHybridInitialImmediateSwitchRoot A strategy hwin tag) row

/-- Initialize the process-two owner at the canonical left-live root. -/
noncomputable def
    initialProfiledRawJointHybridInitialImmediateSwitchLeftOwner
    (rootInput : In₁ × In₂) :
    ProfiledRawJointHybridInitialImmediateSwitchLeftOwner A strategy hwin
      (profiledRawJointHybridInitialImmediateSwitchLeftTag rootInput) :=
  let tag := profiledRawJointHybridInitialImmediateSwitchLeftTag rootInput
  initialProfiledRawJointUnitLeftPolicyOwner A strategy
    (profiledRawJointHybridInitialImmediateSwitchSource A strategy tag)
    (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin tag)
    (profiledRawJointHybridInitialImmediateSwitchControllerBank A strategy hwin
      tag)
    (profiledRawJointHybridInitialImmediateSwitchRoot A strategy hwin tag)

/-- Initialize its process-one receiver mirror at an entry row. -/
noncomputable def
    initialProfiledRawJointHybridInitialImmediateSwitchLeftReceiver
    (rootInput : In₁ × In₂) (row : PairedEntryRow) :
    ProfiledRawJointHybridInitialImmediateSwitchLeftReceiver A strategy hwin
      (profiledRawJointHybridInitialImmediateSwitchLeftTag rootInput) :=
  let tag := profiledRawJointHybridInitialImmediateSwitchLeftTag rootInput
  initialProfiledRawJointUnitLeftPolicyReceiver A strategy
    (profiledRawJointHybridInitialImmediateSwitchSource A strategy tag)
    (profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin tag)
    (profiledRawJointHybridInitialImmediateSwitchRoot A strategy hwin tag) row

@[simp] theorem
    initialProfiledRawJointHybridInitialImmediateSwitchRightOwner_source
    (rootInput : In₁ × In₂) :
    (initialProfiledRawJointHybridInitialImmediateSwitchRightOwner A strategy
      hwin rootInput).1 =
      profiledRawJointHybridInitialImmediateSwitchRoot A strategy hwin
        (profiledRawJointHybridInitialImmediateSwitchRightTag rootInput) :=
  rfl

@[simp] theorem
    initialProfiledRawJointHybridInitialImmediateSwitchLeftOwner_source
    (rootInput : In₁ × In₂) :
    (initialProfiledRawJointHybridInitialImmediateSwitchLeftOwner A strategy
      hwin rootInput).1 =
      profiledRawJointHybridInitialImmediateSwitchRoot A strategy hwin
        (profiledRawJointHybridInitialImmediateSwitchLeftTag rootInput) :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
