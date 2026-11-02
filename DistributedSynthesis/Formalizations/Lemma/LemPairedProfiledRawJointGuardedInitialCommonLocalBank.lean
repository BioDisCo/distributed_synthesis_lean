/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonPolicyLocalAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedInitialCommonPolicyBank

/-!
# A genuinely local bank for the guarded common policy

This file installs the occurrence-sensitive rational common policy in the two
finite local ambiguity carriers.  A local state stores one bank control and
one physical shadow.  The proof-only invariant says that the shadow's common
pair is exactly the pair selected by that control.

The receive transitions use the successor selected by the same rational
policy package.  A no-receive transition does not guess a hierarchy or a
leader: it follows the strict owner already stored in the current guarded
pair.  Thus no executable definition below accepts a graph, orientation,
leader bit, semantic world, or history.
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

private abbrev CommonControl :=
  ProfiledRawJointGuardedInitialCommonControl A strategy hwin

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

/-! ## The policy-selected allowed child -/

/-- The exact occurrence-sensitive child selected by the package belonging
to this bank control. -/
noncomputable def profiledRawJointGuardedInitialCommonControlSuccessor
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonSuccessor A strategy hwin
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
        control) input :=
  let package := profiledRawJointGuardedInitialCommonPackage A strategy hwin
    control.1
  package.successorChild A strategy hwin control.2.state control.2.reachable
    input

@[simp] theorem
    profiledRawJointGuardedInitialCommonControlSuccessor_pair
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    (profiledRawJointGuardedInitialCommonControlSuccessor A strategy hwin
      control input).1 =
      profiledRawJointGuardedInitialCommonControlPair A strategy hwin
        (profiledRawJointGuardedInitialCommonControlNext A strategy hwin
          control input) :=
  rfl

/-- Bank-level form of the exact source-incidence law for the selected
child. -/
theorem profiledRawJointGuardedInitialCommonControlSuccessor_source_incidence
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ∃ world : ProfiledRawJointCommonBaseWorld A strategy,
      ∃ current : In₁ × In₂,
        (profiledRawJointGuardedInitialCommonControlSuccessor A strategy hwin
          control input).1.1.1 =
            profiledRawJointGuardedCommonRightMoveOfWorld A strategy hwin world
              current ∧
        (profiledRawJointGuardedInitialCommonControlSuccessor A strategy hwin
          control input).1.1.2 =
            profiledRawJointGuardedCommonLeftMoveOfWorld A strategy hwin world
              current ∧
        (profiledRawJointCommonWorldFamily A
          (profiledRawJointCommonWorldAfterBoth A world current)
          ).incidenceCode A =
          (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
            control).bothNextCode A strategy hwin input :=
  (profiledRawJointGuardedInitialCommonControlSuccessor A strategy hwin
    control input).property

/-! ## Finite local common states -/

/-- Process one's bank control paired with its unresolved common/strict-left
shadow. -/
structure ProfiledRawJointGuardedInitialCommonOneState where
  control : CommonControl A strategy hwin
  shadow : ProfiledRawJointGuardedCommonOneShadow A strategy hwin
  common_eq : shadow.common =
    profiledRawJointGuardedInitialCommonControlPair A strategy hwin control

/-- Process-two mirror. -/
structure ProfiledRawJointGuardedInitialCommonTwoState where
  control : CommonControl A strategy hwin
  shadow : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin
  common_eq : shadow.common =
    profiledRawJointGuardedInitialCommonControlPair A strategy hwin control

noncomputable instance
    profiledRawJointGuardedInitialCommonOneStateFintype :
    Fintype (ProfiledRawJointGuardedInitialCommonOneState A strategy hwin) := by
  classical
  let Rep := Σ control : CommonControl A strategy hwin,
    { shadow : ProfiledRawJointGuardedCommonOneShadow A strategy hwin //
      shadow.common =
        profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          control }
  let equiv :
      ProfiledRawJointGuardedInitialCommonOneState A strategy hwin ≃ Rep :=
    { toFun := fun state ↦ ⟨state.control, state.shadow, state.common_eq⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; rcases state with ⟨control, shadow, h⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointGuardedInitialCommonTwoStateFintype :
    Fintype (ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin) := by
  classical
  let Rep := Σ control : CommonControl A strategy hwin,
    { shadow : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin //
      shadow.common =
        profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          control }
  let equiv :
      ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin ≃ Rep :=
    { toFun := fun state ↦ ⟨state.control, state.shadow, state.common_eq⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; rcases state with ⟨control, shadow, h⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- The two local common states refer to the same finite policy occurrence.
This is a proof invariant, not an executable leader or graph test. -/
def ProfiledRawJointGuardedInitialCommonStatesAgree
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin) :
    Prop :=
  one.control = two.control

theorem ProfiledRawJointGuardedInitialCommonStatesAgree.shadows
    {one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin}
    {two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin}
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two) :
    ProfiledRawJointGuardedCommonShadowsAgree A strategy hwin one.shadow
      two.shadow := by
  unfold ProfiledRawJointGuardedInitialCommonStatesAgree at hagrees
  unfold ProfiledRawJointGuardedCommonShadowsAgree
  rw [one.common_eq, two.common_eq, hagrees]

/-! ## Fresh entry into the ambiguity carrier -/

noncomputable def profiledRawJointGuardedInitialCommonStartOne
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    Out₁ × ProfiledRawJointGuardedInitialCommonOneState A strategy hwin :=
  let child := profiledRawJointGuardedInitialCommonControlSuccessor A strategy
    hwin control input
  let result :=
    profiledRawJointGuardedCommonStartOneShadowOfSuccessor A strategy hwin
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin control)
      input child
  (result.1,
    ⟨profiledRawJointGuardedInitialCommonControlNext A strategy hwin control
      input, result.2, by rfl⟩)

noncomputable def profiledRawJointGuardedInitialCommonStartTwo
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    Out₂ × ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin :=
  let child := profiledRawJointGuardedInitialCommonControlSuccessor A strategy
    hwin control input
  let result :=
    profiledRawJointGuardedCommonStartTwoShadowOfSuccessor A strategy hwin
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin control)
      input child
  (result.1,
    ⟨profiledRawJointGuardedInitialCommonControlNext A strategy hwin control
      input, result.2, by rfl⟩)

@[simp] theorem profiledRawJointGuardedInitialCommonStartOne_control
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    (profiledRawJointGuardedInitialCommonStartOne A strategy hwin control
      input).2.control =
      profiledRawJointGuardedInitialCommonControlNext A strategy hwin control
        input :=
  rfl

@[simp] theorem profiledRawJointGuardedInitialCommonStartTwo_control
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    (profiledRawJointGuardedInitialCommonStartTwo A strategy hwin control
      input).2.control =
      profiledRawJointGuardedInitialCommonControlNext A strategy hwin control
        input :=
  rfl

theorem profiledRawJointGuardedInitialCommonStart_states_agree
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      (profiledRawJointGuardedInitialCommonStartOne A strategy hwin control
        input).2
      (profiledRawJointGuardedInitialCommonStartTwo A strategy hwin control
        input).2 :=
  rfl

@[simp] theorem profiledRawJointGuardedInitialCommonStartOne_source
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    (profiledRawJointGuardedInitialCommonStartOne A strategy hwin control
      input).2.shadow.source =
      profiledRawJointGuardedInitialCommonControlPair A strategy hwin
        control :=
  rfl

@[simp] theorem profiledRawJointGuardedInitialCommonStartTwo_source
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    (profiledRawJointGuardedInitialCommonStartTwo A strategy hwin control
      input).2.shadow.source =
      profiledRawJointGuardedInitialCommonControlPair A strategy hwin
        control :=
  rfl

/-- Exact strict-left target retained by process one at the fresh ambiguous
receive. -/
@[simp] theorem profiledRawJointGuardedInitialCommonStartOne_target
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    (profiledRawJointGuardedInitialCommonStartOne A strategy hwin control
      input).2.shadow.strictTarget =
      ((profiledRawJointGuardedInitialCommonControlPair A strategy hwin
        control).leftRootRecord A strategy hwin input).2.1.target .both :=
  rfl

/-- Exact strict-right mirror retained by process two. -/
@[simp] theorem profiledRawJointGuardedInitialCommonStartTwo_target
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    (profiledRawJointGuardedInitialCommonStartTwo A strategy hwin control
      input).2.shadow.strictTarget =
      ((profiledRawJointGuardedInitialCommonControlPair A strategy hwin
        control).rightRootRecord A strategy hwin input).2.1.target .both :=
  rfl

theorem profiledRawJointGuardedInitialCommonStart_outputs
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ((profiledRawJointGuardedInitialCommonStartOne A strategy hwin control
        input).1,
      (profiledRawJointGuardedInitialCommonStartTwo A strategy hwin control
        input).1) =
      (((profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          control).rightRootRecord A strategy hwin input).2.1.physical.closingBoth,
        ((profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          control).leftRootRecord A strategy hwin input).2.1.physical.closingBoth) :=
  profiledRawJointGuardedCommonStartSuccessorShadows_outputs A strategy hwin
    (profiledRawJointGuardedInitialCommonControlPair A strategy hwin control)
    input
    (profiledRawJointGuardedInitialCommonControlSuccessor A strategy hwin
      control input)

/-! ## Repeated simultaneous receives -/

noncomputable def profiledRawJointGuardedInitialCommonOneRecv
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × ProfiledRawJointGuardedInitialCommonOneState A strategy hwin :=
  let input := (own, delivered)
  let nextControl := profiledRawJointGuardedInitialCommonControlNext A strategy
    hwin one.control input
  let child := profiledRawJointGuardedInitialCommonControlSuccessor A strategy
    hwin one.control input
  let result := profiledRawJointGuardedCommonOneShadowRecvTwoShadow A strategy
    hwin one.shadow two.shadow child.1 own delivered
  (result.1, ⟨nextControl, result.2, by rfl⟩)

noncomputable def profiledRawJointGuardedInitialCommonTwoRecv
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin :=
  let input := (delivered, own)
  let nextControl := profiledRawJointGuardedInitialCommonControlNext A strategy
    hwin two.control input
  let child := profiledRawJointGuardedInitialCommonControlSuccessor A strategy
    hwin two.control input
  let result := profiledRawJointGuardedCommonTwoShadowRecvOneShadow A strategy
    hwin two.shadow one.shadow child.1 own delivered
  (result.1, ⟨nextControl, result.2, by rfl⟩)

theorem profiledRawJointGuardedInitialCommonRecv_states_agree
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      (profiledRawJointGuardedInitialCommonOneRecv A strategy hwin one two
        input.1 input.2).2
      (profiledRawJointGuardedInitialCommonTwoRecv A strategy hwin two one
        input.2 input.1).2 := by
  unfold ProfiledRawJointGuardedInitialCommonStatesAgree at *
  simp only [profiledRawJointGuardedInitialCommonOneRecv,
    profiledRawJointGuardedInitialCommonTwoRecv]
  rw [hagrees]

@[simp] theorem profiledRawJointGuardedInitialCommonOneRecv_source
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (own : In₁) (delivered : In₂) :
    (profiledRawJointGuardedInitialCommonOneRecv A strategy hwin one two own
      delivered).2.shadow.source = one.shadow.common :=
  rfl

@[simp] theorem profiledRawJointGuardedInitialCommonTwoRecv_source
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (own : In₂) (delivered : In₁) :
    (profiledRawJointGuardedInitialCommonTwoRecv A strategy hwin two one own
      delivered).2.shadow.source = two.shadow.common :=
  rfl

@[simp] theorem profiledRawJointGuardedInitialCommonOneRecv_target
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (own : In₁) (delivered : In₂) :
    (profiledRawJointGuardedInitialCommonOneRecv A strategy hwin one two own
      delivered).2.shadow.strictTarget =
      (one.shadow.common.leftRootRecord A strategy hwin
        (own, delivered)).2.1.target .both :=
  rfl

@[simp] theorem profiledRawJointGuardedInitialCommonTwoRecv_target
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (own : In₂) (delivered : In₁) :
    (profiledRawJointGuardedInitialCommonTwoRecv A strategy hwin two one own
      delivered).2.shadow.strictTarget =
      (two.shadow.common.rightRootRecord A strategy hwin
        (delivered, own)).2.1.target .both :=
  rfl

theorem profiledRawJointGuardedInitialCommonRecv_outputs
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedInitialCommonOneRecv A strategy hwin one two
        input.1 input.2).1,
      (profiledRawJointGuardedInitialCommonTwoRecv A strategy hwin two one
        input.2 input.1).1) =
      ((one.shadow.common.rightRootRecord A strategy hwin input
        ).2.1.physical.closingBoth,
        (one.shadow.common.leftRootRecord A strategy hwin input
          ).2.1.physical.closingBoth) := by
  unfold ProfiledRawJointGuardedInitialCommonStatesAgree at hagrees
  simp only [profiledRawJointGuardedInitialCommonOneRecv,
    profiledRawJointGuardedInitialCommonTwoRecv]
  rw [← hagrees]
  exact profiledRawJointGuardedCommonShadowRecvShadows_outputs A strategy hwin
    one.shadow two.shadow (by
      unfold ProfiledRawJointGuardedCommonShadowsAgree
      rw [one.common_eq, two.common_eq, hagrees])
    (profiledRawJointGuardedInitialCommonControlSuccessor A strategy hwin
      one.control input).1 input

/-! ## The first strict exit -/

noncomputable def profiledRawJointGuardedInitialCommonOneNoRecv
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (own : In₁) :
    Out₁ × ProfiledRawJointGuardedCommonRightOwner A strategy hwin :=
  profiledRawJointGuardedCommonOneShadowNoRecv A strategy hwin one.shadow own

noncomputable def profiledRawJointGuardedInitialCommonTwoNoRecv
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (own : In₂) :
    Out₂ × ProfiledRawJointGuardedCommonLeftOwner A strategy hwin :=
  profiledRawJointGuardedCommonTwoShadowNoRecv A strategy hwin two.shadow own

/-- At the first strict-right round, the blind owner's source and the
receiver's retained source are the same current guarded pair. -/
theorem profiledRawJointGuardedInitialCommon_strictRight_sources
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedInitialCommonOneNoRecv A strategy hwin one
      input.1).2.1 =
      (profiledRawJointGuardedInitialCommonTwoRecv A strategy hwin two one
        input.2 input.1).2.shadow.source := by
  simp only [profiledRawJointGuardedInitialCommonOneNoRecv,
    profiledRawJointGuardedInitialCommonTwoRecv,
    profiledRawJointGuardedCommonOneShadowNoRecv,
    profiledRawJointGuardedCommonNoRecvOne,
    profiledRawJointGuardedCommonTwoShadowRecvOneShadow,
    profiledRawJointGuardedCommonStartTwoShadow]
  exact (hagrees.shadows A strategy hwin)

/-- Strict-left mirror. -/
theorem profiledRawJointGuardedInitialCommon_strictLeft_sources
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedInitialCommonTwoNoRecv A strategy hwin two
      input.2).2.1 =
      (profiledRawJointGuardedInitialCommonOneRecv A strategy hwin one two
        input.1 input.2).2.shadow.source := by
  simp only [profiledRawJointGuardedInitialCommonTwoNoRecv,
    profiledRawJointGuardedInitialCommonOneRecv,
    profiledRawJointGuardedCommonTwoShadowNoRecv,
    profiledRawJointGuardedCommonNoRecvTwo,
    profiledRawJointGuardedCommonOneShadowRecvTwoShadow,
    profiledRawJointGuardedCommonStartOneShadow]
  exact (hagrees.shadows A strategy hwin).symm

theorem profiledRawJointGuardedInitialCommon_strictRight_outputs
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedInitialCommonOneNoRecv A strategy hwin one
        input.1).1,
      (profiledRawJointGuardedInitialCommonTwoRecv A strategy hwin two one
        input.2 input.1).1) =
      ((one.shadow.common.rightRootRecord A strategy hwin input).2.2,
        pairedRightInformedForRow .both
          (one.shadow.common.rightRootRecord A strategy hwin input
            ).2.1.physical) := by
  exact profiledRawJointGuardedCommonShadows_strictRight_root_pair A strategy
    hwin one.shadow two.shadow (hagrees.shadows A strategy hwin)
    (profiledRawJointGuardedInitialCommonControlSuccessor A strategy hwin
      two.control input).1 input

theorem profiledRawJointGuardedInitialCommon_strictLeft_outputs
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedInitialCommonOneRecv A strategy hwin one two
        input.1 input.2).1,
      (profiledRawJointGuardedInitialCommonTwoNoRecv A strategy hwin two
        input.2).1) =
      (pairedLeftInformedForRow .both
          (one.shadow.common.leftRootRecord A strategy hwin input
            ).2.1.physical,
        (one.shadow.common.leftRootRecord A strategy hwin input).2.2) := by
  exact profiledRawJointGuardedCommonShadows_strictLeft_root_pair A strategy
    hwin one.shadow two.shadow (hagrees.shadows A strategy hwin)
    (profiledRawJointGuardedInitialCommonControlSuccessor A strategy hwin
      one.control input).1 input

end

end DetParityAutomaton

end DistributedSynthesis
