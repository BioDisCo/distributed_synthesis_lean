/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedLinkedInitialCommonPolicyBank

/-!
# Local installation of the parent-linked guarded common bank

The two local states below are the same ambiguity shadows used by the guarded
tail construction, but their common control comes from the parent-linked
policy.  The child pair is selected once by the current policy move and is
installed by both processes.  No local transition is told whether the round
is common or strict, and no graph/orientation/leader data occur in a runtime
map.
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
  ProfiledRawJointGuardedLinkedInitialCommonControl A strategy hwin

/-! ## Finite local common states -/

structure ProfiledRawJointGuardedLinkedInitialCommonOneState where
  control : CommonControl A strategy hwin
  shadow : ProfiledRawJointGuardedCommonOneShadow A strategy hwin
  common_eq : shadow.common =
    profiledRawJointGuardedLinkedInitialCommonControlPair A strategy hwin
      control

structure ProfiledRawJointGuardedLinkedInitialCommonTwoState where
  control : CommonControl A strategy hwin
  shadow : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin
  common_eq : shadow.common =
    profiledRawJointGuardedLinkedInitialCommonControlPair A strategy hwin
      control

noncomputable instance
    profiledRawJointGuardedLinkedInitialCommonOneStateFintype :
    Fintype
      (ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin) := by
  classical
  let Rep := Σ control : CommonControl A strategy hwin,
    { shadow : ProfiledRawJointGuardedCommonOneShadow A strategy hwin //
      shadow.common =
        profiledRawJointGuardedLinkedInitialCommonControlPair A strategy hwin
          control }
  let equiv :
      ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin ≃
        Rep :=
    { toFun := fun state ↦ ⟨state.control, state.shadow, state.common_eq⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; rcases state with ⟨a, b, h⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointGuardedLinkedInitialCommonTwoStateFintype :
    Fintype
      (ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin) := by
  classical
  let Rep := Σ control : CommonControl A strategy hwin,
    { shadow : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin //
      shadow.common =
        profiledRawJointGuardedLinkedInitialCommonControlPair A strategy hwin
          control }
  let equiv :
      ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin ≃
        Rep :=
    { toFun := fun state ↦ ⟨state.control, state.shadow, state.common_eq⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; rcases state with ⟨a, b, h⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Proof-only synchronization of the two local common controls. -/
def ProfiledRawJointGuardedLinkedInitialCommonStatesAgree
    (one : ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin) :
    Prop :=
  one.control = two.control

theorem ProfiledRawJointGuardedLinkedInitialCommonStatesAgree.shadows
    {one : ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin}
    {two : ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin}
    (hagrees : ProfiledRawJointGuardedLinkedInitialCommonStatesAgree A strategy
      hwin one two) :
    ProfiledRawJointGuardedCommonShadowsAgree A strategy hwin one.shadow
      two.shadow := by
  unfold ProfiledRawJointGuardedLinkedInitialCommonStatesAgree at hagrees
  unfold ProfiledRawJointGuardedCommonShadowsAgree
  rw [one.common_eq, two.common_eq, hagrees]

/-! ## Fresh common entry -/

noncomputable def profiledRawJointGuardedLinkedInitialCommonStartOne
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    Out₁ ×
      ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin :=
  let child :=
    profiledRawJointGuardedLinkedInitialCommonControlSuccessor A strategy hwin
      control input
  let result :=
    profiledRawJointGuardedCommonStartOneShadowOfSuccessor A strategy hwin
      (profiledRawJointGuardedLinkedInitialCommonControlPair A strategy hwin
        control) input child
  (result.1,
    ⟨profiledRawJointGuardedLinkedInitialCommonControlNext A strategy hwin
      control input, result.2,
      profiledRawJointGuardedLinkedInitialCommonControlSuccessor_pair A
        strategy hwin control input⟩)

noncomputable def profiledRawJointGuardedLinkedInitialCommonStartTwo
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    Out₂ ×
      ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin :=
  let child :=
    profiledRawJointGuardedLinkedInitialCommonControlSuccessor A strategy hwin
      control input
  let result :=
    profiledRawJointGuardedCommonStartTwoShadowOfSuccessor A strategy hwin
      (profiledRawJointGuardedLinkedInitialCommonControlPair A strategy hwin
        control) input child
  (result.1,
    ⟨profiledRawJointGuardedLinkedInitialCommonControlNext A strategy hwin
      control input, result.2,
      profiledRawJointGuardedLinkedInitialCommonControlSuccessor_pair A
        strategy hwin control input⟩)

theorem profiledRawJointGuardedLinkedInitialCommonStart_states_agree
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ProfiledRawJointGuardedLinkedInitialCommonStatesAgree A strategy hwin
      (profiledRawJointGuardedLinkedInitialCommonStartOne A strategy hwin
        control input).2
      (profiledRawJointGuardedLinkedInitialCommonStartTwo A strategy hwin
        control input).2 :=
  rfl

theorem profiledRawJointGuardedLinkedInitialCommonStart_outputs
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ((profiledRawJointGuardedLinkedInitialCommonStartOne A strategy hwin
        control input).1,
      (profiledRawJointGuardedLinkedInitialCommonStartTwo A strategy hwin
        control input).1) =
      let pair :=
        profiledRawJointGuardedLinkedInitialCommonControlPair A strategy hwin
          control
      ((pair.rightRootRecord A strategy hwin input).2.1.physical.closingBoth,
        (pair.leftRootRecord A strategy hwin input).2.1.physical.closingBoth) :=
  profiledRawJointGuardedCommonStartSuccessorShadows_outputs A strategy hwin
    (profiledRawJointGuardedLinkedInitialCommonControlPair A strategy hwin
      control) input
    (profiledRawJointGuardedLinkedInitialCommonControlSuccessor A strategy hwin
      control input)

/-! ## Repeated simultaneous receive -/

noncomputable def profiledRawJointGuardedLinkedInitialCommonOneRecv
    (one : ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ ×
      ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin :=
  let input := (own, delivered)
  let child :=
    profiledRawJointGuardedLinkedInitialCommonControlSuccessor A strategy hwin
      one.control input
  let result := profiledRawJointGuardedCommonOneShadowRecvTwoShadow A strategy
    hwin one.shadow two.shadow child.1 own delivered
  (result.1,
    ⟨profiledRawJointGuardedLinkedInitialCommonControlNext A strategy hwin
      one.control input, result.2,
      profiledRawJointGuardedLinkedInitialCommonControlSuccessor_pair A
        strategy hwin one.control input⟩)

noncomputable def profiledRawJointGuardedLinkedInitialCommonTwoRecv
    (two : ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin)
    (one : ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ ×
      ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin :=
  let input := (delivered, own)
  let child :=
    profiledRawJointGuardedLinkedInitialCommonControlSuccessor A strategy hwin
      two.control input
  let result := profiledRawJointGuardedCommonTwoShadowRecvOneShadow A strategy
    hwin two.shadow one.shadow child.1 own delivered
  (result.1,
    ⟨profiledRawJointGuardedLinkedInitialCommonControlNext A strategy hwin
      two.control input, result.2,
      profiledRawJointGuardedLinkedInitialCommonControlSuccessor_pair A
        strategy hwin two.control input⟩)

theorem profiledRawJointGuardedLinkedInitialCommonRecv_states_agree
    (one : ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedLinkedInitialCommonStatesAgree A strategy
      hwin one two) (input : In₁ × In₂) :
    ProfiledRawJointGuardedLinkedInitialCommonStatesAgree A strategy hwin
      (profiledRawJointGuardedLinkedInitialCommonOneRecv A strategy hwin one
        two input.1 input.2).2
      (profiledRawJointGuardedLinkedInitialCommonTwoRecv A strategy hwin two
        one input.2 input.1).2 := by
  unfold ProfiledRawJointGuardedLinkedInitialCommonStatesAgree at *
  simp only [profiledRawJointGuardedLinkedInitialCommonOneRecv,
    profiledRawJointGuardedLinkedInitialCommonTwoRecv]
  rw [hagrees]

theorem profiledRawJointGuardedLinkedInitialCommonRecv_outputs
    (one : ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedLinkedInitialCommonStatesAgree A strategy
      hwin one two) (input : In₁ × In₂) :
    ((profiledRawJointGuardedLinkedInitialCommonOneRecv A strategy hwin one
        two input.1 input.2).1,
      (profiledRawJointGuardedLinkedInitialCommonTwoRecv A strategy hwin two
        one input.2 input.1).1) =
      ((one.shadow.common.rightRootRecord A strategy hwin input
        ).2.1.physical.closingBoth,
        (one.shadow.common.leftRootRecord A strategy hwin input
          ).2.1.physical.closingBoth) := by
  unfold ProfiledRawJointGuardedLinkedInitialCommonStatesAgree at hagrees
  simp only [profiledRawJointGuardedLinkedInitialCommonOneRecv,
    profiledRawJointGuardedLinkedInitialCommonTwoRecv]
  rw [← hagrees]
  exact profiledRawJointGuardedCommonShadowRecvShadows_outputs A strategy hwin
    one.shadow two.shadow (by
      unfold ProfiledRawJointGuardedCommonShadowsAgree
      rw [one.common_eq, two.common_eq, hagrees])
    (profiledRawJointGuardedLinkedInitialCommonControlSuccessor A strategy hwin
      one.control input).1 input

/-! ## First strict exit -/

noncomputable def profiledRawJointGuardedLinkedInitialCommonOneNoRecv
    (one : ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin)
    (own : In₁) :
    Out₁ × ProfiledRawJointGuardedCommonRightOwner A strategy hwin :=
  profiledRawJointGuardedCommonOneShadowNoRecv A strategy hwin one.shadow own

noncomputable def profiledRawJointGuardedLinkedInitialCommonTwoNoRecv
    (two : ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin)
    (own : In₂) :
    Out₂ × ProfiledRawJointGuardedCommonLeftOwner A strategy hwin :=
  profiledRawJointGuardedCommonTwoShadowNoRecv A strategy hwin two.shadow own

theorem profiledRawJointGuardedLinkedInitialCommon_strictRight_sources
    (one : ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedLinkedInitialCommonStatesAgree A strategy
      hwin one two) (input : In₁ × In₂) :
    (profiledRawJointGuardedLinkedInitialCommonOneNoRecv A strategy hwin one
      input.1).2.1 =
      (profiledRawJointGuardedLinkedInitialCommonTwoRecv A strategy hwin two
        one input.2 input.1).2.shadow.source := by
  simp only [profiledRawJointGuardedLinkedInitialCommonOneNoRecv,
    profiledRawJointGuardedLinkedInitialCommonTwoRecv,
    profiledRawJointGuardedCommonOneShadowNoRecv,
    profiledRawJointGuardedCommonNoRecvOne,
    profiledRawJointGuardedCommonTwoShadowRecvOneShadow,
    profiledRawJointGuardedCommonStartTwoShadow]
  exact hagrees.shadows A strategy hwin

theorem profiledRawJointGuardedLinkedInitialCommon_strictLeft_sources
    (one : ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedLinkedInitialCommonStatesAgree A strategy
      hwin one two) (input : In₁ × In₂) :
    (profiledRawJointGuardedLinkedInitialCommonTwoNoRecv A strategy hwin two
      input.2).2.1 =
      (profiledRawJointGuardedLinkedInitialCommonOneRecv A strategy hwin one
        two input.1 input.2).2.shadow.source := by
  simp only [profiledRawJointGuardedLinkedInitialCommonTwoNoRecv,
    profiledRawJointGuardedLinkedInitialCommonOneRecv,
    profiledRawJointGuardedCommonTwoShadowNoRecv,
    profiledRawJointGuardedCommonNoRecvTwo,
    profiledRawJointGuardedCommonOneShadowRecvTwoShadow,
    profiledRawJointGuardedCommonStartOneShadow]
  exact (hagrees.shadows A strategy hwin).symm

theorem profiledRawJointGuardedLinkedInitialCommon_strictRight_outputs
    (one : ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedLinkedInitialCommonStatesAgree A strategy
      hwin one two) (input : In₁ × In₂) :
    ((profiledRawJointGuardedLinkedInitialCommonOneNoRecv A strategy hwin one
        input.1).1,
      (profiledRawJointGuardedLinkedInitialCommonTwoRecv A strategy hwin two
        one input.2 input.1).1) =
      ((one.shadow.common.rightRootRecord A strategy hwin input).2.2,
        pairedRightInformedForRow .both
          (one.shadow.common.rightRootRecord A strategy hwin input
            ).2.1.physical) :=
  profiledRawJointGuardedCommonShadows_strictRight_root_pair A strategy hwin
    one.shadow two.shadow (hagrees.shadows A strategy hwin)
    (profiledRawJointGuardedLinkedInitialCommonControlSuccessor A strategy hwin
      two.control input).1 input

theorem profiledRawJointGuardedLinkedInitialCommon_strictLeft_outputs
    (one : ProfiledRawJointGuardedLinkedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedLinkedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedLinkedInitialCommonStatesAgree A strategy
      hwin one two) (input : In₁ × In₂) :
    ((profiledRawJointGuardedLinkedInitialCommonOneRecv A strategy hwin one
        two input.1 input.2).1,
      (profiledRawJointGuardedLinkedInitialCommonTwoNoRecv A strategy hwin two
        input.2).1) =
      (pairedLeftInformedForRow .both
          (one.shadow.common.leftRootRecord A strategy hwin input
            ).2.1.physical,
        (one.shadow.common.leftRootRecord A strategy hwin input).2.2) :=
  profiledRawJointGuardedCommonShadows_strictLeft_root_pair A strategy hwin
    one.shadow two.shadow (hagrees.shadows A strategy hwin)
    (profiledRawJointGuardedLinkedInitialCommonControlSuccessor A strategy hwin
      one.control input).1 input

end


end DetParityAutomaton

end DistributedSynthesis
