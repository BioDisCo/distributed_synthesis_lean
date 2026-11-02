/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryKey

/-!
# Recurrent local common controls below the parent-linked entry key

This file installs the reachable parent-linked key in the existing guarded
common shadow carrier.  The key selects one complete annotated move.  Its
child pair is an allowed common successor, both local shadows install that
same pair, and the key successor carries exactly the corresponding pair and
literal-cross annotation.

The construction is recurrent: simultaneous receives advance the key and
both shadows together, while a first strict exit uses the strict source
already retained in the shadows.  All executable maps use finite local
states and locally delivered data only.
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

private abbrev Key (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
    strategy hwin initial

/-! ## One allowed child from every reachable key -/

/-- The child pair selected by a key's annotated move is an allowed child of
the pair carried by that same key. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_childPair_allowed
    (initial : CommonPoint A strategy) (key : Key A strategy hwin initial)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonSuccessorAllowed A strategy hwin
      (key.pair A strategy hwin) input
      ((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt A
        strategy hwin initial key).2 input).1 := by
  let move :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt A
      strategy hwin initial key
  have hvalid :=
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt_realizes
      A strategy hwin initial key).1
  rcases hvalid.2 with
    ⟨point, _hcode, _hannotation, hpointMove, hchildren⟩
  have hcurrent : point.move A strategy hwin = key.pair A strategy hwin :=
    hpointMove.trans
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt_current
        A strategy hwin initial key)
  have hchild :
      (point.step A strategy input).move A strategy hwin =
        (move.2 input).1 := by
    have := congrArg Prod.fst (hchildren input)
    simpa [move,
      profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf] using this
  rw [← hcurrent, ← hchild]
  refine ⟨point.world A strategy, input, rfl, rfl, ?_⟩
  exact ProfiledRawJointGuardedCommonSemanticPoint.step_code A strategy hwin
    point input

/-- Allowed-child package consumed by the guarded shadow constructor. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
    (initial : CommonPoint A strategy) (key : Key A strategy hwin initial)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonSuccessor A strategy hwin
      (key.pair A strategy hwin) input :=
  ⟨((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt A
      strategy hwin initial key).2 input).1,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_childPair_allowed
      A strategy hwin initial key input⟩

/-! ## Finite local states -/

structure
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
    (initial : CommonPoint A strategy) where
  key : Key A strategy hwin initial
  shadow : ProfiledRawJointGuardedCommonOneShadow A strategy hwin
  common_eq : shadow.common = key.pair A strategy hwin

structure
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
    (initial : CommonPoint A strategy) where
  key : Key A strategy hwin initial
  shadow : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin
  common_eq : shadow.common = key.pair A strategy hwin

set_option synthInstance.maxHeartbeats 1000000 in
noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneStateFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
        A strategy hwin initial) := by
  classical
  let Rep := Σ key : Key A strategy hwin initial,
    { shadow : ProfiledRawJointGuardedCommonOneShadow A strategy hwin //
      shadow.common = key.pair A strategy hwin }
  let equiv :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
          A strategy hwin initial ≃ Rep :=
    { toFun := fun state ↦ ⟨state.key, state.shadow, state.common_eq⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; rcases state with ⟨a, b, h⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

set_option synthInstance.maxHeartbeats 1000000 in
noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoStateFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
        A strategy hwin initial) := by
  classical
  let Rep := Σ key : Key A strategy hwin initial,
    { shadow : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin //
      shadow.common = key.pair A strategy hwin }
  let equiv :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
          A strategy hwin initial ≃ Rep :=
    { toFun := fun state ↦ ⟨state.key, state.shadow, state.common_eq⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; rcases state with ⟨a, b, h⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Proof-side agreement of the two copies of the finite rational-policy
key. -/
def
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
    {initial : CommonPoint A strategy}
    (one :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
        A strategy hwin initial)
    (two :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
        A strategy hwin initial) : Prop :=
  one.key = two.key

theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree.shadows
    {initial : CommonPoint A strategy}
    {one :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
        A strategy hwin initial}
    {two :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
        A strategy hwin initial}
    (hagrees :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
        A strategy hwin one two) :
    ProfiledRawJointGuardedCommonShadowsAgree A strategy hwin one.shadow
      two.shadow := by
  unfold
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
    ProfiledRawJointGuardedCommonShadowsAgree at *
  rw [one.common_eq, two.common_eq, hagrees]

/-! ## Fresh entry into the recurrent common carrier -/

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStartOne
    (initial : CommonPoint A strategy) (key : Key A strategy hwin initial)
    (input : In₁ × In₂) :
    Out₁ ×
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
        A strategy hwin initial :=
  let child :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
      A strategy hwin initial key input
  let result :=
    profiledRawJointGuardedCommonStartOneShadowOfSuccessor A strategy hwin
      (key.pair A strategy hwin) input child
  (result.1,
    ⟨key.successor A strategy hwin initial input, result.2,
      (key.successor_pair A strategy hwin initial input).symm⟩)

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStartTwo
    (initial : CommonPoint A strategy) (key : Key A strategy hwin initial)
    (input : In₁ × In₂) :
    Out₂ ×
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
        A strategy hwin initial :=
  let child :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
      A strategy hwin initial key input
  let result :=
    profiledRawJointGuardedCommonStartTwoShadowOfSuccessor A strategy hwin
      (key.pair A strategy hwin) input child
  (result.1,
    ⟨key.successor A strategy hwin initial input, result.2,
      (key.successor_pair A strategy hwin initial input).symm⟩)

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStart_states_agree
    (initial : CommonPoint A strategy) (key : Key A strategy hwin initial)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
      A strategy hwin
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStartOne
        A strategy hwin initial key input).2
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStartTwo
        A strategy hwin initial key input).2 :=
  rfl

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStart_outputs
    (initial : CommonPoint A strategy) (key : Key A strategy hwin initial)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStartOne
        A strategy hwin initial key input).1,
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStartTwo
        A strategy hwin initial key input).1) =
      (((key.pair A strategy hwin).rightRootRecord A strategy hwin input
          ).2.1.physical.closingBoth,
        ((key.pair A strategy hwin).leftRootRecord A strategy hwin input
          ).2.1.physical.closingBoth) :=
  profiledRawJointGuardedCommonStartSuccessorShadows_outputs A strategy hwin
    (key.pair A strategy hwin) input
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
      A strategy hwin initial key input)

/-! ## Repeated simultaneous receives -/

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneRecv
    {initial : CommonPoint A strategy}
    (one :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
        A strategy hwin initial)
    (two :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
        A strategy hwin initial)
    (own : In₁) (delivered : In₂) :
    Out₁ ×
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
        A strategy hwin initial :=
  let input := (own, delivered)
  let child :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
      A strategy hwin initial one.key input
  let result :=
    profiledRawJointGuardedCommonOneShadowRecvTwoShadow A strategy hwin
      one.shadow two.shadow child.1 own delivered
  (result.1,
    ⟨one.key.successor A strategy hwin initial input, result.2,
      (one.key.successor_pair A strategy hwin initial input).symm⟩)

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoRecv
    {initial : CommonPoint A strategy}
    (two :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
        A strategy hwin initial)
    (one :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
        A strategy hwin initial)
    (own : In₂) (delivered : In₁) :
    Out₂ ×
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
        A strategy hwin initial :=
  let input := (delivered, own)
  let child :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
      A strategy hwin initial two.key input
  let result :=
    profiledRawJointGuardedCommonTwoShadowRecvOneShadow A strategy hwin
      two.shadow one.shadow child.1 own delivered
  (result.1,
    ⟨two.key.successor A strategy hwin initial input, result.2,
      (two.key.successor_pair A strategy hwin initial input).symm⟩)

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonRecv_states_agree
    {initial : CommonPoint A strategy}
    (one :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
        A strategy hwin initial)
    (two :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
        A strategy hwin initial)
    (hagrees :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
        A strategy hwin one two)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
      A strategy hwin
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneRecv
        A strategy hwin one two input.1 input.2).2
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoRecv
        A strategy hwin two one input.2 input.1).2 := by
  change one.key.successor A strategy hwin initial input =
    two.key.successor A strategy hwin initial input
  exact congrArg
    (fun key ↦ key.successor A strategy hwin initial input) hagrees

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonRecv_outputs
    {initial : CommonPoint A strategy}
    (one :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
        A strategy hwin initial)
    (two :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
        A strategy hwin initial)
    (hagrees :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
        A strategy hwin one two)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneRecv
        A strategy hwin one two input.1 input.2).1,
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoRecv
        A strategy hwin two one input.2 input.1).1) =
      (((one.key.pair A strategy hwin).rightRootRecord A strategy hwin input
          ).2.1.physical.closingBoth,
        ((one.key.pair A strategy hwin).leftRootRecord A strategy hwin input
          ).2.1.physical.closingBoth) := by
  have hshadows := hagrees.shadows A strategy hwin
  change
    ((profiledRawJointGuardedCommonOneShadowRecvTwoShadow A strategy hwin
        one.shadow two.shadow
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
            A strategy hwin initial one.key input).1 input.1 input.2).1,
      (profiledRawJointGuardedCommonTwoShadowRecvOneShadow A strategy hwin
        two.shadow one.shadow
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
            A strategy hwin initial two.key input).1 input.2 input.1).1) = _
  have hchild :
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
        A strategy hwin initial one.key input).1 =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
        A strategy hwin initial two.key input).1 :=
    congrArg
      (fun key ↦
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
          A strategy hwin initial key input).1) hagrees
  rw [← hchild]
  have houtputs :=
    profiledRawJointGuardedCommonShadowRecvShadows_outputs A strategy hwin
    one.shadow two.shadow hshadows
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
      A strategy hwin initial one.key input).1 input
  rw [one.common_eq] at houtputs
  exact houtputs

/-! ## First strict exit from the recurrent common carrier -/

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneNoRecv
    {initial : CommonPoint A strategy}
    (one :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
        A strategy hwin initial)
    (own : In₁) :
    Out₁ × ProfiledRawJointGuardedCommonRightOwner A strategy hwin :=
  profiledRawJointGuardedCommonOneShadowNoRecv A strategy hwin one.shadow own

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoNoRecv
    {initial : CommonPoint A strategy}
    (two :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
        A strategy hwin initial)
    (own : In₂) :
    Out₂ × ProfiledRawJointGuardedCommonLeftOwner A strategy hwin :=
  profiledRawJointGuardedCommonTwoShadowNoRecv A strategy hwin two.shadow own

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommon_strictRight_sources
    {initial : CommonPoint A strategy}
    (one :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
        A strategy hwin initial)
    (two :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
        A strategy hwin initial)
    (hagrees :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
        A strategy hwin one two)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneNoRecv
      A strategy hwin one input.1).2.1 =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoRecv
        A strategy hwin two one input.2 input.1).2.shadow.source := by
  simp only [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneNoRecv,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoRecv,
    profiledRawJointGuardedCommonOneShadowNoRecv,
    profiledRawJointGuardedCommonNoRecvOne,
    profiledRawJointGuardedCommonTwoShadowRecvOneShadow,
    profiledRawJointGuardedCommonStartTwoShadow]
  exact hagrees.shadows A strategy hwin

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommon_strictLeft_sources
    {initial : CommonPoint A strategy}
    (one :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
        A strategy hwin initial)
    (two :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
        A strategy hwin initial)
    (hagrees :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
        A strategy hwin one two)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoNoRecv
      A strategy hwin two input.2).2.1 =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneRecv
        A strategy hwin one two input.1 input.2).2.shadow.source := by
  simp only [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoNoRecv,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneRecv,
    profiledRawJointGuardedCommonTwoShadowNoRecv,
    profiledRawJointGuardedCommonNoRecvTwo,
    profiledRawJointGuardedCommonOneShadowRecvTwoShadow,
    profiledRawJointGuardedCommonStartOneShadow]
  exact (hagrees.shadows A strategy hwin).symm

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommon_strictRight_outputs
    {initial : CommonPoint A strategy}
    (one :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
        A strategy hwin initial)
    (two :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
        A strategy hwin initial)
    (hagrees :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
        A strategy hwin one two)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneNoRecv
        A strategy hwin one input.1).1,
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoRecv
        A strategy hwin two one input.2 input.1).1) =
      (((one.key.pair A strategy hwin).rightRootRecord A strategy hwin input
          ).2.2,
        pairedRightInformedForRow .both
          ((one.key.pair A strategy hwin).rightRootRecord A strategy hwin
            input).2.1.physical) := by
  have hshadows := hagrees.shadows A strategy hwin
  change
    ((profiledRawJointGuardedCommonOneShadowNoRecv A strategy hwin one.shadow
        input.1).1,
      (profiledRawJointGuardedCommonTwoShadowRecvOneShadow A strategy hwin
        two.shadow one.shadow
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
            A strategy hwin initial two.key input).1 input.2 input.1).1) = _
  have hchild :
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
        A strategy hwin initial one.key input).1 =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
        A strategy hwin initial two.key input).1 :=
    congrArg
      (fun key ↦
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
          A strategy hwin initial key input).1) hagrees
  rw [← hchild]
  have houtputs :=
    profiledRawJointGuardedCommonShadows_strictRight_root_pair A strategy hwin
      one.shadow two.shadow hshadows
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
        A strategy hwin initial one.key input).1 input
  rw [one.common_eq] at houtputs
  exact houtputs

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommon_strictLeft_outputs
    {initial : CommonPoint A strategy}
    (one :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
        A strategy hwin initial)
    (two :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
        A strategy hwin initial)
    (hagrees :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
        A strategy hwin one two)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneRecv
        A strategy hwin one two input.1 input.2).1,
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoNoRecv
        A strategy hwin two input.2).1) =
      (pairedLeftInformedForRow .both
          ((one.key.pair A strategy hwin).leftRootRecord A strategy hwin input
            ).2.1.physical,
        ((one.key.pair A strategy hwin).leftRootRecord A strategy hwin input
          ).2.2) := by
  have hshadows := hagrees.shadows A strategy hwin
  change
    ((profiledRawJointGuardedCommonOneShadowRecvTwoShadow A strategy hwin
        one.shadow two.shadow
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
            A strategy hwin initial one.key input).1 input.1 input.2).1,
      (profiledRawJointGuardedCommonTwoShadowNoRecv A strategy hwin two.shadow
        input.2).1) = _
  have houtputs :=
    profiledRawJointGuardedCommonShadows_strictLeft_root_pair A strategy hwin
      one.shadow two.shadow hshadows
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
        A strategy hwin initial one.key input).1 input
  rw [one.common_eq] at houtputs
  exact houtputs

end

end DetParityAutomaton

end DistributedSynthesis
