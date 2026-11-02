/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedCommonBackbone
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPersistentPhysicalClose
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonOneRoundReplacement
import DistributedSynthesis.Formalizations.Lemma.LemProfiledRawJointFiniteCodeFailFast

/-!
# Fail-fast audit of the common/strict sibling lambda

After a locally ambiguous receive, the next `noRecv` must be executable by
the same process control in two globally different cases:

* the preceding round was simultaneous, so the proof state is the common
  successor; or
* it was strict-left (respectively strict-right), so the proof state is its
  one-sided sibling.

The exact root-pinned policy keeps both states in one finite policy, and the
active finite slot is literally equal.  That is not yet a local transition:
the two states are distinct (`common` versus `oneSided` code tags), and
`ProfiledRawJointLambdaFamilyMove.Valid` relates blind lambdas only inside
one installed move.  It has no cross-state clause.  Moreover a live slot
stores DPA data and the *receiver* initial profile, not the blind sender
strategy; `profiledRawJointFiniteCode_doesNotDetermineBlindLambda` gives a
kernel-checked collision at exactly that granularity.

This file isolates the weakest missing condition: equality of the physical
blind emissions, pointwise in the blind input history.  It neither assumes
equality of complete lambdas nor selects a fresh policy.  The final
certificate equivalences show that all selection/profile obligations follow
from existing `Valid`; only this pointwise equality remains.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

local notation "CommonControl" =>
  ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin

/-! ## The exact two sibling pairs -/

/-- The one-sided state selected by the strict-left interpretation of an
ambiguous simultaneous input.  Its right lane is the live lane. -/
noncomputable def profiledRawJointHybridRootPinnedCommonStrictLeftKey
    (control : CommonControl) (input : In₁ × In₂) :
    ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy hwin
      control.1 :=
  (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin control
    ).strictSuccessorKey A (profiledRawJointCommonOneRoundStrictLeft input)

/-- Strict-right mirror; its left lane is live. -/
noncomputable def profiledRawJointHybridRootPinnedCommonStrictRightKey
    (control : CommonControl) (input : In₁ × In₂) :
    ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy hwin
      control.1 :=
  (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin control
    ).strictSuccessorKey A (profiledRawJointCommonOneRoundStrictRight input)

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The simultaneous and strict-left siblings have the same live finite
right slot. -/
theorem profiledRawJointHybridRootPinnedCommonStrictLeft_rightSlot_eq
    (control : CommonControl) (input : In₁ × In₂) :
    (profiledRawJointHybridRootPinnedCommonNext A strategy hwin control input
      ).2.incidenceCode.family.right () =
      (profiledRawJointHybridRootPinnedCommonStrictLeftKey A strategy hwin
        control input).incidenceCode.family.right () := by
  rfl

/-- Strict-right/left-slot mirror. -/
theorem profiledRawJointHybridRootPinnedCommonStrictRight_leftSlot_eq
    (control : CommonControl) (input : In₁ × In₂) :
    (profiledRawJointHybridRootPinnedCommonNext A strategy hwin control input
      ).2.incidenceCode.family.left () =
      (profiledRawJointHybridRootPinnedCommonStrictRightKey A strategy hwin
        control input).incidenceCode.family.left () := by
  rfl

/-- Slot equality does not identify the policy states: their public code tags
are different constructors. -/
theorem profiledRawJointHybridRootPinnedCommonStrictLeft_states_ne
    (control : CommonControl) (input : In₁ × In₂) :
    (profiledRawJointHybridRootPinnedCommonNext A strategy hwin control input
      ).2.state ≠
      (profiledRawJointHybridRootPinnedCommonStrictLeftKey A strategy hwin
        control input).state := by
  intro heq
  have hcode := congrArg (fun state ↦ state.2.1) heq
  change
    (profiledRawJointHybridRootPinnedCommonNext A strategy hwin control input
      ).2.state.2.1 =
      (profiledRawJointHybridRootPinnedCommonStrictLeftKey A strategy hwin
        control input).state.2.1 at hcode
  rw [(profiledRawJointHybridRootPinnedCommonNext A strategy hwin control
    input).2.state_code,
    (profiledRawJointHybridRootPinnedCommonStrictLeftKey A strategy hwin
      control input).state_code] at hcode
  cases hcode

/-- Strict-right mirror. -/
theorem profiledRawJointHybridRootPinnedCommonStrictRight_states_ne
    (control : CommonControl) (input : In₁ × In₂) :
    (profiledRawJointHybridRootPinnedCommonNext A strategy hwin control input
      ).2.state ≠
      (profiledRawJointHybridRootPinnedCommonStrictRightKey A strategy hwin
        control input).state := by
  intro heq
  have hcode := congrArg (fun state ↦ state.2.1) heq
  change
    (profiledRawJointHybridRootPinnedCommonNext A strategy hwin control input
      ).2.state.2.1 =
      (profiledRawJointHybridRootPinnedCommonStrictRightKey A strategy hwin
        control input).state.2.1 at hcode
  rw [(profiledRawJointHybridRootPinnedCommonNext A strategy hwin control
    input).2.state_code,
    (profiledRawJointHybridRootPinnedCommonStrictRightKey A strategy hwin
      control input).state_code] at hcode
  cases hcode

end

/-! ## Installed moves and the weakest physical compatibility predicate -/

/-- Policy-free data of the common move installed after the ambiguous round.
The audit needs no reachability proof or policy table from that state. -/
noncomputable def
    profiledRawJointHybridRootPinnedCommonSuccessorMoveData
    (control : CommonControl) (input : In₁ × In₂) :
    ProfiledRawJointHybridCommonMoveData A strategy :=
  (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin
    (profiledRawJointHybridRootPinnedCommonNext A strategy hwin control input)
    ).toCommonMoveData A

/-- Installed move at the strict-left sibling, still in the one original
root-pinned policy. -/
noncomputable def profiledRawJointHybridRootPinnedCommonStrictLeftInstalled
    (control : CommonControl) (input : In₁ × In₂) :
    ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
      strategy hwin control.1
        (profiledRawJointHybridRootPinnedCommonStrictLeftKey A strategy hwin
          control input) :=
  Classical.choice
    (nonempty_profiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove
      A strategy hwin control.1
        (profiledRawJointHybridRootPinnedCommonStrictLeftKey A strategy hwin
          control input))

/-- Strict-right mirror. -/
noncomputable def profiledRawJointHybridRootPinnedCommonStrictRightInstalled
    (control : CommonControl) (input : In₁ × In₂) :
    ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
      strategy hwin control.1
        (profiledRawJointHybridRootPinnedCommonStrictRightKey A strategy hwin
          control input) :=
  Classical.choice
    (nonempty_profiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove
      A strategy hwin control.1
        (profiledRawJointHybridRootPinnedCommonStrictRightKey A strategy hwin
          control input))

/-- Physical process-one emission of the move installed at the hypothetical
common successor.  `none` is retained in the codomain so the predicate itself
does not smuggle in a lambda-selection witness. -/
noncomputable def profiledRawJointHybridRootPinnedCommonRightBlindEmission
    (control : CommonControl) (input : In₁ × In₂)
    (past : List In₁) (own : In₁) : Option Out₁ :=
  ((profiledRawJointHybridRootPinnedCommonSuccessorMoveData A strategy hwin
      control input).rawMove.rightLambda ()).map
        (fun lambda ↦ lambda.blind past own)

/-- The same local emission read from the strict-left sibling state. -/
noncomputable def profiledRawJointHybridRootPinnedStrictLeftRightBlindEmission
    (control : CommonControl) (input : In₁ × In₂)
    (past : List In₁) (own : In₁) : Option Out₁ :=
  ((profiledRawJointHybridRootPinnedCommonStrictLeftInstalled A strategy hwin
      control input).rawMove.rightLambda ()).map
        (fun lambda ↦ lambda.blind past own)

/-- The exact missing process-one obligation.  It asks only for equality of
locally emitted outputs throughout the blind phase, not equality of complete
proof-side lambdas. -/
def ProfiledRawJointHybridRootPinnedRightSiblingBlindCompatible
    (control : CommonControl) (input : In₁ × In₂) : Prop :=
  ∀ past own,
    profiledRawJointHybridRootPinnedCommonRightBlindEmission A strategy hwin
        control input past own =
      profiledRawJointHybridRootPinnedStrictLeftRightBlindEmission A strategy
        hwin control input past own

/-- Process-two common-successor blind emission. -/
noncomputable def profiledRawJointHybridRootPinnedCommonLeftBlindEmission
    (control : CommonControl) (input : In₁ × In₂)
    (past : List In₂) (own : In₂) : Option Out₂ :=
  ((profiledRawJointHybridRootPinnedCommonSuccessorMoveData A strategy hwin
      control input).rawMove.leftLambda ()).map
        (fun lambda ↦ lambda.blind past own)

/-- Process-two strict-right sibling emission. -/
noncomputable def profiledRawJointHybridRootPinnedStrictRightLeftBlindEmission
    (control : CommonControl) (input : In₁ × In₂)
    (past : List In₂) (own : In₂) : Option Out₂ :=
  ((profiledRawJointHybridRootPinnedCommonStrictRightInstalled A strategy hwin
      control input).rawMove.leftLambda ()).map
        (fun lambda ↦ lambda.blind past own)

/-- Exact process-two mirror obligation. -/
def ProfiledRawJointHybridRootPinnedLeftSiblingBlindCompatible
    (control : CommonControl) (input : In₁ × In₂) : Prop :=
  ∀ past own,
    profiledRawJointHybridRootPinnedCommonLeftBlindEmission A strategy hwin
        control input past own =
      profiledRawJointHybridRootPinnedStrictRightLeftBlindEmission A strategy
        hwin control input past own

/-! ## Exact selection/profile certificates -/

/-- Everything required to execute the ambiguous process-one blind phase.
The first four equations are already consequences of the installed-move
validity laws; `blind_output_eq` is the genuinely new field. -/
structure ProfiledRawJointHybridRootPinnedRightSiblingLocalCertificate
    (control : CommonControl) (input : In₁ × In₂) where
  commonLambda : ProcOnePairedRightLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  strictLambda : ProcOnePairedRightLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  common_selected :
    (profiledRawJointHybridRootPinnedCommonSuccessorMoveData A strategy hwin
      control input).rawMove.rightLambda () = some commonLambda
  strict_selected :
    (profiledRawJointHybridRootPinnedCommonStrictLeftInstalled A strategy hwin
      control input).rawMove.rightLambda () = some strictLambda
  common_profile :
    rightInitialFirstProfile commonLambda =
      ((profiledRawJointHybridRootPinnedCommonSuccessorMoveData A strategy hwin
        control input).world.procOneSlot A).2
  strict_profile :
    rightInitialFirstProfile strictLambda =
      ((profiledRawJointHybridRootPinnedCommonSuccessorMoveData A strategy hwin
        control input).world.procOneSlot A).2
  blind_output_eq : ∀ past own,
    commonLambda.blind past own = strictLambda.blind past own

/-- Process-two mirror certificate. -/
structure ProfiledRawJointHybridRootPinnedLeftSiblingLocalCertificate
    (control : CommonControl) (input : In₁ × In₂) where
  commonLambda : ProcTwoPairedLeftLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  strictLambda : ProcTwoPairedLeftLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  common_selected :
    (profiledRawJointHybridRootPinnedCommonSuccessorMoveData A strategy hwin
      control input).rawMove.leftLambda () = some commonLambda
  strict_selected :
    (profiledRawJointHybridRootPinnedCommonStrictRightInstalled A strategy hwin
      control input).rawMove.leftLambda () = some strictLambda
  common_profile :
    leftInitialFirstProfile commonLambda =
      ((profiledRawJointHybridRootPinnedCommonSuccessorMoveData A strategy hwin
        control input).world.procTwoSlot A).2
  strict_profile :
    leftInitialFirstProfile strictLambda =
      ((profiledRawJointHybridRootPinnedCommonSuccessorMoveData A strategy hwin
        control input).world.procTwoSlot A).2
  blind_output_eq : ∀ past own,
    commonLambda.blind past own = strictLambda.blind past own

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The right certificate exists exactly when the missing pointwise blind
compatibility holds.  In the reverse direction, both selected lambdas and
both profile equations are reconstructed from the already-proved `Valid`
laws and live-slot equality. -/
theorem
    nonempty_profiledRawJointHybridRootPinnedRightSiblingLocalCertificate_iff
    (control : CommonControl) (input : In₁ × In₂) :
    Nonempty
        (ProfiledRawJointHybridRootPinnedRightSiblingLocalCertificate A
          strategy hwin control input) ↔
      ProfiledRawJointHybridRootPinnedRightSiblingBlindCompatible A strategy
        hwin control input := by
  constructor
  · rintro ⟨certificate⟩ past own
    unfold profiledRawJointHybridRootPinnedCommonRightBlindEmission
    unfold profiledRawJointHybridRootPinnedStrictLeftRightBlindEmission
    rw [certificate.common_selected, certificate.strict_selected]
    exact congrArg some (certificate.blind_output_eq past own)
  · intro hcompatible
    let commonData :=
      profiledRawJointHybridRootPinnedCommonSuccessorMoveData A strategy hwin
        control input
    let strictInstalled :=
      profiledRawJointHybridRootPinnedCommonStrictLeftInstalled A strategy hwin
        control input
    let source := commonData.world.procOneSlot A
    have hcommonSlot :
        (profiledRawJointHybridRootPinnedCommonNext A strategy hwin control
          input).2.incidenceCode.family.right () = some source := by
      exact commonData.right_slot A
    have hstrictSlot :
        (profiledRawJointHybridRootPinnedCommonStrictLeftKey A strategy hwin
          control input).incidenceCode.family.right () = some source := by
      rw [← profiledRawJointHybridRootPinnedCommonStrictLeft_rightSlot_eq A
        strategy hwin control input]
      exact hcommonSlot
    rcases (strictInstalled.move_valid A).2.2.2.1 () source hstrictSlot with
      ⟨strictLambda, hstrictSelected, hstrictProfile, _⟩
    let commonLambda := commonData.rightLambda A
    have hcommonSelected :
        commonData.rawMove.rightLambda () = some commonLambda :=
      commonData.rightLambda_selected A
    have hcommonProfile :
        rightInitialFirstProfile commonLambda = source.2 :=
      commonData.rightLambda_initialProfile A
    refine ⟨⟨commonLambda, strictLambda, hcommonSelected, hstrictSelected,
      hcommonProfile, hstrictProfile, ?_⟩⟩
    intro past own
    have hpoint := hcompatible past own
    unfold profiledRawJointHybridRootPinnedCommonRightBlindEmission at hpoint
    unfold profiledRawJointHybridRootPinnedStrictLeftRightBlindEmission at hpoint
    rw [hcommonSelected, hstrictSelected] at hpoint
    exact Option.some.inj hpoint

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two mirror: again the pointwise blind equality is precisely the
only field not supplied by the current finite-code validity interface. -/
theorem
    nonempty_profiledRawJointHybridRootPinnedLeftSiblingLocalCertificate_iff
    (control : CommonControl) (input : In₁ × In₂) :
    Nonempty
        (ProfiledRawJointHybridRootPinnedLeftSiblingLocalCertificate A strategy
          hwin control input) ↔
      ProfiledRawJointHybridRootPinnedLeftSiblingBlindCompatible A strategy
        hwin control input := by
  constructor
  · rintro ⟨certificate⟩ past own
    unfold profiledRawJointHybridRootPinnedCommonLeftBlindEmission
    unfold profiledRawJointHybridRootPinnedStrictRightLeftBlindEmission
    rw [certificate.common_selected, certificate.strict_selected]
    exact congrArg some (certificate.blind_output_eq past own)
  · intro hcompatible
    let commonData :=
      profiledRawJointHybridRootPinnedCommonSuccessorMoveData A strategy hwin
        control input
    let strictInstalled :=
      profiledRawJointHybridRootPinnedCommonStrictRightInstalled A strategy hwin
        control input
    let source := commonData.world.procTwoSlot A
    have hcommonSlot :
        (profiledRawJointHybridRootPinnedCommonNext A strategy hwin control
          input).2.incidenceCode.family.left () = some source := by
      exact commonData.left_slot A
    have hstrictSlot :
        (profiledRawJointHybridRootPinnedCommonStrictRightKey A strategy hwin
          control input).incidenceCode.family.left () = some source := by
      rw [← profiledRawJointHybridRootPinnedCommonStrictRight_leftSlot_eq A
        strategy hwin control input]
      exact hcommonSlot
    rcases (strictInstalled.move_valid A).2.2.2.2.2.1 () source hstrictSlot with
      ⟨strictLambda, hstrictSelected, hstrictProfile, _⟩
    let commonLambda := commonData.leftLambda A
    have hcommonSelected :
        commonData.rawMove.leftLambda () = some commonLambda :=
      commonData.leftLambda_selected A
    have hcommonProfile :
        leftInitialFirstProfile commonLambda = source.2 :=
      commonData.leftLambda_initialProfile A
    refine ⟨⟨commonLambda, strictLambda, hcommonSelected, hstrictSelected,
      hcommonProfile, hstrictProfile, ?_⟩⟩
    intro past own
    have hpoint := hcompatible past own
    unfold profiledRawJointHybridRootPinnedCommonLeftBlindEmission at hpoint
    unfold profiledRawJointHybridRootPinnedStrictRightLeftBlindEmission at hpoint
    rw [hcommonSelected, hstrictSelected] at hpoint
    exact Option.some.inj hpoint

end

end DetParityAutomaton

end DistributedSynthesis
