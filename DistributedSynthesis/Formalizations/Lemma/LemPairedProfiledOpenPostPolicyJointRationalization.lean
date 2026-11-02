/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyPinnedProvenance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenHiddenDescriptorFamilyAlphabet
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenClassifiedAutomaton

/-!
# One joint family rationalization below an outer policy

The original paired-entry construction first rationalizes the input-free run,
then extracts its lambda, and only afterwards applies finite block narrowing.
The crucial post-rationalization invariant is that every literal close remains
in the image of the *same* rational policy.

This file records the descriptor-family version of that ordering.  The strong
table law is the conjunction of the ordinary classified-table law and
outer-policy edge safety.  Root pinning and union narrowing are then performed
once under that conjunction.  Weakening forgets only the proof-side policy
law; the returned runtime value is the existing finite pinned family move and
uses definitionally the same controller.

Thus this construction never compares two independently rationalized tables.
It is the reusable join needed by an outer input-free automaton whose legal
transition exposes one simultaneous semantic family of block strategies.

**Status.**  This is a conditional adapter, not an unconditional outer-run
construction.  The existing indexed classified-move policy does not supply
its `hjoint` premise, because those classified tables were already narrowed
independently before the outer basis call.  The intended consumer is the new
raw-move coded-observable policy: its one selected simultaneous semantic move
must first be projected to the right and left families below the same policy
state.  Until that concrete projection is instantiated, this file must not be
used as evidence that the main theorem is closed.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Policy-image edges of a two-sorted outer run -/

/-- A chosen family state is in the one-step image of a fixed family state of
the outer rational policy.  Only existence of a proof-side direction matters;
the direction is not exposed to either process. -/
def ProfiledOpenOuterPolicyEdge
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (FamilyAllowed : Finset (ProfiledOpenClassifiedAnchor A) →
      TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
        (ProfiledOpenClassifiedDirection A) → Prop)
    (policy :
      (twoSortedFamilyRunAutomaton
        (profiledOpenClassifiedAnchorPriority A) initialRoots
        FamilyAllowed).RationalTransitionPolicy)
    (sourceRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (actual : ProfiledOpenClassifiedAnchor A)
    (targetRoots : Finset (ProfiledOpenClassifiedAnchor A)) : Prop :=
  ∃ direction,
    policy.successor (.family sourceRoots) direction =
      .chosen actual targetRoots

/-- A right classified response table is safe for the outer policy when every
row of every root/input entry emits a chosen state in the policy image. -/
def ProfiledOpenHiddenDescriptorRightOuterPolicySafe
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (FamilyAllowed : Finset (ProfiledOpenClassifiedAnchor A) →
      TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
        (ProfiledOpenClassifiedDirection A) → Prop)
    (policy :
      (twoSortedFamilyRunAutomaton
        (profiledOpenClassifiedAnchorPriority A) initialRoots
        FamilyAllowed).RationalTransitionPolicy)
    (sourceRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (responses :
      ((ProfiledOpenHiddenDescriptorRightRoot A descriptor × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) : Prop :=
  ∀ member (move : In₂ × In₁) row,
    let output := responses ((member, move.1), move.2)
    ProfiledOpenOuterPolicyEdge A initialRoots FamilyAllowed policy sourceRoots
      (.left (output.2 row).1)
      (profiledOpenLeftClassifiedRoots A (output.2 row).2)

/-- Mirror policy-image law for left classified response tables. -/
def ProfiledOpenHiddenDescriptorLeftOuterPolicySafe
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (FamilyAllowed : Finset (ProfiledOpenClassifiedAnchor A) →
      TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
        (ProfiledOpenClassifiedDirection A) → Prop)
    (policy :
      (twoSortedFamilyRunAutomaton
        (profiledOpenClassifiedAnchorPriority A) initialRoots
        FamilyAllowed).RationalTransitionPolicy)
    (sourceRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (responses :
      ((ProfiledOpenHiddenDescriptorLeftRoot A descriptor × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) : Prop :=
  ∀ member (move : In₁ × In₂) row,
    let output := responses ((member, move.1), move.2)
    ProfiledOpenOuterPolicyEdge A initialRoots FamilyAllowed policy sourceRoots
      (.right (output.2 row).1)
      (profiledOpenRightClassifiedRoots A (output.2 row).2)

/-! ## One strong extraction, then proof-only weakening -/

/-- The strong right law imposed during the unique union extraction. -/
def ProfiledOpenHiddenDescriptorRightJointAllowed
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (FamilyAllowed : Finset (ProfiledOpenClassifiedAnchor A) →
      TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
        (ProfiledOpenClassifiedDirection A) → Prop)
    (policy :
      (twoSortedFamilyRunAutomaton
        (profiledOpenClassifiedAnchorPriority A) initialRoots
        FamilyAllowed).RationalTransitionPolicy)
    (sourceRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (responses :
      ((ProfiledOpenHiddenDescriptorRightRoot A descriptor × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) : Prop :=
  ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor responses ∧
    ProfiledOpenHiddenDescriptorRightOuterPolicySafe A initialRoots
      FamilyAllowed policy sourceRoots descriptor responses

/-- The strong left law. -/
def ProfiledOpenHiddenDescriptorLeftJointAllowed
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (FamilyAllowed : Finset (ProfiledOpenClassifiedAnchor A) →
      TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
        (ProfiledOpenClassifiedDirection A) → Prop)
    (policy :
      (twoSortedFamilyRunAutomaton
        (profiledOpenClassifiedAnchorPriority A) initialRoots
        FamilyAllowed).RationalTransitionPolicy)
    (sourceRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (responses :
      ((ProfiledOpenHiddenDescriptorLeftRoot A descriptor × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) : Prop :=
  ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor responses ∧
    ProfiledOpenHiddenDescriptorLeftOuterPolicySafe A initialRoots
      FamilyAllowed policy sourceRoots descriptor responses

/-- One right union move whose literal controller carries both the ordinary
finite classified law and the outer-policy image law. -/
noncomputable abbrev ProfiledOpenRightPostPolicyJointMove
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode)
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (FamilyAllowed : Finset (ProfiledOpenClassifiedAnchor A) →
      TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
        (ProfiledOpenClassifiedDirection A) → Prop)
    (policy :
      (twoSortedFamilyRunAutomaton
        (profiledOpenClassifiedAnchorPriority A) initialRoots
        FamilyAllowed).RationalTransitionPolicy)
    (sourceRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (expected : ProfiledOpenHiddenDescriptorRightExpected A family) :=
  FiniteDescriptorFamilyPinnedProvenanceMove
    (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A family ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightJointAllowed A initialRoots
        FamilyAllowed policy sourceRoots descriptor.1 responses)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)
    expected

/-- Right post-policy extraction.  The only substantive premise is
`hjoint`: the semantic family chosen by the outer transition must satisfy the
ordinary classified law and must name successors in that same transition's
policy image. -/
noncomputable def profiledOpenRightPostPolicyJointMoveOfStrategies
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode)
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (FamilyAllowed : Finset (ProfiledOpenClassifiedAnchor A) →
      TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
        (ProfiledOpenClassifiedDirection A) → Prop)
    (policy :
      (twoSortedFamilyRunAutomaton
        (profiledOpenClassifiedAnchorPriority A) initialRoots
        FamilyAllowed).RationalTransitionPolicy)
    (sourceRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (expected : ProfiledOpenHiddenDescriptorRightExpected A family)
    [Inhabited (Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorRightCarrier A family ↦
        ProfiledOpenHiddenDescriptorRightRoot A descriptor.1))]
    (receiver : ∀ _member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorRightCarrier A family ↦
        ProfiledOpenHiddenDescriptorRightRoot A descriptor.1),
      ReceiverBlockStrategy In₂ In₁ (ProfiledOpenRightClassifiedOutput A))
    (sender : SenderBlockStrategy In₁ Out₁)
    (hwin : ∀ member env,
      (profiledOpenHiddenDescriptorRightMonitor A member.1.1 member.2).WinsPlay
        (pairPlay (receiver member) sender env))
    (hroot : ∀ member input,
      pairPlay (receiver member) sender (fun _ ↦ input) 0 =
        expected member input)
    (hjoint : ∀ past,
      DescriptorRootUnionAllowed
        (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A family ↦
          ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
        (fun descriptor responses ↦
          ProfiledOpenHiddenDescriptorRightJointAllowed A initialRoots
            FamilyAllowed policy sourceRoots descriptor.1 responses)
        (finiteRootFamilyReceiver receiver past)) :
    ProfiledOpenRightPostPolicyJointMove A family initialRoots FamilyAllowed
      policy sourceRoots expected := by
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨receiver default [] default⟩
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      family ↦ ProfiledOpenHiddenDescriptorRightRoot A descriptor.1
  let M := fun descriptor (root : Root descriptor) ↦
    profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root
  let Strong := fun descriptor (responses :
      ((Root descriptor × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) ↦
    ProfiledOpenHiddenDescriptorRightJointAllowed A initialRoots
      FamilyAllowed policy sourceRoots descriptor.1 responses
  let Weak := fun descriptor (responses :
      ((Root descriptor × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) ↦
    ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses
  apply finiteDescriptorFamilyPinnedProvenanceMoveOfStrategies Root M Strong
    Weak expected (fun _ _ h ↦ h.1)
    (finiteRootFamilyReceiver receiver []) (hjoint []) receiver sender hwin
    hroot hjoint

/-- Forgetting the proof-only outer-policy law returns exactly the existing
right pinned-family runtime type, on the same controller. -/
noncomputable def ProfiledOpenRightPostPolicyJointMove.toPinnedMove
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    {family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode}
    {initialRoots : Finset (ProfiledOpenClassifiedAnchor A)}
    {FamilyAllowed : Finset (ProfiledOpenClassifiedAnchor A) →
      TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
        (ProfiledOpenClassifiedDirection A) → Prop}
    {policy :
      (twoSortedFamilyRunAutomaton
        (profiledOpenClassifiedAnchorPriority A) initialRoots
        FamilyAllowed).RationalTransitionPolicy}
    {sourceRoots : Finset (ProfiledOpenClassifiedAnchor A)}
    {expected : ProfiledOpenHiddenDescriptorRightExpected A family}
    (move : ProfiledOpenRightPostPolicyJointMove A family initialRoots
      FamilyAllowed policy sourceRoots expected) :
    ProfiledOpenHiddenDescriptorRightPinnedFamilyMove A family expected :=
  FiniteDescriptorFamilyPinnedProvenanceMove.toPinnedMove
    (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A family ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightJointAllowed A initialRoots
        FamilyAllowed policy sourceRoots descriptor.1 responses)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)
    expected move

/-- Left union move with the same post-policy ordering. -/
noncomputable abbrev ProfiledOpenLeftPostPolicyJointMove
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode)
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (FamilyAllowed : Finset (ProfiledOpenClassifiedAnchor A) →
      TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
        (ProfiledOpenClassifiedDirection A) → Prop)
    (policy :
      (twoSortedFamilyRunAutomaton
        (profiledOpenClassifiedAnchorPriority A) initialRoots
        FamilyAllowed).RationalTransitionPolicy)
    (sourceRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (expected : ProfiledOpenHiddenDescriptorLeftExpected A family) :=
  FiniteDescriptorFamilyPinnedProvenanceMove
    (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A family ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftJointAllowed A initialRoots
        FamilyAllowed policy sourceRoots descriptor.1 responses)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)
    expected

/-- Left post-policy extraction, performed once for the entire descriptor
union. -/
noncomputable def profiledOpenLeftPostPolicyJointMoveOfStrategies
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode)
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (FamilyAllowed : Finset (ProfiledOpenClassifiedAnchor A) →
      TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
        (ProfiledOpenClassifiedDirection A) → Prop)
    (policy :
      (twoSortedFamilyRunAutomaton
        (profiledOpenClassifiedAnchorPriority A) initialRoots
        FamilyAllowed).RationalTransitionPolicy)
    (sourceRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (expected : ProfiledOpenHiddenDescriptorLeftExpected A family)
    [Inhabited (Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorLeftCarrier A family ↦
        ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1))]
    (receiver : ∀ _member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorLeftCarrier A family ↦
        ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1),
      ReceiverBlockStrategy In₁ In₂ (ProfiledOpenLeftClassifiedOutput A))
    (sender : SenderBlockStrategy In₂ Out₂)
    (hwin : ∀ member env,
      (profiledOpenHiddenDescriptorLeftMonitor A member.1.1 member.2).WinsPlay
        (pairPlay (receiver member) sender env))
    (hroot : ∀ member input,
      pairPlay (receiver member) sender (fun _ ↦ input) 0 =
        expected member input)
    (hjoint : ∀ past,
      DescriptorRootUnionAllowed
        (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A family ↦
          ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
        (fun descriptor responses ↦
          ProfiledOpenHiddenDescriptorLeftJointAllowed A initialRoots
            FamilyAllowed policy sourceRoots descriptor.1 responses)
        (finiteRootFamilyReceiver receiver past)) :
    ProfiledOpenLeftPostPolicyJointMove A family initialRoots FamilyAllowed
      policy sourceRoots expected := by
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨receiver default [] default⟩
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      family ↦ ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1
  let M := fun descriptor (root : Root descriptor) ↦
    profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root
  let Strong := fun descriptor (responses :
      ((Root descriptor × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) ↦
    ProfiledOpenHiddenDescriptorLeftJointAllowed A initialRoots
      FamilyAllowed policy sourceRoots descriptor.1 responses
  let Weak := fun descriptor (responses :
      ((Root descriptor × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) ↦
    ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses
  apply finiteDescriptorFamilyPinnedProvenanceMoveOfStrategies Root M Strong
    Weak expected (fun _ _ h ↦ h.1)
    (finiteRootFamilyReceiver receiver []) (hjoint []) receiver sender hwin
    hroot hjoint

/-- Runtime projection of the left joint move. -/
noncomputable def ProfiledOpenLeftPostPolicyJointMove.toPinnedMove
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    {family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode}
    {initialRoots : Finset (ProfiledOpenClassifiedAnchor A)}
    {FamilyAllowed : Finset (ProfiledOpenClassifiedAnchor A) →
      TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
        (ProfiledOpenClassifiedDirection A) → Prop}
    {policy :
      (twoSortedFamilyRunAutomaton
        (profiledOpenClassifiedAnchorPriority A) initialRoots
        FamilyAllowed).RationalTransitionPolicy}
    {sourceRoots : Finset (ProfiledOpenClassifiedAnchor A)}
    {expected : ProfiledOpenHiddenDescriptorLeftExpected A family}
    (move : ProfiledOpenLeftPostPolicyJointMove A family initialRoots
      FamilyAllowed policy sourceRoots expected) :
    ProfiledOpenHiddenDescriptorLeftPinnedFamilyMove A family expected :=
  FiniteDescriptorFamilyPinnedProvenanceMove.toPinnedMove
    (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A family ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftJointAllowed A initialRoots
        FamilyAllowed policy sourceRoots descriptor.1 responses)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)
    expected move

end

end DetParityAutomaton

end DistributedSynthesis
