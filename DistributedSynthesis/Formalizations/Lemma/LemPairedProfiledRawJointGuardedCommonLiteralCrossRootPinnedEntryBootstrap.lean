/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryKey
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossLocalCarrier
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingBlindForkInvariant

/-!
# Entry-aligned blind bootstrap below a root-pinned common occurrence

At an ambiguous simultaneous receive, the strict and simultaneous meanings
must not be represented by independently rationalized controls.  This file
installs both meanings in the two members of the literal cross tables selected
at the exact predecessor occurrence.  The actual entry input is consumed in
all four table roots before the unresolved fork is exposed.

Each endpoint retains one blind sender and the two possible receiver members
for the opposite orientation.  Its no-receive transition advances only the
sender.  The blind relation therefore equates exactly the sender coordinates;
receiver coordinates may diverge at later receive steps without invalidating
blind output coherence.  Consequently the hidden member is observationally
irrelevant under an arbitrary finite no-receive prefix.  The final theorems
state this directly as reachable `NoRecvOutputCoherent` facts for the
acknowledged relay.

The root-pinned policy is used to identify the retained table pair with the
unique guarded root move.  No executable map receives a graph, orientation,
leader bit, semantic history, or partner input hidden from that endpoint.
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

private abbrev Extra :=
  ProfiledRawJointGuardedCommonLiteralCrossExtra A

private abbrev RightSender :=
  ProfiledRawJointGuardedCommonRightLiteralCrossSenderState A

private abbrev RightReceiver :=
  ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState A

private abbrev LeftSender :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossSenderState A

private abbrev LeftReceiver :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState A

/-! ## Entry-aligned finite controls -/

/-- Process one retains the right-oriented blind sender and both members of
the left-oriented receiver. -/
abbrev ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneShared :=
  RightSender A × FiniteDelayedFork (LeftReceiver A)

/-- Process two retains the mirror sender/receiver pair. -/
abbrev ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoShared :=
  LeftSender A × FiniteDelayedFork (RightReceiver A)

/-- The Boolean selects only the receiver member.  It is finite controller
state, not a graph or leader observation. -/
abbrev ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneControl :=
  Bool × ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneShared A

abbrev ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoControl :=
  Bool × ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoShared A

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneControlFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneControl A) :=
  by infer_instance

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoControlFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoControl A) :=
  by infer_instance

/-- The literal table pair selected at the exact predecessor occurrence. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra
    (initial : CommonPoint A strategy) : Extra A :=
  profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin initial

/-- Consuming the entry record in every process-one table root.  The sender
uses only process one's local input; the receiver candidates use the delivered
input that is available at the ambiguous receive. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneSharedInitial
    (initial : CommonPoint A strategy) (entry : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneShared A :=
  let extra :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra A strategy
      hwin initial
  let senderRoot :=
    profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A extra.1
  let receiverRoot := fun member ↦
    profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
      member
  ((profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A senderRoot
      entry.1).2,
    ⟨(profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
        (receiverRoot false) entry.1 entry.2).2,
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
        (receiverRoot true) entry.1 entry.2).2⟩)

/-- Process-two mirror of the entry-aligned shared value. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoSharedInitial
    (initial : CommonPoint A strategy) (entry : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoShared A :=
  let extra :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra A strategy
      hwin initial
  let senderRoot :=
    profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A extra.2
  let receiverRoot := fun member ↦
    profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A extra.1
      member
  ((profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A senderRoot
      entry.2).2,
    ⟨(profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
        (receiverRoot false) entry.2 entry.1).2,
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
        (receiverRoot true) entry.2 entry.1).2⟩)

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial
    (initial : CommonPoint A strategy) (entry : In₁ × In₂)
    (member : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneControl A :=
  (member,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneSharedInitial A
      strategy hwin initial entry)

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial
    (initial : CommonPoint A strategy) (entry : In₁ × In₂)
    (member : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoControl A :=
  (member,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoSharedInitial A
      strategy hwin initial entry)

/-! ## The retained IDs are the root-pinned IDs -/

/-- The bootstrap annotation is exactly the annotation of the unique guarded
root move; it is not selected again at the child code. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra_eq_rootMove
    (initial : CommonPoint A strategy) :
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra A strategy
        hwin initial =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy
        hwin initial).rootMove.2 := by
  rw [profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy_rootMove A
    strategy hwin initial]
  rfl

/-! ## Endpoint-local no-receive bisimulation -/

/-- Process one advances only its retained blind sender. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne
    (state :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneControl A)
    (input : In₁) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneControl A ×
      Out₁ :=
  let next :=
    profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A state.2.1
      input
  ((state.1, next.2, state.2.2), next.1)

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo
    (state :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoControl A)
    (input : In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoControl A ×
      Out₂ :=
  let next :=
    profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A state.2.1 input
  ((state.1, next.2, state.2.2), next.1)

/-- Two process-one candidates are blind-related precisely when their blind
sender controls agree.  Their receiver candidates are deliberately omitted:
later receive steps may advance different private members, whereas a
no-receive output reads only this sender coordinate. -/
def ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindOne
    (left right :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneControl A) :
    Prop :=
  left.2.1 = right.2.1

/-- Process-two mirror. -/
def ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindTwo
    (left right :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoControl A) :
    Prop :=
  left.2.1 = right.2.1

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Member choice cannot affect a process-one no-receive output, and the
complete shared state remains equal after the step. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindOne_noRecv
    (left right :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneControl A)
    (input : In₁)
    (hblind :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindOne A left
        right) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne A left
        input).2 =
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne A
          right input).2 ∧
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindOne A
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne A
          left input).1
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne A
          right input).1 := by
  rcases left with ⟨leftMember, leftShared⟩
  rcases right with ⟨rightMember, rightShared⟩
  rcases leftShared with ⟨leftSender, leftReceivers⟩
  rcases rightShared with ⟨rightSender, rightReceivers⟩
  change leftSender = rightSender at hblind
  subst rightSender
  exact ⟨rfl, rfl⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two mirror. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindTwo_noRecv
    (left right :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoControl A)
    (input : In₂)
    (hblind :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindTwo A left
        right) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo A left
        input).2 =
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo A
          right input).2 ∧
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindTwo A
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo A
          left input).1
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo A
          right input).1 := by
  rcases left with ⟨leftMember, leftShared⟩
  rcases right with ⟨rightMember, rightShared⟩
  rcases leftShared with ⟨leftSender, leftReceivers⟩
  rcases rightShared with ⟨rightSender, rightReceivers⟩
  change leftSender = rightSender at hblind
  subst rightSender
  exact ⟨rfl, rfl⟩

/-- The two endpoint laws in the exact generic form used by the acknowledged
blind-fork invariant. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindNoRecvLaws :
    FiniteAcknowledgedDelayedCarrier.BlindNoRecvLaws
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne A)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo A)
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindOne A)
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindTwo A) :=
  {
    one :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindOne_noRecv A
    two :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindTwo_noRecv A
  }

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_blindOne
    (initial : CommonPoint A strategy) (entry : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindOne A
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
        strategy hwin initial entry false)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
        strategy hwin initial entry true) :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_blindTwo
    (initial : CommonPoint A strategy) (entry : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindTwo A
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
        strategy hwin initial entry false)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
        strategy hwin initial entry true) :=
  rfl

/-! ## Reachable acknowledged-fork coherence -/

private abbrev OneControl :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneControl A

private abbrev TwoControl :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoControl A

private abbrev OneRelay :=
  FiniteAcknowledgedDelayedCarrier (Fin 5) (OneControl A)

private abbrev TwoRelay :=
  FiniteAcknowledgedDelayedCarrier (Fin 5) (TwoControl A)

/-- The unresolved process-one entry fork contains the two members of one
shared table state and hence, in particular, one blind sender state. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneFork
    (initial : CommonPoint A strategy) (entry : In₁ × In₂) :
    OneRelay A :=
  ⟨.fork 0
      ⟨profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
          strategy hwin initial entry false,
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
          strategy hwin initial entry true⟩,
    none⟩

/-- Process-two mirror entry fork. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoFork
    (initial : CommonPoint A strategy) (entry : In₁ × In₂) :
    TwoRelay A :=
  ⟨.fork 0
      ⟨profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
          strategy hwin initial entry false,
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
          strategy hwin initial entry true⟩,
    none⟩

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneFork_blind
    (initial : CommonPoint A strategy) (entry : In₁ × In₂) :
    FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindOne A)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneFork A
        strategy hwin initial entry) :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoFork_blind
    (initial : CommonPoint A strategy) (entry : In₁ × In₂) :
    FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindTwo A)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoFork A
        strategy hwin initial entry) :=
  rfl

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneBlindRun
    (state : OneRelay A) : List In₁ → OneRelay A
  | [] => state
  | input :: rest =>
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneBlindRun
        (FiniteAcknowledgedDelayedCarrier.noRecvMealy
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne A)
          state input).1 rest

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoBlindRun
    (state : TwoRelay A) : List In₂ → TwoRelay A
  | [] => state
  | input :: rest =>
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoBlindRun
        (FiniteAcknowledgedDelayedCarrier.noRecvMealy
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo A)
          state input).1 rest

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The process-one blind relation is preserved at every state reachable by
a finite no-receive prefix. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneBlindRun_blind
    (state : OneRelay A)
    (hblind : FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindOne A)
      state) :
    ∀ past : List In₁,
      FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork
        (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindOne A)
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneBlindRun A
          state past) := by
  intro past
  induction past generalizing state with
  | nil => exact hblind
  | cons input rest ih =>
      simp only [
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneBlindRun]
      apply ih
      exact hblind.noRecv
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne A)
        (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindOne A)
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindOne_noRecv
          A)
        state input

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two mirror. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoBlindRun_blind
    (state : TwoRelay A)
    (hblind : FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindTwo A)
      state) :
    ∀ past : List In₂,
      FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork
        (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindTwo A)
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoBlindRun A
          state past) := by
  intro past
  induction past generalizing state with
  | nil => exact hblind
  | cons input rest ih =>
      simp only [
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoBlindRun]
      apply ih
      exact hblind.noRecv
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo A)
        (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindTwo A)
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindTwo_noRecv
          A)
        state input

/-- Exact reachable process-one blind-output coherence after any finite
no-receive prefix below the honest entry. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOne_reachable_coherent
    (initial : CommonPoint A strategy) (entry : In₁ × In₂)
    (past : List In₁) (input : In₁) :
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne A)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneBlindRun A
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneFork A
          strategy hwin initial entry) past)
      input := by
  apply FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork.noRecvOutputCoherent
    (Blind :=
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindOne A)
    (hstep :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindOne_noRecv A)
  exact
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneBlindRun_blind A
      _
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneFork_blind A
        strategy hwin initial entry) past

/-- Exact reachable process-two mirror. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwo_reachable_coherent
    (initial : CommonPoint A strategy) (entry : In₁ × In₂)
    (past : List In₂) (input : In₂) :
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo A)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoBlindRun A
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoFork A
          strategy hwin initial entry) past)
      input := by
  apply FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork.noRecvOutputCoherent
    (Blind :=
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindTwo A)
    (hstep :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBlindTwo_noRecv A)
  exact
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoBlindRun_blind A
      _
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoFork_blind A
        strategy hwin initial entry) past

end

end DetParityAutomaton

end DistributedSynthesis
