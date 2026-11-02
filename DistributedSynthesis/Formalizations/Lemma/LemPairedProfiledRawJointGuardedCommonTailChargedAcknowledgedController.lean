/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingBlindForkInvariant
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalSelectedTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailChargedNoRecvBisimulation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailChargedReceiveDispatcher

/-!
# Acknowledged finite controller for the charged common tail

The first charged carrier retained one bare shadow.  That representation is
enough until the next receive, but a blind non-receive has to advance both
honest meanings of the shadow.  The generic five-colour acknowledged carrier
already implements exactly this protocol: it advances one two-candidate fork,
resolves the old fork from delivered finite metadata, and installs one fresh
fork on the current receive.

This file connects the charged common-tail tables to that generic carrier.
An underlying local control stores the common root against which its old
leader-free transition is interpreted.  Receive forks use the charged strict
cross candidates when a represented pending pair is detected; all other
pairs install a duplicate fork around the old core receive.  Consequently a
fresh unresolved fork is always witnessed by one of the finite no-receive
bisimulations.

No executable map accepts a graph, direction, leader bit, history, or view.
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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

private abbrev CommonRoot :=
  ProfiledRawJointGuardedInitialCommonControl A strategy hwin

private abbrev OldOne :=
  ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin initialBank
    (ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin)
    (ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin)

private abbrev OldTwo :=
  ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin initialBank
    (ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin)
    (ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin)

private abbrev RightShadow :=
  ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A strategy hwin

private abbrev LeftShadow :=
  ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy hwin

private abbrev OneBisim :=
  ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
    hwin initialBank

private abbrev TwoBisim :=
  ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
    hwin initialBank

/-- The old local state together with the common root used by its total old
transition map.  The root is finite and is advanced as part of a receive
candidate, so no global or semantic parameter is consulted at runtime. -/
abbrev ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl :=
  CommonRoot A strategy hwin × OldOne A strategy hwin initialBank

abbrev ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl :=
  CommonRoot A strategy hwin × OldTwo A strategy hwin initialBank

private noncomputable def oldKernel (root : CommonRoot A strategy hwin) :=
  profiledRawJointGuardedCommonTailCoreKernel A strategy hwin initialBank root

/-! ## Underlying graph-blind maps -/

noncomputable def
    profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne
    (state :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    (input : In₁) :
    ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank × Out₁ :=
  let next := (oldKernel A strategy hwin initialBank state.1).noRecvOne
    state.2 input
  ((state.1, next.2), next.1)

noncomputable def
    profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo
    (state :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (input : In₂) :
    ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank × Out₂ :=
  let next := (oldKernel A strategy hwin initialBank state.1).noRecvTwo
    state.2 input
  ((state.1, next.2), next.1)

/-- Process one's open receive meaning.  A represented strict/common pair
uses the charged output and the strict meaning of its shadow. -/
noncomputable def
    profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne
    (one :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    (own : In₁)
    (two :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (delivered : In₂) :
    ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank × Out₁ :=
  match profiledRawJointGuardedCommonTailRightPendingOfOldPair? A strategy hwin
      initialBank one.2 two.2 with
  | some pending =>
      let shadow : RightShadow A strategy hwin :=
        ⟨pending, (own, delivered)⟩
      ((pending.receiver.control,
          shadow.oneCandidate A strategy hwin initialBank false),
        (profiledRawJointGuardedCommonTailRightChargedCrossOutput A strategy
          hwin pending (own, delivered)).1)
  | none =>
      match profiledRawJointGuardedCommonTailLeftPendingOfOldPair? A strategy
          hwin initialBank one.2 two.2 with
      | some pending =>
          let shadow : LeftShadow A strategy hwin :=
            ⟨pending, (own, delivered)⟩
          ((pending.receiver.control,
              shadow.oneCandidate A strategy hwin initialBank false),
            (profiledRawJointGuardedCommonTailLeftChargedCrossOutput A strategy
              hwin pending (own, delivered)).1)
      | none =>
          let next := (oldKernel A strategy hwin initialBank one.1).recvOne
            one.2 own two.2 delivered
          ((one.1, next.2), next.1)

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo
    (two :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (own : In₂)
    (one :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    (delivered : In₁) :
    ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank × Out₂ :=
  match profiledRawJointGuardedCommonTailRightPendingOfOldPair? A strategy hwin
      initialBank one.2 two.2 with
  | some pending =>
      let shadow : RightShadow A strategy hwin :=
        ⟨pending, (delivered, own)⟩
      ((pending.receiver.control,
          shadow.twoCandidate A strategy hwin initialBank false),
        (profiledRawJointGuardedCommonTailRightChargedCrossOutput A strategy
          hwin pending (delivered, own)).2)
  | none =>
      match profiledRawJointGuardedCommonTailLeftPendingOfOldPair? A strategy
          hwin initialBank one.2 two.2 with
      | some pending =>
          let shadow : LeftShadow A strategy hwin :=
            ⟨pending, (delivered, own)⟩
          ((pending.receiver.control,
              shadow.twoCandidate A strategy hwin initialBank false),
            (profiledRawJointGuardedCommonTailLeftChargedCrossOutput A strategy
              hwin pending (delivered, own)).2)
      | none =>
          let next := (oldKernel A strategy hwin initialBank two.1).recvTwo
            two.2 own one.2 delivered
          ((two.1, next.2), next.1)

/-- Exact closed meaning for the current receive.  At a charged cross both
coordinates come from the same old-table close; elsewhere this is the
duplicate of the two open core continuations. -/
noncomputable def
    profiledRawJointGuardedCommonTailChargedAcknowledgedClose
    (one :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    (own : In₁)
    (two :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (delivered : In₂) :
    ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank ×
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank :=
  match profiledRawJointGuardedCommonTailRightPendingOfOldPair? A strategy hwin
      initialBank one.2 two.2 with
  | some pending =>
      let shadow : RightShadow A strategy hwin :=
        ⟨pending, (own, delivered)⟩
      ((pending.receiver.control,
          shadow.oneCandidate A strategy hwin initialBank true),
        (pending.receiver.control,
          shadow.twoCandidate A strategy hwin initialBank true))
  | none =>
      match profiledRawJointGuardedCommonTailLeftPendingOfOldPair? A strategy
          hwin initialBank one.2 two.2 with
      | some pending =>
          let shadow : LeftShadow A strategy hwin :=
            ⟨pending, (own, delivered)⟩
          ((pending.receiver.control,
              shadow.oneCandidate A strategy hwin initialBank true),
            (pending.receiver.control,
              shadow.twoCandidate A strategy hwin initialBank true))
      | none =>
          ((profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne A
              strategy hwin initialBank one own two delivered).1,
            (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo A
              strategy hwin initialBank two delivered one own).1)

/-! ## Blind relations generated by finite bisimulation states -/

/-- Two rooted process-one controls are blind-related when they are exactly
the false and true meanings of one finite no-receive bisimulation. -/
def ProfiledRawJointGuardedCommonTailChargedAcknowledgedBlindOne
    (left right :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank) : Prop :=
  ∃ state : OneBisim A strategy hwin initialBank,
    left = (state.root, state.candidate false) ∧
      right = (state.root, state.candidate true)

/-- Process-two mirror. -/
def ProfiledRawJointGuardedCommonTailChargedAcknowledgedBlindTwo
    (left right :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank) : Prop :=
  ∃ state : TwoBisim A strategy hwin initialBank,
    left = (state.root, state.candidate false) ∧
      right = (state.root, state.candidate true)

/-- A duplicate fork always has a process-one bisimulation witness. -/
noncomputable def
    profiledRawJointGuardedCommonTailChargedNoRecvOneBisimulationRefl
    (root : CommonRoot A strategy hwin)
    (control : OldOne A strategy hwin initialBank) :
    OneBisim A strategy hwin initialBank where
  root := root
  candidate := fun _ ↦ control
  compatible :=
    profiledRawJointGuardedCommonTailNoRecvOneCompatible_of_step_eq A strategy
      hwin initialBank (by intro input; rfl)

/-- Duplicate process-two witness. -/
noncomputable def
    profiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulationRefl
    (root : CommonRoot A strategy hwin)
    (control : OldTwo A strategy hwin initialBank) :
    TwoBisim A strategy hwin initialBank where
  root := root
  candidate := fun _ ↦ control
  compatible :=
    profiledRawJointGuardedCommonTailNoRecvTwoCompatible_of_step_eq A strategy
      hwin initialBank (by intro input; rfl)

/-- The finite bisimulation relation supplies exactly the generic blind-step
law for process one. -/
theorem
    profiledRawJointGuardedCommonTailChargedAcknowledgedBlindOne_noRecv
    (left right :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    (input : In₁)
    (hblind :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedBlindOne A strategy
        hwin initialBank left right) :
    (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne A strategy
        hwin initialBank left input).2 =
        (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne A
          strategy hwin initialBank right input).2 ∧
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedBlindOne A strategy
        hwin initialBank
        (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne A
          strategy hwin initialBank left input).1
        (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne A
          strategy hwin initialBank right input).1 := by
  rcases hblind with ⟨state, rfl, rfl⟩
  constructor
  · exact
      (ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation.step_output_eq_candidate
        A strategy hwin initialBank state input false).symm.trans
        (ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation.step_output_eq_candidate
          A strategy hwin initialBank state input true)
  · refine ⟨(state.step A strategy hwin initialBank input).2, ?_, ?_⟩ <;> rfl

/-- Process-two blind-step law. -/
theorem
    profiledRawJointGuardedCommonTailChargedAcknowledgedBlindTwo_noRecv
    (left right :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (input : In₂)
    (hblind :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedBlindTwo A strategy
        hwin initialBank left right) :
    (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo A strategy
        hwin initialBank left input).2 =
        (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo A
          strategy hwin initialBank right input).2 ∧
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedBlindTwo A strategy
        hwin initialBank
        (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo A
          strategy hwin initialBank left input).1
        (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo A
          strategy hwin initialBank right input).1 := by
  rcases hblind with ⟨state, rfl, rfl⟩
  constructor
  · exact
      (ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation.step_output_eq_candidate
        A strategy hwin initialBank state input false).symm.trans
        (ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation.step_output_eq_candidate
          A strategy hwin initialBank state input true)
  · refine ⟨(state.step A strategy hwin initialBank input).2, ?_, ?_⟩ <;> rfl

/-- Both endpoint-local no-receive laws in the generic acknowledged-carrier
format. -/
def profiledRawJointGuardedCommonTailChargedAcknowledgedBlindNoRecvLaws :
    FiniteAcknowledgedDelayedCarrier.BlindNoRecvLaws
      (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne A strategy
        hwin initialBank)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo A strategy
        hwin initialBank)
      (ProfiledRawJointGuardedCommonTailChargedAcknowledgedBlindOne A strategy
        hwin initialBank)
      (ProfiledRawJointGuardedCommonTailChargedAcknowledgedBlindTwo A strategy
        hwin initialBank) where
  one :=
    profiledRawJointGuardedCommonTailChargedAcknowledgedBlindOne_noRecv A
      strategy hwin initialBank
  two :=
    profiledRawJointGuardedCommonTailChargedAcknowledgedBlindTwo_noRecv A
      strategy hwin initialBank

/-! ## Every receive fork has a finite blind witness -/

/-- The process-one bisimulation installed by a receive.  The two hard
overlap laws are used only in their corresponding charged branch; a normal
old-core receive gets the reflexive duplicate witness. -/
noncomputable def
    profiledRawJointGuardedCommonTailChargedAcknowledgedReceiveOneBisimulation
    (realizations :
      ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations A
        strategy hwin initialBank)
    (one :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    (own : In₁)
    (two :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (delivered : In₂) : OneBisim A strategy hwin initialBank :=
  match profiledRawJointGuardedCommonTailRightPendingOfOldPair? A strategy hwin
      initialBank one.2 two.2 with
  | some pending =>
      (realizations.rightBisimulations A strategy hwin initialBank
        (⟨pending, (own, delivered)⟩ : RightShadow A strategy hwin)).1
  | none =>
      match profiledRawJointGuardedCommonTailLeftPendingOfOldPair? A strategy
          hwin initialBank one.2 two.2 with
      | some pending =>
          (realizations.leftBisimulations A strategy hwin initialBank
            (⟨pending, (own, delivered)⟩ : LeftShadow A strategy hwin)).1
      | none =>
          let next := (oldKernel A strategy hwin initialBank one.1).recvOne
            one.2 own two.2 delivered
          profiledRawJointGuardedCommonTailChargedNoRecvOneBisimulationRefl A
            strategy hwin initialBank one.1 next.2

/-- Process-two receive witness. -/
noncomputable def
    profiledRawJointGuardedCommonTailChargedAcknowledgedReceiveTwoBisimulation
    (realizations :
      ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations A
        strategy hwin initialBank)
    (two :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (own : In₂)
    (one :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    (delivered : In₁) : TwoBisim A strategy hwin initialBank :=
  match profiledRawJointGuardedCommonTailRightPendingOfOldPair? A strategy hwin
      initialBank one.2 two.2 with
  | some pending =>
      (realizations.rightBisimulations A strategy hwin initialBank
        (⟨pending, (delivered, own)⟩ : RightShadow A strategy hwin)).2
  | none =>
      match profiledRawJointGuardedCommonTailLeftPendingOfOldPair? A strategy
          hwin initialBank one.2 two.2 with
      | some pending =>
          (realizations.leftBisimulations A strategy hwin initialBank
            (⟨pending, (delivered, own)⟩ : LeftShadow A strategy hwin)).2
      | none =>
          let next := (oldKernel A strategy hwin initialBank two.1).recvTwo
            two.2 own one.2 delivered
          profiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulationRefl A
            strategy hwin initialBank two.1 next.2

theorem
    profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne_eq_witness_false
    (realizations :
      ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations A
        strategy hwin initialBank)
    (one :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    (own : In₁)
    (two :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (delivered : In₂) :
    (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne A strategy
        hwin initialBank one own two delivered).1 =
      let witness :=
        profiledRawJointGuardedCommonTailChargedAcknowledgedReceiveOneBisimulation
          A strategy hwin initialBank realizations one own two delivered
      (witness.root, witness.candidate false) := by
  simp only
    [profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne,
      profiledRawJointGuardedCommonTailChargedAcknowledgedReceiveOneBisimulation]
  split
  · rfl
  · split <;> rfl

theorem
    profiledRawJointGuardedCommonTailChargedAcknowledgedCloseOne_eq_witness_true
    (realizations :
      ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations A
        strategy hwin initialBank)
    (one :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    (own : In₁)
    (two :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (delivered : In₂) :
    (profiledRawJointGuardedCommonTailChargedAcknowledgedClose A strategy hwin
        initialBank one own two delivered).1 =
      let witness :=
        profiledRawJointGuardedCommonTailChargedAcknowledgedReceiveOneBisimulation
          A strategy hwin initialBank realizations one own two delivered
      (witness.root, witness.candidate true) := by
  simp only
    [profiledRawJointGuardedCommonTailChargedAcknowledgedClose,
      profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne,
      profiledRawJointGuardedCommonTailChargedAcknowledgedReceiveOneBisimulation]
  split
  · rfl
  · split <;> rfl

theorem
    profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo_eq_witness_false
    (realizations :
      ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations A
        strategy hwin initialBank)
    (two :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (own : In₂)
    (one :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    (delivered : In₁) :
    (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo A strategy
        hwin initialBank two own one delivered).1 =
      let witness :=
        profiledRawJointGuardedCommonTailChargedAcknowledgedReceiveTwoBisimulation
          A strategy hwin initialBank realizations two own one delivered
      (witness.root, witness.candidate false) := by
  simp only
    [profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo,
      profiledRawJointGuardedCommonTailChargedAcknowledgedReceiveTwoBisimulation]
  split
  · rfl
  · split <;> rfl

theorem
    profiledRawJointGuardedCommonTailChargedAcknowledgedCloseTwo_eq_witness_true
    (realizations :
      ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations A
        strategy hwin initialBank)
    (one :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    (own : In₁)
    (two :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (delivered : In₂) :
    (profiledRawJointGuardedCommonTailChargedAcknowledgedClose A strategy hwin
        initialBank one own two delivered).2 =
      let witness :=
        profiledRawJointGuardedCommonTailChargedAcknowledgedReceiveTwoBisimulation
          A strategy hwin initialBank realizations two delivered one own
      (witness.root, witness.candidate true) := by
  simp only
    [profiledRawJointGuardedCommonTailChargedAcknowledgedClose,
      profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo,
      profiledRawJointGuardedCommonTailChargedAcknowledgedReceiveTwoBisimulation]
  split
  · rfl
  · split <;> rfl

/-! ## Generic exact-closing law bundle and concrete controller -/

/-- Every receive-created open/closed pair is blind-related.  This is the
point at which the two hard overlap realizations enter the operational
controller; all future blind evolution is handled by the finite
bisimulation and the generic acknowledged relay. -/
def profiledRawJointGuardedCommonTailChargedAcknowledgedBlindReceiveLaws
    (realizations :
      ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations A
        strategy hwin initialBank) :
    FiniteAcknowledgedDelayedCarrier.ExactClosingBlindReceiveLaws
      (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne A
        strategy hwin initialBank)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo A
        strategy hwin initialBank)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedClose A strategy
        hwin initialBank)
      (fun _ _ ↦ True)
      (ProfiledRawJointGuardedCommonTailChargedAcknowledgedBlindOne A strategy
        hwin initialBank)
      (ProfiledRawJointGuardedCommonTailChargedAcknowledgedBlindTwo A strategy
        hwin initialBank) where
  one := by
    intro one inputOne two inputTwo _
    let witness :=
      profiledRawJointGuardedCommonTailChargedAcknowledgedReceiveOneBisimulation
        A strategy hwin initialBank realizations one inputOne two inputTwo
    refine ⟨witness, ?_, ?_⟩
    · exact
        profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne_eq_witness_false
          A strategy hwin initialBank realizations one inputOne two inputTwo
    · exact
        profiledRawJointGuardedCommonTailChargedAcknowledgedCloseOne_eq_witness_true
          A strategy hwin initialBank realizations one inputOne two inputTwo
  two := by
    intro one inputOne two inputTwo _
    let witness :=
      profiledRawJointGuardedCommonTailChargedAcknowledgedReceiveTwoBisimulation
        A strategy hwin initialBank realizations two inputTwo one inputOne
    refine ⟨witness, ?_, ?_⟩
    · exact
        profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo_eq_witness_false
          A strategy hwin initialBank realizations two inputTwo one inputOne
    · exact
        profiledRawJointGuardedCommonTailChargedAcknowledgedCloseTwo_eq_witness_true
          A strategy hwin initialBank realizations one inputOne two inputTwo

/-- With the selected-pair relation chosen as `True`, the underlying maps
have the four closure facts required by the generic relational invariant.
The meaningful correctness content is in the blind receive and no-receive
laws above. -/
def profiledRawJointGuardedCommonTailChargedAcknowledgedRelationLaws
    (root : CommonRoot A strategy hwin) :
    FiniteAcknowledgedDelayedCarrier.ExactClosingRelationLaws
      ((root, .initial root) :
        ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A
          strategy hwin initialBank)
      ((root, .initial root) :
        ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A
          strategy hwin initialBank)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne A strategy
        hwin initialBank)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo A strategy
        hwin initialBank)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne A
        strategy hwin initialBank)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo A
        strategy hwin initialBank)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedClose A strategy
        hwin initialBank)
      (fun _ _ ↦ True) where
  initial := trivial
  strictRight := by intros; trivial
  strictLeft := by intros; trivial
  both := by intros; trivial

/-- Complete output-aware law package for the acknowledged charged
controller. -/
def profiledRawJointGuardedCommonTailChargedAcknowledgedBlindForkLaws
    (root : CommonRoot A strategy hwin)
    (realizations :
      ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations A
        strategy hwin initialBank) :
    FiniteAcknowledgedDelayedCarrier.ExactClosingBlindForkLaws
      ((root, .initial root) :
        ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A
          strategy hwin initialBank)
      ((root, .initial root) :
        ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A
          strategy hwin initialBank)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne A strategy
        hwin initialBank)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo A strategy
        hwin initialBank)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne A
        strategy hwin initialBank)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo A
        strategy hwin initialBank)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedClose A strategy
        hwin initialBank)
      (fun _ _ ↦ True)
      (ProfiledRawJointGuardedCommonTailChargedAcknowledgedBlindOne A strategy
        hwin initialBank)
      (ProfiledRawJointGuardedCommonTailChargedAcknowledgedBlindTwo A strategy
        hwin initialBank) where
  relation :=
    profiledRawJointGuardedCommonTailChargedAcknowledgedRelationLaws A strategy
      hwin initialBank root
  noRecv :=
    profiledRawJointGuardedCommonTailChargedAcknowledgedBlindNoRecvLaws A
      strategy hwin initialBank
  receive :=
    profiledRawJointGuardedCommonTailChargedAcknowledgedBlindReceiveLaws A
      strategy hwin initialBank realizations

/-- The actual finite paired Mealy controller.  The five-colour relay is the
only extra executable memory above the rooted old controls. -/
noncomputable def
    profiledRawJointGuardedCommonTailChargedAcknowledgedController
    (root : CommonRoot A strategy hwin) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController
    ((root, .initial root) :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    ((root, .initial root) :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedClose A strategy hwin
      initialBank)

/-! ## Canonical semantic and physical traces -/

/-- The deterministic selected pair below the acknowledgement relays.  It is
the proof-side trace against which charged physical cuts are read. -/
noncomputable def
    profiledRawJointGuardedCommonTailChargedAcknowledgedSemanticTrace
    (root : CommonRoot A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) : Nat →
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
          hwin initialBank ×
        ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A
          strategy hwin initialBank :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
    ((root, .initial root) :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    ((root, .initial root) :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedClose A strategy hwin
      initialBank) env

/-- Process-one output of the canonical charged semantic run. -/
noncomputable def
    profiledRawJointGuardedCommonTailChargedAcknowledgedSemanticOutputOne
    (root : CommonRoot A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) : Nat → Out₁ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputOne
    ((root, .initial root) :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    ((root, .initial root) :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedClose A strategy hwin
      initialBank) env

/-- Process-two output of the canonical charged semantic run. -/
noncomputable def
    profiledRawJointGuardedCommonTailChargedAcknowledgedSemanticOutputTwo
    (root : CommonRoot A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) : Nat → Out₂ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputTwo
    ((root, .initial root) :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    ((root, .initial root) :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedClose A strategy hwin
      initialBank) env

/-- The canonical semantic run supplies all three graph-case preservation and
output equations required by the generic acknowledged trace adapter. -/
noncomputable def
    profiledRawJointGuardedCommonTailChargedAcknowledgedSelectedTraceLaws
    (root : CommonRoot A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :=
  FiniteAcknowledgedDelayedCarrier.exactClosingCanonicalSelectedTraceLaws
    ((root, .initial root) :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A strategy
        hwin initialBank)
    ((root, .initial root) :
      ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A strategy
        hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo A strategy
      hwin initialBank)
    (profiledRawJointGuardedCommonTailChargedAcknowledgedClose A strategy hwin
      initialBank) env (fun _ _ ↦ True)

/-- Output-aware invariant for the actual acknowledged charged Mealy trace.
In particular, unresolved receive forks may survive arbitrary strict runs
without changing either emitted physical output. -/
noncomputable def
    profiledRawJointGuardedCommonTailChargedAcknowledgedMealyTraceInvariant
    (root : CommonRoot A strategy hwin)
    (realizations :
      ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations A
        strategy hwin initialBank)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointGuardedCommonTailChargedAcknowledgedController A strategy
      hwin initialBank root).LiteralCrossMealyTraceInvariant env := by
  exact
    FiniteAcknowledgedDelayedCarrier.ExactClosingSelectedTraceLaws.toMealyTraceInvariant
      (initialOne := ((root, .initial root) :
        ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A
          strategy hwin initialBank))
      (initialTwo := ((root, .initial root) :
        ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A
          strategy hwin initialBank))
      (noRecvOne :=
        profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne A
          strategy hwin initialBank)
      (noRecvTwo :=
        profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo A
          strategy hwin initialBank)
      (openRecvOne :=
        profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne A
          strategy hwin initialBank)
      (openRecvTwo :=
        profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo A
          strategy hwin initialBank)
      (close :=
        profiledRawJointGuardedCommonTailChargedAcknowledgedClose A strategy
          hwin initialBank)
      (Rel := fun _ _ ↦ True)
      (BlindOne :=
        ProfiledRawJointGuardedCommonTailChargedAcknowledgedBlindOne A strategy
          hwin initialBank)
      (BlindTwo :=
        ProfiledRawJointGuardedCommonTailChargedAcknowledgedBlindTwo A strategy
          hwin initialBank)
      (Selected :=
        FiniteAcknowledgedDelayedCarrier.ExactClosingCanonicalSelected
          ((root, .initial root) :
            ProfiledRawJointGuardedCommonTailChargedAcknowledgedOneControl A
              strategy hwin initialBank)
          ((root, .initial root) :
            ProfiledRawJointGuardedCommonTailChargedAcknowledgedTwoControl A
              strategy hwin initialBank)
          (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvOne A
            strategy hwin initialBank)
          (profiledRawJointGuardedCommonTailChargedAcknowledgedNoRecvTwo A
            strategy hwin initialBank)
          (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvOne A
            strategy hwin initialBank)
          (profiledRawJointGuardedCommonTailChargedAcknowledgedOpenRecvTwo A
            strategy hwin initialBank)
          (profiledRawJointGuardedCommonTailChargedAcknowledgedClose A strategy
            hwin initialBank) env)
      (env := env)
      (expectedOutputOne :=
        profiledRawJointGuardedCommonTailChargedAcknowledgedSemanticOutputOne A
          strategy hwin initialBank root env)
      (expectedOutputTwo :=
        profiledRawJointGuardedCommonTailChargedAcknowledgedSemanticOutputTwo A
          strategy hwin initialBank root env)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedBlindForkLaws A
        strategy hwin initialBank root realizations)
      (profiledRawJointGuardedCommonTailChargedAcknowledgedSelectedTraceLaws A
        strategy hwin initialBank root env)

/-- Moore-facing trace invariant for the finite physical controller. -/
noncomputable def
    profiledRawJointGuardedCommonTailChargedAcknowledgedTraceInvariant
    (root : CommonRoot A strategy hwin)
    (realizations :
      ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations A
        strategy hwin initialBank)
    (env : EnvironmentSequence In₁ In₂) :
    ((profiledRawJointGuardedCommonTailChargedAcknowledgedController A
      strategy hwin initialBank root).mooreize
        ).LiteralCrossGraphTraceInvariant env :=
  (profiledRawJointGuardedCommonTailChargedAcknowledgedMealyTraceInvariant A
    strategy hwin initialBank root realizations env).toMooreTraceInvariant _

/-- The physical charged-controller word is exactly its canonical semantic
reference word.  This is the equality consumed by automatic-cut alignment. -/
theorem
    profiledRawJointGuardedCommonTailChargedAcknowledgedTraceWord_eq_referenceWord
    (root : CommonRoot A strategy hwin)
    (realizations :
      ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations A
        strategy hwin initialBank)
    (env : EnvironmentSequence In₁ In₂) :
    let controller :=
      (profiledRawJointGuardedCommonTailChargedAcknowledgedController A
        strategy hwin initialBank root).mooreize
    controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo env =
      (profiledRawJointGuardedCommonTailChargedAcknowledgedTraceInvariant A
        strategy hwin initialBank root realizations env).referenceWord
          controller := by
  dsimp only
  exact
    (profiledRawJointGuardedCommonTailChargedAcknowledgedTraceInvariant A
      strategy hwin initialBank root realizations env
      ).globalMachineTraceWord_eq_referenceWord _

end

end DetParityAutomaton

end DistributedSynthesis
