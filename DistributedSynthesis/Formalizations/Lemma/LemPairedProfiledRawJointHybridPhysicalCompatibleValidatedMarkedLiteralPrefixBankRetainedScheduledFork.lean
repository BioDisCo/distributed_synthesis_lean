/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOperationalCloseMemberSchedule
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankRetainedActivePending

/-!
# Scheduled selection from child-restart forks

The lemmas concern forks whose two members are already child restarts.
Branchwise blind iteration preserves their installed child and bank tag,
and selection by a proof-side schedule recovers the corresponding member.
This construction applies at restart boundaries. Interior strict receives
instead retain the advanced parent occurrence.

`OperationalCloseMemberSchedule.closeMember k` is proof-side data derived from
the physical graph word.  It is never passed to a process.  This file proves
that selecting that member from a locally stored open/closed restart fork is
an honest installation of the fork's one exact marked-bank child.

The fork members may use different finite entry anchors, but they share their
child `BankControl`.  Hence they have the same live sender, emit the same blind
outputs, and remain blind-related through an arbitrary list of open-round
inputs.  It must not be used as the receive adapter for the pre-narrowed
parent-linked child payload.
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

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev OneStage :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage A
    strategy hwin

private abbrev TwoStage :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage A
    strategy hwin

/-! ## Arbitrary blind-block iteration -/

/-- Run one concrete process-one stage through a list of blind inputs. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecvRun
    (blindPhase : Bool) :
    OneStage A strategy hwin → List In₁ → OneStage A strategy hwin
  | state, [] => state
  | state, input :: inputs =>
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecvRun
        blindPhase
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecv
          A strategy hwin blindPhase state input).1 inputs

/-- Process-two concrete blind run. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecvRun
    (blindPhase : Bool) :
    TwoStage A strategy hwin → List In₂ → TwoStage A strategy hwin
  | state, [] => state
  | state, input :: inputs =>
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecvRun
        blindPhase
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecv
          A strategy hwin blindPhase state input).1 inputs

/-- Advance both interpretations of a process-one ambiguity through one
whole blind block. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneForkNoRecvRun
    (blindPhase : Bool) :
    FiniteDelayedFork (OneStage A strategy hwin) → List In₁ →
      FiniteDelayedFork (OneStage A strategy hwin)
  | fork, [] => fork
  | fork, input :: inputs =>
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneForkNoRecvRun
        blindPhase
        (fork.noRecvMealy
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecv
            A strategy hwin blindPhase) input).1 inputs

/-- Process-two ambiguity run. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoForkNoRecvRun
    (blindPhase : Bool) :
    FiniteDelayedFork (TwoStage A strategy hwin) → List In₂ →
      FiniteDelayedFork (TwoStage A strategy hwin)
  | fork, [] => fork
  | fork, input :: inputs =>
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoForkNoRecvRun
        blindPhase
        (fork.noRecvMealy
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecv
            A strategy hwin blindPhase) input).1 inputs

/-- Branchwise fork execution is exactly ordinary execution of the selected
honest stage. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneForkNoRecvRun_candidate
    (blindPhase : Bool) (fork : FiniteDelayedFork (OneStage A strategy hwin))
    (inputs : List In₁) (member : Bool) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneForkNoRecvRun
        A strategy hwin blindPhase fork inputs).candidate member =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecvRun
        A strategy hwin blindPhase (fork.candidate member) inputs := by
  induction inputs generalizing fork with
  | nil => rfl
  | cons input inputs ih =>
      simp only
        [profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneForkNoRecvRun,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecvRun]
      rw [ih]
      rw [FiniteDelayedFork.noRecvMealy_candidate]
      rfl

/-- Process-two branchwise execution. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoForkNoRecvRun_candidate
    (blindPhase : Bool) (fork : FiniteDelayedFork (TwoStage A strategy hwin))
    (inputs : List In₂) (member : Bool) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoForkNoRecvRun
        A strategy hwin blindPhase fork inputs).candidate member =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecvRun
        A strategy hwin blindPhase (fork.candidate member) inputs := by
  induction inputs generalizing fork with
  | nil => rfl
  | cons input inputs ih =>
      simp only
        [profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoForkNoRecvRun,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecvRun]
      rw [ih]
      rw [FiniteDelayedFork.noRecvMealy_candidate]
      rfl

/-- A blind block does not change the installed process-one bank tag. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecvRun_activeTag
    (blindPhase : Bool) (state : OneStage A strategy hwin)
    (inputs : List In₁) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecvRun
        A strategy hwin blindPhase state inputs).activeTag A strategy hwin =
      state.activeTag A strategy hwin := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input inputs ih =>
      simp only
        [profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecvRun]
      rw [ih]
      rfl

/-- Process-two tag retention. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecvRun_activeTag
    (blindPhase : Bool) (state : TwoStage A strategy hwin)
    (inputs : List In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecvRun
        A strategy hwin blindPhase state inputs).activeTag A strategy hwin =
      state.activeTag A strategy hwin := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input inputs ih =>
      simp only
        [profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecvRun]
      rw [ih]
      rfl

/-- One-step blind preservation iterates over an arbitrary process-one open
block. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartForkBlind.noRecvRun
    (blindPhase : Bool) (fork : FiniteDelayedFork (OneStage A strategy hwin))
    (hblind :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartForkBlind
        A strategy hwin fork)
    (inputs : List In₁) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartForkBlind
      A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneForkNoRecvRun
        A strategy hwin blindPhase fork inputs) := by
  induction inputs generalizing fork with
  | nil => exact hblind
  | cons input inputs ih =>
      apply ih
      exact
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartForkBlind.noRecv
          A strategy hwin blindPhase fork hblind input

/-- Process-two arbitrary blind-block preservation. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartForkBlind.noRecvRun
    (blindPhase : Bool) (fork : FiniteDelayedFork (TwoStage A strategy hwin))
    (hblind :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartForkBlind
        A strategy hwin fork)
    (inputs : List In₂) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartForkBlind
      A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoForkNoRecvRun
        A strategy hwin blindPhase fork inputs) := by
  induction inputs generalizing fork with
  | nil => exact hblind
  | cons input inputs ih =>
      apply ih
      exact
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartForkBlind.noRecv
          A strategy hwin blindPhase fork hblind input

/-! ## Proof-side scheduled member -/

/-- Choose the finite entry anchors corresponding to an already stored
open/closed member. -/
def profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedAnchorsForMember
    (openAnchors closedAnchors : Bool × Bool) (member : Bool) : Bool × Bool :=
  if member then closedAnchors else openAnchors

/-- The schedule-selected process-one member is literally the canonical
restart at the exact child and the selected anchors.  The schedule is used
only in this proof-side observation. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartFork_scheduledCandidate
    {graphs : Nat → Graph} (schedule : OperationalCloseMemberSchedule graphs)
    (k : Nat) (child : BankControl A strategy hwin)
    (openAnchors closedAnchors : Bool × Bool) (phase : Bool) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartFork
        A strategy hwin (child, openAnchors) (child, closedAnchors) phase
      ).candidate (schedule.closeMember k) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageInitial
        A strategy hwin
        (child,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedAnchorsForMember
            openAnchors closedAnchors (schedule.closeMember k)) phase := by
  cases hmember : schedule.closeMember k <;> rfl

/-- Process-two scheduled member. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartFork_scheduledCandidate
    {graphs : Nat → Graph} (schedule : OperationalCloseMemberSchedule graphs)
    (k : Nat) (child : BankControl A strategy hwin)
    (openAnchors closedAnchors : Bool × Bool) (phase : Bool) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartFork
        A strategy hwin (child, openAnchors) (child, closedAnchors) phase
      ).candidate (schedule.closeMember k) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageInitial
        A strategy hwin
        (child,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedAnchorsForMember
            openAnchors closedAnchors (schedule.closeMember k)) phase := by
  cases hmember : schedule.closeMember k <;> rfl

/-- After any process-one open block, the schedule-selected branch still
carries exactly the child installed at the close. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartFork_scheduledCandidate_child_after_noRecvRun
    {graphs : Nat → Graph} (schedule : OperationalCloseMemberSchedule graphs)
    (k : Nat) (child : BankControl A strategy hwin)
    (openAnchors closedAnchors : Bool × Bool) (phase blindPhase : Bool)
    (inputs : List In₁) :
    (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.activeTag
      A strategy hwin
      ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneForkNoRecvRun
            A strategy hwin blindPhase
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartFork
              A strategy hwin (child, openAnchors) (child, closedAnchors) phase)
            inputs).candidate (schedule.closeMember k))).1 = child := by
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneForkNoRecvRun_candidate]
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecvRun_activeTag]
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartFork_scheduledCandidate]
  rfl

/-- Process-two scheduled child retention. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartFork_scheduledCandidate_child_after_noRecvRun
    {graphs : Nat → Graph} (schedule : OperationalCloseMemberSchedule graphs)
    (k : Nat) (child : BankControl A strategy hwin)
    (openAnchors closedAnchors : Bool × Bool) (phase blindPhase : Bool)
    (inputs : List In₂) :
    (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.activeTag
      A strategy hwin
      ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoForkNoRecvRun
            A strategy hwin blindPhase
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartFork
              A strategy hwin (child, openAnchors) (child, closedAnchors) phase)
            inputs).candidate (schedule.closeMember k))).1 = child := by
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoForkNoRecvRun_candidate]
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecvRun_activeTag]
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartFork_scheduledCandidate]
  rfl

/-- Same-child process-one forks remain blind-coherent through every list of
open-round inputs, independently of the proof-side scheduled member. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartFork_scheduled_blind_after_noRecvRun
    {graphs : Nat → Graph} (_schedule : OperationalCloseMemberSchedule graphs)
    (_k : Nat) (child : BankControl A strategy hwin)
    (openAnchors closedAnchors : Bool × Bool) (phase blindPhase : Bool)
    (inputs : List In₁) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartForkBlind
      A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneForkNoRecvRun
        A strategy hwin blindPhase
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartFork
          A strategy hwin (child, openAnchors) (child, closedAnchors) phase)
        inputs) := by
  apply
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartForkBlind.noRecvRun
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartFork_blind_of_same_child
      A strategy hwin child openAnchors closedAnchors phase

/-- Process-two scheduled blind-block theorem. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartFork_scheduled_blind_after_noRecvRun
    {graphs : Nat → Graph} (_schedule : OperationalCloseMemberSchedule graphs)
    (_k : Nat) (child : BankControl A strategy hwin)
    (openAnchors closedAnchors : Bool × Bool) (phase blindPhase : Bool)
    (inputs : List In₂) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartForkBlind
      A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoForkNoRecvRun
        A strategy hwin blindPhase
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartFork
          A strategy hwin (child, openAnchors) (child, closedAnchors) phase)
        inputs) := by
  apply
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartForkBlind.noRecvRun
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartFork_blind_of_same_child
      A strategy hwin child openAnchors closedAnchors phase

end

end DetParityAutomaton

end DistributedSynthesis
