/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralRightForkCoherence
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredMemberControl

/-!
# The finite pending right-seam fork

At an ambiguous receive the blind endpoint must not prematurely choose between
the open and closed right-seam interpretations.  It retains two finite pieces
of proof-side data instead:

* a member-tagged copy of the one literally shared table sender control; and
* the latest exact finite stage, when one has been delivered.

The stage is replaced, not accumulated.  While no acknowledgement is received,
both candidates advance through the shared table and retain that same stage.
Consequently the arbitrary-depth output coherence proved for the member fork
lifts verbatim to this pending carrier.

The member tag and retained stage are finite controller data.  No transition
below receives a graph, orientation, hierarchy side, leader bit, history, or
view signal.
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

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev Key
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin package

private abbrev Installed
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :=
  package.literalRightSeamInstalled A strategy hwin key

private abbrev SenderControl
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :=
  ProfiledRawJointLiteralRightBothExactSenderState A strategy hwin
    (Installed A strategy hwin package key)

private abbrev Stage
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin package

private abbrev MemberCandidate
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamMemberSenderCandidate A
    strategy hwin package

private abbrev SharedSender
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
    hwin package

/-! ## Generic shared-member interface -/

/-- Read one proof-side member at a literally shared staged sender state. -/
noncomputable def literalRightSeamDeferredSharedStep
    (package : Package A strategy hwin initial)
    (member : Bool) (shared : SharedSender A strategy hwin package)
    (input : In₂) : SharedSender A strategy hwin package × Out₂ :=
  let next := package.literalRightSeamMemberSenderNoRecv A strategy hwin
    (⟨shared.1, member, shared.2⟩ : MemberCandidate A strategy hwin package)
    input
  (package.literalRightSeamMemberSenderForget A strategy hwin next.1, next.2)

/-- The concrete right heterogeneous table instantiates the reusable
deferred-member step laws. -/
theorem literalRightSeamDeferredSharedStepLaws
    (package : Package A strategy hwin initial) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (package.literalRightSeamDeferredSharedStep A strategy hwin) := by
  refine { outputEq := ?_, stateEq := ?_ }
  · intro shared input
    let falseCandidate : MemberCandidate A strategy hwin package :=
      ⟨shared.1, false, shared.2⟩
    let trueCandidate : MemberCandidate A strategy hwin package :=
      ⟨shared.1, true, shared.2⟩
    have hfalse :=
      (package.literalRightSeamMemberSenderNoRecv_forget A strategy hwin
        falseCandidate input).2
    have htrue :=
      (package.literalRightSeamMemberSenderNoRecv_forget A strategy hwin
        trueCandidate input).2
    exact hfalse.trans htrue.symm
  · intro shared input
    let falseCandidate : MemberCandidate A strategy hwin package :=
      ⟨shared.1, false, shared.2⟩
    let trueCandidate : MemberCandidate A strategy hwin package :=
      ⟨shared.1, true, shared.2⟩
    have hfalse :=
      (package.literalRightSeamMemberSenderNoRecv_forget A strategy hwin
        falseCandidate input).1
    have htrue :=
      (package.literalRightSeamMemberSenderNoRecv_forget A strategy hwin
        trueCandidate input).1
    exact hfalse.trans htrue.symm

/-! ## Pending candidates -/

/-- One unresolved table member together with the latest exact stage.  The
stage is package-wide, while the dependent seam key remains inside the member
candidate. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate
    (package : Package A strategy hwin initial) :=
  MemberCandidate A strategy hwin package × Option (Stage A strategy hwin package)

noncomputable instance literalRightSeamPendingSenderCandidateFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate A
        strategy hwin package) := by
  classical
  infer_instance

/-- A blind no-receive advances only the member-tagged shared table control.
The latest exact stage is retained literally. -/
noncomputable def literalRightSeamPendingSenderNoRecv
    (package : Package A strategy hwin initial)
    (candidate :
      ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate A
        strategy hwin package)
    (input : In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate A
        strategy hwin package × Out₂ :=
  let next := package.literalRightSeamMemberSenderNoRecv A strategy hwin
    candidate.1 input
  ((next.1, candidate.2), next.2)

/-- Projecting a pending no-receive recovers the member transition, while the
retained stage is unchanged. -/
theorem literalRightSeamPendingSenderNoRecv_projection
    (package : Package A strategy hwin initial)
    (candidate :
      ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate A
        strategy hwin package)
    (input : In₂) :
    (package.literalRightSeamPendingSenderNoRecv A strategy hwin candidate
        input).1.1 =
        (package.literalRightSeamMemberSenderNoRecv A strategy hwin
          candidate.1 input).1 ∧
      (package.literalRightSeamPendingSenderNoRecv A strategy hwin candidate
        input).1.2 = candidate.2 ∧
      (package.literalRightSeamPendingSenderNoRecv A strategy hwin candidate
        input).2 =
        (package.literalRightSeamMemberSenderNoRecv A strategy hwin
          candidate.1 input).2 := by
  simp [literalRightSeamPendingSenderNoRecv]

/-! ## Canonical pending fork -/

/-- The unresolved false/true table members at one shared sender control and
one shared latest stage. -/
def literalRightSeamPendingSenderFork
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package)) :
    FiniteDelayedFork
      (ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate A
        strategy hwin package) :=
  ⟨(⟨key, false, control⟩, stage), (⟨key, true, control⟩, stage)⟩

/-- Forgetting the retained stage gives exactly the underlying member fork. -/
@[simp] theorem literalRightSeamPendingSenderFork_open_member
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package)) :
    (package.literalRightSeamPendingSenderFork A strategy hwin key control
      stage).openControl.1 =
      (package.literalRightSeamMemberSenderFork A strategy hwin key control
        ).openControl := rfl

@[simp] theorem literalRightSeamPendingSenderFork_closed_member
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package)) :
    (package.literalRightSeamPendingSenderFork A strategy hwin key control
      stage).closedControl.1 =
      (package.literalRightSeamMemberSenderFork A strategy hwin key control
        ).closedControl := rfl

@[simp] theorem literalRightSeamPendingSenderFork_open_stage
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package)) :
    (package.literalRightSeamPendingSenderFork A strategy hwin key control
      stage).openControl.2 = stage := rfl

@[simp] theorem literalRightSeamPendingSenderFork_closed_stage
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package)) :
    (package.literalRightSeamPendingSenderFork A strategy hwin key control
      stage).closedControl.2 = stage := rfl

/-- The pending fork has one physical blind output for every private input. -/
theorem literalRightSeamPendingSenderFork_noRecvOutputCoherent
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package))
    (input : In₂) :
    (package.literalRightSeamPendingSenderFork A strategy hwin key control
      stage).NoRecvMealyOutputCoherent
        (package.literalRightSeamPendingSenderNoRecv A strategy hwin) input := by
  exact package.literalRightSeamMemberSenderFork_noRecvOutputCoherent A
    strategy hwin key control input

/-- One blind step replaces the shared table control and retains one stage;
it does not accumulate another layer of fork data. -/
theorem literalRightSeamPendingSenderFork_noRecvMealy
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package))
    (input : In₂) :
    let table :=
      profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
        hwin (Installed A strategy hwin package key)
    (package.literalRightSeamPendingSenderFork A strategy hwin key control
      stage).noRecvMealy
        (package.literalRightSeamPendingSenderNoRecv A strategy hwin) input =
      (package.literalRightSeamPendingSenderFork A strategy hwin key
          ((table.memberController false).step control input) stage,
        ((table.memberController false).labelOf control).1 input) := by
  dsimp only
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      (Installed A strategy hwin package key)
  have hstep :
      (table.memberController false).step control input =
        (table.memberController true).step control input :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable_noRecv_step_eq
      A strategy hwin (Installed A strategy hwin package key) control input
  change
    (FiniteDelayedFork.mk
        ((⟨key, false, (table.memberController false).step control input⟩ :
          MemberCandidate A strategy hwin package), stage)
        ((⟨key, true, (table.memberController true).step control input⟩ :
          MemberCandidate A strategy hwin package), stage),
      ((table.memberController false).labelOf control).1 input) =
      (FiniteDelayedFork.mk
        ((⟨key, false, (table.memberController false).step control input⟩ :
          MemberCandidate A strategy hwin package), stage)
        ((⟨key, true, (table.memberController false).step control input⟩ :
          MemberCandidate A strategy hwin package), stage),
      ((table.memberController false).labelOf control).1 input)
  rw [hstep]

/-- After any number of unresolved blind steps, the next blind output remains
independent of which proof-side member will eventually be acknowledged. -/
theorem literalRightSeamPendingSenderFork_noRecv_preserves_coherent
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package))
    (input nextInput : In₂) :
    ((package.literalRightSeamPendingSenderFork A strategy hwin key control
      stage).noRecvMealy
        (package.literalRightSeamPendingSenderNoRecv A strategy hwin) input).1
      |>.NoRecvMealyOutputCoherent
        (package.literalRightSeamPendingSenderNoRecv A strategy hwin)
        nextInput := by
  rw [package.literalRightSeamPendingSenderFork_noRecvMealy A strategy hwin key
    control stage input]
  exact package.literalRightSeamPendingSenderFork_noRecvOutputCoherent A
    strategy hwin key _ stage nextInput

/-! ## Fresh re-encapsulation at a new right/`both` seam -/

/-- Re-encapsulate the two *new* seam alternatives in one fresh shared table.
The open member is the literal restart (`false`) and the closed member is the
fresh recurrent reading (`true`).  Both are stored at the same executable
sender root.  No raw recurrent/table sum is returned here.

The stage starts at `none`: it is refreshed by the informed endpoint on the
first opposite-direction receive and later delivered back at the reversal. -/
noncomputable def literalRightSeamFreshPendingSenderFork
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :
    FiniteDelayedFork
      (ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate A
        strategy hwin package) :=
  package.literalRightSeamPendingSenderFork A strategy hwin key
    (package.literalRightSeamStagedSenderInitial A strategy hwin key).2 none

/-- The new open alternative is exactly the false table member. -/
@[simp] theorem literalRightSeamFreshPendingSenderFork_open
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :
    (package.literalRightSeamFreshPendingSenderFork A strategy hwin key
      ).openControl =
      ((⟨key, false,
          (package.literalRightSeamStagedSenderInitial A strategy hwin key).2⟩,
        none) :
        ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate A
          strategy hwin package) :=
  rfl

/-- The new closed alternative is the true table member at literally the same
sender root, not a raw recurrent control. -/
@[simp] theorem literalRightSeamFreshPendingSenderFork_closed
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :
    (package.literalRightSeamFreshPendingSenderFork A strategy hwin key
      ).closedControl =
      ((⟨key, true,
          (package.literalRightSeamStagedSenderInitial A strategy hwin key).2⟩,
        none) :
        ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate A
          strategy hwin package) :=
  rfl

/-- After forgetting the proof-side member, both new alternatives are the one
executable staged-table sender root.  This is the concrete anti-mismatch
equation: the fork never pairs a recurrent control with a table control. -/
theorem literalRightSeamFreshPendingSenderFork_forget_pair
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :
    (package.literalRightSeamMemberSenderForget A strategy hwin
        (package.literalRightSeamFreshPendingSenderFork A strategy hwin key
          ).openControl.1,
      package.literalRightSeamMemberSenderForget A strategy hwin
        (package.literalRightSeamFreshPendingSenderFork A strategy hwin key
          ).closedControl.1) =
      (package.literalRightSeamStagedSenderInitial A strategy hwin key,
        package.literalRightSeamStagedSenderInitial A strategy hwin key) := by
  rfl

/-- The freshly re-encapsulated fork is blind-output coherent immediately. -/
theorem literalRightSeamFreshPendingSenderFork_noRecvOutputCoherent
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (input : In₂) :
    (package.literalRightSeamFreshPendingSenderFork A strategy hwin key
      ).NoRecvMealyOutputCoherent
        (package.literalRightSeamPendingSenderNoRecv A strategy hwin) input := by
  exact package.literalRightSeamPendingSenderFork_noRecvOutputCoherent A
    strategy hwin key
      (package.literalRightSeamStagedSenderInitial A strategy hwin key).2 none
      input

/-- One blind round after fresh re-encapsulation is again one canonical
pending table fork, at the shared next table control and still with no stage. -/
theorem literalRightSeamFreshPendingSenderFork_noRecvMealy
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (input : In₂) :
    let table :=
      profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
        hwin (Installed A strategy hwin package key)
    (package.literalRightSeamFreshPendingSenderFork A strategy hwin key
      ).noRecvMealy
        (package.literalRightSeamPendingSenderNoRecv A strategy hwin) input =
      (package.literalRightSeamPendingSenderFork A strategy hwin key
          ((table.memberController false).step
            (package.literalRightSeamStagedSenderInitial A strategy hwin
              key).2 input) none,
        ((table.memberController false).labelOf
          (package.literalRightSeamStagedSenderInitial A strategy hwin key).2
          ).1 input) := by
  exact package.literalRightSeamPendingSenderFork_noRecvMealy A strategy hwin
    key (package.literalRightSeamStagedSenderInitial A strategy hwin key).2
      none input

/-- The fresh pending representation stays coherent at arbitrary blind depth. -/
theorem literalRightSeamFreshPendingSenderFork_noRecv_preserves_coherent
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (input nextInput : In₂) :
    ((package.literalRightSeamFreshPendingSenderFork A strategy hwin key
      ).noRecvMealy
        (package.literalRightSeamPendingSenderNoRecv A strategy hwin) input).1
      |>.NoRecvMealyOutputCoherent
        (package.literalRightSeamPendingSenderNoRecv A strategy hwin)
        nextInput := by
  exact package.literalRightSeamPendingSenderFork_noRecv_preserves_coherent A
    strategy hwin key
      (package.literalRightSeamStagedSenderInitial A strategy hwin key).2 none
      input nextInput

/-! ## Direct acknowledged-relay statements -/

theorem literalRightSeamPendingSenderRelay_noRecvOutputCoherent
    (package : Package A strategy hwin initial)
    (id : Fin 5) (ack : Option (Fin 5 × Bool))
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package))
    (input : In₂) :
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
      (package.literalRightSeamPendingSenderNoRecv A strategy hwin)
      (⟨.fork id
          (package.literalRightSeamPendingSenderFork A strategy hwin key
            control stage), ack⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5)
          (ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate
            A strategy hwin package))
      input :=
  package.literalRightSeamPendingSenderFork_noRecvOutputCoherent A strategy hwin
    key control stage input

theorem literalRightSeamPendingSenderRelay_noRecv_preserves_coherent
    (package : Package A strategy hwin initial)
    (id : Fin 5) (ack : Option (Fin 5 × Bool))
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package))
    (input nextInput : In₂) :
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
      (package.literalRightSeamPendingSenderNoRecv A strategy hwin)
      (FiniteAcknowledgedDelayedCarrier.noRecvMealy
        (package.literalRightSeamPendingSenderNoRecv A strategy hwin)
        (⟨.fork id
            (package.literalRightSeamPendingSenderFork A strategy hwin key
              control stage), ack⟩ :
          FiniteAcknowledgedDelayedCarrier (Fin 5)
            (ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate
              A strategy hwin package)) input).1
      nextInput := by
  exact package.literalRightSeamPendingSenderFork_noRecv_preserves_coherent A
    strategy hwin key control stage input nextInput

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
