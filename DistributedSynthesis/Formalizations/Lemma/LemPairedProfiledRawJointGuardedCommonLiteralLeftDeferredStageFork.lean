/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralLeftForkCoherence
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredMemberControl

/-!
# The left seam's deferred exact-stage fork

At a locally ambiguous left/common boundary, process one cannot immediately
choose between the ordinary and exact continuations.  The two continuations
therefore retain the false/true member of one literally shared sender table.
The latest exact stage is carried as inert finite payload until a later
receive resolves the member.  A nonreceive advances only the shared table
control and leaves that payload unchanged.

This module proves the concrete arbitrary-depth fact needed by the combined
outer carrier: adding the exact stage payload does not disturb the existing
false/true sender coherence.  It deliberately does not normalize a selected
member to the recurrent kernel; that later map also needs the delivered
partner staged state and belongs to the combined receive adapter.

The Boolean is an unresolved occurrence member stored in the acknowledged
carrier.  No executable map receives a graph, orientation, hierarchy side,
leader bit, history, or view.
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
  ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin package

private abbrev Installed
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :=
  package.literalLeftSeamInstalled A strategy hwin key

private abbrev SenderControl
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :=
  ProfiledRawJointLiteralLeftBothExactSenderState A strategy hwin
    (Installed A strategy hwin package key)

private abbrev Stage
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin package

private abbrev MemberCandidate
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamMemberSenderCandidate A strategy
    hwin package

private abbrev SharedSender
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy hwin
    package

/-! ## Generic shared-member interface -/

/-- Read one proof-side member at a literally shared staged sender state. -/
noncomputable def literalLeftSeamDeferredSharedStep
    (package : Package A strategy hwin initial)
    (member : Bool) (shared : SharedSender A strategy hwin package)
    (input : In₁) : SharedSender A strategy hwin package × Out₁ :=
  let next := package.literalLeftSeamMemberSenderNoRecv A strategy hwin
    (⟨shared.1, member, shared.2⟩ : MemberCandidate A strategy hwin package)
    input
  (package.literalLeftSeamMemberSenderForget A strategy hwin next.1, next.2)

/-- The concrete heterogeneous table supplies exactly the two laws required
by the reusable deferred-member carrier. -/
theorem literalLeftSeamDeferredSharedStepLaws
    (package : Package A strategy hwin initial) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (package.literalLeftSeamDeferredSharedStep A strategy hwin) := by
  refine { outputEq := ?_, stateEq := ?_ }
  · intro shared input
    let falseCandidate : MemberCandidate A strategy hwin package :=
      ⟨shared.1, false, shared.2⟩
    let trueCandidate : MemberCandidate A strategy hwin package :=
      ⟨shared.1, true, shared.2⟩
    have hfalse :=
      (package.literalLeftSeamMemberSenderNoRecv_forget A strategy hwin
        falseCandidate input).2
    have htrue :=
      (package.literalLeftSeamMemberSenderNoRecv_forget A strategy hwin
        trueCandidate input).2
    exact hfalse.trans htrue.symm
  · intro shared input
    let falseCandidate : MemberCandidate A strategy hwin package :=
      ⟨shared.1, false, shared.2⟩
    let trueCandidate : MemberCandidate A strategy hwin package :=
      ⟨shared.1, true, shared.2⟩
    have hfalse :=
      (package.literalLeftSeamMemberSenderNoRecv_forget A strategy hwin
        falseCandidate input).1
    have htrue :=
      (package.literalLeftSeamMemberSenderNoRecv_forget A strategy hwin
        trueCandidate input).1
    exact hfalse.trans htrue.symm

/-! ## Finite pending state -/

/-- A still-unresolved shared sender member together with the latest exact
stage delivered by the informed endpoint.  `none` only totalizes roots before
a live stage has been installed. -/
abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate
    (package : Package A strategy hwin initial) :=
  MemberCandidate A strategy hwin package × Option (Stage A strategy hwin package)

noncomputable instance literalLeftSeamDeferredSenderCandidateFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate A
        strategy hwin package) := by
  classical
  infer_instance

/-- State-first nonreceive.  The exact stage is payload, not an accumulated
history: it is retained literally while the shared table member advances. -/
noncomputable def literalLeftSeamDeferredSenderNoRecv
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate A
        strategy hwin package)
    (input : In₁) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate A
        strategy hwin package × Out₁ :=
  let next := package.literalLeftSeamMemberSenderNoRecv A strategy hwin
    state.1 input
  ((next.1, state.2), next.2)

/-- Projecting a deferred step recovers the member transition, and the latest
stage is retained literally. -/
theorem literalLeftSeamDeferredSenderNoRecv_projection
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate A
        strategy hwin package)
    (input : In₁) :
    (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin state
        input).1.1 =
        (package.literalLeftSeamMemberSenderNoRecv A strategy hwin state.1
          input).1 ∧
      (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin state
        input).1.2 = state.2 ∧
      (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin state
        input).2 =
        (package.literalLeftSeamMemberSenderNoRecv A strategy hwin state.1
          input).2 := by
  simp [literalLeftSeamDeferredSenderNoRecv]

/-- The canonical unresolved false/true pair at one shared table control and
one common exact-stage payload. -/
def literalLeftSeamDeferredSenderFork
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package)) :
    FiniteDelayedFork
      (ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate A
        strategy hwin package) :=
  ⟨(⟨key, false, control⟩, stage), (⟨key, true, control⟩, stage)⟩

@[simp] theorem literalLeftSeamDeferredSenderFork_open
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package)) :
    (package.literalLeftSeamDeferredSenderFork A strategy hwin key control
      stage).openControl = (⟨key, false, control⟩, stage) :=
  rfl

@[simp] theorem literalLeftSeamDeferredSenderFork_closed
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package)) :
    (package.literalLeftSeamDeferredSenderFork A strategy hwin key control
      stage).closedControl = (⟨key, true, control⟩, stage) :=
  rfl

@[simp] theorem literalLeftSeamDeferredSenderFork_open_member
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package)) :
    (package.literalLeftSeamDeferredSenderFork A strategy hwin key control
      stage).openControl.1 =
      (package.literalLeftSeamMemberSenderFork A strategy hwin key control
        ).openControl :=
  rfl

@[simp] theorem literalLeftSeamDeferredSenderFork_closed_member
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package)) :
    (package.literalLeftSeamDeferredSenderFork A strategy hwin key control
      stage).closedControl.1 =
      (package.literalLeftSeamMemberSenderFork A strategy hwin key control
        ).closedControl :=
  rfl

@[simp] theorem literalLeftSeamDeferredSenderFork_open_stage
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package)) :
    (package.literalLeftSeamDeferredSenderFork A strategy hwin key control
      stage).openControl.2 = stage :=
  rfl

@[simp] theorem literalLeftSeamDeferredSenderFork_closed_stage
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package)) :
    (package.literalLeftSeamDeferredSenderFork A strategy hwin key control
      stage).closedControl.2 = stage :=
  rfl

/-! ## Arbitrary blind depth -/

/-- Carrying an identical exact-stage payload preserves the already checked
false/true physical output equality. -/
theorem literalLeftSeamDeferredSenderFork_noRecvOutputCoherent
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package))
    (input : In₁) :
    (package.literalLeftSeamDeferredSenderFork A strategy hwin key control
      stage).NoRecvMealyOutputCoherent
        (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin) input := by
  exact package.literalLeftSeamMemberSenderFork_noRecvOutputCoherent A strategy
    hwin key control input

/-- One blind nonreceive reconstructs the same deferred fork at the shared
next table control, with the exact-stage payload unchanged. -/
theorem literalLeftSeamDeferredSenderFork_noRecvMealy
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package))
    (input : In₁) :
    let table :=
      profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
        hwin (Installed A strategy hwin package key)
    (package.literalLeftSeamDeferredSenderFork A strategy hwin key control
      stage).noRecvMealy
        (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin) input =
      (package.literalLeftSeamDeferredSenderFork A strategy hwin key
          ((table.memberController false).step control input) stage,
        ((table.memberController false).labelOf control).1 input) := by
  dsimp only [literalLeftSeamDeferredSenderFork,
    literalLeftSeamDeferredSenderNoRecv]
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy hwin
      (Installed A strategy hwin package key)
  have hstep :
      (table.memberController false).step control input =
        (table.memberController true).step control input :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable_noRecv_step_eq
      A strategy hwin (Installed A strategy hwin package key) control input
  change
    (FiniteDelayedFork.mk
        (⟨⟨key, false,
            (table.memberController false).step control input⟩, stage⟩ :
          ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate
            A strategy hwin package)
        (⟨⟨key, true,
            (table.memberController true).step control input⟩, stage⟩ :
          ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate
            A strategy hwin package),
      ((table.memberController false).labelOf control).1 input) =
      (FiniteDelayedFork.mk
        (⟨⟨key, false,
            (table.memberController false).step control input⟩, stage⟩ :
          ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate
            A strategy hwin package)
        (⟨⟨key, true,
            (table.memberController false).step control input⟩, stage⟩ :
          ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate
            A strategy hwin package),
      ((table.memberController false).labelOf control).1 input)
  rw [hstep]

/-- Hence the deferred false/true pair remains output-coherent at every
subsequent blind depth. -/
theorem literalLeftSeamDeferredSenderFork_noRecv_preserves_coherent
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package))
    (input nextInput : In₁) :
    ((package.literalLeftSeamDeferredSenderFork A strategy hwin key control
      stage).noRecvMealy
        (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin) input).1
      |>.NoRecvMealyOutputCoherent
        (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin)
        nextInput := by
  rw [package.literalLeftSeamDeferredSenderFork_noRecvMealy A strategy hwin
    key control stage input]
  exact package.literalLeftSeamDeferredSenderFork_noRecvOutputCoherent A
    strategy hwin key _ stage nextInput

/-! ## Fresh re-encapsulation at a new left/`both` seam -/

/-- Re-encapsulate the two *new* left-seam alternatives in one fresh shared
table.  The open and closed interpretations are stored as the false/true
members of one executable sender root; no recurrent/table sum is exposed to
the blind endpoint.

The exact stage starts at `none`.  A later receive refreshes that finite
payload, so repeated hierarchy changes replace the previous stage instead of
accumulating a history. -/
noncomputable def literalLeftSeamFreshDeferredSenderFork
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :
    FiniteDelayedFork
      (ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate A
        strategy hwin package) :=
  package.literalLeftSeamDeferredSenderFork A strategy hwin key
    (package.literalLeftSeamStagedSenderInitial A strategy hwin key).2 none

@[simp] theorem literalLeftSeamFreshDeferredSenderFork_open
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :
    (package.literalLeftSeamFreshDeferredSenderFork A strategy hwin key
      ).openControl =
      ((⟨key, false,
          (package.literalLeftSeamStagedSenderInitial A strategy hwin key).2⟩,
        none) :
        ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate A
          strategy hwin package) :=
  rfl

@[simp] theorem literalLeftSeamFreshDeferredSenderFork_closed
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :
    (package.literalLeftSeamFreshDeferredSenderFork A strategy hwin key
      ).closedControl =
      ((⟨key, true,
          (package.literalLeftSeamStagedSenderInitial A strategy hwin key).2⟩,
        none) :
        ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate A
          strategy hwin package) :=
  rfl

/-- Forgetting the proof-side member yields the identical staged-table sender
root on both branches.  This is the left-side anti-mismatch equation. -/
theorem literalLeftSeamFreshDeferredSenderFork_forget_pair
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :
    (package.literalLeftSeamMemberSenderForget A strategy hwin
        (package.literalLeftSeamFreshDeferredSenderFork A strategy hwin key
          ).openControl.1,
      package.literalLeftSeamMemberSenderForget A strategy hwin
        (package.literalLeftSeamFreshDeferredSenderFork A strategy hwin key
          ).closedControl.1) =
      (package.literalLeftSeamStagedSenderInitial A strategy hwin key,
        package.literalLeftSeamStagedSenderInitial A strategy hwin key) := by
  rfl

/-- The freshly re-encapsulated left fork has one physical blind output. -/
theorem literalLeftSeamFreshDeferredSenderFork_noRecvOutputCoherent
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (input : In₁) :
    (package.literalLeftSeamFreshDeferredSenderFork A strategy hwin key
      ).NoRecvMealyOutputCoherent
        (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin) input := by
  exact package.literalLeftSeamDeferredSenderFork_noRecvOutputCoherent A
    strategy hwin key
      (package.literalLeftSeamStagedSenderInitial A strategy hwin key).2 none
      input

/-- One blind step reconstructs a canonical fresh pending fork at the common
next table control and retains the empty stage. -/
theorem literalLeftSeamFreshDeferredSenderFork_noRecvMealy
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (input : In₁) :
    let table :=
      profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
        hwin (Installed A strategy hwin package key)
    (package.literalLeftSeamFreshDeferredSenderFork A strategy hwin key
      ).noRecvMealy
        (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin) input =
      (package.literalLeftSeamDeferredSenderFork A strategy hwin key
          ((table.memberController false).step
            (package.literalLeftSeamStagedSenderInitial A strategy hwin
              key).2 input) none,
        ((table.memberController false).labelOf
          (package.literalLeftSeamStagedSenderInitial A strategy hwin key).2
          ).1 input) := by
  exact package.literalLeftSeamDeferredSenderFork_noRecvMealy A strategy hwin
    key (package.literalLeftSeamStagedSenderInitial A strategy hwin key).2
      none input

/-- The fresh left pending representation stays coherent at arbitrary blind
depth. -/
theorem literalLeftSeamFreshDeferredSenderFork_noRecv_preserves_coherent
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (input nextInput : In₁) :
    ((package.literalLeftSeamFreshDeferredSenderFork A strategy hwin key
      ).noRecvMealy
        (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin) input).1
      |>.NoRecvMealyOutputCoherent
        (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin)
        nextInput := by
  exact package.literalLeftSeamDeferredSenderFork_noRecv_preserves_coherent A
    strategy hwin key
      (package.literalLeftSeamStagedSenderInitial A strategy hwin key).2 none
      input nextInput

/-! ## Direct acknowledged-relay statements -/

theorem literalLeftSeamDeferredSenderRelay_noRecvOutputCoherent
    (package : Package A strategy hwin initial)
    (id : Fin 5) (ack : Option (Fin 5 × Bool))
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package))
    (input : In₁) :
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
      (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin)
      (⟨.fork id
          (package.literalLeftSeamDeferredSenderFork A strategy hwin key
            control stage), ack⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5)
          (ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate
            A strategy hwin package))
      input :=
  package.literalLeftSeamDeferredSenderFork_noRecvOutputCoherent A strategy
    hwin key control stage input

theorem literalLeftSeamDeferredSenderRelay_noRecv_preserves_coherent
    (package : Package A strategy hwin initial)
    (id : Fin 5) (ack : Option (Fin 5 × Bool))
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (stage : Option (Stage A strategy hwin package))
    (input nextInput : In₁) :
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
      (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin)
      (FiniteAcknowledgedDelayedCarrier.noRecvMealy
        (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin)
        (⟨.fork id
            (package.literalLeftSeamDeferredSenderFork A strategy hwin key
              control stage), ack⟩ :
          FiniteAcknowledgedDelayedCarrier (Fin 5)
            (ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate
              A strategy hwin package)) input).1
      nextInput := by
  exact package.literalLeftSeamDeferredSenderFork_noRecv_preserves_coherent A
    strategy hwin key control stage input nextInput

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
