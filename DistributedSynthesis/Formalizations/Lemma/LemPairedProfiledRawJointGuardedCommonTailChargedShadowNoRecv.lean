/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailChargedReceiveResolution

/-!
# Non-receive from a charged cross shadow

A charged shadow has two honest ordinary interpretations.  Before choosing a
smaller replacement carrier, this module exposes the exact graph-blind test:
run the ordinary local non-receive dispatcher on both interpretations.  The
result is finite and depends only on the stored shadow and the current own
input.  In particular no graph, orientation, leader bit, or semantic history
is an argument of these maps.
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

private noncomputable def profiledRawJointGuardedCommonTailOldKernel
    (root : ProfiledRawJointGuardedInitialCommonControl A strategy hwin) :=
  profiledRawJointGuardedCommonTailCoreKernel A strategy hwin initialBank root

/-! ## The finite two-interpretation transition tables -/

/-- Both honest process-one results after a right charged shadow observes a
non-receive.  The Boolean coordinate is the old one-way/simultaneous bit. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.noRecvOneTable
    (state : RightShadow A strategy hwin) (input : In₁) :
    Bool → Out₁ × OldOne A strategy hwin initialBank :=
  fun closed ↦
    (profiledRawJointGuardedCommonTailOldKernel A strategy hwin initialBank
      state.pending.receiver.control).noRecvOne
      (state.oneCandidate A strategy hwin initialBank closed) input

/-- Process-two mirror for a right charged shadow. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.noRecvTwoTable
    (state : RightShadow A strategy hwin) (input : In₂) :
    Bool → Out₂ × OldTwo A strategy hwin initialBank :=
  fun closed ↦
    (profiledRawJointGuardedCommonTailOldKernel A strategy hwin initialBank
      state.pending.receiver.control).noRecvTwo
      (state.twoCandidate A strategy hwin initialBank closed) input

/-- Strict-left process-one mirror. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.noRecvOneTable
    (state : LeftShadow A strategy hwin) (input : In₁) :
    Bool → Out₁ × OldOne A strategy hwin initialBank :=
  fun closed ↦
    (profiledRawJointGuardedCommonTailOldKernel A strategy hwin initialBank
      state.pending.receiver.control).noRecvOne
      (state.oneCandidate A strategy hwin initialBank closed) input

/-- Strict-left process-two mirror. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.noRecvTwoTable
    (state : LeftShadow A strategy hwin) (input : In₂) :
    Bool → Out₂ × OldTwo A strategy hwin initialBank :=
  fun closed ↦
    (profiledRawJointGuardedCommonTailOldKernel A strategy hwin initialBank
      state.pending.receiver.control).noRecvTwo
      (state.twoCandidate A strategy hwin initialBank closed) input

/-! ## Endpoint normal forms -/

@[simp] theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.noRecvOneTable_false
    (state : RightShadow A strategy hwin) (input : In₁) :
    state.noRecvOneTable A strategy hwin initialBank input false =
      (profiledRawJointGuardedCommonTailOldKernel A strategy hwin initialBank
        state.pending.receiver.control).noRecvOne
        (state.oneCandidate A strategy hwin initialBank false) input :=
  rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.noRecvOneTable_true
    (state : RightShadow A strategy hwin) (input : In₁) :
    state.noRecvOneTable A strategy hwin initialBank input true =
      (profiledRawJointGuardedCommonTailOldKernel A strategy hwin initialBank
        state.pending.receiver.control).noRecvOne
        (state.oneCandidate A strategy hwin initialBank true) input :=
  rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.noRecvTwoTable_false
    (state : RightShadow A strategy hwin) (input : In₂) :
    state.noRecvTwoTable A strategy hwin initialBank input false =
      (profiledRawJointGuardedCommonTailOldKernel A strategy hwin initialBank
        state.pending.receiver.control).noRecvTwo
        (state.twoCandidate A strategy hwin initialBank false) input :=
  rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.noRecvTwoTable_true
    (state : RightShadow A strategy hwin) (input : In₂) :
    state.noRecvTwoTable A strategy hwin initialBank input true =
      (profiledRawJointGuardedCommonTailOldKernel A strategy hwin initialBank
        state.pending.receiver.control).noRecvTwo
        (state.twoCandidate A strategy hwin initialBank true) input :=
  rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.noRecvOneTable_false
    (state : LeftShadow A strategy hwin) (input : In₁) :
    state.noRecvOneTable A strategy hwin initialBank input false =
      (profiledRawJointGuardedCommonTailOldKernel A strategy hwin initialBank
        state.pending.receiver.control).noRecvOne
        (state.oneCandidate A strategy hwin initialBank false) input :=
  rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.noRecvOneTable_true
    (state : LeftShadow A strategy hwin) (input : In₁) :
    state.noRecvOneTable A strategy hwin initialBank input true =
      (profiledRawJointGuardedCommonTailOldKernel A strategy hwin initialBank
        state.pending.receiver.control).noRecvOne
        (state.oneCandidate A strategy hwin initialBank true) input :=
  rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.noRecvTwoTable_false
    (state : LeftShadow A strategy hwin) (input : In₂) :
    state.noRecvTwoTable A strategy hwin initialBank input false =
      (profiledRawJointGuardedCommonTailOldKernel A strategy hwin initialBank
        state.pending.receiver.control).noRecvTwo
        (state.twoCandidate A strategy hwin initialBank false) input :=
  rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.noRecvTwoTable_true
    (state : LeftShadow A strategy hwin) (input : In₂) :
    state.noRecvTwoTable A strategy hwin initialBank input true =
      (profiledRawJointGuardedCommonTailOldKernel A strategy hwin initialBank
        state.pending.receiver.control).noRecvTwo
        (state.twoCandidate A strategy hwin initialBank true) input :=
  rfl

/-! ## Finite deferred forks for the two non-definitional coordinates -/

/-- A process-one charged ambiguity after one or more non-receives.  The two
ordinary controls are the correlated one-way and simultaneous
interpretations.  Repeated local non-receives update these two finite values;
no input history is accumulated. -/
structure ProfiledRawJointGuardedCommonTailChargedOneFork where
  root : ProfiledRawJointGuardedInitialCommonControl A strategy hwin
  openControl : OldOne A strategy hwin initialBank
  closedControl : OldOne A strategy hwin initialBank

/-- Process-two mirror. -/
structure ProfiledRawJointGuardedCommonTailChargedTwoFork where
  root : ProfiledRawJointGuardedInitialCommonControl A strategy hwin
  openControl : OldTwo A strategy hwin initialBank
  closedControl : OldTwo A strategy hwin initialBank

noncomputable instance
    profiledRawJointGuardedCommonTailChargedOneForkFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTailChargedOneFork A strategy hwin
        initialBank) := by
  classical
  let Rep := ProfiledRawJointGuardedInitialCommonControl A strategy hwin ×
    OldOne A strategy hwin initialBank ×
      OldOne A strategy hwin initialBank
  let equiv :
      ProfiledRawJointGuardedCommonTailChargedOneFork A strategy hwin
          initialBank ≃ Rep :=
    { toFun := fun state ↦
        (state.root, state.openControl, state.closedControl)
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by
        intro state
        rcases state with ⟨root, openState, closedState⟩
        rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointGuardedCommonTailChargedTwoForkFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTailChargedTwoFork A strategy hwin
        initialBank) := by
  classical
  let Rep := ProfiledRawJointGuardedInitialCommonControl A strategy hwin ×
    OldTwo A strategy hwin initialBank ×
      OldTwo A strategy hwin initialBank
  let equiv :
      ProfiledRawJointGuardedCommonTailChargedTwoFork A strategy hwin
          initialBank ≃ Rep :=
    { toFun := fun state ↦
        (state.root, state.openControl, state.closedControl)
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by
        intro state
        rcases state with ⟨root, openState, closedState⟩
        rfl }
  exact Fintype.ofEquiv Rep equiv.symm

namespace ProfiledRawJointGuardedCommonTailChargedOneFork

noncomputable def candidate
    (state : ProfiledRawJointGuardedCommonTailChargedOneFork A strategy hwin
      initialBank) (closed : Bool) : OldOne A strategy hwin initialBank :=
  if closed then state.closedControl else state.openControl

/-- The branchwise result of the next graph-blind local non-receive. -/
noncomputable def noRecvTable
    (state : ProfiledRawJointGuardedCommonTailChargedOneFork A strategy hwin
      initialBank) (input : In₁) (closed : Bool) :
    Out₁ × OldOne A strategy hwin initialBank :=
  (profiledRawJointGuardedCommonTailOldKernel A strategy hwin initialBank
    state.root).noRecvOne
    (state.candidate A strategy hwin initialBank closed) input

/-- Output uniformity is the exact semantic invariant needed to execute the
fork.  It is stated only on the two finite branch results. -/
def NoRecvOutputCoherent
    (state : ProfiledRawJointGuardedCommonTailChargedOneFork A strategy hwin
      initialBank) (input : In₁) : Prop :=
  (state.noRecvTable A strategy hwin initialBank input false).1 =
    (state.noRecvTable A strategy hwin initialBank input true).1

/-- Update both candidates and emit the open candidate's output.  Under the
reachable coherence invariant the emitted value is also the closed
candidate's value. -/
noncomputable def noRecv
    (state : ProfiledRawJointGuardedCommonTailChargedOneFork A strategy hwin
      initialBank) (input : In₁) :
    Out₁ ×
      ProfiledRawJointGuardedCommonTailChargedOneFork A strategy hwin
        initialBank :=
  let openResult := state.noRecvTable A strategy hwin initialBank input false
  let closedResult := state.noRecvTable A strategy hwin initialBank input true
  (openResult.1, ⟨state.root, openResult.2, closedResult.2⟩)

@[simp] theorem candidate_false
    (state : ProfiledRawJointGuardedCommonTailChargedOneFork A strategy hwin
      initialBank) :
    state.candidate A strategy hwin initialBank false = state.openControl := by
  simp [candidate]

@[simp] theorem candidate_true
    (state : ProfiledRawJointGuardedCommonTailChargedOneFork A strategy hwin
      initialBank) :
    state.candidate A strategy hwin initialBank true = state.closedControl := by
  simp [candidate]

@[simp] theorem noRecv_root
    (state : ProfiledRawJointGuardedCommonTailChargedOneFork A strategy hwin
      initialBank) (input : In₁) :
    (state.noRecv A strategy hwin initialBank input).2.root = state.root :=
  rfl

@[simp] theorem noRecv_candidate
    (state : ProfiledRawJointGuardedCommonTailChargedOneFork A strategy hwin
      initialBank) (input : In₁) (closed : Bool) :
    (state.noRecv A strategy hwin initialBank input).2.candidate A strategy hwin
        initialBank closed =
      (state.noRecvTable A strategy hwin initialBank input closed).2 := by
  cases closed <;> rfl

theorem noRecv_output_eq
    (state : ProfiledRawJointGuardedCommonTailChargedOneFork A strategy hwin
      initialBank) (input : In₁)
    (hcoherent : state.NoRecvOutputCoherent A strategy hwin initialBank input)
    (closed : Bool) :
    (state.noRecv A strategy hwin initialBank input).1 =
      (state.noRecvTable A strategy hwin initialBank input closed).1 := by
  cases closed
  · rfl
  · exact hcoherent

end ProfiledRawJointGuardedCommonTailChargedOneFork

namespace ProfiledRawJointGuardedCommonTailChargedTwoFork

noncomputable def candidate
    (state : ProfiledRawJointGuardedCommonTailChargedTwoFork A strategy hwin
      initialBank) (closed : Bool) : OldTwo A strategy hwin initialBank :=
  if closed then state.closedControl else state.openControl

noncomputable def noRecvTable
    (state : ProfiledRawJointGuardedCommonTailChargedTwoFork A strategy hwin
      initialBank) (input : In₂) (closed : Bool) :
    Out₂ × OldTwo A strategy hwin initialBank :=
  (profiledRawJointGuardedCommonTailOldKernel A strategy hwin initialBank
    state.root).noRecvTwo
    (state.candidate A strategy hwin initialBank closed) input

def NoRecvOutputCoherent
    (state : ProfiledRawJointGuardedCommonTailChargedTwoFork A strategy hwin
      initialBank) (input : In₂) : Prop :=
  (state.noRecvTable A strategy hwin initialBank input false).1 =
    (state.noRecvTable A strategy hwin initialBank input true).1

noncomputable def noRecv
    (state : ProfiledRawJointGuardedCommonTailChargedTwoFork A strategy hwin
      initialBank) (input : In₂) :
    Out₂ ×
      ProfiledRawJointGuardedCommonTailChargedTwoFork A strategy hwin
        initialBank :=
  let openResult := state.noRecvTable A strategy hwin initialBank input false
  let closedResult := state.noRecvTable A strategy hwin initialBank input true
  (openResult.1, ⟨state.root, openResult.2, closedResult.2⟩)

@[simp] theorem candidate_false
    (state : ProfiledRawJointGuardedCommonTailChargedTwoFork A strategy hwin
      initialBank) :
    state.candidate A strategy hwin initialBank false = state.openControl := by
  simp [candidate]

@[simp] theorem candidate_true
    (state : ProfiledRawJointGuardedCommonTailChargedTwoFork A strategy hwin
      initialBank) :
    state.candidate A strategy hwin initialBank true = state.closedControl := by
  simp [candidate]

@[simp] theorem noRecv_root
    (state : ProfiledRawJointGuardedCommonTailChargedTwoFork A strategy hwin
      initialBank) (input : In₂) :
    (state.noRecv A strategy hwin initialBank input).2.root = state.root :=
  rfl

@[simp] theorem noRecv_candidate
    (state : ProfiledRawJointGuardedCommonTailChargedTwoFork A strategy hwin
      initialBank) (input : In₂) (closed : Bool) :
    (state.noRecv A strategy hwin initialBank input).2.candidate A strategy hwin
        initialBank closed =
      (state.noRecvTable A strategy hwin initialBank input closed).2 := by
  cases closed <;> rfl

theorem noRecv_output_eq
    (state : ProfiledRawJointGuardedCommonTailChargedTwoFork A strategy hwin
      initialBank) (input : In₂)
    (hcoherent : state.NoRecvOutputCoherent A strategy hwin initialBank input)
    (closed : Bool) :
    (state.noRecv A strategy hwin initialBank input).1 =
      (state.noRecvTable A strategy hwin initialBank input closed).1 := by
  cases closed
  · rfl
  · exact hcoherent

end ProfiledRawJointGuardedCommonTailChargedTwoFork

/-! ## Enter the deferred fork from the difficult shadow coordinates -/

/-- A right shadow followed by process-one non-receipt keeps both honest
ordinary continuations in one finite fork. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.noRecvOne
    (state : RightShadow A strategy hwin) (input : In₁) :
    Out₁ ×
      ProfiledRawJointGuardedCommonTailChargedOneFork A strategy hwin
        initialBank :=
  let openResult := state.noRecvOneTable A strategy hwin initialBank input false
  let closedResult := state.noRecvOneTable A strategy hwin initialBank input true
  (openResult.1,
    ⟨state.pending.receiver.control, openResult.2, closedResult.2⟩)

/-- Left-shadow/process-two mirror. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.noRecvTwo
    (state : LeftShadow A strategy hwin) (input : In₂) :
    Out₂ ×
      ProfiledRawJointGuardedCommonTailChargedTwoFork A strategy hwin
        initialBank :=
  let openResult := state.noRecvTwoTable A strategy hwin initialBank input false
  let closedResult := state.noRecvTwoTable A strategy hwin initialBank input true
  (openResult.1,
    ⟨state.pending.receiver.control, openResult.2, closedResult.2⟩)

@[simp] theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.noRecvOne_candidate
    (state : RightShadow A strategy hwin) (input : In₁) (closed : Bool) :
    (state.noRecvOne A strategy hwin initialBank input).2.candidate A strategy
        hwin initialBank closed =
      (state.noRecvOneTable A strategy hwin initialBank input closed).2 := by
  cases closed <;> rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.noRecvTwo_candidate
    (state : LeftShadow A strategy hwin) (input : In₂) (closed : Bool) :
    (state.noRecvTwo A strategy hwin initialBank input).2.candidate A strategy
        hwin initialBank closed =
      (state.noRecvTwoTable A strategy hwin initialBank input closed).2 := by
  cases closed <;> rfl

def ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.NoRecvOneCoherent
    (state : RightShadow A strategy hwin) (input : In₁) : Prop :=
  (state.noRecvOneTable A strategy hwin initialBank input false).1 =
    (state.noRecvOneTable A strategy hwin initialBank input true).1

def ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.NoRecvTwoCoherent
    (state : LeftShadow A strategy hwin) (input : In₂) : Prop :=
  (state.noRecvTwoTable A strategy hwin initialBank input false).1 =
    (state.noRecvTwoTable A strategy hwin initialBank input true).1

theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.noRecvOne_output_eq
    (state : RightShadow A strategy hwin) (input : In₁)
    (hcoherent : state.NoRecvOneCoherent A strategy hwin initialBank input)
    (closed : Bool) :
    (state.noRecvOne A strategy hwin initialBank input).1 =
      (state.noRecvOneTable A strategy hwin initialBank input closed).1 := by
  cases closed
  · rfl
  · exact hcoherent

theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.noRecvTwo_output_eq
    (state : LeftShadow A strategy hwin) (input : In₂)
    (hcoherent : state.NoRecvTwoCoherent A strategy hwin initialBank input)
    (closed : Bool) :
    (state.noRecvTwo A strategy hwin initialBank input).1 =
      (state.noRecvTwoTable A strategy hwin initialBank input closed).1 := by
  cases closed
  · rfl
  · exact hcoherent

/-! ## The two definitional collapses -/

theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.noRecvTwo_eq
    (state : RightShadow A strategy hwin) (input : In₂) :
    state.noRecvTwoTable A strategy hwin initialBank input false =
      state.noRecvTwoTable A strategy hwin initialBank input true := by
  simp [ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.noRecvTwoTable,
    profiledRawJointGuardedCommonTailOldKernel,
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.twoCandidate,
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.resolvedRight,
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.leftOwner,
    profiledRawJointGuardedCommonTailRightChargedCrossImmediateRoots,
    profiledRawJointGuardedCommonTailRightChargedCrossClose,
    profiledRawJointGuardedCommonTailResolveRightStep,
    profiledRawJointGuardedCommonTailCoreKernel,
    profiledRawJointGuardedCommonTailCoreAdapter,
    profiledRawJointGuardedCommonTailCoreNoRecvTwo,
    profiledRawJointGuardedCommonTailTwoOfRightReceiver,
    profiledRawJointGuardedCommonRightStagedStartLeftOwner,
    profiledRawJointGuardedHybridCombinedLeaderFreeKernel,
    profiledRawJointIndexedPolicyLeaderFreeKernel,
    ProfiledRawJointLeaderFreeKernel.noRecvTwo]

/-- The strict-left mirror collapses definitionally at process one: its
one-way interpretation is a resolved old-left receiver whose staged close is
literally the close used by the simultaneous interpretation's right owner. -/
theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.noRecvOne_eq
    (state : LeftShadow A strategy hwin) (input : In₁) :
    state.noRecvOneTable A strategy hwin initialBank input false =
      state.noRecvOneTable A strategy hwin initialBank input true := by
  simp [ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.noRecvOneTable,
    profiledRawJointGuardedCommonTailOldKernel,
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.oneCandidate,
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.resolvedLeft,
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.rightOwner,
    profiledRawJointGuardedCommonTailLeftChargedCrossImmediateRoots,
    profiledRawJointGuardedCommonTailLeftChargedCrossClose,
    profiledRawJointGuardedCommonTailResolveLeftStep,
    profiledRawJointGuardedCommonTailCoreKernel,
    profiledRawJointGuardedCommonTailCoreAdapter,
    profiledRawJointGuardedCommonTailCoreNoRecvOne,
    profiledRawJointGuardedCommonTailOneOfLeftReceiver,
    profiledRawJointGuardedCommonLeftStagedStartRightOwner,
    profiledRawJointGuardedHybridCombinedLeaderFreeKernel,
    profiledRawJointIndexedPolicyLeaderFreeKernel,
    ProfiledRawJointLeaderFreeKernel.noRecvOne]

end

end DetParityAutomaton

end DistributedSynthesis
