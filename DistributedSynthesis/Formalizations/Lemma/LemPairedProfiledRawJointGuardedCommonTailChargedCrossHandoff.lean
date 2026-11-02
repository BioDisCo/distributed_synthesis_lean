/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCoreStrictTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailPendingRebase
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCrossAnchorLocalFactorization

/-!
# Charging a simultaneous cross to the old strict epoch

At a simultaneous receive immediately following a strict-right prefix, both
processes can reconstruct the same pending strict state.  They can therefore
read one old-right narrowed record jointly.  The physical close uses that
record's `closingBoth` and `informedBoth` coordinates; its checked target is
installed immediately as the next left-oriented recurrent root.  The left
case is symmetric.

This is importantly different from continuing the old strict round: the blind
owner output is not the output of the simultaneous close.  The target equation
in `pairedRightCloseTarget` is stated for `closingBoth`, and it is precisely
that coordinate which makes the handoff a post-close root.

All executable maps below are indexed only by the finite pending state and the
two current inputs.  The orientation in their names is the type of the stored
pending payload, not a runtime graph or strict-leader argument.
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

private abbrev InitialOne :=
  ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin

private abbrev InitialTwo :=
  ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin

private abbrev ExceptionalOne :=
  ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin

private abbrev ExceptionalTwo :=
  ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin

private abbrev OneControl :=
  ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin initialBank
    (InitialOne A strategy hwin) (ExceptionalOne A strategy hwin)

private abbrev TwoControl :=
  ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin initialBank
    (InitialTwo A strategy hwin) (ExceptionalTwo A strategy hwin)

/-! ## Correct physical close outputs -/

/-- The simultaneous output charged to an old strict-right record. -/
noncomputable def profiledRawJointGuardedCommonTailRightChargedCrossOutput
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) : Out₁ × Out₂ :=
  let record := profiledRawJointGuardedCommonTailResolveRightRecord A strategy
    hwin pending (input.2, input.1)
  let physical := profiledRawJointTargetRightPhysicalLetter A record
  (pairedRightClosingForRow .both physical.2.1,
    pairedRightInformedForRow .both physical.2.1)

/-- Strict-left mirror. -/
noncomputable def profiledRawJointGuardedCommonTailLeftChargedCrossOutput
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) : Out₁ × Out₂ :=
  let record := profiledRawJointGuardedCommonTailResolveLeftRecord A strategy
    hwin pending input
  let physical := profiledRawJointTargetLeftPhysicalLetter A record
  (pairedLeftInformedForRow .both physical.2.1,
    pairedLeftClosingForRow .both physical.2.1)

/-- The right-charged output is literally the `both` close record checked by
the staged target. -/
theorem profiledRawJointGuardedCommonTailRightChargedCross_roundRecord
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    let record := profiledRawJointGuardedCommonTailResolveRightRecord A strategy
      hwin pending (input.2, input.1)
    bothRoundRecord input
        (profiledRawJointGuardedCommonTailRightChargedCrossOutput A strategy
          hwin pending input).1
        (profiledRawJointGuardedCommonTailRightChargedCrossOutput A strategy
          hwin pending input).2 =
      let physical := profiledRawJointTargetRightPhysicalLetter A record
      bothRoundRecord input
        (pairedRightClosingForRow .both physical.2.1)
        (pairedRightInformedForRow .both physical.2.1) := by
  rfl

/-- Left mirror. -/
theorem profiledRawJointGuardedCommonTailLeftChargedCross_roundRecord
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    let record := profiledRawJointGuardedCommonTailResolveLeftRecord A strategy
      hwin pending input
    bothRoundRecord input
        (profiledRawJointGuardedCommonTailLeftChargedCrossOutput A strategy hwin
          pending input).1
        (profiledRawJointGuardedCommonTailLeftChargedCrossOutput A strategy hwin
          pending input).2 =
      let physical := profiledRawJointTargetLeftPhysicalLetter A record
      bothRoundRecord input
        (pairedLeftInformedForRow .both physical.2.1)
        (pairedLeftClosingForRow .both physical.2.1) := by
  rfl

/-! ## Immediate post-close root installation -/

/-- Compute the checked close from the same pre-step state as the physical
right record. -/
noncomputable def profiledRawJointGuardedCommonTailRightChargedCrossClose
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin :=
  let ownerControl := profiledRawJointGuardedCommonRightOwnerFor A strategy
    hwin pending.receiver.shadow pending.owner
  profiledRawJointGuardedCommonRightStageClose A strategy hwin
    pending.receiver.shadow.source
    (ownerControl, pending.receiver.shadow.strictReceiver)
    (input.2, input.1) .both

/-- Left mirror. -/
noncomputable def profiledRawJointGuardedCommonTailLeftChargedCrossClose
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin :=
  let ownerControl := profiledRawJointGuardedCommonLeftOwnerFor A strategy hwin
    pending.receiver.shadow pending.owner
  profiledRawJointGuardedCommonLeftStageClose A strategy hwin
    pending.receiver.shadow.source
    (ownerControl, pending.receiver.shadow.strictReceiver) input .both

/-- Proof-side projection of the right close to the two recurrent initial
controls.  These are the post-close alternatives retained by the local shadow
below; they must not by themselves replace the local state, because a single
receiver cannot tell `right` from `both` (or `left` from `both`). -/
noncomputable def
    profiledRawJointGuardedCommonTailRightChargedCrossImmediateRoots
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    OneControl A strategy hwin initialBank ×
      TwoControl A strategy hwin initialBank :=
  let close := profiledRawJointGuardedCommonTailRightChargedCrossClose A
    strategy hwin pending input
  let key := profiledRawJointGuardedCommonRightStagedCombinedKey A strategy
    hwin initialBank close
  (.leftReceiver key
      (profiledRawJointGuardedCommonRightStagedInitialLeftReceiver A strategy
        hwin initialBank close),
    .leftOwner key
      (profiledRawJointGuardedCommonRightStagedInitialLeftOwner A strategy
        hwin initialBank close))

/-- Left proof-side post-close roots. -/
noncomputable def
    profiledRawJointGuardedCommonTailLeftChargedCrossImmediateRoots
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    OneControl A strategy hwin initialBank ×
      TwoControl A strategy hwin initialBank :=
  let close := profiledRawJointGuardedCommonTailLeftChargedCrossClose A
    strategy hwin pending input
  let key := profiledRawJointGuardedCommonLeftStagedCombinedKey A strategy hwin
    initialBank close
  (.rightOwner key
      (profiledRawJointGuardedCommonLeftStagedInitialRightOwner A strategy
        hwin initialBank close),
    .rightReceiver key
      (profiledRawJointGuardedCommonLeftStagedInitialRightReceiver A strategy
        hwin initialBank close))

/-- The two installed right-cross controls carry literally the same checked
target key. -/
theorem profiledRawJointGuardedCommonTailRightChargedCrossResponse_controls
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    let close := profiledRawJointGuardedCommonTailRightChargedCrossClose A
      strategy hwin pending input
    let key := profiledRawJointGuardedCommonRightStagedCombinedKey A strategy
      hwin initialBank close
    (profiledRawJointGuardedCommonTailRightChargedCrossImmediateRoots A strategy
      hwin initialBank pending input).1 =
        .leftReceiver key
          (profiledRawJointGuardedCommonRightStagedInitialLeftReceiver A
            strategy hwin initialBank close) ∧
      (profiledRawJointGuardedCommonTailRightChargedCrossImmediateRoots A
        strategy hwin initialBank pending input).2 =
        .leftOwner key
          (profiledRawJointGuardedCommonRightStagedInitialLeftOwner A strategy
            hwin initialBank close) := by
  exact ⟨rfl, rfl⟩

/-- Left mirror. -/
theorem profiledRawJointGuardedCommonTailLeftChargedCrossResponse_controls
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    let close := profiledRawJointGuardedCommonTailLeftChargedCrossClose A
      strategy hwin pending input
    let key := profiledRawJointGuardedCommonLeftStagedCombinedKey A strategy
      hwin initialBank close
    (profiledRawJointGuardedCommonTailLeftChargedCrossImmediateRoots A strategy
      hwin initialBank pending input).1 =
        .rightOwner key
          (profiledRawJointGuardedCommonLeftStagedInitialRightOwner A strategy
            hwin initialBank close) ∧
      (profiledRawJointGuardedCommonTailLeftChargedCrossImmediateRoots A
        strategy hwin initialBank pending input).2 =
        .rightReceiver key
          (profiledRawJointGuardedCommonLeftStagedInitialRightReceiver A
            strategy hwin initialBank close) := by
  exact ⟨rfl, rfl⟩

/-! ## The one-bit two-alternative local shadows -/

/-- Finite information retained after a process receives at a right-pending
cross.  The same value represents both possibilities invisible at that local
receive: continuation of the old right epoch and its checked simultaneous
close.  All candidate controls are deterministic projections of this value. -/
structure ProfiledRawJointGuardedCommonTailRightChargedCrossShadow where
  pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin
  input : In₁ × In₂

/-- Strict-left mirror. -/
structure ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow where
  pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin
  input : In₁ × In₂

noncomputable instance
    profiledRawJointGuardedCommonTailRightChargedCrossShadowFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A strategy
        hwin) := by
  classical
  let Rep := ProfiledRawJointGuardedCommonRightPending A strategy hwin ×
    (In₁ × In₂)
  let equiv :
      ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A strategy hwin
        ≃ Rep :=
    { toFun := fun state ↦ (state.pending, state.input)
      invFun := fun state ↦ ⟨state.1, state.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; cases state; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointGuardedCommonTailLeftChargedCrossShadowFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy
        hwin) := by
  classical
  let Rep := ProfiledRawJointGuardedCommonLeftPending A strategy hwin ×
    (In₁ × In₂)
  let equiv :
      ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy hwin
        ≃ Rep :=
    { toFun := fun state ↦ (state.pending, state.input)
      invFun := fun state ↦ ⟨state.1, state.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; cases state; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

namespace ProfiledRawJointGuardedCommonTailRightChargedCrossShadow

/-- The common/reversal candidate available to process one. -/
noncomputable def rebaseOne
    (state : ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A
      strategy hwin) : Out₁ × OneControl A strategy hwin initialBank :=
  profiledRawJointGuardedCommonTailRightPendingRebaseOne A strategy hwin
    initialBank state.pending.owner state.pending.receiver state.input.1
      state.input.2

/-- The continuing old-right candidate available to process two. -/
noncomputable def resolvedRight
    (state : ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A
      strategy hwin) :
    ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin :=
  (profiledRawJointGuardedCommonTailResolveRightStep A strategy hwin
    state.pending (state.input.2, state.input.1)).2

/-- The post-close left receiver candidate. -/
noncomputable def leftReceiver
    (state : ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A
      strategy hwin) : OneControl A strategy hwin initialBank :=
  (profiledRawJointGuardedCommonTailRightChargedCrossImmediateRoots A strategy
    hwin initialBank state.pending state.input).1

/-- The post-close left owner candidate. -/
noncomputable def leftOwner
    (state : ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A
      strategy hwin) : TwoControl A strategy hwin initialBank :=
  (profiledRawJointGuardedCommonTailRightChargedCrossImmediateRoots A strategy
    hwin initialBank state.pending state.input).2

end ProfiledRawJointGuardedCommonTailRightChargedCrossShadow

namespace ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow

/-- Continuing old-left candidate at process one. -/
noncomputable def resolvedLeft
    (state : ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy
      hwin) : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin :=
  (profiledRawJointGuardedCommonTailResolveLeftStep A strategy hwin
    state.pending state.input).2

/-- Common/reversal candidate at process two. -/
noncomputable def rebaseTwo
    (state : ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy
      hwin) : Out₂ × TwoControl A strategy hwin initialBank :=
  profiledRawJointGuardedCommonTailLeftPendingRebaseTwo A strategy hwin
    initialBank state.pending.owner state.pending.receiver state.input.2
      state.input.1

/-- Post-close right owner. -/
noncomputable def rightOwner
    (state : ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy
      hwin) : OneControl A strategy hwin initialBank :=
  (profiledRawJointGuardedCommonTailLeftChargedCrossImmediateRoots A strategy
    hwin initialBank state.pending state.input).1

/-- Post-close right receiver. -/
noncomputable def rightReceiver
    (state : ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy
      hwin) : TwoControl A strategy hwin initialBank :=
  (profiledRawJointGuardedCommonTailLeftChargedCrossImmediateRoots A strategy
    hwin initialBank state.pending state.input).2

end ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow

/-! ## One finite joint table and its graph-blind local projections -/

/-- Correct right-cross response: both local coordinates retain the same
finite two-alternative shadow. -/
noncomputable def profiledRawJointGuardedCommonTailRightChargedCrossResponse
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    (Out₁ ×
        ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A strategy
          hwin) ×
      (Out₂ ×
        ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A strategy
          hwin) :=
  let output := profiledRawJointGuardedCommonTailRightChargedCrossOutput A
    strategy hwin pending input
  let shadow :
      ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A strategy
        hwin := ⟨pending, input⟩
  ((output.1, shadow), (output.2, shadow))

/-- Left response. -/
noncomputable def profiledRawJointGuardedCommonTailLeftChargedCrossResponse
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    (Out₁ ×
        ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy
          hwin) ×
      (Out₂ ×
        ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy
          hwin) :=
  let output := profiledRawJointGuardedCommonTailLeftChargedCrossOutput A
    strategy hwin pending input
  let shadow :
      ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy
        hwin := ⟨pending, input⟩
  ((output.1, shadow), (output.2, shadow))

/-- All pending right closes are selected by one finite joint move. -/
noncomputable def profiledRawJointGuardedCommonTailRightChargedCrossJointMove :
    ProfiledRawJointGuardedRightCrossAnchorLocalFactorizationMove A strategy hwin
      (ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A strategy
        hwin)
      (ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A strategy
        hwin) :=
  fun pending input ↦
    profiledRawJointGuardedCommonTailRightChargedCrossResponse A strategy hwin
      pending input

/-- Left mirror. -/
noncomputable def profiledRawJointGuardedCommonTailLeftChargedCrossJointMove :
    ProfiledRawJointGuardedLeftCrossAnchorLocalFactorizationMove A strategy hwin
      (ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy hwin)
      (ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy
        hwin) :=
  fun pending input ↦
    profiledRawJointGuardedCommonTailLeftChargedCrossResponse A strategy hwin
      pending input

/-- The generic factorization theorem now makes the corrected right close
locally executable by the two receiving processes. -/
theorem profiledRawJointGuardedCommonTailRightChargedCross_local_pair
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecvOne A strategy hwin
        (profiledRawJointGuardedCommonTailRightChargedCrossJointMove A strategy
          hwin)
        (default, ⟨pending, input⟩) pending.owner pending.receiver input.1
          input.2,
      profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecvTwo A strategy hwin
        (profiledRawJointGuardedCommonTailRightChargedCrossJointMove A strategy
          hwin)
        (default, ⟨pending, input⟩) pending.receiver pending.owner input.2
          input.1) =
      profiledRawJointGuardedCommonTailRightChargedCrossResponse A strategy
        hwin pending input := by
  exact profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecv_pair A strategy hwin
    (profiledRawJointGuardedCommonTailRightChargedCrossJointMove A strategy
      hwin) (default, ⟨pending, input⟩)
      (default, ⟨pending, input⟩) pending input

/-- Left local factorization. -/
theorem profiledRawJointGuardedCommonTailLeftChargedCross_local_pair
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecvOne A strategy hwin
        (profiledRawJointGuardedCommonTailLeftChargedCrossJointMove A strategy
          hwin)
        (default, ⟨pending, input⟩) pending.receiver pending.owner input.1
          input.2,
      profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecvTwo A strategy hwin
        (profiledRawJointGuardedCommonTailLeftChargedCrossJointMove A strategy
          hwin)
        (default, ⟨pending, input⟩) pending.owner pending.receiver input.2
          input.1) =
      profiledRawJointGuardedCommonTailLeftChargedCrossResponse A strategy hwin
        pending input := by
  exact profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecv_pair A strategy hwin
    (profiledRawJointGuardedCommonTailLeftChargedCrossJointMove A strategy hwin
      ) (default, ⟨pending, input⟩)
      (default, ⟨pending, input⟩) pending input

end

end DetParityAutomaton

end DistributedSynthesis
