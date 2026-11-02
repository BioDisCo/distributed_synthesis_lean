/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailChargedCrossHandoff

/-!
# The three-graph local table at a charged strict/common cross

At a pending strict-right state, process one observes the same receive event
on `left` and `both`, while process two observes the same receive event on
`right` and `both`.  Consequently the simultaneous case is not allowed to
select a third, graph-specific local action.  It is assembled from those two
shared receive handlers.  The strict-left table is symmetric.

The receive handlers below use the old epoch's charged close.  A receiving
process retains one finite shadow with its two honest interpretations; a
nonreceiving process enters the unique continuation determined by its local
event.  Thus the proof-side three-graph split leaves one fresh shared
ambiguity object, rather than two independently chosen controller roots.

Only the proof-side table evaluator inspects `Graph`.  None of the four local
handlers accepts a graph, an orientation, a leader bit, or a semantic history.
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

private abbrev RightShadow :=
  ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A strategy hwin

private abbrev LeftShadow :=
  ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy hwin

/-! ## Finite post-step local carriers -/

/-- After a right-pending round, process one either knows that it did not
receive, or retains the single receive ambiguity shared by `left` and `both`.
-/
abbrev ProfiledRawJointGuardedCommonTailRightChargedNextOne :=
  OneControl A strategy hwin initialBank ⊕ RightShadow A strategy hwin

/-- Process two's mirror carrier: nonreceive is uniquely `left`, receive is
the shared `right`/`both` ambiguity. -/
abbrev ProfiledRawJointGuardedCommonTailRightChargedNextTwo :=
  TwoControl A strategy hwin initialBank ⊕ RightShadow A strategy hwin

abbrev ProfiledRawJointGuardedCommonTailLeftChargedNextOne :=
  OneControl A strategy hwin initialBank ⊕ LeftShadow A strategy hwin

abbrev ProfiledRawJointGuardedCommonTailLeftChargedNextTwo :=
  TwoControl A strategy hwin initialBank ⊕ LeftShadow A strategy hwin

/-! ## Right-pending local handlers -/

/-- Process one's graph-blind nonreceive handler. -/
noncomputable def
    profiledRawJointGuardedCommonTailRightChargedNoRecvOne
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (input : In₁) :
    Out₁ × ProfiledRawJointGuardedCommonTailRightChargedNextOne A strategy
      hwin initialBank :=
  let next := profiledRawJointGuardedCommonTailRightOwnerNoRecvOne A strategy
    hwin initialBank owner input
  (next.1, .inl next.2)

/-- Process two's graph-blind nonreceive handler.  Its local event uniquely
selects the strict-left/common continuation. -/
noncomputable def
    profiledRawJointGuardedCommonTailRightChargedNoRecvTwo
    (receiver : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (input : In₂) :
    Out₂ × ProfiledRawJointGuardedCommonTailRightChargedNextTwo A strategy
      hwin initialBank :=
  let next := profiledRawJointGuardedCommonTailCommonNoRecvTwo A strategy hwin
    initialBank receiver input
  (next.1, .inl next.2)

/-- Process one's one receive handler, used unchanged in the `left` and
`both` proof-side cases.  The anchor supplies only an unreachable fallback;
on a represented pending pair it is ignored by reconstruction. -/
noncomputable def profiledRawJointGuardedCommonTailRightChargedRecvOne
    (anchor : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (receiver : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × ProfiledRawJointGuardedCommonTailRightChargedNextOne A strategy
      hwin initialBank :=
  let fallback : Out₁ × RightShadow A strategy hwin :=
    (default, ⟨anchor, (own, delivered)⟩)
  let next := profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecvOne A strategy hwin
    (profiledRawJointGuardedCommonTailRightChargedCrossJointMove A strategy
      hwin) fallback owner receiver own delivered
  (next.1, .inr next.2)

/-- Process two's single receive handler, shared by `right` and `both`. -/
noncomputable def profiledRawJointGuardedCommonTailRightChargedRecvTwo
    (anchor : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (receiver : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × ProfiledRawJointGuardedCommonTailRightChargedNextTwo A strategy
      hwin initialBank :=
  let fallback : Out₂ × RightShadow A strategy hwin :=
    (default, ⟨anchor, (delivered, own)⟩)
  let next := profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecvTwo A strategy hwin
    (profiledRawJointGuardedCommonTailRightChargedCrossJointMove A strategy
      hwin) fallback receiver owner own delivered
  (next.1, .inr next.2)

/-! ## Left-pending local handlers -/

noncomputable def
    profiledRawJointGuardedCommonTailLeftChargedNoRecvOne
    (receiver : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (input : In₁) :
    Out₁ × ProfiledRawJointGuardedCommonTailLeftChargedNextOne A strategy
      hwin initialBank :=
  let next := profiledRawJointGuardedCommonTailCommonNoRecvOne A strategy hwin
    initialBank receiver input
  (next.1, .inl next.2)

noncomputable def
    profiledRawJointGuardedCommonTailLeftChargedNoRecvTwo
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (input : In₂) :
    Out₂ × ProfiledRawJointGuardedCommonTailLeftChargedNextTwo A strategy
      hwin initialBank :=
  let next := profiledRawJointGuardedCommonTailLeftOwnerNoRecvTwo A strategy
    hwin initialBank owner input
  (next.1, .inl next.2)

noncomputable def profiledRawJointGuardedCommonTailLeftChargedRecvOne
    (anchor : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (receiver : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × ProfiledRawJointGuardedCommonTailLeftChargedNextOne A strategy
      hwin initialBank :=
  let fallback : Out₁ × LeftShadow A strategy hwin :=
    (default, ⟨anchor, (own, delivered)⟩)
  let next := profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecvOne A strategy hwin
    (profiledRawJointGuardedCommonTailLeftChargedCrossJointMove A strategy
      hwin) fallback receiver owner own delivered
  (next.1, .inr next.2)

noncomputable def profiledRawJointGuardedCommonTailLeftChargedRecvTwo
    (anchor : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (receiver : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × ProfiledRawJointGuardedCommonTailLeftChargedNextTwo A strategy
      hwin initialBank :=
  let fallback : Out₂ × LeftShadow A strategy hwin :=
    (default, ⟨anchor, (delivered, own)⟩)
  let next := profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecvTwo A strategy hwin
    (profiledRawJointGuardedCommonTailLeftChargedCrossJointMove A strategy
      hwin) fallback owner receiver own delivered
  (next.1, .inr next.2)

/-! ## Proof-side three-graph evaluator -/

/-- Evaluate the four graph-blind right-pending handlers according to the
physical graph.  This is a proof-side global product, not a local API. -/
noncomputable def profiledRawJointGuardedCommonTailRightChargedLocalStep
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) (graph : Graph) :
    (Out₁ × ProfiledRawJointGuardedCommonTailRightChargedNextOne A
      strategy hwin initialBank) ×
    (Out₂ × ProfiledRawJointGuardedCommonTailRightChargedNextTwo A
      strategy hwin initialBank) :=
  match graph with
  | .right =>
      (profiledRawJointGuardedCommonTailRightChargedNoRecvOne A strategy hwin
          initialBank pending.owner input.1,
        profiledRawJointGuardedCommonTailRightChargedRecvTwo A strategy hwin
          initialBank pending pending.receiver pending.owner input.2 input.1)
  | .left =>
      (profiledRawJointGuardedCommonTailRightChargedRecvOne A strategy hwin
          initialBank pending pending.owner pending.receiver input.1 input.2,
        profiledRawJointGuardedCommonTailRightChargedNoRecvTwo A strategy hwin
          initialBank pending.receiver input.2)
  | .both =>
      (profiledRawJointGuardedCommonTailRightChargedRecvOne A strategy hwin
          initialBank pending pending.owner pending.receiver input.1 input.2,
        profiledRawJointGuardedCommonTailRightChargedRecvTwo A strategy hwin
          initialBank pending pending.receiver pending.owner input.2 input.1)

/-- Left mirror. -/
noncomputable def profiledRawJointGuardedCommonTailLeftChargedLocalStep
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) (graph : Graph) :
    (Out₁ × ProfiledRawJointGuardedCommonTailLeftChargedNextOne A
      strategy hwin initialBank) ×
    (Out₂ × ProfiledRawJointGuardedCommonTailLeftChargedNextTwo A
      strategy hwin initialBank) :=
  match graph with
  | .right =>
      (profiledRawJointGuardedCommonTailLeftChargedNoRecvOne A strategy hwin
          initialBank pending.receiver input.1,
        profiledRawJointGuardedCommonTailLeftChargedRecvTwo A strategy hwin
          initialBank pending pending.owner pending.receiver input.2 input.1)
  | .left =>
      (profiledRawJointGuardedCommonTailLeftChargedRecvOne A strategy hwin
          initialBank pending pending.receiver pending.owner input.1 input.2,
        profiledRawJointGuardedCommonTailLeftChargedNoRecvTwo A strategy hwin
          initialBank pending.owner input.2)
  | .both =>
      (profiledRawJointGuardedCommonTailLeftChargedRecvOne A strategy hwin
          initialBank pending pending.receiver pending.owner input.1 input.2,
        profiledRawJointGuardedCommonTailLeftChargedRecvTwo A strategy hwin
          initialBank pending pending.owner pending.receiver input.2 input.1)

/-! ## Exact case laws and the single fresh shadow -/

theorem profiledRawJointGuardedCommonTailRightChargedLocalStep_right
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonTailRightChargedLocalStep A strategy hwin
        initialBank pending input .right =
      (profiledRawJointGuardedCommonTailRightChargedNoRecvOne A strategy hwin
          initialBank pending.owner input.1,
        profiledRawJointGuardedCommonTailRightChargedRecvTwo A strategy hwin
          initialBank pending pending.receiver pending.owner input.2
            input.1) := by
  rfl

theorem profiledRawJointGuardedCommonTailRightChargedLocalStep_left
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonTailRightChargedLocalStep A strategy hwin
        initialBank pending input .left =
      (profiledRawJointGuardedCommonTailRightChargedRecvOne A strategy hwin
          initialBank pending pending.owner pending.receiver input.1 input.2,
        profiledRawJointGuardedCommonTailRightChargedNoRecvTwo A strategy hwin
          initialBank pending.receiver input.2) := by
  rfl

theorem profiledRawJointGuardedCommonTailRightChargedLocalStep_both
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonTailRightChargedLocalStep A strategy hwin
        initialBank pending input .both =
      let shadow : RightShadow A strategy hwin := ⟨pending, input⟩
      let output :=
        profiledRawJointGuardedCommonTailRightChargedCrossOutput A strategy
          hwin pending input
      ((output.1, .inr shadow), (output.2, .inr shadow)) := by
  simp [profiledRawJointGuardedCommonTailRightChargedLocalStep,
    profiledRawJointGuardedCommonTailRightChargedRecvOne,
    profiledRawJointGuardedCommonTailRightChargedRecvTwo,
    profiledRawJointGuardedCommonTailRightChargedCrossJointMove,
    profiledRawJointGuardedCommonTailRightChargedCrossResponse,
    profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecvOne,
    profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecvTwo]

/-- In a strict-right physical round only process two retains the fresh
receive shadow.  Process one's nonreceive branch is already exact. -/
theorem
    profiledRawJointGuardedCommonTailRightChargedLocalStep_right_normal
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonTailRightChargedLocalStep A strategy hwin
        initialBank pending input .right =
      let exact :=
        profiledRawJointGuardedCommonTailRightOwnerNoRecvOne A strategy hwin
          initialBank pending.owner input.1
      let shadow : RightShadow A strategy hwin := ⟨pending, input⟩
      let output :=
        profiledRawJointGuardedCommonTailRightChargedCrossOutput A strategy
          hwin pending input
      ((exact.1, .inl exact.2), (output.2, .inr shadow)) := by
  simp [profiledRawJointGuardedCommonTailRightChargedLocalStep,
    profiledRawJointGuardedCommonTailRightChargedNoRecvOne,
    profiledRawJointGuardedCommonTailRightChargedRecvTwo,
    profiledRawJointGuardedCommonTailRightChargedCrossJointMove,
    profiledRawJointGuardedCommonTailRightChargedCrossResponse,
    profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecvTwo]

/-- In a strict-left physical round only process one retains the fresh
receive shadow. -/
theorem
    profiledRawJointGuardedCommonTailRightChargedLocalStep_left_normal
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonTailRightChargedLocalStep A strategy hwin
        initialBank pending input .left =
      let exact :=
        profiledRawJointGuardedCommonTailCommonNoRecvTwo A strategy hwin
          initialBank pending.receiver input.2
      let shadow : RightShadow A strategy hwin := ⟨pending, input⟩
      let output :=
        profiledRawJointGuardedCommonTailRightChargedCrossOutput A strategy
          hwin pending input
      ((output.1, .inr shadow), (exact.1, .inl exact.2)) := by
  simp [profiledRawJointGuardedCommonTailRightChargedLocalStep,
    profiledRawJointGuardedCommonTailRightChargedRecvOne,
    profiledRawJointGuardedCommonTailRightChargedNoRecvTwo,
    profiledRawJointGuardedCommonTailRightChargedCrossJointMove,
    profiledRawJointGuardedCommonTailRightChargedCrossResponse,
    profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecvOne]

/-- Process one's receive action and retained state are literally shared by
the `left` and `both` cases. -/
theorem
    profiledRawJointGuardedCommonTailRightCharged_recvOne_left_eq_both
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonTailRightChargedLocalStep A strategy hwin
      initialBank pending input .left).1 =
    (profiledRawJointGuardedCommonTailRightChargedLocalStep A strategy hwin
      initialBank pending input .both).1 := by
  rfl

/-- Process two's receive action and retained state are literally shared by
the `right` and `both` cases. -/
theorem
    profiledRawJointGuardedCommonTailRightCharged_recvTwo_right_eq_both
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonTailRightChargedLocalStep A strategy hwin
      initialBank pending input .right).2 =
    (profiledRawJointGuardedCommonTailRightChargedLocalStep A strategy hwin
      initialBank pending input .both).2 := by
  rfl

theorem profiledRawJointGuardedCommonTailLeftChargedLocalStep_right
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonTailLeftChargedLocalStep A strategy hwin
        initialBank pending input .right =
      (profiledRawJointGuardedCommonTailLeftChargedNoRecvOne A strategy hwin
          initialBank pending.receiver input.1,
        profiledRawJointGuardedCommonTailLeftChargedRecvTwo A strategy hwin
          initialBank pending pending.owner pending.receiver input.2 input.1) :=
  by rfl

theorem profiledRawJointGuardedCommonTailLeftChargedLocalStep_left
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonTailLeftChargedLocalStep A strategy hwin
        initialBank pending input .left =
      (profiledRawJointGuardedCommonTailLeftChargedRecvOne A strategy hwin
          initialBank pending pending.receiver pending.owner input.1 input.2,
        profiledRawJointGuardedCommonTailLeftChargedNoRecvTwo A strategy hwin
          initialBank pending.owner input.2) := by
  rfl

theorem profiledRawJointGuardedCommonTailLeftChargedLocalStep_both
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonTailLeftChargedLocalStep A strategy hwin
        initialBank pending input .both =
      let shadow : LeftShadow A strategy hwin := ⟨pending, input⟩
      let output :=
        profiledRawJointGuardedCommonTailLeftChargedCrossOutput A strategy hwin
          pending input
      ((output.1, .inr shadow), (output.2, .inr shadow)) := by
  simp [profiledRawJointGuardedCommonTailLeftChargedLocalStep,
    profiledRawJointGuardedCommonTailLeftChargedRecvOne,
    profiledRawJointGuardedCommonTailLeftChargedRecvTwo,
    profiledRawJointGuardedCommonTailLeftChargedCrossJointMove,
    profiledRawJointGuardedCommonTailLeftChargedCrossResponse,
    profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecvOne,
    profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecvTwo]

theorem
    profiledRawJointGuardedCommonTailLeftChargedLocalStep_right_normal
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonTailLeftChargedLocalStep A strategy hwin
        initialBank pending input .right =
      let exact :=
        profiledRawJointGuardedCommonTailCommonNoRecvOne A strategy hwin
          initialBank pending.receiver input.1
      let shadow : LeftShadow A strategy hwin := ⟨pending, input⟩
      let output :=
        profiledRawJointGuardedCommonTailLeftChargedCrossOutput A strategy hwin
          pending input
      ((exact.1, .inl exact.2), (output.2, .inr shadow)) := by
  simp [profiledRawJointGuardedCommonTailLeftChargedLocalStep,
    profiledRawJointGuardedCommonTailLeftChargedNoRecvOne,
    profiledRawJointGuardedCommonTailLeftChargedRecvTwo,
    profiledRawJointGuardedCommonTailLeftChargedCrossJointMove,
    profiledRawJointGuardedCommonTailLeftChargedCrossResponse,
    profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecvTwo]

theorem profiledRawJointGuardedCommonTailLeftChargedLocalStep_left_normal
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonTailLeftChargedLocalStep A strategy hwin
        initialBank pending input .left =
      let exact :=
        profiledRawJointGuardedCommonTailLeftOwnerNoRecvTwo A strategy hwin
          initialBank pending.owner input.2
      let shadow : LeftShadow A strategy hwin := ⟨pending, input⟩
      let output :=
        profiledRawJointGuardedCommonTailLeftChargedCrossOutput A strategy hwin
          pending input
      ((output.1, .inr shadow), (exact.1, .inl exact.2)) := by
  simp [profiledRawJointGuardedCommonTailLeftChargedLocalStep,
    profiledRawJointGuardedCommonTailLeftChargedRecvOne,
    profiledRawJointGuardedCommonTailLeftChargedNoRecvTwo,
    profiledRawJointGuardedCommonTailLeftChargedCrossJointMove,
    profiledRawJointGuardedCommonTailLeftChargedCrossResponse,
    profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecvOne]

theorem profiledRawJointGuardedCommonTailLeftCharged_recvOne_left_eq_both
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonTailLeftChargedLocalStep A strategy hwin
      initialBank pending input .left).1 =
    (profiledRawJointGuardedCommonTailLeftChargedLocalStep A strategy hwin
      initialBank pending input .both).1 := by
  rfl

theorem profiledRawJointGuardedCommonTailLeftCharged_recvTwo_right_eq_both
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonTailLeftChargedLocalStep A strategy hwin
      initialBank pending input .right).2 =
    (profiledRawJointGuardedCommonTailLeftChargedLocalStep A strategy hwin
      initialBank pending input .both).2 := by
  rfl

/-! ## One-bit interpretation of a receive shadow -/

/-- The two possible process-one continuations represented by one right
receive shadow: honest `left`, or simultaneous close. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.oneCandidate
    (state : RightShadow A strategy hwin) (closed : Bool) :
    OneControl A strategy hwin initialBank :=
  if closed then state.leftReceiver A strategy hwin initialBank
  else (state.rebaseOne A strategy hwin initialBank).2

/-- Process two interprets the same bit as honest `right`, or simultaneous
close.  The strict candidate is embedded in the recurrent local carrier. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.twoCandidate
    (state : RightShadow A strategy hwin) (closed : Bool) :
    TwoControl A strategy hwin initialBank :=
  if closed then state.leftOwner A strategy hwin initialBank
  else
    .exceptional
      (profiledRawJointGuardedCommonTailTwoOfRightReceiver A strategy hwin
        (state.resolvedRight A strategy hwin))

noncomputable def
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.oneCandidate
    (state : LeftShadow A strategy hwin) (closed : Bool) :
    OneControl A strategy hwin initialBank :=
  if closed then state.rightOwner A strategy hwin initialBank
  else
    .exceptional
      (profiledRawJointGuardedCommonTailOneOfLeftReceiver A strategy hwin
        (state.resolvedLeft A strategy hwin))

noncomputable def
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.twoCandidate
    (state : LeftShadow A strategy hwin) (closed : Bool) :
    TwoControl A strategy hwin initialBank :=
  if closed then state.rightReceiver A strategy hwin initialBank
  else (state.rebaseTwo A strategy hwin initialBank).2

@[simp] theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.oneCandidate_false
    (state : RightShadow A strategy hwin) :
    state.oneCandidate A strategy hwin initialBank false =
      (state.rebaseOne A strategy hwin initialBank).2 := by
  simp [ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.oneCandidate]

@[simp] theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.oneCandidate_true
    (state : RightShadow A strategy hwin) :
    state.oneCandidate A strategy hwin initialBank true =
      state.leftReceiver A strategy hwin initialBank := by
  simp [ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.oneCandidate]

@[simp] theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.twoCandidate_false
    (state : RightShadow A strategy hwin) :
    state.twoCandidate A strategy hwin initialBank false =
      .exceptional
        (profiledRawJointGuardedCommonTailTwoOfRightReceiver A strategy hwin
          (state.resolvedRight A strategy hwin)) := by
  simp [ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.twoCandidate]

@[simp] theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.twoCandidate_true
    (state : RightShadow A strategy hwin) :
    state.twoCandidate A strategy hwin initialBank true =
      state.leftOwner A strategy hwin initialBank := by
  simp [ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.twoCandidate]

@[simp] theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.oneCandidate_false
    (state : LeftShadow A strategy hwin) :
    state.oneCandidate A strategy hwin initialBank false =
      .exceptional
        (profiledRawJointGuardedCommonTailOneOfLeftReceiver A strategy hwin
          (state.resolvedLeft A strategy hwin)) := by
  simp [ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.oneCandidate]

@[simp] theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.oneCandidate_true
    (state : LeftShadow A strategy hwin) :
    state.oneCandidate A strategy hwin initialBank true =
      state.rightOwner A strategy hwin initialBank := by
  simp [ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.oneCandidate]

@[simp] theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.twoCandidate_false
    (state : LeftShadow A strategy hwin) :
    state.twoCandidate A strategy hwin initialBank false =
      (state.rebaseTwo A strategy hwin initialBank).2 := by
  simp [ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.twoCandidate]

@[simp] theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.twoCandidate_true
    (state : LeftShadow A strategy hwin) :
    state.twoCandidate A strategy hwin initialBank true =
      state.rightReceiver A strategy hwin initialBank := by
  simp [ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.twoCandidate]

/-! ## Resolution on the next receive -/

/-- A process-one right shadow is resolved solely from the shape of the
delivered finite carrier.  An exact partner means the preceding event was the
one-way `left` case; delivery of the same shadow means it was `both`.
The mismatched-shadow branch is an unreachable totalization. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.resolveOne
    (state : RightShadow A strategy hwin)
    (delivered :
      ProfiledRawJointGuardedCommonTailRightChargedNextTwo A strategy hwin
        initialBank) : OneControl A strategy hwin initialBank := by
  classical
  exact match delivered with
  | .inl _ => state.oneCandidate A strategy hwin initialBank false
  | .inr other =>
      if other = state then state.oneCandidate A strategy hwin initialBank true
      else state.oneCandidate A strategy hwin initialBank false

/-- Process-two mirror: an exact process-one carrier means the preceding
event was `right`; the same shadow means `both`. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.resolveTwo
    (state : RightShadow A strategy hwin)
    (delivered :
      ProfiledRawJointGuardedCommonTailRightChargedNextOne A strategy hwin
        initialBank) : TwoControl A strategy hwin initialBank := by
  classical
  exact match delivered with
  | .inl _ => state.twoCandidate A strategy hwin initialBank false
  | .inr other =>
      if other = state then state.twoCandidate A strategy hwin initialBank true
      else state.twoCandidate A strategy hwin initialBank false

noncomputable def
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.resolveOne
    (state : LeftShadow A strategy hwin)
    (delivered :
      ProfiledRawJointGuardedCommonTailLeftChargedNextTwo A strategy hwin
        initialBank) : OneControl A strategy hwin initialBank := by
  classical
  exact match delivered with
  | .inl _ => state.oneCandidate A strategy hwin initialBank false
  | .inr other =>
      if other = state then state.oneCandidate A strategy hwin initialBank true
      else state.oneCandidate A strategy hwin initialBank false

noncomputable def
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.resolveTwo
    (state : LeftShadow A strategy hwin)
    (delivered :
      ProfiledRawJointGuardedCommonTailLeftChargedNextOne A strategy hwin
        initialBank) : TwoControl A strategy hwin initialBank := by
  classical
  exact match delivered with
  | .inl _ => state.twoCandidate A strategy hwin initialBank false
  | .inr other =>
      if other = state then state.twoCandidate A strategy hwin initialBank true
      else state.twoCandidate A strategy hwin initialBank false

@[simp] theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.resolveOne_exact
    (state : RightShadow A strategy hwin)
    (exact : TwoControl A strategy hwin initialBank) :
    state.resolveOne A strategy hwin initialBank (.inl exact) =
      state.oneCandidate A strategy hwin initialBank false := by
  rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.resolveOne_same
    (state : RightShadow A strategy hwin) :
    state.resolveOne A strategy hwin initialBank (.inr state) =
      state.oneCandidate A strategy hwin initialBank true := by
  simp [ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.resolveOne]

@[simp] theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.resolveTwo_exact
    (state : RightShadow A strategy hwin)
    (exact : OneControl A strategy hwin initialBank) :
    state.resolveTwo A strategy hwin initialBank (.inl exact) =
      state.twoCandidate A strategy hwin initialBank false := by
  rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.resolveTwo_same
    (state : RightShadow A strategy hwin) :
    state.resolveTwo A strategy hwin initialBank (.inr state) =
      state.twoCandidate A strategy hwin initialBank true := by
  simp [ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.resolveTwo]

@[simp] theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.resolveOne_exact
    (state : LeftShadow A strategy hwin)
    (exact : TwoControl A strategy hwin initialBank) :
    state.resolveOne A strategy hwin initialBank (.inl exact) =
      state.oneCandidate A strategy hwin initialBank false := by
  rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.resolveOne_same
    (state : LeftShadow A strategy hwin) :
    state.resolveOne A strategy hwin initialBank (.inr state) =
      state.oneCandidate A strategy hwin initialBank true := by
  simp [ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.resolveOne]

@[simp] theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.resolveTwo_exact
    (state : LeftShadow A strategy hwin)
    (exact : OneControl A strategy hwin initialBank) :
    state.resolveTwo A strategy hwin initialBank (.inl exact) =
      state.twoCandidate A strategy hwin initialBank false := by
  rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.resolveTwo_same
    (state : LeftShadow A strategy hwin) :
    state.resolveTwo A strategy hwin initialBank (.inr state) =
      state.twoCandidate A strategy hwin initialBank true := by
  simp [ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.resolveTwo]

/-- Both local candidate tables are functions of the same single bit.  This
is the replace-not-accumulate invariant exposed at the switching seam. -/
theorem
    profiledRawJointGuardedCommonTailRightChargedCross_oneFreshAmbiguity
    (state : RightShadow A strategy hwin) :
    ∃ candidates : Bool →
        OneControl A strategy hwin initialBank ×
          TwoControl A strategy hwin initialBank,
      candidates = fun closed ↦
        (state.oneCandidate A strategy hwin initialBank closed,
          state.twoCandidate A strategy hwin initialBank closed) := by
  exact ⟨_, rfl⟩

theorem
    profiledRawJointGuardedCommonTailLeftChargedCross_oneFreshAmbiguity
    (state : LeftShadow A strategy hwin) :
    ∃ candidates : Bool →
        OneControl A strategy hwin initialBank ×
          TwoControl A strategy hwin initialBank,
      candidates = fun closed ↦
        (state.oneCandidate A strategy hwin initialBank closed,
          state.twoCandidate A strategy hwin initialBank closed) := by
  exact ⟨_, rfl⟩

end

end DetParityAutomaton

end DistributedSynthesis
