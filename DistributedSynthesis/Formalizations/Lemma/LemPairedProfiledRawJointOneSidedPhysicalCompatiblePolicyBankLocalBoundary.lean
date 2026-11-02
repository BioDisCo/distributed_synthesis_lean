/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankBlock
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingLocalInstallation
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredMemberControl

/-!
# Endpoint-local reversal data for the recurrent physical policy bank

The recurrent bank resolves a bare closing target to a linked successor of
the same accepting policy.  This file checks that this operation can be
placed on the informed side of a physical reversal without giving the blind
side a target or member oracle.

The informed endpoint stores a finite resolved packet consisting of the bare
target, its linked lift, and the resulting bank state.  Its receive-created
fork consists of an open staged-receiver branch carrying that packet and a
closed opposite-owner branch installed from the same packet.  The other
endpoint receives no target and its executable blind transition cannot read
the carrier's proof-side member.  If delivery is delayed, the two informed
branches take the same owner step, emit the same output, and coalesce.  At a
later delivery the other endpoint reads the delivered finite branch: the
staged branch retains its old receiver, whereas the owner branch constructs
the fresh simultaneous receiver.

The construction is total.  If the successor annotation has no table for the
new orientation, it reuses the old receiver's finite move as a fallback.  The
proof-side `some` hypotheses below show that this branch is not taken at a
legal reversal.  No executable definition receives a graph, orientation,
semantic source, history, reachability proof, or hidden member.
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
  ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
    (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)

/-! ## The finite packet computed by an informed closing receiver -/

/-- Runtime result of resolving one locally computed closing target. -/
structure ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget where
  target : ProfiledRawJointIncidenceCode A (I := Unit)
  childCode : LinkedCode A
  successor : BankControl A strategy hwin

noncomputable instance :
    Fintype
      (ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) := by
  classical
  let Rep :=
    ProfiledRawJointIncidenceCode A (I := Unit) × LinkedCode A ×
      BankControl A strategy hwin
  let equiv :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
          hwin ≃ Rep := {
    toFun := fun packet ↦
      (packet.target, packet.childCode, packet.successor)
    invFun := fun packet ↦ ⟨packet.1, packet.2.1, packet.2.2⟩
    left_inv := by intro packet; cases packet; rfl
    right_inv := by intro packet; cases packet; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Total receiver-side target resolution.  Its only non-control argument is
the target contained in the receiver's locally evaluated finite record. -/
noncomputable def
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
      hwin :=
  let childCode :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
      hwin state target
  ⟨target, childCode,
    profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
      state childCode⟩

/-- Process-two receives a right-block record and resolves one of its finite
row targets.  The target is computed from that record, not supplied as a
separate oracle. -/
noncomputable def
    profiledRawJointOneSidedPhysicalCompatibleBankResolveRightRecord
    (state : BankControl A strategy hwin)
    (record : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
      hwin :=
  profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy hwin
    state (record.target row)

/-- Process-one mirror for a locally evaluated left-block record. -/
noncomputable def
    profiledRawJointOneSidedPhysicalCompatibleBankResolveLeftRecord
    (state : BankControl A strategy hwin)
    (record : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
      hwin :=
  profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy hwin
    state (record.target row)

@[simp] theorem
    profiledRawJointOneSidedPhysicalCompatibleBankResolveRightRecord_target
    (state : BankControl A strategy hwin)
    (record : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    (profiledRawJointOneSidedPhysicalCompatibleBankResolveRightRecord A
      strategy hwin state record row).target = record.target row :=
  rfl

@[simp] theorem
    profiledRawJointOneSidedPhysicalCompatibleBankResolveLeftRecord_target
    (state : BankControl A strategy hwin)
    (record : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    (profiledRawJointOneSidedPhysicalCompatibleBankResolveLeftRecord A
      strategy hwin state record row).target = record.target row :=
  rfl

@[simp] theorem
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_target
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin state target).target = target :=
  rfl

@[simp] theorem
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_childCode
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin state target).childCode =
      profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
        hwin state target :=
  rfl

@[simp] theorem
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_successor
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin state target).successor =
      profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state
        (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
          strategy hwin state target) :=
  rfl

/-- On a legal installed-right-table target, the locally computed packet is
an exact same-policy transition and its successor remains reachable. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleBankResolveRightPacket_spec
    (state : BankControl A strategy hwin)
    (hreachable :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : state.2.1.2.1 = some move)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A move.1 target) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target
    packet.childCode.1 = target ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target packet.childCode ∧
      packet.successor.1 = state.1 ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        packet.successor := by
  dsimp only
  exact
    profiledRawJointOneSidedPhysicalCompatibleBankResolveRightTarget_spec A
      strategy hwin state hreachable currentCode hcurrentCode root hroot move
        hmove target htarget

/-- Left-orientation mirror. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleBankResolveLeftPacket_spec
    (state : BankControl A strategy hwin)
    (hreachable :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : state.2.1.2.2 = some move)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A move.1 target) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target
    packet.childCode.1 = target ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target packet.childCode ∧
      packet.successor.1 = state.1 ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        packet.successor := by
  dsimp only
  exact
    profiledRawJointOneSidedPhysicalCompatibleBankResolveLeftTarget_spec A
      strategy hwin state hreachable currentCode hcurrentCode root hroot move
        hmove target htarget

/-! ## The fallback is unreachable at a genuine reversal -/

/-- If an exact resolved target has a live left slot, its same-policy
successor contains a left physical move.  Thus a right-to-left reversal can
install its next owner directly from the resolved packet. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_leftMove_exists
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left target () =
      some root) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      packet.successor.2.1.2.2 = some move := by
  dsimp only
  let childCode :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
      hwin state target
  rcases hrealizes with
    ⟨linkedMove, source, actual, hcode, hsourceMove, _hcompatible,
      hchildren, hchildCode, hbare, hsuccessor⟩
  change childCode = sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.2.1 linkedMove actual at hchildCode
  change childCode.1 = target at hbare
  change
    (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
        state.1).successor state.2 childCode =
      (childCode,
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)
          (profiledRawJointOneSidedCodeParityDPA A state.1.1.1)).step
            state.2.2 childCode) at hsuccessor
  have hstepCode : (source.step A actual).code A = target := by
    calc
      (source.step A actual).code A = childCode.1 := by
        rw [ProfiledRawJointOneSidedSemanticState.step_code]
        rw [hcode, hsourceMove, hchildCode]
        rfl
      _ = target := hbare
  have hstepRoot :
      profiledRawJointOneSidedCurrentSlots A .left
          ((source.step A actual).code A) () = some root := by
    rw [hstepCode]
    exact hroot
  obtain ⟨semanticMember, hmember, _hrootShape, _hmemory⟩ :=
    (source.step A actual).exists_left_member_of_currentSlot A () root
      hstepRoot
  cases hside : actual.side with
  | left =>
      simp [ProfiledRawJointOneSidedSemanticState.step, hside,
        ProfiledRawJointSemanticFamily.leftActualChild] at hmember
  | right =>
      have hsemanticMember :
          (source.family.semanticChild A actual.direction).left () =
            some semanticMember := by
        simpa [ProfiledRawJointOneSidedSemanticState.step, hside,
          ProfiledRawJointSemanticFamily.rightActualChild] using hmember
      obtain ⟨move, hannotation, _hnextRoot⟩ :=
        profiledRawJointHybridPhysicalAnnotationOf_rightActual_liveRoot A
          strategy hwin source.family actual.direction semanticMember
            hsemanticMember
      have hchildAnnotation :
          childCode.2 =
            profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
              source.family actual.direction := by
        rw [hchildCode]
        change linkedMove.2 actual = _
        rw [← hchildren actual]
        rfl
      have hsuccessorData :
          (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
            hwin state childCode).2.1 = childCode := by
        exact congrArg Prod.fst hsuccessor
      have hsuccessorAnnotation :
          (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
            hwin state childCode).2.1.2 =
              profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
                source.family actual.direction := by
        exact (congrArg Prod.snd hsuccessorData).trans hchildAnnotation
      refine ⟨move, ?_⟩
      change
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
          hwin state childCode).2.1.2.2 = some move
      rw [hsuccessorAnnotation]
      exact hannotation

/-- Mirrored fact for a left-to-right reversal. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_rightMove_exists
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right target () =
      some root) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      packet.successor.2.1.2.1 = some move := by
  dsimp only
  let childCode :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
      hwin state target
  rcases hrealizes with
    ⟨linkedMove, source, actual, hcode, hsourceMove, _hcompatible,
      hchildren, hchildCode, hbare, hsuccessor⟩
  change childCode = sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.2.1 linkedMove actual at hchildCode
  change childCode.1 = target at hbare
  change
    (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
        state.1).successor state.2 childCode =
      (childCode,
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)
          (profiledRawJointOneSidedCodeParityDPA A state.1.1.1)).step
            state.2.2 childCode) at hsuccessor
  have hstepCode : (source.step A actual).code A = target := by
    calc
      (source.step A actual).code A = childCode.1 := by
        rw [ProfiledRawJointOneSidedSemanticState.step_code]
        rw [hcode, hsourceMove, hchildCode]
        rfl
      _ = target := hbare
  have hstepRoot :
      profiledRawJointOneSidedCurrentSlots A .right
          ((source.step A actual).code A) () = some root := by
    rw [hstepCode]
    exact hroot
  obtain ⟨semanticMember, hmember, _hrootShape, _hmemory⟩ :=
    (source.step A actual).exists_right_member_of_currentSlot A () root
      hstepRoot
  cases hside : actual.side with
  | right =>
      simp [ProfiledRawJointOneSidedSemanticState.step, hside,
        ProfiledRawJointSemanticFamily.rightActualChild] at hmember
  | left =>
      have hsemanticMember :
          (source.family.semanticChild A actual.direction).right () =
            some semanticMember := by
        simpa [ProfiledRawJointOneSidedSemanticState.step, hside,
          ProfiledRawJointSemanticFamily.leftActualChild] using hmember
      obtain ⟨move, hannotation, _hnextRoot⟩ :=
        profiledRawJointHybridPhysicalAnnotationOf_leftActual_liveRoot A
          strategy hwin source.family actual.direction semanticMember
            hsemanticMember
      have hchildAnnotation :
          childCode.2 =
            profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
              source.family actual.direction := by
        rw [hchildCode]
        change linkedMove.2 actual = _
        rw [← hchildren actual]
        rfl
      have hsuccessorData :
          (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
            hwin state childCode).2.1 = childCode := by
        exact congrArg Prod.fst hsuccessor
      have hsuccessorAnnotation :
          (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
            hwin state childCode).2.1.2 =
              profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
                source.family actual.direction := by
        exact (congrArg Prod.snd hsuccessorData).trans hchildAnnotation
      refine ⟨move, ?_⟩
      change
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
          hwin state childCode).2.1.2.1 = some move
      rw [hsuccessorAnnotation]
      exact hannotation

/-! ## Proof-side paired reversal data

The following two products are convenient certificates: each keeps a new
owner beside the old/new receiver fork whose correctness it explains.  They
are not endpoint controls, because the owner and receiver belong to opposite
endpoints.  The genuinely endpoint-local split is constructed below.
-/

/-! ### Right-to-left paired data -/

abbrev ProfiledRawJointRecurrentRightToLeftShared :=
  ProfiledRawJointLeftPhysicalSiblingExceptional A

abbrev ProfiledRawJointRecurrentRightToLeftPayload :=
  FiniteDelayedFork (ProfiledRawJointLeftPhysicalSiblingReceiver A)

abbrev ProfiledRawJointRecurrentRightToLeftPending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentRightToLeftShared A)
    (ProfiledRawJointRecurrentRightToLeftPayload A)

noncomputable instance :
    Fintype (ProfiledRawJointRecurrentRightToLeftPending A) := by
  classical
  infer_instance

/-- Read the newly installed left move, falling back to the old open
receiver's move only outside the legal reversal invariant. -/
noncomputable def profiledRawJointRecurrentRightToLeftMove
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldOpen : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    ProfiledRawJointLeftPhysicalSiblingMove A :=
  packet.successor.2.1.2.2.getD oldOpen.1

/-- The sole owner executed during the blind suffix is installed from the
new bank successor. -/
noncomputable def profiledRawJointRecurrentRightToLeftShared
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldOpen : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    ProfiledRawJointRecurrentRightToLeftShared A :=
  let move := profiledRawJointRecurrentRightToLeftMove A strategy hwin packet
    oldOpen
  ⟨move, (move.memberController A false).initial⟩

/-- The old open receiver has already advanced in the preceding table.  The
closed receiver is freshly rooted at the new successor table. -/
noncomputable def profiledRawJointRecurrentRightToLeftReceiverFork
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldOpen : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    ProfiledRawJointRecurrentRightToLeftPayload A :=
  let move := profiledRawJointRecurrentRightToLeftMove A strategy hwin packet
    oldOpen
  ⟨oldOpen, initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both⟩

/-- Canonical unresolved boundary fork.  Its member is the only differing
field; the new owner and the complete old/new receiver fork are shared. -/
noncomputable def profiledRawJointRecurrentRightToLeftPendingFork
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldOpen : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    FiniteDelayedFork (ProfiledRawJointRecurrentRightToLeftPending A) :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberFork
    (profiledRawJointRecurrentRightToLeftShared A strategy hwin packet oldOpen)
    (profiledRawJointRecurrentRightToLeftReceiverFork A strategy hwin packet
      oldOpen)

/-- A member-independent step on the proof-side paired certificate.  This is
not yet an endpoint control; the executable local step is defined below. -/
noncomputable def profiledRawJointRecurrentRightToLeftSharedStep
    (_member : Bool)
    (shared : ProfiledRawJointRecurrentRightToLeftShared A)
    (input : In₂) :
    ProfiledRawJointRecurrentRightToLeftShared A × Out₂ :=
  let next := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A shared.1
    false shared.2 input
  (⟨shared.1, next.2⟩, next.1)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRecurrentRightToLeftSharedStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentRightToLeftSharedStep A) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def profiledRawJointRecurrentRightToLeftNoRecv
    (pending : ProfiledRawJointRecurrentRightToLeftPending A)
    (input : In₂) :
    ProfiledRawJointRecurrentRightToLeftPending A × Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentRightToLeftSharedStep A) pending input

/-- The next receive activates exactly the receiver selected by the retained
member; it does not reconstruct a receiver from a target code. -/
def profiledRawJointRecurrentRightToLeftSelectedReceiver
    (pending : ProfiledRawJointRecurrentRightToLeftPending A) :
    ProfiledRawJointLeftPhysicalSiblingReceiver A :=
  pending.2.2.candidate pending.1

@[simp] theorem
    profiledRawJointRecurrentRightToLeftPendingFork_open_selected
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldOpen : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    profiledRawJointRecurrentRightToLeftSelectedReceiver A
        (profiledRawJointRecurrentRightToLeftPendingFork A strategy hwin packet
          oldOpen).openControl = oldOpen :=
  rfl

@[simp] theorem
    profiledRawJointRecurrentRightToLeftPendingFork_closed_selected
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldOpen : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    profiledRawJointRecurrentRightToLeftSelectedReceiver A
        (profiledRawJointRecurrentRightToLeftPendingFork A strategy hwin packet
          oldOpen).closedControl =
      initialProfiledRawJointLeftPhysicalSiblingReceiver A
        (profiledRawJointRecurrentRightToLeftMove A strategy hwin packet
          oldOpen) .both :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointRecurrentRightToLeftNoRecv_selectedReceiver
    (pending : ProfiledRawJointRecurrentRightToLeftPending A)
    (input : In₂) :
    profiledRawJointRecurrentRightToLeftSelectedReceiver A
        (profiledRawJointRecurrentRightToLeftNoRecv A pending input).1 =
      profiledRawJointRecurrentRightToLeftSelectedReceiver A pending :=
  rfl

/-- Execute an arbitrary blind suffix without exposing its retained member
or dormant receiver fork to the owner transition. -/
noncomputable def profiledRawJointRecurrentRightToLeftBlindRun
    (pending : ProfiledRawJointRecurrentRightToLeftPending A) :
    List In₂ → ProfiledRawJointRecurrentRightToLeftPending A
  | [] => pending
  | input :: rest =>
      profiledRawJointRecurrentRightToLeftBlindRun
        (profiledRawJointRecurrentRightToLeftNoRecv A pending input).1 rest

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- At every blind depth, the eventual receive selects exactly the same old
or new dormant receiver as at the reversal boundary. -/
theorem profiledRawJointRecurrentRightToLeftBlindRun_selectedReceiver
    (pending : ProfiledRawJointRecurrentRightToLeftPending A)
    (inputs : List In₂) :
    profiledRawJointRecurrentRightToLeftSelectedReceiver A
        (profiledRawJointRecurrentRightToLeftBlindRun A pending inputs) =
      profiledRawJointRecurrentRightToLeftSelectedReceiver A pending := by
  induction inputs generalizing pending with
  | nil => rfl
  | cons input rest ih =>
      rw [profiledRawJointRecurrentRightToLeftBlindRun]
      rw [ih]
      exact
        profiledRawJointRecurrentRightToLeftNoRecv_selectedReceiver A pending
          input

/-- Under the legal `some` case, the runtime fallback disappears and the
shared owner is exactly the new bank table's initial owner. -/
theorem profiledRawJointRecurrentRightToLeftShared_eq_of_move
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldOpen : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.2.2 = some move) :
    profiledRawJointRecurrentRightToLeftShared A strategy hwin packet
        oldOpen =
      ⟨move, (move.memberController A false).initial⟩ := by
  have hselected :
      profiledRawJointRecurrentRightToLeftMove A strategy hwin packet
        oldOpen = move := by
    unfold profiledRawJointRecurrentRightToLeftMove
    rw [hmove]
    rfl
  unfold profiledRawJointRecurrentRightToLeftShared
  rw [hselected]

/-! ### Left-to-right paired data -/

abbrev ProfiledRawJointRecurrentLeftToRightShared :=
  ProfiledRawJointRightPhysicalSiblingExceptional A

abbrev ProfiledRawJointRecurrentLeftToRightPayload :=
  FiniteDelayedFork (ProfiledRawJointRightPhysicalSiblingReceiver A)

abbrev ProfiledRawJointRecurrentLeftToRightPending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentLeftToRightShared A)
    (ProfiledRawJointRecurrentLeftToRightPayload A)

noncomputable instance :
    Fintype (ProfiledRawJointRecurrentLeftToRightPending A) := by
  classical
  infer_instance

noncomputable def profiledRawJointRecurrentLeftToRightMove
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldOpen : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    ProfiledRawJointRightPhysicalSiblingMove A :=
  packet.successor.2.1.2.1.getD oldOpen.1

noncomputable def profiledRawJointRecurrentLeftToRightShared
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldOpen : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    ProfiledRawJointRecurrentLeftToRightShared A :=
  let move := profiledRawJointRecurrentLeftToRightMove A strategy hwin packet
    oldOpen
  ⟨move, (move.memberController A false).initial⟩

noncomputable def profiledRawJointRecurrentLeftToRightReceiverFork
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldOpen : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    ProfiledRawJointRecurrentLeftToRightPayload A :=
  let move := profiledRawJointRecurrentLeftToRightMove A strategy hwin packet
    oldOpen
  ⟨oldOpen, initialProfiledRawJointRightPhysicalSiblingReceiver A move .both⟩

noncomputable def profiledRawJointRecurrentLeftToRightPendingFork
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldOpen : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    FiniteDelayedFork (ProfiledRawJointRecurrentLeftToRightPending A) :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberFork
    (profiledRawJointRecurrentLeftToRightShared A strategy hwin packet oldOpen)
    (profiledRawJointRecurrentLeftToRightReceiverFork A strategy hwin packet
      oldOpen)

noncomputable def profiledRawJointRecurrentLeftToRightSharedStep
    (_member : Bool)
    (shared : ProfiledRawJointRecurrentLeftToRightShared A)
    (input : In₁) :
    ProfiledRawJointRecurrentLeftToRightShared A × Out₁ :=
  let next := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A shared.1
    false shared.2 input
  (⟨shared.1, next.2⟩, next.1)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRecurrentLeftToRightSharedStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentLeftToRightSharedStep A) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def profiledRawJointRecurrentLeftToRightNoRecv
    (pending : ProfiledRawJointRecurrentLeftToRightPending A)
    (input : In₁) :
    ProfiledRawJointRecurrentLeftToRightPending A × Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentLeftToRightSharedStep A) pending input

def profiledRawJointRecurrentLeftToRightSelectedReceiver
    (pending : ProfiledRawJointRecurrentLeftToRightPending A) :
    ProfiledRawJointRightPhysicalSiblingReceiver A :=
  pending.2.2.candidate pending.1

@[simp] theorem
    profiledRawJointRecurrentLeftToRightPendingFork_open_selected
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldOpen : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    profiledRawJointRecurrentLeftToRightSelectedReceiver A
        (profiledRawJointRecurrentLeftToRightPendingFork A strategy hwin packet
          oldOpen).openControl = oldOpen :=
  rfl

@[simp] theorem
    profiledRawJointRecurrentLeftToRightPendingFork_closed_selected
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldOpen : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    profiledRawJointRecurrentLeftToRightSelectedReceiver A
        (profiledRawJointRecurrentLeftToRightPendingFork A strategy hwin packet
          oldOpen).closedControl =
      initialProfiledRawJointRightPhysicalSiblingReceiver A
        (profiledRawJointRecurrentLeftToRightMove A strategy hwin packet
          oldOpen) .both :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointRecurrentLeftToRightNoRecv_selectedReceiver
    (pending : ProfiledRawJointRecurrentLeftToRightPending A)
    (input : In₁) :
    profiledRawJointRecurrentLeftToRightSelectedReceiver A
        (profiledRawJointRecurrentLeftToRightNoRecv A pending input).1 =
      profiledRawJointRecurrentLeftToRightSelectedReceiver A pending :=
  rfl

noncomputable def profiledRawJointRecurrentLeftToRightBlindRun
    (pending : ProfiledRawJointRecurrentLeftToRightPending A) :
    List In₁ → ProfiledRawJointRecurrentLeftToRightPending A
  | [] => pending
  | input :: rest =>
      profiledRawJointRecurrentLeftToRightBlindRun
        (profiledRawJointRecurrentLeftToRightNoRecv A pending input).1 rest

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRecurrentLeftToRightBlindRun_selectedReceiver
    (pending : ProfiledRawJointRecurrentLeftToRightPending A)
    (inputs : List In₁) :
    profiledRawJointRecurrentLeftToRightSelectedReceiver A
        (profiledRawJointRecurrentLeftToRightBlindRun A pending inputs) =
      profiledRawJointRecurrentLeftToRightSelectedReceiver A pending := by
  induction inputs generalizing pending with
  | nil => rfl
  | cons input rest ih =>
      rw [profiledRawJointRecurrentLeftToRightBlindRun]
      rw [ih]
      exact
        profiledRawJointRecurrentLeftToRightNoRecv_selectedReceiver A pending
          input

theorem profiledRawJointRecurrentLeftToRightShared_eq_of_move
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldOpen : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.2.1 = some move) :
    profiledRawJointRecurrentLeftToRightShared A strategy hwin packet
        oldOpen =
      ⟨move, (move.memberController A false).initial⟩ := by
  have hselected :
      profiledRawJointRecurrentLeftToRightMove A strategy hwin packet
        oldOpen = move := by
    unfold profiledRawJointRecurrentLeftToRightMove
    rw [hmove]
    rfl
  unfold profiledRawJointRecurrentLeftToRightShared
  rw [hselected]

/-! ### Blind laws for the paired certificates -/

/-- The paired certificates have member-independent steps.  The local laws
used by the executable endpoint split are stated separately below. -/
noncomputable def profiledRawJointRecurrentPairedBoundaryBlindNoRecvLaws :
    FiniteAcknowledgedDelayedCarrier.BlindNoRecvLaws
      (profiledRawJointRecurrentLeftToRightNoRecv A)
      (profiledRawJointRecurrentRightToLeftNoRecv A)
      (FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind :
        ProfiledRawJointRecurrentLeftToRightPending A →
          ProfiledRawJointRecurrentLeftToRightPending A → Prop)
      (FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind :
        ProfiledRawJointRecurrentRightToLeftPending A →
          ProfiledRawJointRecurrentRightToLeftPending A → Prop) where
  one :=
    FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
      (profiledRawJointRecurrentLeftToRightSharedStep A)
      (profiledRawJointRecurrentLeftToRightSharedStep_laws A)
  two :=
    FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
      (profiledRawJointRecurrentRightToLeftSharedStep A)
      (profiledRawJointRecurrentRightToLeftSharedStep_laws A)

/-! ## Complementary deferred state at the other endpoint

At a simultaneous/strict ambiguity, the other endpoint cannot see the target
resolved by the receiver.  Its two carrier candidates therefore retain a
proof-side member bit, the same old owner, and the same old receiver; the bit
is not an oracle available to the executable owner step.  A blind suffix
advances only that old owner.  At a later delivery, the selected candidate
and the delivered informed bridge together choose the old receiver or create
the fresh receiver.  The informed endpoint's complementary staged/owner
bridge is defined in the next section.
-/

/-! ### Right-to-left: blind process one, informed process two -/

abbrev ProfiledRawJointRecurrentRightToLeftBlindShared :=
  ProfiledRawJointRightPhysicalSiblingExceptional A

abbrev ProfiledRawJointRecurrentRightToLeftBlindPayload :=
  ProfiledRawJointLeftPhysicalSiblingReceiver A

abbrev ProfiledRawJointRecurrentRightToLeftBlindControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentRightToLeftBlindShared A)
    (ProfiledRawJointRecurrentRightToLeftBlindPayload A)

/-- The informed endpoint keeps the resolved packet and the new left owner,
if that owner exists.  Both fields are computed from its local closing
record. -/
abbrev ProfiledRawJointRecurrentRightToLeftInformedControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
      hwin ×
    Option (ProfiledRawJointLeftPhysicalSiblingExceptional A)

noncomputable instance :
    Fintype (ProfiledRawJointRecurrentRightToLeftBlindControl A) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentRightToLeftInformedControl A strategy hwin) := by
  classical
  infer_instance

/-- Install the informed endpoint directly from its locally resolved packet.
The optional branch makes the finite definition total; the live-target
theorems below prove that a legal reversal produces `some`. -/
noncomputable def profiledRawJointRecurrentRightToLeftInformedOfPacket
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) :
    ProfiledRawJointRecurrentRightToLeftInformedControl A strategy hwin :=
  (packet, packet.successor.2.1.2.2.map fun move =>
    ⟨move, (move.memberController A false).initial⟩)

/-- The blind endpoint's canonical unresolved fork contains no resolved
target, linked code, bank successor, or new owner. -/
def profiledRawJointRecurrentRightToLeftBlindFork
    (oldOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    FiniteDelayedFork
      (ProfiledRawJointRecurrentRightToLeftBlindControl A) :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberFork oldOwner oldReceiver

/-- During a blind suffix process one advances only its old right owner from
its private input.  The unresolved member and old receiver are retained. -/
noncomputable def profiledRawJointRecurrentRightToLeftBlindSharedStep
    (_member : Bool)
    (shared : ProfiledRawJointRecurrentRightToLeftBlindShared A)
    (input : In₁) :
    ProfiledRawJointRecurrentRightToLeftBlindShared A × Out₁ :=
  let next := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A shared.1
    false shared.2 input
  (⟨shared.1, next.2⟩, next.1)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRecurrentRightToLeftBlindSharedStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentRightToLeftBlindSharedStep A) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def profiledRawJointRecurrentRightToLeftBlindNoRecv
    (control : ProfiledRawJointRecurrentRightToLeftBlindControl A)
    (input : In₁) :
    ProfiledRawJointRecurrentRightToLeftBlindControl A × Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentRightToLeftBlindSharedStep A) control input

/-- Once its control is delivered, process two advances its new left owner
using only its own input.  The resolved packet is retained for receiver
installation at the partner. -/
noncomputable def profiledRawJointRecurrentRightToLeftInformedNoRecv
    (control :
      ProfiledRawJointRecurrentRightToLeftInformedControl A strategy hwin)
    (input : In₂) :
    ProfiledRawJointRecurrentRightToLeftInformedControl A strategy hwin ×
      Out₂ :=
  match control.2 with
  | none => (control, default)
  | some owner =>
      let next := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A
        owner.1 false owner.2 input
      ((control.1, some ⟨owner.1, next.2⟩), next.1)

@[simp] theorem
    profiledRawJointRecurrentRightToLeftInformedNoRecv_packet
    (control :
      ProfiledRawJointRecurrentRightToLeftInformedControl A strategy hwin)
    (input : In₂) :
    (profiledRawJointRecurrentRightToLeftInformedNoRecv A strategy hwin
      control input).1.1 = control.1 := by
  rcases control with ⟨packet, owner⟩
  cases owner <;> rfl

/-- At the next receive, an open member retains the old receiver.  A closed
member obtains the new owner from the delivered informed control and creates
the fresh receiver at that moment. -/
noncomputable def profiledRawJointRecurrentRightToLeftSelectReceiver
    (blind : ProfiledRawJointRecurrentRightToLeftBlindControl A)
    (informed :
      ProfiledRawJointRecurrentRightToLeftInformedControl A strategy hwin) :
    ProfiledRawJointLeftPhysicalSiblingReceiver A :=
  if blind.1 then
    match informed.2 with
    | none => blind.2.2
    | some owner =>
        initialProfiledRawJointLeftPhysicalSiblingReceiver A owner.1 .both
  else
    blind.2.2

@[simp] theorem
    profiledRawJointRecurrentRightToLeftSelectReceiver_open
    (oldOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (informed :
      ProfiledRawJointRecurrentRightToLeftInformedControl A strategy hwin) :
    profiledRawJointRecurrentRightToLeftSelectReceiver A strategy hwin
        (profiledRawJointRecurrentRightToLeftBlindFork A oldOwner
          oldReceiver).openControl informed =
      oldReceiver :=
  rfl

theorem profiledRawJointRecurrentRightToLeftInformedOfPacket_owner_of_move
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.2.2 = some move) :
    (profiledRawJointRecurrentRightToLeftInformedOfPacket A strategy hwin
      packet).2 = some ⟨move, (move.memberController A false).initial⟩ := by
  simp [profiledRawJointRecurrentRightToLeftInformedOfPacket, hmove]

theorem profiledRawJointRecurrentRightToLeftSelectReceiver_closed_of_move
    (oldOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.2.2 = some move) :
    profiledRawJointRecurrentRightToLeftSelectReceiver A strategy hwin
        (profiledRawJointRecurrentRightToLeftBlindFork A oldOwner
          oldReceiver).closedControl
        (profiledRawJointRecurrentRightToLeftInformedOfPacket A strategy hwin
          packet) =
      initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both := by
  simp [profiledRawJointRecurrentRightToLeftSelectReceiver,
    profiledRawJointRecurrentRightToLeftBlindFork,
    profiledRawJointRecurrentRightToLeftInformedOfPacket, hmove]

noncomputable def profiledRawJointRecurrentRightToLeftLocalBlindRun
    (control : ProfiledRawJointRecurrentRightToLeftBlindControl A) :
    List In₁ → ProfiledRawJointRecurrentRightToLeftBlindControl A
  | [] => control
  | input :: rest =>
      profiledRawJointRecurrentRightToLeftLocalBlindRun
        (profiledRawJointRecurrentRightToLeftBlindNoRecv A control input).1
        rest

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledRawJointRecurrentRightToLeftBlindNoRecv_member
    (control : ProfiledRawJointRecurrentRightToLeftBlindControl A)
    (input : In₁) :
    (profiledRawJointRecurrentRightToLeftBlindNoRecv A control input).1.1 =
      control.1 :=
  rfl

@[simp] theorem profiledRawJointRecurrentRightToLeftBlindNoRecv_payload
    (control : ProfiledRawJointRecurrentRightToLeftBlindControl A)
    (input : In₁) :
    (profiledRawJointRecurrentRightToLeftBlindNoRecv A control input).1.2.2 =
      control.2.2 :=
  rfl

theorem profiledRawJointRecurrentRightToLeftLocalBlindRun_member
    (control : ProfiledRawJointRecurrentRightToLeftBlindControl A)
    (inputs : List In₁) :
    (profiledRawJointRecurrentRightToLeftLocalBlindRun A control inputs).1 =
      control.1 := by
  induction inputs generalizing control with
  | nil => rfl
  | cons input rest ih =>
      rw [profiledRawJointRecurrentRightToLeftLocalBlindRun, ih]
      rfl

theorem profiledRawJointRecurrentRightToLeftLocalBlindRun_payload
    (control : ProfiledRawJointRecurrentRightToLeftBlindControl A)
    (inputs : List In₁) :
    (profiledRawJointRecurrentRightToLeftLocalBlindRun A control inputs).2.2 =
      control.2.2 := by
  induction inputs generalizing control with
  | nil => rfl
  | cons input rest ih =>
      rw [profiledRawJointRecurrentRightToLeftLocalBlindRun, ih]
      rfl

end

theorem profiledRawJointRecurrentRightToLeftLocalBlindRun_selectReceiver
    (control : ProfiledRawJointRecurrentRightToLeftBlindControl A)
    (inputs : List In₁)
    (informed :
      ProfiledRawJointRecurrentRightToLeftInformedControl A strategy hwin) :
    profiledRawJointRecurrentRightToLeftSelectReceiver A strategy hwin
        (profiledRawJointRecurrentRightToLeftLocalBlindRun A control inputs)
        informed =
      profiledRawJointRecurrentRightToLeftSelectReceiver A strategy hwin
        control informed := by
  unfold profiledRawJointRecurrentRightToLeftSelectReceiver
  rw [profiledRawJointRecurrentRightToLeftLocalBlindRun_member A control inputs]
  rw [profiledRawJointRecurrentRightToLeftLocalBlindRun_payload A control inputs]

/-- At a legal right-to-left reversal the informed control contains an
actual new left owner.  In particular, the total `none` branch is
unreachable. -/
theorem
    profiledRawJointRecurrentRightToLeftInformedOfResolvePacket_owner_exists
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left target () =
      some root) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      (profiledRawJointRecurrentRightToLeftInformedOfPacket A strategy hwin
        packet).2 =
        some ⟨move, (move.memberController A false).initial⟩ := by
  dsimp only
  obtain ⟨move, hmove⟩ :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_leftMove_exists
      A strategy hwin state target hrealizes root hroot
  exact ⟨move,
    profiledRawJointRecurrentRightToLeftInformedOfPacket_owner_of_move A
      strategy hwin _ move hmove⟩

/-- The result survives every blind prefix: once the informed control is
delivered, the closed branch constructs the fresh left receiver rooted at
the bank successor. -/
theorem
    profiledRawJointRecurrentRightToLeftLocalBlindRun_closed_selects_fresh
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left target () =
      some root)
    (oldOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (inputs : List In₁) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      profiledRawJointRecurrentRightToLeftSelectReceiver A strategy hwin
          (profiledRawJointRecurrentRightToLeftLocalBlindRun A
            (profiledRawJointRecurrentRightToLeftBlindFork A oldOwner
              oldReceiver).closedControl inputs)
          (profiledRawJointRecurrentRightToLeftInformedOfPacket A strategy hwin
            packet) =
        initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both := by
  dsimp only
  obtain ⟨move, hmove⟩ :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_leftMove_exists
      A strategy hwin state target hrealizes root hroot
  refine ⟨move, ?_⟩
  rw [profiledRawJointRecurrentRightToLeftLocalBlindRun_selectReceiver A
    strategy hwin]
  exact
    profiledRawJointRecurrentRightToLeftSelectReceiver_closed_of_move A
      strategy hwin oldOwner oldReceiver _ move hmove

/-! ### Left-to-right: blind process two, informed process one -/

abbrev ProfiledRawJointRecurrentLeftToRightBlindShared :=
  ProfiledRawJointLeftPhysicalSiblingExceptional A

abbrev ProfiledRawJointRecurrentLeftToRightBlindPayload :=
  ProfiledRawJointRightPhysicalSiblingReceiver A

abbrev ProfiledRawJointRecurrentLeftToRightBlindControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentLeftToRightBlindShared A)
    (ProfiledRawJointRecurrentLeftToRightBlindPayload A)

abbrev ProfiledRawJointRecurrentLeftToRightInformedControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
      hwin ×
    Option (ProfiledRawJointRightPhysicalSiblingExceptional A)

noncomputable instance :
    Fintype (ProfiledRawJointRecurrentLeftToRightBlindControl A) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentLeftToRightInformedControl A strategy hwin) := by
  classical
  infer_instance

noncomputable def profiledRawJointRecurrentLeftToRightInformedOfPacket
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) :
    ProfiledRawJointRecurrentLeftToRightInformedControl A strategy hwin :=
  (packet, packet.successor.2.1.2.1.map fun move =>
    ⟨move, (move.memberController A false).initial⟩)

def profiledRawJointRecurrentLeftToRightBlindFork
    (oldOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    FiniteDelayedFork
      (ProfiledRawJointRecurrentLeftToRightBlindControl A) :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberFork oldOwner oldReceiver

noncomputable def profiledRawJointRecurrentLeftToRightBlindSharedStep
    (_member : Bool)
    (shared : ProfiledRawJointRecurrentLeftToRightBlindShared A)
    (input : In₂) :
    ProfiledRawJointRecurrentLeftToRightBlindShared A × Out₂ :=
  let next := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A shared.1
    false shared.2 input
  (⟨shared.1, next.2⟩, next.1)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRecurrentLeftToRightBlindSharedStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentLeftToRightBlindSharedStep A) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def profiledRawJointRecurrentLeftToRightBlindNoRecv
    (control : ProfiledRawJointRecurrentLeftToRightBlindControl A)
    (input : In₂) :
    ProfiledRawJointRecurrentLeftToRightBlindControl A × Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentLeftToRightBlindSharedStep A) control input

noncomputable def profiledRawJointRecurrentLeftToRightInformedNoRecv
    (control :
      ProfiledRawJointRecurrentLeftToRightInformedControl A strategy hwin)
    (input : In₁) :
    ProfiledRawJointRecurrentLeftToRightInformedControl A strategy hwin ×
      Out₁ :=
  match control.2 with
  | none => (control, default)
  | some owner =>
      let next := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A
        owner.1 false owner.2 input
      ((control.1, some ⟨owner.1, next.2⟩), next.1)

@[simp] theorem
    profiledRawJointRecurrentLeftToRightInformedNoRecv_packet
    (control :
      ProfiledRawJointRecurrentLeftToRightInformedControl A strategy hwin)
    (input : In₁) :
    (profiledRawJointRecurrentLeftToRightInformedNoRecv A strategy hwin
      control input).1.1 = control.1 := by
  rcases control with ⟨packet, owner⟩
  cases owner <;> rfl

noncomputable def profiledRawJointRecurrentLeftToRightSelectReceiver
    (blind : ProfiledRawJointRecurrentLeftToRightBlindControl A)
    (informed :
      ProfiledRawJointRecurrentLeftToRightInformedControl A strategy hwin) :
    ProfiledRawJointRightPhysicalSiblingReceiver A :=
  if blind.1 then
    match informed.2 with
    | none => blind.2.2
    | some owner =>
        initialProfiledRawJointRightPhysicalSiblingReceiver A owner.1 .both
  else
    blind.2.2

@[simp] theorem
    profiledRawJointRecurrentLeftToRightSelectReceiver_open
    (oldOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (informed :
      ProfiledRawJointRecurrentLeftToRightInformedControl A strategy hwin) :
    profiledRawJointRecurrentLeftToRightSelectReceiver A strategy hwin
        (profiledRawJointRecurrentLeftToRightBlindFork A oldOwner
          oldReceiver).openControl informed =
      oldReceiver :=
  rfl

theorem profiledRawJointRecurrentLeftToRightInformedOfPacket_owner_of_move
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.2.1 = some move) :
    (profiledRawJointRecurrentLeftToRightInformedOfPacket A strategy hwin
      packet).2 = some ⟨move, (move.memberController A false).initial⟩ := by
  simp [profiledRawJointRecurrentLeftToRightInformedOfPacket, hmove]

theorem profiledRawJointRecurrentLeftToRightSelectReceiver_closed_of_move
    (oldOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.2.1 = some move) :
    profiledRawJointRecurrentLeftToRightSelectReceiver A strategy hwin
        (profiledRawJointRecurrentLeftToRightBlindFork A oldOwner
          oldReceiver).closedControl
        (profiledRawJointRecurrentLeftToRightInformedOfPacket A strategy hwin
          packet) =
      initialProfiledRawJointRightPhysicalSiblingReceiver A move .both := by
  simp [profiledRawJointRecurrentLeftToRightSelectReceiver,
    profiledRawJointRecurrentLeftToRightBlindFork,
    profiledRawJointRecurrentLeftToRightInformedOfPacket, hmove]

noncomputable def profiledRawJointRecurrentLeftToRightLocalBlindRun
    (control : ProfiledRawJointRecurrentLeftToRightBlindControl A) :
    List In₂ → ProfiledRawJointRecurrentLeftToRightBlindControl A
  | [] => control
  | input :: rest =>
      profiledRawJointRecurrentLeftToRightLocalBlindRun
        (profiledRawJointRecurrentLeftToRightBlindNoRecv A control input).1
        rest

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledRawJointRecurrentLeftToRightBlindNoRecv_member
    (control : ProfiledRawJointRecurrentLeftToRightBlindControl A)
    (input : In₂) :
    (profiledRawJointRecurrentLeftToRightBlindNoRecv A control input).1.1 =
      control.1 :=
  rfl

@[simp] theorem profiledRawJointRecurrentLeftToRightBlindNoRecv_payload
    (control : ProfiledRawJointRecurrentLeftToRightBlindControl A)
    (input : In₂) :
    (profiledRawJointRecurrentLeftToRightBlindNoRecv A control input).1.2.2 =
      control.2.2 :=
  rfl

theorem profiledRawJointRecurrentLeftToRightLocalBlindRun_member
    (control : ProfiledRawJointRecurrentLeftToRightBlindControl A)
    (inputs : List In₂) :
    (profiledRawJointRecurrentLeftToRightLocalBlindRun A control inputs).1 =
      control.1 := by
  induction inputs generalizing control with
  | nil => rfl
  | cons input rest ih =>
      rw [profiledRawJointRecurrentLeftToRightLocalBlindRun, ih]
      rfl

theorem profiledRawJointRecurrentLeftToRightLocalBlindRun_payload
    (control : ProfiledRawJointRecurrentLeftToRightBlindControl A)
    (inputs : List In₂) :
    (profiledRawJointRecurrentLeftToRightLocalBlindRun A control inputs).2.2 =
      control.2.2 := by
  induction inputs generalizing control with
  | nil => rfl
  | cons input rest ih =>
      rw [profiledRawJointRecurrentLeftToRightLocalBlindRun, ih]
      rfl

end

theorem profiledRawJointRecurrentLeftToRightLocalBlindRun_selectReceiver
    (control : ProfiledRawJointRecurrentLeftToRightBlindControl A)
    (inputs : List In₂)
    (informed :
      ProfiledRawJointRecurrentLeftToRightInformedControl A strategy hwin) :
    profiledRawJointRecurrentLeftToRightSelectReceiver A strategy hwin
        (profiledRawJointRecurrentLeftToRightLocalBlindRun A control inputs)
        informed =
      profiledRawJointRecurrentLeftToRightSelectReceiver A strategy hwin
        control informed := by
  unfold profiledRawJointRecurrentLeftToRightSelectReceiver
  rw [profiledRawJointRecurrentLeftToRightLocalBlindRun_member A control inputs]
  rw [profiledRawJointRecurrentLeftToRightLocalBlindRun_payload A control inputs]

/-- Mirrored non-fallback result for a legal left-to-right reversal. -/
theorem
    profiledRawJointRecurrentLeftToRightInformedOfResolvePacket_owner_exists
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right target () =
      some root) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      (profiledRawJointRecurrentLeftToRightInformedOfPacket A strategy hwin
        packet).2 =
        some ⟨move, (move.memberController A false).initial⟩ := by
  dsimp only
  obtain ⟨move, hmove⟩ :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_rightMove_exists
      A strategy hwin state target hrealizes root hroot
  exact ⟨move,
    profiledRawJointRecurrentLeftToRightInformedOfPacket_owner_of_move A
      strategy hwin _ move hmove⟩

/-- Mirrored arbitrary-prefix receive selection. -/
theorem
    profiledRawJointRecurrentLeftToRightLocalBlindRun_closed_selects_fresh
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right target () =
      some root)
    (oldOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (inputs : List In₂) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      profiledRawJointRecurrentLeftToRightSelectReceiver A strategy hwin
          (profiledRawJointRecurrentLeftToRightLocalBlindRun A
            (profiledRawJointRecurrentLeftToRightBlindFork A oldOwner
              oldReceiver).closedControl inputs)
          (profiledRawJointRecurrentLeftToRightInformedOfPacket A strategy hwin
            packet) =
        initialProfiledRawJointRightPhysicalSiblingReceiver A move .both := by
  dsimp only
  obtain ⟨move, hmove⟩ :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_rightMove_exists
      A strategy hwin state target hrealizes root hroot
  refine ⟨move, ?_⟩
  rw [profiledRawJointRecurrentLeftToRightLocalBlindRun_selectReceiver A
    strategy hwin]
  exact
    profiledRawJointRecurrentLeftToRightSelectReceiver_closed_of_move A
      strategy hwin oldOwner oldReceiver _ move hmove

/-! ### Local blind-output coherence -/

/-- Blind laws for the deferred endpoint in the two reversal orientations. -/
noncomputable def profiledRawJointRecurrentBoundaryBlindNoRecvLaws :
    FiniteAcknowledgedDelayedCarrier.BlindNoRecvLaws
      (profiledRawJointRecurrentRightToLeftBlindNoRecv A)
      (profiledRawJointRecurrentLeftToRightBlindNoRecv A)
      (FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind :
        ProfiledRawJointRecurrentRightToLeftBlindControl A →
          ProfiledRawJointRecurrentRightToLeftBlindControl A → Prop)
      (FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind :
        ProfiledRawJointRecurrentLeftToRightBlindControl A →
          ProfiledRawJointRecurrentLeftToRightBlindControl A → Prop) where
  one :=
    FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
      (profiledRawJointRecurrentRightToLeftBlindSharedStep A)
      (profiledRawJointRecurrentRightToLeftBlindSharedStep_laws A)
  two :=
    FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
      (profiledRawJointRecurrentLeftToRightBlindSharedStep A)
      (profiledRawJointRecurrentLeftToRightBlindSharedStep_laws A)

/-! ## Actual informed-endpoint reversal bridge

At a strict right receive, process two owns the unresolved fork.  Its open
branch is a right-receiver descriptor containing the locally resolved packet;
its closed branch is the left owner installed from that packet.  A further
process-two no-receive starts exactly that same left owner in either branch.
Thus the outputs agree and the branches coalesce.  Process one carries no
member and learns the branch only from a later delivered control.  The mirror
statement holds at a strict left receive.
-/

/-! ### Right-to-left bridge on process two -/

abbrev ProfiledRawJointRecurrentRightToLeftStagedReceiver :=
  BankControl A strategy hwin ×
    ProfiledRawJointRightPhysicalSiblingReceiver A ×
      Option
        (ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A
          strategy hwin)

/-- Installed left-owner mode.  It retains the successor bank state and the
right receiver which becomes dormant at this reversal. -/
abbrev ProfiledRawJointRecurrentRightToLeftInstalledOwner :=
  BankControl A strategy hwin ×
    ProfiledRawJointLeftPhysicalSiblingExceptional A ×
      ProfiledRawJointRightPhysicalSiblingReceiver A

abbrev ProfiledRawJointRecurrentRightToLeftBridgeControl :=
  ProfiledRawJointRecurrentRightToLeftStagedReceiver A strategy hwin ⊕
    ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentRightToLeftStagedReceiver A strategy hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin) := by
  classical
  infer_instance

/-- Stage a packet already computed from the informed endpoint's current
record. -/
def profiledRawJointRecurrentRightToLeftStagePacket
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) :
    ProfiledRawJointRecurrentRightToLeftStagedReceiver A strategy hwin :=
  (state, receiver, some packet)

/-- The record-facing version makes explicit that the target is read from a
finite receiver output at the informed endpoint. -/
noncomputable def profiledRawJointRecurrentRightToLeftStageRecord
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (record : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    ProfiledRawJointRecurrentRightToLeftStagedReceiver A strategy hwin :=
  profiledRawJointRecurrentRightToLeftStagePacket A strategy hwin state receiver
    (profiledRawJointOneSidedPhysicalCompatibleBankResolveRightRecord A
      strategy hwin state record row)

/-- Total no-receive transition on the actual process-two bridge.  Missing
packets or missing left lanes are unreachable totalization cases. -/
noncomputable def profiledRawJointRecurrentRightToLeftBridgeNoRecv
    (control :
      ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin)
    (input : In₂) :
    ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin × Out₂ :=
  match control with
  | .inl staged =>
      match staged.2.2 with
      | none => (.inl staged, default)
      | some packet =>
          match packet.successor.2.1.2.2 with
          | none => (.inl staged, default)
          | some move =>
              let next := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep
                A move false (move.memberController A false).initial input
              (.inr
                (packet.successor, ⟨move, next.2⟩, staged.2.1), next.1)
  | .inr installed =>
      let owner := installed.2.1
      let next := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A
        owner.1 false owner.2 input
      (.inr (installed.1, ⟨owner.1, next.2⟩, installed.2.2), next.1)

/-- Exact relation between the open staged descriptor and the simultaneous
new owner.  After one blind step the two branches are literally equal. -/
inductive ProfiledRawJointRecurrentRightToLeftBridgeBlind :
    ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin →
      ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin → Prop
  | staged
      (state : BankControl A strategy hwin)
      (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
      (packet :
        ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A
          strategy hwin)
      (move : ProfiledRawJointLeftPhysicalSiblingMove A)
      (hmove : packet.successor.2.1.2.2 = some move) :
      ProfiledRawJointRecurrentRightToLeftBridgeBlind
        (.inl
          (profiledRawJointRecurrentRightToLeftStagePacket A strategy hwin
            state receiver packet))
        (.inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩, receiver))
  | recurrent
      (installed :
        ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin) :
      ProfiledRawJointRecurrentRightToLeftBridgeBlind
        (.inr installed) (.inr installed)

theorem profiledRawJointRecurrentRightToLeftBridgeBlind_noRecv
    (left right :
      ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin)
    (input : In₂)
    (hblind : ProfiledRawJointRecurrentRightToLeftBridgeBlind A strategy hwin
      left right) :
    (profiledRawJointRecurrentRightToLeftBridgeNoRecv A strategy hwin left
        input).2 =
        (profiledRawJointRecurrentRightToLeftBridgeNoRecv A strategy hwin right
          input).2 ∧
      ProfiledRawJointRecurrentRightToLeftBridgeBlind A strategy hwin
        (profiledRawJointRecurrentRightToLeftBridgeNoRecv A strategy hwin left
          input).1
        (profiledRawJointRecurrentRightToLeftBridgeNoRecv A strategy hwin right
          input).1 := by
  cases hblind with
  | staged state receiver packet move hmove =>
      simp only [profiledRawJointRecurrentRightToLeftBridgeNoRecv,
        profiledRawJointRecurrentRightToLeftStagePacket, hmove]
      exact ⟨trivial, .recurrent _⟩
  | recurrent installed =>
      exact ⟨rfl, .recurrent _⟩

/-- A locally staged legal target creates precisely the non-vacuous
open/closed blind pair required at a right-to-left receive. -/
theorem profiledRawJointRecurrentRightToLeftStagePacket_blind
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left target () =
      some root) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      ProfiledRawJointRecurrentRightToLeftBridgeBlind A strategy hwin
        (.inl
          (profiledRawJointRecurrentRightToLeftStagePacket A strategy hwin
            state receiver packet))
        (.inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩, receiver)) := by
  dsimp only
  obtain ⟨move, hmove⟩ :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_leftMove_exists
      A strategy hwin state target hrealizes root hroot
  exact ⟨move, .staged state receiver _ move hmove⟩

/-- Record-facing form: the finite closing record itself creates the exact
staged/owner blind pair. -/
theorem profiledRawJointRecurrentRightToLeftStageRecord_blind
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (record : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow)
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state (record.target row)
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state (record.target row)))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left
      (record.target row) () = some root) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      ProfiledRawJointRecurrentRightToLeftBridgeBlind A strategy hwin
        (.inl
          (profiledRawJointRecurrentRightToLeftStageRecord A strategy hwin
            state receiver record row))
        (.inr
          ((profiledRawJointOneSidedPhysicalCompatibleBankResolveRightRecord A
              strategy hwin state record row).successor,
            ⟨move, (move.memberController A false).initial⟩, receiver)) := by
  simpa [profiledRawJointRecurrentRightToLeftStageRecord,
    profiledRawJointOneSidedPhysicalCompatibleBankResolveRightRecord] using
    (profiledRawJointRecurrentRightToLeftStagePacket_blind A strategy hwin
      state receiver (record.target row) hrealizes root hroot)

/-! #### The genuine aligned right-receiver step -/

/-- Advance one installed right receiver from its matching delivered owner,
then resolve and stage the target emitted in that same local record. -/
noncomputable def profiledRawJointRecurrentRightReceiveFor
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    ProfiledRawJointRecurrentRightToLeftStagedReceiver A strategy hwin ×
      Out₂ :=
  let next := stepProfiledRawJointRightPhysicalSiblingReceiverFor A receiver.1
    owner receiver.2.1 receiver.2.2.1 input
  match next.2.2.2.2 with
  | none => ((state, next.2, none), next.1)
  | some target =>
      ((state, next.2,
        some
          (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A
            strategy hwin state target)), next.1)

@[simp] theorem profiledRawJointRecurrentRightReceiveFor_packet
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    (profiledRawJointRecurrentRightReceiveFor A strategy hwin state receiver
      owner input).1.2.2 =
      some
        (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A
          strategy hwin state
          (((receiver.1.memberController A false).labelOf owner).2
            receiver.2.2.1 input |>.target receiver.2.1)) :=
  rfl

@[simp] theorem profiledRawJointRecurrentRightReceiveFor_receiver
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    (profiledRawJointRecurrentRightReceiveFor A strategy hwin state receiver
      owner input).1.2.1 =
      (stepProfiledRawJointRightPhysicalSiblingReceiverFor A receiver.1 owner
        receiver.2.1 receiver.2.2.1 input).2 :=
  rfl

@[simp] theorem profiledRawJointRecurrentRightReceiveFor_output
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    (profiledRawJointRecurrentRightReceiveFor A strategy hwin state receiver
      owner input).2 =
      (stepProfiledRawJointRightPhysicalSiblingReceiverFor A receiver.1 owner
        receiver.2.1 receiver.2.2.1 input).1 :=
  rfl

/-- If the target emitted by the aligned receive is an exact live child, that
very receive creates the staged/installed blind pair.  The closed branch
retains the receiver advanced by the open branch. -/
theorem profiledRawJointRecurrentRightReceiveFor_blind
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : target =
      (((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input |>.target receiver.2.1))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left target () =
      some root) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      let next := profiledRawJointRecurrentRightReceiveFor A strategy hwin
        state receiver owner input
      let packet :=
        profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
          hwin state target
      ProfiledRawJointRecurrentRightToLeftBridgeBlind A strategy hwin
        (.inl next.1)
        (.inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩, next.1.2.1)) := by
  subst target
  let next := stepProfiledRawJointRightPhysicalSiblingReceiverFor A receiver.1
    owner receiver.2.1 receiver.2.2.1 input
  simpa [profiledRawJointRecurrentRightReceiveFor, next] using
    (profiledRawJointRecurrentRightToLeftStagePacket_blind A strategy hwin
      state next.2
      ((((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input).target receiver.2.1) hrealizes root hroot)

/-- The endpoint that did not receive needs only its old receiver.  A later
delivered staged control selects that old continuation; a delivered new owner
constructs the fresh simultaneous receiver. -/
noncomputable def profiledRawJointRecurrentRightToLeftDeliveredReceiver
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (delivered :
      ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin) :
    ProfiledRawJointLeftPhysicalSiblingReceiver A :=
  match delivered with
  | .inl _ => oldReceiver
  | .inr installed =>
      initialProfiledRawJointLeftPhysicalSiblingReceiver A
        installed.2.1.1 .both

@[simp] theorem profiledRawJointRecurrentRightToLeftDeliveredReceiver_open
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (staged :
      ProfiledRawJointRecurrentRightToLeftStagedReceiver A strategy hwin) :
    profiledRawJointRecurrentRightToLeftDeliveredReceiver A strategy hwin
      oldReceiver (.inl staged) = oldReceiver :=
  rfl

@[simp] theorem profiledRawJointRecurrentRightToLeftDeliveredReceiver_closed
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (installed :
      ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin) :
    profiledRawJointRecurrentRightToLeftDeliveredReceiver A strategy hwin
      oldReceiver (.inr installed) =
        initialProfiledRawJointLeftPhysicalSiblingReceiver A
          installed.2.1.1 .both :=
  rfl

/-- If delivery is delayed by one blind round, the two candidate controls
have coalesced and therefore install the same receiver. -/
theorem
    profiledRawJointRecurrentRightToLeftDeliveredReceiver_eq_after_noRecv
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (left right :
      ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin)
    (input : In₂)
    (hblind : ProfiledRawJointRecurrentRightToLeftBridgeBlind A strategy hwin
      left right) :
    profiledRawJointRecurrentRightToLeftDeliveredReceiver A strategy hwin
        oldReceiver
        (profiledRawJointRecurrentRightToLeftBridgeNoRecv A strategy hwin left
          input).1 =
      profiledRawJointRecurrentRightToLeftDeliveredReceiver A strategy hwin
        oldReceiver
        (profiledRawJointRecurrentRightToLeftBridgeNoRecv A strategy hwin right
          input).1 := by
  cases hblind with
  | staged state receiver packet move hmove =>
      simp [profiledRawJointRecurrentRightToLeftBridgeNoRecv,
        profiledRawJointRecurrentRightToLeftStagePacket, hmove]
  | recurrent installed => rfl

/-! ### Left-to-right bridge on process one -/

abbrev ProfiledRawJointRecurrentLeftToRightStagedReceiver :=
  BankControl A strategy hwin ×
    ProfiledRawJointLeftPhysicalSiblingReceiver A ×
      Option
        (ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A
          strategy hwin)

abbrev ProfiledRawJointRecurrentLeftToRightInstalledOwner :=
  BankControl A strategy hwin ×
    ProfiledRawJointRightPhysicalSiblingExceptional A ×
      ProfiledRawJointLeftPhysicalSiblingReceiver A

abbrev ProfiledRawJointRecurrentLeftToRightBridgeControl :=
  ProfiledRawJointRecurrentLeftToRightStagedReceiver A strategy hwin ⊕
    ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentLeftToRightStagedReceiver A strategy hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin) := by
  classical
  infer_instance

def profiledRawJointRecurrentLeftToRightStagePacket
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) :
    ProfiledRawJointRecurrentLeftToRightStagedReceiver A strategy hwin :=
  (state, receiver, some packet)

noncomputable def profiledRawJointRecurrentLeftToRightStageRecord
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (record : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    ProfiledRawJointRecurrentLeftToRightStagedReceiver A strategy hwin :=
  profiledRawJointRecurrentLeftToRightStagePacket A strategy hwin state receiver
    (profiledRawJointOneSidedPhysicalCompatibleBankResolveLeftRecord A
      strategy hwin state record row)

noncomputable def profiledRawJointRecurrentLeftToRightBridgeNoRecv
    (control :
      ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin)
    (input : In₁) :
    ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin × Out₁ :=
  match control with
  | .inl staged =>
      match staged.2.2 with
      | none => (.inl staged, default)
      | some packet =>
          match packet.successor.2.1.2.1 with
          | none => (.inl staged, default)
          | some move =>
              let next := profiledRawJointRightPhysicalSiblingMemberNoRecvStep
                A move false (move.memberController A false).initial input
              (.inr
                (packet.successor, ⟨move, next.2⟩, staged.2.1), next.1)
  | .inr installed =>
      let owner := installed.2.1
      let next := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A
        owner.1 false owner.2 input
      (.inr (installed.1, ⟨owner.1, next.2⟩, installed.2.2), next.1)

inductive ProfiledRawJointRecurrentLeftToRightBridgeBlind :
    ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin →
      ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin → Prop
  | staged
      (state : BankControl A strategy hwin)
      (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
      (packet :
        ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A
          strategy hwin)
      (move : ProfiledRawJointRightPhysicalSiblingMove A)
      (hmove : packet.successor.2.1.2.1 = some move) :
      ProfiledRawJointRecurrentLeftToRightBridgeBlind
        (.inl
          (profiledRawJointRecurrentLeftToRightStagePacket A strategy hwin
            state receiver packet))
        (.inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩, receiver))
  | recurrent
      (installed :
        ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin) :
      ProfiledRawJointRecurrentLeftToRightBridgeBlind
        (.inr installed) (.inr installed)

theorem profiledRawJointRecurrentLeftToRightBridgeBlind_noRecv
    (left right :
      ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin)
    (input : In₁)
    (hblind : ProfiledRawJointRecurrentLeftToRightBridgeBlind A strategy hwin
      left right) :
    (profiledRawJointRecurrentLeftToRightBridgeNoRecv A strategy hwin left
        input).2 =
        (profiledRawJointRecurrentLeftToRightBridgeNoRecv A strategy hwin right
          input).2 ∧
      ProfiledRawJointRecurrentLeftToRightBridgeBlind A strategy hwin
        (profiledRawJointRecurrentLeftToRightBridgeNoRecv A strategy hwin left
          input).1
        (profiledRawJointRecurrentLeftToRightBridgeNoRecv A strategy hwin right
          input).1 := by
  cases hblind with
  | staged state receiver packet move hmove =>
      simp only [profiledRawJointRecurrentLeftToRightBridgeNoRecv,
        profiledRawJointRecurrentLeftToRightStagePacket, hmove]
      exact ⟨trivial, .recurrent _⟩
  | recurrent installed =>
      exact ⟨rfl, .recurrent _⟩

theorem profiledRawJointRecurrentLeftToRightStagePacket_blind
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right target () =
      some root) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      ProfiledRawJointRecurrentLeftToRightBridgeBlind A strategy hwin
        (.inl
          (profiledRawJointRecurrentLeftToRightStagePacket A strategy hwin
            state receiver packet))
        (.inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩, receiver)) := by
  dsimp only
  obtain ⟨move, hmove⟩ :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_rightMove_exists
      A strategy hwin state target hrealizes root hroot
  exact ⟨move, .staged state receiver _ move hmove⟩

/-- Mirrored record-facing bridge creation. -/
theorem profiledRawJointRecurrentLeftToRightStageRecord_blind
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (record : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow)
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state (record.target row)
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state (record.target row)))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right
      (record.target row) () = some root) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      ProfiledRawJointRecurrentLeftToRightBridgeBlind A strategy hwin
        (.inl
          (profiledRawJointRecurrentLeftToRightStageRecord A strategy hwin
            state receiver record row))
        (.inr
          ((profiledRawJointOneSidedPhysicalCompatibleBankResolveLeftRecord A
              strategy hwin state record row).successor,
            ⟨move, (move.memberController A false).initial⟩, receiver)) := by
  simpa [profiledRawJointRecurrentLeftToRightStageRecord,
    profiledRawJointOneSidedPhysicalCompatibleBankResolveLeftRecord] using
    (profiledRawJointRecurrentLeftToRightStagePacket_blind A strategy hwin
      state receiver (record.target row) hrealizes root hroot)

/-! #### The genuine aligned left-receiver step -/

noncomputable def profiledRawJointRecurrentLeftReceiveFor
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    ProfiledRawJointRecurrentLeftToRightStagedReceiver A strategy hwin ×
      Out₁ :=
  let next := stepProfiledRawJointLeftPhysicalSiblingReceiverFor A receiver.1
    owner receiver.2.1 receiver.2.2.1 input
  match next.2.2.2.2 with
  | none => ((state, next.2, none), next.1)
  | some target =>
      ((state, next.2,
        some
          (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A
            strategy hwin state target)), next.1)

@[simp] theorem profiledRawJointRecurrentLeftReceiveFor_packet
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    (profiledRawJointRecurrentLeftReceiveFor A strategy hwin state receiver
      owner input).1.2.2 =
      some
        (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A
          strategy hwin state
          (((receiver.1.memberController A false).labelOf owner).2
            receiver.2.2.1 input |>.target receiver.2.1)) :=
  rfl

@[simp] theorem profiledRawJointRecurrentLeftReceiveFor_receiver
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    (profiledRawJointRecurrentLeftReceiveFor A strategy hwin state receiver
      owner input).1.2.1 =
      (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A receiver.1 owner
        receiver.2.1 receiver.2.2.1 input).2 :=
  rfl

@[simp] theorem profiledRawJointRecurrentLeftReceiveFor_output
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    (profiledRawJointRecurrentLeftReceiveFor A strategy hwin state receiver
      owner input).2 =
      (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A receiver.1 owner
        receiver.2.1 receiver.2.2.1 input).1 :=
  rfl

theorem profiledRawJointRecurrentLeftReceiveFor_blind
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : target =
      (((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input |>.target receiver.2.1))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right target () =
      some root) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      let next := profiledRawJointRecurrentLeftReceiveFor A strategy hwin
        state receiver owner input
      let packet :=
        profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
          hwin state target
      ProfiledRawJointRecurrentLeftToRightBridgeBlind A strategy hwin
        (.inl next.1)
        (.inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩, next.1.2.1)) := by
  subst target
  let next := stepProfiledRawJointLeftPhysicalSiblingReceiverFor A receiver.1
    owner receiver.2.1 receiver.2.2.1 input
  simpa [profiledRawJointRecurrentLeftReceiveFor, next] using
    (profiledRawJointRecurrentLeftToRightStagePacket_blind A strategy hwin
      state next.2
      ((((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input).target receiver.2.1) hrealizes root hroot)

noncomputable def profiledRawJointRecurrentLeftToRightDeliveredReceiver
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (delivered :
      ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin) :
    ProfiledRawJointRightPhysicalSiblingReceiver A :=
  match delivered with
  | .inl _ => oldReceiver
  | .inr installed =>
      initialProfiledRawJointRightPhysicalSiblingReceiver A
        installed.2.1.1 .both

@[simp] theorem profiledRawJointRecurrentLeftToRightDeliveredReceiver_open
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (staged :
      ProfiledRawJointRecurrentLeftToRightStagedReceiver A strategy hwin) :
    profiledRawJointRecurrentLeftToRightDeliveredReceiver A strategy hwin
      oldReceiver (.inl staged) = oldReceiver :=
  rfl

@[simp] theorem profiledRawJointRecurrentLeftToRightDeliveredReceiver_closed
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (installed :
      ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin) :
    profiledRawJointRecurrentLeftToRightDeliveredReceiver A strategy hwin
      oldReceiver (.inr installed) =
        initialProfiledRawJointRightPhysicalSiblingReceiver A
          installed.2.1.1 .both :=
  rfl

theorem
    profiledRawJointRecurrentLeftToRightDeliveredReceiver_eq_after_noRecv
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (left right :
      ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin)
    (input : In₁)
    (hblind : ProfiledRawJointRecurrentLeftToRightBridgeBlind A strategy hwin
      left right) :
    profiledRawJointRecurrentLeftToRightDeliveredReceiver A strategy hwin
        oldReceiver
        (profiledRawJointRecurrentLeftToRightBridgeNoRecv A strategy hwin left
          input).1 =
      profiledRawJointRecurrentLeftToRightDeliveredReceiver A strategy hwin
        oldReceiver
        (profiledRawJointRecurrentLeftToRightBridgeNoRecv A strategy hwin right
          input).1 := by
  cases hblind with
  | staged state receiver packet move hmove =>
      simp [profiledRawJointRecurrentLeftToRightBridgeNoRecv,
        profiledRawJointRecurrentLeftToRightStagePacket, hmove]
  | recurrent installed => rfl

/-! ### Exact bridge blind laws -/

/-- These are the actual receive-created blind relations: the first field is
the process-one left-to-right bridge and the second is the process-two
right-to-left bridge. -/
noncomputable def profiledRawJointRecurrentBridgeBlindNoRecvLaws :
    FiniteAcknowledgedDelayedCarrier.BlindNoRecvLaws
      (profiledRawJointRecurrentLeftToRightBridgeNoRecv A strategy hwin)
      (profiledRawJointRecurrentRightToLeftBridgeNoRecv A strategy hwin)
      (ProfiledRawJointRecurrentLeftToRightBridgeBlind A strategy hwin)
      (ProfiledRawJointRecurrentRightToLeftBridgeBlind A strategy hwin) where
  one := profiledRawJointRecurrentLeftToRightBridgeBlind_noRecv A strategy hwin
  two := profiledRawJointRecurrentRightToLeftBridgeBlind_noRecv A strategy hwin

/-! ## Full alternating recurrent control sums -/

/-- Process one is either in its left-to-right informed bridge or in the
complementary deferred state of a right-to-left ambiguity. -/
abbrev ProfiledRawJointRecurrentBoundaryOneControl :=
  ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin ⊕
    ProfiledRawJointRecurrentRightToLeftBlindControl A

/-- Process-two mirror. -/
abbrev ProfiledRawJointRecurrentBoundaryTwoControl :=
  ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin ⊕
    ProfiledRawJointRecurrentLeftToRightBlindControl A

noncomputable instance :
    Fintype (ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin) := by
  classical
  infer_instance

noncomputable def profiledRawJointRecurrentBoundaryNoRecvOne
    (control : ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin)
    (input : In₁) :
    ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin × Out₁ :=
  match control with
  | .inl bridge =>
      let next := profiledRawJointRecurrentLeftToRightBridgeNoRecv A strategy
        hwin bridge input
      (.inl next.1, next.2)
  | .inr deferred =>
      let next := profiledRawJointRecurrentRightToLeftBlindNoRecv A deferred
        input
      (.inr next.1, next.2)

noncomputable def profiledRawJointRecurrentBoundaryNoRecvTwo
    (control : ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin)
    (input : In₂) :
    ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin × Out₂ :=
  match control with
  | .inl bridge =>
      let next := profiledRawJointRecurrentRightToLeftBridgeNoRecv A strategy
        hwin bridge input
      (.inl next.1, next.2)
  | .inr deferred =>
      let next := profiledRawJointRecurrentLeftToRightBlindNoRecv A deferred
        input
      (.inr next.1, next.2)

inductive ProfiledRawJointRecurrentBoundaryOneBlind :
    ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin →
      ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin → Prop
  | bridge {left right}
      (hblind : ProfiledRawJointRecurrentLeftToRightBridgeBlind A strategy hwin
        left right) :
      ProfiledRawJointRecurrentBoundaryOneBlind (.inl left) (.inl right)
  | deferred {left right}
      (hblind : FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left
        right) :
      ProfiledRawJointRecurrentBoundaryOneBlind (.inr left) (.inr right)

inductive ProfiledRawJointRecurrentBoundaryTwoBlind :
    ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin →
      ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin → Prop
  | bridge {left right}
      (hblind : ProfiledRawJointRecurrentRightToLeftBridgeBlind A strategy hwin
        left right) :
      ProfiledRawJointRecurrentBoundaryTwoBlind (.inl left) (.inl right)
  | deferred {left right}
      (hblind : FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left
        right) :
      ProfiledRawJointRecurrentBoundaryTwoBlind (.inr left) (.inr right)

theorem profiledRawJointRecurrentBoundaryOneBlind_noRecv
    (left right :
      ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin)
    (input : In₁)
    (hblind : ProfiledRawJointRecurrentBoundaryOneBlind A strategy hwin left
      right) :
    (profiledRawJointRecurrentBoundaryNoRecvOne A strategy hwin left input).2 =
        (profiledRawJointRecurrentBoundaryNoRecvOne A strategy hwin right
          input).2 ∧
      ProfiledRawJointRecurrentBoundaryOneBlind A strategy hwin
        (profiledRawJointRecurrentBoundaryNoRecvOne A strategy hwin left
          input).1
        (profiledRawJointRecurrentBoundaryNoRecvOne A strategy hwin right
          input).1 := by
  cases hblind with
  | bridge hblind =>
      obtain ⟨hout, hnext⟩ :=
        profiledRawJointRecurrentLeftToRightBridgeBlind_noRecv A strategy hwin
          _ _ input hblind
      exact ⟨hout, .bridge hnext⟩
  | deferred hblind =>
      obtain ⟨hout, hnext⟩ :=
        (profiledRawJointRecurrentBoundaryBlindNoRecvLaws A).one _ _ input
          hblind
      exact ⟨hout, .deferred hnext⟩

theorem profiledRawJointRecurrentBoundaryTwoBlind_noRecv
    (left right :
      ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin)
    (input : In₂)
    (hblind : ProfiledRawJointRecurrentBoundaryTwoBlind A strategy hwin left
      right) :
    (profiledRawJointRecurrentBoundaryNoRecvTwo A strategy hwin left input).2 =
        (profiledRawJointRecurrentBoundaryNoRecvTwo A strategy hwin right
          input).2 ∧
      ProfiledRawJointRecurrentBoundaryTwoBlind A strategy hwin
        (profiledRawJointRecurrentBoundaryNoRecvTwo A strategy hwin left
          input).1
        (profiledRawJointRecurrentBoundaryNoRecvTwo A strategy hwin right
          input).1 := by
  cases hblind with
  | bridge hblind =>
      obtain ⟨hout, hnext⟩ :=
        profiledRawJointRecurrentRightToLeftBridgeBlind_noRecv A strategy hwin
          _ _ input hblind
      exact ⟨hout, .bridge hnext⟩
  | deferred hblind =>
      obtain ⟨hout, hnext⟩ :=
        (profiledRawJointRecurrentBoundaryBlindNoRecvLaws A).two _ _ input
          hblind
      exact ⟨hout, .deferred hnext⟩

/-- The complete alternating sums satisfy the no-receive part of the exact
closing interface. -/
noncomputable def profiledRawJointRecurrentBoundaryFullBlindNoRecvLaws :
    FiniteAcknowledgedDelayedCarrier.BlindNoRecvLaws
      (profiledRawJointRecurrentBoundaryNoRecvOne A strategy hwin)
      (profiledRawJointRecurrentBoundaryNoRecvTwo A strategy hwin)
      (ProfiledRawJointRecurrentBoundaryOneBlind A strategy hwin)
      (ProfiledRawJointRecurrentBoundaryTwoBlind A strategy hwin) where
  one := profiledRawJointRecurrentBoundaryOneBlind_noRecv A strategy hwin
  two := profiledRawJointRecurrentBoundaryTwoBlind_noRecv A strategy hwin

/-! ## One-round boundary forks

At a right-to-left boundary, process two evaluates the old right receiver and
therefore learns the next left target.  Process one does not evaluate its
dormant left receiver in that round: its current output is still the output
of the old right owner.  Consequently its simultaneous-receive output is
literally the same output as in the strict-right execution.  The first pair
of definitions and lemmas records this timing equation before constructing
the receiver-side fork.  The second pair is its left-to-right mirror.
-/

/-! ### Right-to-left boundary -/

/-- Process one's local fork at a right-to-left boundary.  Both candidates
advance the same old right owner and retain the same dormant left receiver;
only the proof-side member differs. -/
noncomputable def
    profiledRawJointRecurrentRightToLeftComplementaryReceiveOne
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (input : In₁) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin) × Out₁ :=
  let next := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A move
    false owner input
  let fork := profiledRawJointRecurrentRightToLeftBlindFork A
    (⟨move, next.2⟩ : ProfiledRawJointRightPhysicalSiblingExceptional A)
    oldReceiver
  (⟨.inr fork.openControl, .inr fork.closedControl⟩, next.1)

/-- The complementary endpoint's current-output equation.  This is the
timing-sensitive point: a simultaneous receive does not run the dormant
left receiver one round early. -/
@[simp] theorem
    profiledRawJointRecurrentRightToLeftComplementaryReceiveOne_output
    (state : BankControl A strategy hwin)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (input : In₁) :
    (profiledRawJointRecurrentRightToLeftComplementaryReceiveOne A strategy
        hwin move owner oldReceiver input).2 =
      (profiledRawJointRecurrentBoundaryNoRecvOne A strategy hwin
        (.inl (.inr
          (state,
            (⟨move, owner⟩ :
              ProfiledRawJointRightPhysicalSiblingExceptional A),
            oldReceiver))) input).2 :=
  rfl

/-- The open and exact-close process-one continuations form the canonical
deferred blind pair. -/
theorem
    profiledRawJointRecurrentRightToLeftComplementaryReceiveOne_blind
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (input : In₁) :
    ProfiledRawJointRecurrentBoundaryOneBlind A strategy hwin
      (profiledRawJointRecurrentRightToLeftComplementaryReceiveOne A strategy
        hwin move owner oldReceiver input).1.openControl
      (profiledRawJointRecurrentRightToLeftComplementaryReceiveOne A strategy
        hwin move owner oldReceiver input).1.closedControl := by
  apply ProfiledRawJointRecurrentBoundaryOneBlind.deferred
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberFork_blind _ _

/-- Process two's total receiver-side fork.  The live-target theorem below
shows that the duplicate fallback is unreachable at a legal boundary. -/
noncomputable def profiledRawJointRecurrentRightToLeftReceiveForkTwo
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin) × Out₂ :=
  let next := profiledRawJointRecurrentRightReceiveFor A strategy hwin state
    receiver owner input
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin state target
  let openControl : ProfiledRawJointRecurrentBoundaryTwoControl A strategy
      hwin := .inl (.inl next.1)
  match packet.successor.2.1.2.2 with
  | none => (⟨openControl, openControl⟩, next.2)
  | some move =>
      (⟨openControl,
        .inl (.inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩,
            next.1.2.1))⟩,
        next.2)

@[simp] theorem profiledRawJointRecurrentRightToLeftReceiveForkTwo_output
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    (profiledRawJointRecurrentRightToLeftReceiveForkTwo A strategy hwin state
        receiver owner input).2 =
      (profiledRawJointRecurrentRightReceiveFor A strategy hwin state receiver
        owner input).2 := by
  simp only [profiledRawJointRecurrentRightToLeftReceiveForkTwo]
  split <;> rfl

/-- An exact live target makes the total receiver-side fork the compiled
staged/installed blind pair. -/
theorem profiledRawJointRecurrentRightToLeftReceiveForkTwo_blind
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : target =
      (((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input |>.target receiver.2.1))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left
      target () = some root) :
    ProfiledRawJointRecurrentBoundaryTwoBlind A strategy hwin
      (profiledRawJointRecurrentRightToLeftReceiveForkTwo A strategy hwin state
        receiver owner input).1.openControl
      (profiledRawJointRecurrentRightToLeftReceiveForkTwo A strategy hwin state
        receiver owner input).1.closedControl := by
  subst target
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin state target
  obtain ⟨move, hmove⟩ :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_leftMove_exists
      A strategy hwin state target hrealizes root hroot
  simp only [profiledRawJointRecurrentRightToLeftReceiveForkTwo, target,
    packet, hmove]
  exact .bridge
    (ProfiledRawJointRecurrentRightToLeftBridgeBlind.staged state
      (profiledRawJointRecurrentRightReceiveFor A strategy hwin state receiver
        owner input).1.2.1 packet move hmove)

/-- Both endpoint-local forks created by one aligned right-to-left boundary
round. -/
noncomputable def profiledRawJointRecurrentRightToLeftBoundaryReceive
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (input : In₁ × In₂) :
    (FiniteDelayedFork
        (ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin) × Out₁) ×
      (FiniteDelayedFork
        (ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin) × Out₂) :=
  (profiledRawJointRecurrentRightToLeftComplementaryReceiveOne A strategy hwin
      receiver.1 owner oldReceiver input.1,
    profiledRawJointRecurrentRightToLeftReceiveForkTwo A strategy hwin state
      receiver owner (input.2, input.1))

/-- The aligned right-to-left round simultaneously satisfies the delicate
complementary-output equation and both endpoint-local blind-fork laws. -/
theorem profiledRawJointRecurrentRightToLeftBoundaryReceive_spec
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (input : In₁ × In₂)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : target =
      (((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 (input.2, input.1) |>.target receiver.2.1))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left target () =
      some root) :
    let result := profiledRawJointRecurrentRightToLeftBoundaryReceive A
      strategy hwin state receiver owner oldReceiver input
    result.1.2 =
        (profiledRawJointRecurrentBoundaryNoRecvOne A strategy hwin
          (.inl (.inr
            (state,
              (⟨receiver.1, owner⟩ :
                ProfiledRawJointRightPhysicalSiblingExceptional A),
              oldReceiver))) input.1).2 ∧
      result.2.2 =
        (profiledRawJointRecurrentRightReceiveFor A strategy hwin state
          receiver owner (input.2, input.1)).2 ∧
      ProfiledRawJointRecurrentBoundaryOneBlind A strategy hwin
        result.1.1.openControl result.1.1.closedControl ∧
      ProfiledRawJointRecurrentBoundaryTwoBlind A strategy hwin
        result.2.1.openControl result.2.1.closedControl := by
  dsimp only [profiledRawJointRecurrentRightToLeftBoundaryReceive]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      profiledRawJointRecurrentRightToLeftComplementaryReceiveOne_output A
        strategy hwin state receiver.1 owner oldReceiver input.1
  · exact
      profiledRawJointRecurrentRightToLeftReceiveForkTwo_output A strategy
        hwin state receiver owner (input.2, input.1)
  · exact
      profiledRawJointRecurrentRightToLeftComplementaryReceiveOne_blind A
        strategy hwin receiver.1 owner oldReceiver input.1
  · exact
      profiledRawJointRecurrentRightToLeftReceiveForkTwo_blind A strategy hwin
        state receiver owner (input.2, input.1) target htarget hrealizes root
          hroot

/-! ### Left-to-right boundary -/

/-- Process-two mirror of the complementary endpoint fork. -/
noncomputable def
    profiledRawJointRecurrentLeftToRightComplementaryReceiveTwo
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (input : In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin) × Out₂ :=
  let next := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A move false
    owner input
  let fork := profiledRawJointRecurrentLeftToRightBlindFork A
    (⟨move, next.2⟩ : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    oldReceiver
  (⟨.inr fork.openControl, .inr fork.closedControl⟩, next.1)

@[simp] theorem
    profiledRawJointRecurrentLeftToRightComplementaryReceiveTwo_output
    (state : BankControl A strategy hwin)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (input : In₂) :
    (profiledRawJointRecurrentLeftToRightComplementaryReceiveTwo A strategy
        hwin move owner oldReceiver input).2 =
      (profiledRawJointRecurrentBoundaryNoRecvTwo A strategy hwin
        (.inl (.inr
          (state,
            (⟨move, owner⟩ : ProfiledRawJointLeftPhysicalSiblingExceptional A),
            oldReceiver))) input).2 :=
  rfl

theorem
    profiledRawJointRecurrentLeftToRightComplementaryReceiveTwo_blind
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (input : In₂) :
    ProfiledRawJointRecurrentBoundaryTwoBlind A strategy hwin
      (profiledRawJointRecurrentLeftToRightComplementaryReceiveTwo A strategy
        hwin move owner oldReceiver input).1.openControl
      (profiledRawJointRecurrentLeftToRightComplementaryReceiveTwo A strategy
        hwin move owner oldReceiver input).1.closedControl := by
  apply ProfiledRawJointRecurrentBoundaryTwoBlind.deferred
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberFork_blind _ _

/-- Process one's total receiver-side fork at the mirrored boundary. -/
noncomputable def profiledRawJointRecurrentLeftToRightReceiveForkOne
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin) × Out₁ :=
  let next := profiledRawJointRecurrentLeftReceiveFor A strategy hwin state
    receiver owner input
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin state target
  let openControl : ProfiledRawJointRecurrentBoundaryOneControl A strategy
      hwin := .inl (.inl next.1)
  match packet.successor.2.1.2.1 with
  | none => (⟨openControl, openControl⟩, next.2)
  | some move =>
      (⟨openControl,
        .inl (.inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩,
            next.1.2.1))⟩,
        next.2)

@[simp] theorem profiledRawJointRecurrentLeftToRightReceiveForkOne_output
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    (profiledRawJointRecurrentLeftToRightReceiveForkOne A strategy hwin state
        receiver owner input).2 =
      (profiledRawJointRecurrentLeftReceiveFor A strategy hwin state receiver
        owner input).2 := by
  simp only [profiledRawJointRecurrentLeftToRightReceiveForkOne]
  split <;> rfl

theorem profiledRawJointRecurrentLeftToRightReceiveForkOne_blind
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : target =
      (((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input |>.target receiver.2.1))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right
      target () = some root) :
    ProfiledRawJointRecurrentBoundaryOneBlind A strategy hwin
      (profiledRawJointRecurrentLeftToRightReceiveForkOne A strategy hwin state
        receiver owner input).1.openControl
      (profiledRawJointRecurrentLeftToRightReceiveForkOne A strategy hwin state
        receiver owner input).1.closedControl := by
  subst target
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin state target
  obtain ⟨move, hmove⟩ :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_rightMove_exists
      A strategy hwin state target hrealizes root hroot
  simp only [profiledRawJointRecurrentLeftToRightReceiveForkOne, target,
    packet, hmove]
  exact .bridge
    (ProfiledRawJointRecurrentLeftToRightBridgeBlind.staged state
      (profiledRawJointRecurrentLeftReceiveFor A strategy hwin state receiver
        owner input).1.2.1 packet move hmove)

/-- Mirrored aligned two-endpoint boundary round. -/
noncomputable def profiledRawJointRecurrentLeftToRightBoundaryReceive
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (input : In₁ × In₂) :
    (FiniteDelayedFork
        (ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin) × Out₁) ×
      (FiniteDelayedFork
        (ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin) × Out₂) :=
  (profiledRawJointRecurrentLeftToRightReceiveForkOne A strategy hwin state
      receiver owner input,
    profiledRawJointRecurrentLeftToRightComplementaryReceiveTwo A strategy
      hwin receiver.1 owner oldReceiver input.2)

/-- Mirrored exact boundary-round specification. -/
theorem profiledRawJointRecurrentLeftToRightBoundaryReceive_spec
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (input : In₁ × In₂)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : target =
      (((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input |>.target receiver.2.1))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right target () =
      some root) :
    let result := profiledRawJointRecurrentLeftToRightBoundaryReceive A
      strategy hwin state receiver owner oldReceiver input
    result.2.2 =
        (profiledRawJointRecurrentBoundaryNoRecvTwo A strategy hwin
          (.inl (.inr
            (state,
              (⟨receiver.1, owner⟩ :
                ProfiledRawJointLeftPhysicalSiblingExceptional A),
              oldReceiver))) input.2).2 ∧
      result.1.2 =
        (profiledRawJointRecurrentLeftReceiveFor A strategy hwin state
          receiver owner input).2 ∧
      ProfiledRawJointRecurrentBoundaryOneBlind A strategy hwin
        result.1.1.openControl result.1.1.closedControl ∧
      ProfiledRawJointRecurrentBoundaryTwoBlind A strategy hwin
        result.2.1.openControl result.2.1.closedControl := by
  dsimp only [profiledRawJointRecurrentLeftToRightBoundaryReceive]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      profiledRawJointRecurrentLeftToRightComplementaryReceiveTwo_output A
        strategy hwin state receiver.1 owner oldReceiver input.2
  · exact
      profiledRawJointRecurrentLeftToRightReceiveForkOne_output A strategy hwin
        state receiver owner input
  · exact
      profiledRawJointRecurrentLeftToRightReceiveForkOne_blind A strategy hwin
        state receiver owner input target htarget hrealizes root hroot
  · exact
      profiledRawJointRecurrentLeftToRightComplementaryReceiveTwo_blind A
        strategy hwin receiver.1 owner oldReceiver input.2


end

end DetParityAutomaton

end DistributedSynthesis
