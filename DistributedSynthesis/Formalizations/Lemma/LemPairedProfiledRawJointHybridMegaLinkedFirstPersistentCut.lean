/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedDeferredTailAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTagBankTrackedBootstrap
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredBlindTailCompatibility
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartOperationalCut

/-!
# The represented root at the first persistent strict cut

The mega front installs the exact marked child named by its delivered finite
phase-live tag.  This file turns that fact into the concrete arbitrary-prefix
pair required by the accepted linked-table tail.  A strict-right creation tag
has a live left lane, so its first opposite (persistent) strict cut uses the
left sender/receiver pair; a strict-left tag is the mirror.

All reachability, one-sided-code, live-lane, literal-move, and common-root
obligations are discharged here from the concrete tag.  The only property
intentionally left separate is all-depth blind-sender compatibility: that is
the exact local tree-strategy condition isolated by
`...LinkedDeferredBlindTailCompatibility`.
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

private abbrev LeftSender :=
  ProfiledRawJointLeftFinitePayloadLiteralPrefixSenderState A
    (BankControl A strategy hwin)

private abbrev LeftReceiver :=
  ProfiledRawJointLeftFinitePayloadLiteralPrefixReceiverState A
    (BankControl A strategy hwin)

private abbrev RightSender :=
  ProfiledRawJointRightFinitePayloadLiteralPrefixSenderState A
    (BankControl A strategy hwin)

private abbrev RightReceiver :=
  ProfiledRawJointRightFinitePayloadLiteralPrefixReceiverState A
    (BankControl A strategy hwin)

/-! ## Exact pairs selected by a concrete handoff tag -/

/-- The canonical exact left-table pair at the child installed by a
strict-right creation tag. -/
noncomputable def
    profiledRawJointHybridMegaLinkedRightTagExactLeftPair
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    LeftSender A strategy hwin × LeftReceiver A strategy hwin :=
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
  let child := tag.markedBankChild A strategy hwin
  let relay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
      A strategy hwin (child.linkedRightMove A strategy hwin)
        (child.linkedLeftMove A strategy hwin) false false
  relay.2

/-- Strict-left/right-table mirror. -/
noncomputable def
    profiledRawJointHybridMegaLinkedLeftTagExactRightPair
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    RightSender A strategy hwin × RightReceiver A strategy hwin :=
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
  let child := tag.markedBankChild A strategy hwin
  let relay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
      A strategy hwin (child.linkedRightMove A strategy hwin)
        (child.linkedLeftMove A strategy hwin) false false
  relay.1

/-! ## Live-root package carried by the concrete handoff -/

/-- The exact marked child carried by a strict-right creation tag is a live
left root for the repaired controller.  This is the root-level datum needed
by the cross-cut induction; unlike `PairAtPrefix`, it explicitly retains
reachability, the one-sided public code, and the live lane. -/
theorem
    profiledRawJointHybridMegaLinkedRightTag_markedChild_leftRootReady
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
      A strategy hwin (tag.markedBankChild A strategy hwin) := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
  let code := tag.childIncidence A strategy hwin
  let slot := (tag.initialLeftMove A strategy hwin).1.source
  refine ⟨code, slot, tag.markedBankChild_reachable A strategy hwin, ?_, ?_⟩
  · have hfull := tag.markedBankChild_code A strategy hwin
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
        hwin origin
    let rootReachable :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_reachable A
        strategy hwin origin
    let packet :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
        strategy hwin root.1 root.2 rootReachable
    let installed :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin origin
    let package :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
        strategy hwin origin
    have hrootExtra :
        root.2.1.2.2 =
          profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
            installed.world := by
      change
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
          strategy hwin origin).policy.run []).1.2.2 =
            profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
              installed.world
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank_rootExtra
          A strategy hwin origin
    have hmarked := packet.marked_current
    rw [hrootExtra] at hmarked
    have hsource : packet.source = .common installed.world :=
      (profiledRawJointHybridMarkedLiteralPrefixCurrentCompatible_initial_elim
        A strategy hwin installed.world packet.source hmarked).1
    have hpacketMove : packet.move.1 = some installed.rawMove := by
      calc
        packet.move.1 = packet.source.move A := packet.source_move.symm
        _ = ((.common installed.world :
              ProfiledRawJointHybridSemanticState A strategy).move A) := by
            rw [hsource]
        _ = some installed.rawMove := congrArg some installed.move_eq
    have hrootCode :
        root.2.1.1 =
          .common ((profiledRawJointCommonWorldFamily A installed.world
            ).incidenceCode A) := by
      have hinitial := congrArg (fun state ↦ state.1.1)
        package.policy.accepts.1.1
      simpa [root, package, installed] using hinitial
    have hrequested :
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
            hwin tag.origin).childCode A strategy hwin
            (tag.direction (A := A))).1 = .oneSided code := by
      change
        (root.childCode A strategy hwin (tag.direction (A := A))).1 =
          .oneSided code
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
          A strategy hwin root rootReachable,
        sourceFreeBeliefParentLinkedNext_fst]
      change
        profiledRawJointHybridNext A root.2.1.1 packet.move.1
            (tag.direction (A := A)) = .oneSided code
      rw [hrootCode, hpacketMove]
      rw [installed.incidence_eq]
      simp [tag, code, installed,
        profiledRawJointHybridShadowPhaseLiveRightTag,
        ProfiledRawJointHybridShadowPhaseLiveTag.direction,
        ProfiledRawJointHybridShadowPhaseLiveTag.childIncidence,
        profiledRawJointHybridNext,
        profiledRawJointCommonActualDirection,
        profiledRawJointCommonOneRoundStrictRight,
        profiledRawJointForceBothPivots,
        profiledRawJointHybridShadowPhaseLiveInstalled,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled]
    exact (congrArg Prod.fst hfull).trans hrequested
  · have h :=
      profiledRawJointHybridShadowPhaseLiveRightTag_tailRoot_leftLive A
        strategy hwin origin input
    dsimp only at h
    have hrootCode : (tag.tailRoot A strategy hwin).1.1 = .oneSided code := by
      simpa [tag, code] using tag.tailRoot_publicCode A strategy hwin
    rw [hrootCode] at h
    simpa [profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots, tag, code, slot] using h

/-- Strict-left/right-root mirror. -/
theorem
    profiledRawJointHybridMegaLinkedLeftTag_markedChild_rightRootReady
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
      A strategy hwin (tag.markedBankChild A strategy hwin) := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
  let code := tag.childIncidence A strategy hwin
  let slot := (tag.initialRightMove A strategy hwin).1.source
  refine ⟨code, slot, tag.markedBankChild_reachable A strategy hwin, ?_, ?_⟩
  · have hfull := tag.markedBankChild_code A strategy hwin
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
        hwin origin
    let rootReachable :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_reachable A
        strategy hwin origin
    let packet :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
        strategy hwin root.1 root.2 rootReachable
    let installed :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin origin
    let package :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
        strategy hwin origin
    have hrootExtra :
        root.2.1.2.2 =
          profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
            installed.world := by
      change
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
          strategy hwin origin).policy.run []).1.2.2 =
            profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
              installed.world
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank_rootExtra
          A strategy hwin origin
    have hmarked := packet.marked_current
    rw [hrootExtra] at hmarked
    have hsource : packet.source = .common installed.world :=
      (profiledRawJointHybridMarkedLiteralPrefixCurrentCompatible_initial_elim
        A strategy hwin installed.world packet.source hmarked).1
    have hpacketMove : packet.move.1 = some installed.rawMove := by
      calc
        packet.move.1 = packet.source.move A := packet.source_move.symm
        _ = ((.common installed.world :
              ProfiledRawJointHybridSemanticState A strategy).move A) := by
            rw [hsource]
        _ = some installed.rawMove := congrArg some installed.move_eq
    have hrootCode :
        root.2.1.1 =
          .common ((profiledRawJointCommonWorldFamily A installed.world
            ).incidenceCode A) := by
      have hinitial := congrArg (fun state ↦ state.1.1)
        package.policy.accepts.1.1
      simpa [root, package, installed] using hinitial
    have hrequested :
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
            hwin tag.origin).childCode A strategy hwin
            (tag.direction (A := A))).1 = .oneSided code := by
      change
        (root.childCode A strategy hwin (tag.direction (A := A))).1 =
          .oneSided code
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
          A strategy hwin root rootReachable,
        sourceFreeBeliefParentLinkedNext_fst]
      change
        profiledRawJointHybridNext A root.2.1.1 packet.move.1
            (tag.direction (A := A)) = .oneSided code
      rw [hrootCode, hpacketMove]
      rw [installed.incidence_eq]
      simp [tag, code, installed,
        profiledRawJointHybridShadowPhaseLiveLeftTag,
        ProfiledRawJointHybridShadowPhaseLiveTag.direction,
        ProfiledRawJointHybridShadowPhaseLiveTag.childIncidence,
        profiledRawJointHybridNext,
        profiledRawJointCommonActualDirection,
        profiledRawJointCommonOneRoundStrictLeft,
        profiledRawJointForceBothPivots,
        profiledRawJointHybridShadowPhaseLiveInstalled,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled]
    exact (congrArg Prod.fst hfull).trans hrequested
  · have h :=
      profiledRawJointHybridShadowPhaseLiveLeftTag_tailRoot_rightLive A
        strategy hwin origin input
    dsimp only at h
    have hrootCode : (tag.tailRoot A strategy hwin).1.1 = .oneSided code := by
      simpa [tag, code] using tag.tailRoot_publicCode A strategy hwin
    rw [hrootCode] at h
    simpa [profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots, tag, code, slot] using h

/-- Model-facing first-cut bridge for a suffix dropped at the first
persistent strict-left round.  The strict-right creation tag becomes the
initial retained tag of `FullRestart`, and the dropped environment selects
its live-left root package at time zero. -/
theorem
    profiledRawJointHybridMegaLinkedRightTag_firstStrictRootReady_drop
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (hgraph : (env start).graph = .left) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
      A strategy hwin (tag.markedRetainedChildTag A strategy hwin)
        (OmegaWord.drop env start) := by
  dsimp only
  have hready :=
    profiledRawJointHybridMegaLinkedRightTag_markedChild_leftRootReady A
      strategy hwin origin input
  simpa [
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady,
    OmegaWord.drop, hgraph] using hready

/-- Strict-left creation / strict-right persistent-suffix mirror. -/
theorem
    profiledRawJointHybridMegaLinkedLeftTag_firstStrictRootReady_drop
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (hgraph : (env start).graph = .right) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
      A strategy hwin (tag.markedRetainedChildTag A strategy hwin)
        (OmegaWord.drop env start) := by
  dsimp only
  have hready :=
    profiledRawJointHybridMegaLinkedLeftTag_markedChild_rightRootReady A
      strategy hwin origin input
  simpa [
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady,
    OmegaWord.drop, hgraph] using hready

/-- The exact tag delivered by the concrete process-two-shadow/right-owner
mega handoff feeds the repaired first-root package.  The current handoff
inputs affect the emitted output but not the tag: the tag records the
shadow's common origin and creation input. -/
theorem
    profiledRawJointHybridMegaLinkedTwoShadowRightHandoff_firstStrictRootReady_drop
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hgraph : (env start).graph = .left) :
    let delivered :=
      profiledRawJointHybridTwoShadowRecvRightOwnerPhaseLive A strategy hwin
        shadow owner ownInput deliveredInput
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
      A strategy hwin
        (delivered.2.tag.markedRetainedChildTag A strategy hwin)
        (OmegaWord.drop env start) := by
  simpa using
    (profiledRawJointHybridMegaLinkedRightTag_firstStrictRootReady_drop A
      strategy hwin shadow.origin shadow.input env start hgraph)

/-- Concrete process-one-shadow/left-owner mirror. -/
theorem
    profiledRawJointHybridMegaLinkedOneShadowLeftHandoff_firstStrictRootReady_drop
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hgraph : (env start).graph = .right) :
    let delivered :=
      profiledRawJointHybridOneShadowRecvLeftOwnerPhaseLive A strategy hwin
        shadow owner ownInput deliveredInput
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
      A strategy hwin
        (delivered.2.tag.markedRetainedChildTag A strategy hwin)
        (OmegaWord.drop env start) := by
  simpa using
    (profiledRawJointHybridMegaLinkedLeftTag_firstStrictRootReady_drop A
      strategy hwin shadow.origin shadow.input env start hgraph)

/-- The first persistent strict cut below a strict-right creation tag is
represented at the exact marked child; no reachability or live-lane premise
is exposed. -/
theorem
    profiledRawJointHybridMegaLinkedRightTagExactLeftPair_atPrefix
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
    let child := tag.markedBankChild A strategy hwin
    let exact :=
      profiledRawJointHybridMegaLinkedRightTagExactLeftPair A strategy hwin
        origin input
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
      A strategy hwin child exact.1 exact.2 := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
  let child := tag.markedBankChild A strategy hwin
  let code := tag.childIncidence A strategy hwin
  let slot := (tag.initialLeftMove A strategy hwin).1.source
  have hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin child :=
    tag.markedBankChild_reachable A strategy hwin
  have hcode : child.2.1.1 = .oneSided code := by
    have hfull := tag.markedBankChild_code A strategy hwin
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
        hwin origin
    let rootReachable :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_reachable A
        strategy hwin origin
    let packet :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
        strategy hwin root.1 root.2 rootReachable
    let installed :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin origin
    let package :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
        strategy hwin origin
    have hrootExtra :
        root.2.1.2.2 =
          profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
            installed.world := by
      change
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
          strategy hwin origin).policy.run []).1.2.2 =
            profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
              installed.world
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank_rootExtra
          A strategy hwin origin
    have hmarked := packet.marked_current
    rw [hrootExtra] at hmarked
    have hsource : packet.source = .common installed.world :=
      (profiledRawJointHybridMarkedLiteralPrefixCurrentCompatible_initial_elim
        A strategy hwin installed.world packet.source hmarked).1
    have hpacketMove : packet.move.1 = some installed.rawMove := by
      calc
        packet.move.1 = packet.source.move A := packet.source_move.symm
        _ = ((.common installed.world :
              ProfiledRawJointHybridSemanticState A strategy).move A) := by
            rw [hsource]
        _ = some installed.rawMove := congrArg some installed.move_eq
    have hrootCode :
        root.2.1.1 =
          .common ((profiledRawJointCommonWorldFamily A installed.world
            ).incidenceCode A) := by
      have hinitial := congrArg (fun state ↦ state.1.1)
        package.policy.accepts.1.1
      simpa [root, package, installed] using hinitial
    have hrequested :
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
            hwin tag.origin).childCode A strategy hwin
            (tag.direction (A := A))).1 = .oneSided code := by
      change
        (root.childCode A strategy hwin (tag.direction (A := A))).1 =
          .oneSided code
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
          A strategy hwin root rootReachable,
        sourceFreeBeliefParentLinkedNext_fst]
      change
        profiledRawJointHybridNext A root.2.1.1 packet.move.1
            (tag.direction (A := A)) = .oneSided code
      rw [hrootCode, hpacketMove]
      rw [installed.incidence_eq]
      simp [tag, code, installed,
        profiledRawJointHybridShadowPhaseLiveRightTag,
        ProfiledRawJointHybridShadowPhaseLiveTag.direction,
        ProfiledRawJointHybridShadowPhaseLiveTag.childIncidence,
        profiledRawJointHybridNext,
        profiledRawJointCommonActualDirection,
        profiledRawJointCommonOneRoundStrictRight,
        profiledRawJointForceBothPivots,
        profiledRawJointHybridShadowPhaseLiveInstalled,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled]
    exact (congrArg Prod.fst hfull).trans hrequested
  have hlive : code.family.left () = some slot := by
    have h :=
      profiledRawJointHybridShadowPhaseLiveRightTag_tailRoot_leftLive A
        strategy hwin origin input
    dsimp only at h
    have hrootCode : (tag.tailRoot A strategy hwin).1.1 = .oneSided code := by
      simpa [tag, code] using tag.tailRoot_publicCode A strategy hwin
    rw [hrootCode] at h
    simpa [profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots, tag, code, slot] using h
  obtain ⟨oldMove, hmove, _hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  have hpair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitialOfState_leftPairAtPrefix
      A strategy hwin hreachable code hcode oldMove hmove false false
  simpa [profiledRawJointHybridMegaLinkedRightTagExactLeftPair, tag, child]
    using hpair

/-- Mirror represented-root theorem. -/
theorem
    profiledRawJointHybridMegaLinkedLeftTagExactRightPair_atPrefix
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
    let child := tag.markedBankChild A strategy hwin
    let exact :=
      profiledRawJointHybridMegaLinkedLeftTagExactRightPair A strategy hwin
        origin input
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
      A strategy hwin child exact.1 exact.2 := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
  let child := tag.markedBankChild A strategy hwin
  let code := tag.childIncidence A strategy hwin
  let slot := (tag.initialRightMove A strategy hwin).1.source
  have hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin child :=
    tag.markedBankChild_reachable A strategy hwin
  have hcode : child.2.1.1 = .oneSided code := by
    have hfull := tag.markedBankChild_code A strategy hwin
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
        hwin origin
    let rootReachable :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_reachable A
        strategy hwin origin
    let packet :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
        strategy hwin root.1 root.2 rootReachable
    let installed :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin origin
    let package :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
        strategy hwin origin
    have hrootExtra :
        root.2.1.2.2 =
          profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
            installed.world := by
      change
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
          strategy hwin origin).policy.run []).1.2.2 =
            profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
              installed.world
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank_rootExtra
          A strategy hwin origin
    have hmarked := packet.marked_current
    rw [hrootExtra] at hmarked
    have hsource : packet.source = .common installed.world :=
      (profiledRawJointHybridMarkedLiteralPrefixCurrentCompatible_initial_elim
        A strategy hwin installed.world packet.source hmarked).1
    have hpacketMove : packet.move.1 = some installed.rawMove := by
      calc
        packet.move.1 = packet.source.move A := packet.source_move.symm
        _ = ((.common installed.world :
              ProfiledRawJointHybridSemanticState A strategy).move A) := by
            rw [hsource]
        _ = some installed.rawMove := congrArg some installed.move_eq
    have hrootCode :
        root.2.1.1 =
          .common ((profiledRawJointCommonWorldFamily A installed.world
            ).incidenceCode A) := by
      have hinitial := congrArg (fun state ↦ state.1.1)
        package.policy.accepts.1.1
      simpa [root, package, installed] using hinitial
    have hrequested :
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
            hwin tag.origin).childCode A strategy hwin
            (tag.direction (A := A))).1 = .oneSided code := by
      change
        (root.childCode A strategy hwin (tag.direction (A := A))).1 =
          .oneSided code
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
          A strategy hwin root rootReachable,
        sourceFreeBeliefParentLinkedNext_fst]
      change
        profiledRawJointHybridNext A root.2.1.1 packet.move.1
            (tag.direction (A := A)) = .oneSided code
      rw [hrootCode, hpacketMove]
      rw [installed.incidence_eq]
      simp [tag, code, installed,
        profiledRawJointHybridShadowPhaseLiveLeftTag,
        ProfiledRawJointHybridShadowPhaseLiveTag.direction,
        ProfiledRawJointHybridShadowPhaseLiveTag.childIncidence,
        profiledRawJointHybridNext,
        profiledRawJointCommonActualDirection,
        profiledRawJointCommonOneRoundStrictLeft,
        profiledRawJointForceBothPivots,
        profiledRawJointHybridShadowPhaseLiveInstalled,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled]
    exact (congrArg Prod.fst hfull).trans hrequested
  have hlive : code.family.right () = some slot := by
    have h :=
      profiledRawJointHybridShadowPhaseLiveLeftTag_tailRoot_rightLive A
        strategy hwin origin input
    dsimp only at h
    have hrootCode : (tag.tailRoot A strategy hwin).1.1 = .oneSided code := by
      simpa [tag, code] using tag.tailRoot_publicCode A strategy hwin
    rw [hrootCode] at h
    simpa [profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots, tag, code, slot] using h
  obtain ⟨oldMove, hmove, _hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  have hpair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitialOfState_rightPairAtPrefix
      A strategy hwin hreachable code hcode oldMove hmove false false
  simpa [profiledRawJointHybridMegaLinkedLeftTagExactRightPair, tag, child]
    using hpair

/-! ## Identification with the operational selected controls -/

/-- Process two is blind at the first persistent left cut below a
strict-right creation tag.  This is its actual finite sender state, read from
the full-restart controller's locally selected control at time zero. -/
noncomputable def
    profiledRawJointHybridMegaLinkedRightTagOperationalLeftSenderAtEntry
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) (env : EnvironmentSequence In₁ In₂) :
    LeftSender A strategy hwin :=
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
  let retained := tag.markedRetainedChildTag A strategy hwin
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
    A strategy hwin retained env 0).2.2.1.2.1

/-- The receiving process-one coordinate at the same operational entry. -/
noncomputable def
    profiledRawJointHybridMegaLinkedRightTagOperationalLeftReceiverAtEntry
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) (env : EnvironmentSequence In₁ In₂) :
    LeftReceiver A strategy hwin :=
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
  let retained := tag.markedRetainedChildTag A strategy hwin
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
    A strategy hwin retained env 0).2.2.1.2.2

/-- At the first persistent cut, the actual blind sender is literally the
sender of the represented exact pair. -/
@[simp] theorem
    profiledRawJointHybridMegaLinkedRightTagOperationalLeftSenderAtEntry_eq
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) (env : EnvironmentSequence In₁ In₂) :
    profiledRawJointHybridMegaLinkedRightTagOperationalLeftSenderAtEntry A
        strategy hwin origin input env =
      (profiledRawJointHybridMegaLinkedRightTagExactLeftPair A strategy hwin
        origin input).1 := by
  rfl

/-- Receiver-coordinate mirror at the same entry. -/
@[simp] theorem
    profiledRawJointHybridMegaLinkedRightTagOperationalLeftReceiverAtEntry_eq
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) (env : EnvironmentSequence In₁ In₂) :
    profiledRawJointHybridMegaLinkedRightTagOperationalLeftReceiverAtEntry A
        strategy hwin origin input env =
      (profiledRawJointHybridMegaLinkedRightTagExactLeftPair A strategy hwin
        origin input).2 := by
  rfl

/-- Process-one/right-table mirror. -/
noncomputable def
    profiledRawJointHybridMegaLinkedLeftTagOperationalRightSenderAtEntry
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) (env : EnvironmentSequence In₁ In₂) :
    RightSender A strategy hwin :=
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
  let retained := tag.markedRetainedChildTag A strategy hwin
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
    A strategy hwin retained env 0).2.2.1.1.1

noncomputable def
    profiledRawJointHybridMegaLinkedLeftTagOperationalRightReceiverAtEntry
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) (env : EnvironmentSequence In₁ In₂) :
    RightReceiver A strategy hwin :=
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
  let retained := tag.markedRetainedChildTag A strategy hwin
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
    A strategy hwin retained env 0).2.2.1.1.2

@[simp] theorem
    profiledRawJointHybridMegaLinkedLeftTagOperationalRightSenderAtEntry_eq
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) (env : EnvironmentSequence In₁ In₂) :
    profiledRawJointHybridMegaLinkedLeftTagOperationalRightSenderAtEntry A
        strategy hwin origin input env =
      (profiledRawJointHybridMegaLinkedLeftTagExactRightPair A strategy hwin
        origin input).1 := by
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedLeftTagOperationalRightReceiverAtEntry_eq
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) (env : EnvironmentSequence In₁ In₂) :
    profiledRawJointHybridMegaLinkedLeftTagOperationalRightReceiverAtEntry A
        strategy hwin origin input env =
      (profiledRawJointHybridMegaLinkedLeftTagExactRightPair A strategy hwin
        origin input).2 := by
  rfl

/-! ## Unconditional base entry and the recurrent-cut adapter -/

/-- At the first strict-left persistent suffix below a strict-right front
handoff, the *operationally selected* pair is already represented at the
marked child.  Consequently the existing `physicalTail_exists` theorem may
be applied with no compatibility premise at this first cut. -/
theorem
    profiledRawJointHybridMegaLinkedRightTagFirstPersistentLeftPair_atPrefix
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) (env : EnvironmentSequence In₁ In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
      A strategy hwin (tag.markedBankChild A strategy hwin)
        (profiledRawJointHybridMegaLinkedRightTagOperationalLeftSenderAtEntry A
          strategy hwin origin input env)
        (profiledRawJointHybridMegaLinkedRightTagOperationalLeftReceiverAtEntry A
          strategy hwin origin input env) := by
  simpa [profiledRawJointHybridMegaLinkedRightTagOperationalLeftSenderAtEntry_eq,
    profiledRawJointHybridMegaLinkedRightTagOperationalLeftReceiverAtEntry_eq]
    using
      (profiledRawJointHybridMegaLinkedRightTagExactLeftPair_atPrefix A strategy
        hwin origin input)

/-- Strict-left/right-table mirror of the unconditional first-cut entry. -/
theorem
    profiledRawJointHybridMegaLinkedLeftTagFirstPersistentRightPair_atPrefix
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) (env : EnvironmentSequence In₁ In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
      A strategy hwin (tag.markedBankChild A strategy hwin)
        (profiledRawJointHybridMegaLinkedLeftTagOperationalRightSenderAtEntry A
          strategy hwin origin input env)
        (profiledRawJointHybridMegaLinkedLeftTagOperationalRightReceiverAtEntry A
          strategy hwin origin input env) := by
  simpa [profiledRawJointHybridMegaLinkedLeftTagOperationalRightSenderAtEntry_eq,
    profiledRawJointHybridMegaLinkedLeftTagOperationalRightReceiverAtEntry_eq]
    using
      (profiledRawJointHybridMegaLinkedLeftTagExactRightPair_atPrefix A strategy
        hwin origin input)

/-- Clean adapter for a later strict-left cut.  The represented exact pair
is supplied by the finite bank; the sole recurrent-seam input is that the
physical nonreceiver's retained sender has the same blind tail as the exact
sender.  No root/reachability/current-lane obligation leaks through this
interface. -/
theorem
    profiledRawJointHybridMegaLinkedRightTagPersistentLeftPair_mixedPhysicalTail_exists
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂)
    (actualSender : LeftSender A strategy hwin)
    (hcompatible :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftBlindTailCompatible
        A strategy hwin actualSender
          (profiledRawJointHybridMegaLinkedRightTagExactLeftPair A strategy hwin
            origin input).1)
    (row : PairedEntryRow) (inputs : Nat → In₁ × In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
    let exact :=
      profiledRawJointHybridMegaLinkedRightTagExactLeftPair A strategy hwin
        origin input
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
      (direction : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂))
      (semanticMember : ProcTwoPairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).left () =
          some semanticMember,
        ∃ (anchor : Bool) (past : List (In₁ × In₂)),
          exact.1 =
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
                A strategy hwin (tag.markedBankChild A strategy hwin) family
                  direction semanticMember hmember past ∧
            exact.2 =
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
                A strategy hwin (tag.markedBankChild A strategy hwin) family
                  direction semanticMember hmember anchor past ∧
            (let activation :=
                profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
                  A strategy hwin family direction semanticMember hmember anchor
              let descriptor :=
                profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A
                  activation
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren
                      A strategy hwin (tag.markedBankChild A strategy hwin))
              let tableEnv := OmegaWord.prependList past inputs
              A.AcceptsFrom
                  (pairedCodeStateForRow A row descriptor.source.1.1)
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord
                    A strategy hwin (tag.markedBankChild A strategy hwin) family
                      direction semanticMember hmember anchor row tableEnv) ∧
                ∀ n : Nat,
                  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMixedPairOutput
                      A strategy hwin actualSender exact.1 exact.2 row inputs n =
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord
                      A strategy hwin (tag.markedBankChild A strategy hwin)
                        family direction semanticMember hmember anchor row tableEnv
                          (past.length + n)).outputPair) := by
  exact
    (profiledRawJointHybridMegaLinkedRightTagExactLeftPair_atPrefix A strategy
      hwin origin input).mixedPhysicalTail_exists A strategy hwin hcompatible row
        inputs

/-- Right-table mirror of the recurrent-cut adapter. -/
theorem
    profiledRawJointHybridMegaLinkedLeftTagPersistentRightPair_mixedPhysicalTail_exists
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂)
    (actualSender : RightSender A strategy hwin)
    (hcompatible :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightBlindTailCompatible
        A strategy hwin actualSender
          (profiledRawJointHybridMegaLinkedLeftTagExactRightPair A strategy hwin
            origin input).1)
    (row : PairedEntryRow) (inputs : Nat → In₁ × In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
    let exact :=
      profiledRawJointHybridMegaLinkedLeftTagExactRightPair A strategy hwin
        origin input
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
      (direction : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂))
      (semanticMember : ProcOnePairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).right () =
          some semanticMember,
        ∃ (anchor : Bool) (past : List (In₂ × In₁)),
          exact.1 =
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
                A strategy hwin (tag.markedBankChild A strategy hwin) family
                  direction semanticMember hmember past ∧
            exact.2 =
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
                A strategy hwin (tag.markedBankChild A strategy hwin) family
                  direction semanticMember hmember anchor past ∧
            (let activation :=
                profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
                  A strategy hwin family direction semanticMember hmember anchor
              let descriptor :=
                profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A
                  activation
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren
                      A strategy hwin (tag.markedBankChild A strategy hwin))
              let tableEnv := OmegaWord.prependList past
                (fun k ↦ ((inputs k).2, (inputs k).1))
              A.AcceptsFrom
                  (pairedCodeStateForRow A row descriptor.source.1.1)
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord
                    A strategy hwin (tag.markedBankChild A strategy hwin) family
                      direction semanticMember hmember anchor row tableEnv) ∧
                ∀ n : Nat,
                  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMixedPairOutput
                      A strategy hwin actualSender exact.1 exact.2 row inputs n =
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord
                      A strategy hwin (tag.markedBankChild A strategy hwin)
                        family direction semanticMember hmember anchor row tableEnv
                          (past.length + n)).outputPair) := by
  exact
    (profiledRawJointHybridMegaLinkedLeftTagExactRightPair_atPrefix A strategy
      hwin origin input).mixedPhysicalTail_exists A strategy hwin hcompatible row
        inputs

end

end DetParityAutomaton

end DistributedSynthesis
