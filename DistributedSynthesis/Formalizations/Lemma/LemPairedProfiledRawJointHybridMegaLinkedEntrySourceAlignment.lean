/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedFullRestartAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedCommonRootState

/-!
# Executable source at a linked mega entry

The full-restart relay reconstructs its executable sender from the marked
one-sided child.  Its source is therefore not definitionally the source stored
by the phase-live tag.  The live-lane and restart-source readback theorems show
that the two slots are nevertheless equal.
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

/-- At a strict-right mega entry, the executable fresh left sender is rooted
at the exact left source already stored by the phase-live tag. -/
theorem profiledRawJointHybridMegaLinkedRightEntry_senderSource_eq_tagSource
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂)
    (env : EnvironmentSequence In₁ In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
    let retained := tag.markedRetainedChildTag A strategy hwin
    profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
            A strategy hwin retained env 0).2.1 false =
      (tag.initialLeftMove A strategy hwin).1.source := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
  let child := tag.markedBankChild A strategy hwin
  have hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin child := by
    simpa [tag, child] using
      (profiledRawJointHybridMegaLinkedRightTag_markedChild_leftRootReady A
        strategy hwin origin input)
  obtain ⟨code, slot, hcode, hlive, hsource⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftReady_restartRelay_senderSource
      A strategy hwin child hready false false
  have hmarkedCode :
      child.2.1.1 = .oneSided (tag.childIncidence A strategy hwin) := by
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
    have hpacketSource : packet.source = .common installed.world :=
      (profiledRawJointHybridMarkedLiteralPrefixCurrentCompatible_initial_elim
        A strategy hwin installed.world packet.source hmarked).1
    have hpacketMove : packet.move.1 = some installed.rawMove := by
      calc
        packet.move.1 = packet.source.move A := packet.source_move.symm
        _ = ((.common installed.world :
              ProfiledRawJointHybridSemanticState A strategy).move A) := by
            rw [hpacketSource]
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
            (tag.direction (A := A))).1 =
          .oneSided (tag.childIncidence A strategy hwin) := by
      change
        (root.childCode A strategy hwin (tag.direction (A := A))).1 =
          .oneSided (tag.childIncidence A strategy hwin)
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
          A strategy hwin root rootReachable,
        sourceFreeBeliefParentLinkedNext_fst]
      change
        profiledRawJointHybridNext A root.2.1.1 packet.move.1
            (tag.direction (A := A)) =
          .oneSided (tag.childIncidence A strategy hwin)
      rw [hrootCode, hpacketMove, installed.incidence_eq]
      simp [tag, installed,
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
  have hcodes : code = tag.childIncidence A strategy hwin := by
    exact ProfiledRawJointHybridCode.oneSided.inj
      (hcode.symm.trans hmarkedCode)
  have htagLive :
      (tag.childIncidence A strategy hwin).family.left () =
        some (tag.initialLeftMove A strategy hwin).1.source := by
    have hliveTag :=
      profiledRawJointHybridShadowPhaseLiveRightTag_tailRoot_leftLive A
        strategy hwin origin input
    dsimp only at hliveTag
    rw [tag.tailRoot_publicCode A strategy hwin] at hliveTag
    simpa [tag, profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots] using hliveTag
  have hslot : slot = (tag.initialLeftMove A strategy hwin).1.source := by
    rw [hcodes, htagLive] at hlive
    exact (Option.some.inj hlive).symm
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt_zero,
    child, tag] using hsource.trans hslot

/-- Strict-left / right-sender mirror. -/
theorem profiledRawJointHybridMegaLinkedLeftEntry_senderSource_eq_tagSource
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂)
    (env : EnvironmentSequence In₁ In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
    let retained := tag.markedRetainedChildTag A strategy hwin
    profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
            A strategy hwin retained env 0).1.1 false =
      (tag.initialRightMove A strategy hwin).1.source := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
  let child := tag.markedBankChild A strategy hwin
  have hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin child := by
    simpa [tag, child] using
      (profiledRawJointHybridMegaLinkedLeftTag_markedChild_rightRootReady A
        strategy hwin origin input)
  obtain ⟨code, slot, hcode, hlive, hsource⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightReady_restartRelay_senderSource
      A strategy hwin child hready false false
  have hmarkedCode :
      child.2.1.1 = .oneSided (tag.childIncidence A strategy hwin) := by
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
    have hpacketSource : packet.source = .common installed.world :=
      (profiledRawJointHybridMarkedLiteralPrefixCurrentCompatible_initial_elim
        A strategy hwin installed.world packet.source hmarked).1
    have hpacketMove : packet.move.1 = some installed.rawMove := by
      calc
        packet.move.1 = packet.source.move A := packet.source_move.symm
        _ = ((.common installed.world :
              ProfiledRawJointHybridSemanticState A strategy).move A) := by
            rw [hpacketSource]
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
            (tag.direction (A := A))).1 =
          .oneSided (tag.childIncidence A strategy hwin) := by
      change
        (root.childCode A strategy hwin (tag.direction (A := A))).1 =
          .oneSided (tag.childIncidence A strategy hwin)
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
          A strategy hwin root rootReachable,
        sourceFreeBeliefParentLinkedNext_fst]
      change
        profiledRawJointHybridNext A root.2.1.1 packet.move.1
            (tag.direction (A := A)) =
          .oneSided (tag.childIncidence A strategy hwin)
      rw [hrootCode, hpacketMove, installed.incidence_eq]
      simp [tag, installed,
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
  have hcodes : code = tag.childIncidence A strategy hwin := by
    exact ProfiledRawJointHybridCode.oneSided.inj
      (hcode.symm.trans hmarkedCode)
  have htagLive :
      (tag.childIncidence A strategy hwin).family.right () =
        some (tag.initialRightMove A strategy hwin).1.source := by
    have hliveTag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag_tailRoot_rightLive A
        strategy hwin origin input
    dsimp only at hliveTag
    rw [tag.tailRoot_publicCode A strategy hwin] at hliveTag
    simpa [tag, profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots] using hliveTag
  have hslot : slot = (tag.initialRightMove A strategy hwin).1.source := by
    rw [hcodes, htagLive] at hlive
    exact (Option.some.inj hlive).symm
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt_zero,
    child, tag] using hsource.trans hslot

end

end DetParityAutomaton

end DistributedSynthesis
