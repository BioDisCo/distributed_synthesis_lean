/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedSiblingClose
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedDeferredTailAdapter

/-!
# Guarded root-pinned front above the closed mega-linked adapter

This adapter adds the recurrent guarded sibling front to the already closed
mega-linked controller.  Old front and linked-tail states are embedded
unchanged.  The only overridden old row is the reachable pair of initial
shadows: instead of selecting unrelated post-common policies, it installs the
two guarded projections of one literal root-pinned common world.

A local receive cannot distinguish a strict receive from a simultaneous one.
Consequently a coupled receive always enters the corresponding guarded
receiver, while a non-receive exposes the matching guarded owner.  The same
delayed pattern already used by the initial sibling front then resolves
owner/receiver, receiver/receiver, and mixed recurrent rows.
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
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev OldExceptionalOne :=
  ProfiledRawJointHybridMegaLinkedExceptionalOne A strategy hwin controllers
    initialBank

private abbrev OldExceptionalTwo :=
  ProfiledRawJointHybridMegaLinkedExceptionalTwo A strategy hwin controllers
    initialBank

private abbrev OldOne :=
  ProfiledRawJointHybridMegaOneControl A strategy hwin initialBank Unit
    (OldExceptionalOne A strategy hwin controllers initialBank)

private abbrev OldTwo :=
  ProfiledRawJointHybridMegaTwoControl A strategy hwin initialBank Unit
    (OldExceptionalTwo A strategy hwin controllers initialBank)

/-! ## Added finite exceptional states -/

/-- Coupled ambiguity, guarded-right owner, or guarded-left receiver at
process one. -/
abbrev ProfiledRawJointHybridMegaGuardedFrontOne :=
  ProfiledRawJointHybridGuardedCoupledOne A strategy hwin ⊕
    (ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin ⊕
      ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy hwin)

/-- Coupled ambiguity, guarded-right receiver, or guarded-left owner at
process two. -/
abbrev ProfiledRawJointHybridMegaGuardedFrontTwo :=
  ProfiledRawJointHybridGuardedCoupledTwo A strategy hwin ⊕
    (ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy hwin ⊕
      ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin)

abbrev ProfiledRawJointHybridMegaGuardedLinkedExceptionalOne :=
  OldExceptionalOne A strategy hwin controllers initialBank ⊕
    ProfiledRawJointHybridMegaGuardedFrontOne A strategy hwin

abbrev ProfiledRawJointHybridMegaGuardedLinkedExceptionalTwo :=
  OldExceptionalTwo A strategy hwin controllers initialBank ⊕
    ProfiledRawJointHybridMegaGuardedFrontTwo A strategy hwin

private abbrev ExceptionalOne :=
  ProfiledRawJointHybridMegaGuardedLinkedExceptionalOne A strategy hwin
    controllers initialBank

private abbrev ExceptionalTwo :=
  ProfiledRawJointHybridMegaGuardedLinkedExceptionalTwo A strategy hwin
    controllers initialBank

private abbrev OneControl :=
  ProfiledRawJointHybridMegaOneControl A strategy hwin initialBank Unit
    (ExceptionalOne A strategy hwin controllers initialBank)

private abbrev TwoControl :=
  ProfiledRawJointHybridMegaTwoControl A strategy hwin initialBank Unit
    (ExceptionalTwo A strategy hwin controllers initialBank)

set_option synthInstance.maxHeartbeats 1000000 in
noncomputable instance
    profiledRawJointHybridMegaGuardedLinkedExceptionalOneFintype :
    Fintype (ExceptionalOne A strategy hwin controllers initialBank) := by
  classical
  infer_instance

set_option synthInstance.maxHeartbeats 1000000 in
noncomputable instance
    profiledRawJointHybridMegaGuardedLinkedExceptionalTwoFintype :
    Fintype (ExceptionalTwo A strategy hwin controllers initialBank) := by
  classical
  infer_instance

/-! ## Cast-free embeddings and old-state projection -/

def profiledRawJointHybridMegaGuardedLinkedLiftOldOne
    (state : OldOne A strategy hwin controllers initialBank) :
    OneControl A strategy hwin controllers initialBank :=
  match state with
  | .initial initial => .initial initial
  | .exceptional exceptional => .exceptional (.inl exceptional)
  | .rightOwner child owner => .rightOwner child owner
  | .leftReceiver child receiver => .leftReceiver child receiver

def profiledRawJointHybridMegaGuardedLinkedLiftOldTwo
    (state : OldTwo A strategy hwin controllers initialBank) :
    TwoControl A strategy hwin controllers initialBank :=
  match state with
  | .initial initial => .initial initial
  | .exceptional exceptional => .exceptional (.inl exceptional)
  | .rightReceiver child receiver => .rightReceiver child receiver
  | .leftOwner child owner => .leftOwner child owner

def profiledRawJointHybridMegaGuardedLinkedOldOne?
    (state : OneControl A strategy hwin controllers initialBank) :
    Option (OldOne A strategy hwin controllers initialBank) :=
  match state with
  | .initial initial => some (.initial initial)
  | .exceptional (.inl exceptional) => some (.exceptional exceptional)
  | .exceptional (.inr _) => none
  | .rightOwner child owner => some (.rightOwner child owner)
  | .leftReceiver child receiver => some (.leftReceiver child receiver)

def profiledRawJointHybridMegaGuardedLinkedOldTwo?
    (state : TwoControl A strategy hwin controllers initialBank) :
    Option (OldTwo A strategy hwin controllers initialBank) :=
  match state with
  | .initial initial => some (.initial initial)
  | .exceptional (.inl exceptional) => some (.exceptional exceptional)
  | .exceptional (.inr _) => none
  | .rightReceiver child receiver => some (.rightReceiver child receiver)
  | .leftOwner child owner => some (.leftOwner child owner)

/-! ## Guarded non-receive rows -/

noncomputable def profiledRawJointHybridMegaGuardedLinkedNoRecvOne
    (state : ProfiledRawJointHybridMegaGuardedFrontOne A strategy hwin)
    (input : In₁) :
    Out₁ × OneControl A strategy hwin controllers initialBank := by
  classical
  rcases state with coupled | active
  · let next := startProfiledRawJointHybridGuardedRightOwner A strategy hwin
      coupled input
    exact (next.1, .exceptional (.inr (.inr (.inl next.2))))
  · rcases active with rightOwner | leftReceiver
    · let next := stepProfiledRawJointHybridGuardedRightOwner A strategy hwin
        rightOwner input
      exact (next.1, .exceptional (.inr (.inr (.inl next.2))))
    · exact match
          profiledRawJointHybridMegaGuardedLeftCloseOwnerOne? A strategy hwin
            initialBank leftReceiver input with
      | none => (default, .exceptional (.inr (.inr (.inr leftReceiver))))
      | some installed =>
          (installed.1, .rightOwner installed.2.1 installed.2.2)

noncomputable def profiledRawJointHybridMegaGuardedLinkedNoRecvTwo
    (state : ProfiledRawJointHybridMegaGuardedFrontTwo A strategy hwin)
    (input : In₂) :
    Out₂ × TwoControl A strategy hwin controllers initialBank := by
  classical
  rcases state with coupled | active
  · let next := startProfiledRawJointHybridGuardedLeftOwner A strategy hwin
      coupled input
    exact (next.1, .exceptional (.inr (.inr (.inr next.2))))
  · rcases active with rightReceiver | leftOwner
    · exact match
          profiledRawJointHybridMegaGuardedRightCloseOwnerTwo? A strategy hwin
            initialBank rightReceiver input with
      | none =>
          (default, .exceptional (.inr (.inr (.inl rightReceiver))))
      | some installed =>
          (installed.1, .leftOwner installed.2.1 installed.2.2)
    · let next := stepProfiledRawJointHybridGuardedLeftOwner A strategy hwin
        leftOwner input
      exact (next.1, .exceptional (.inr (.inr (.inr next.2))))

/-! ## Guarded receive rows -/

/-- Continue an already installed ordinary left receiver while the other
endpoint is still carrying the synchronized guarded-right target. -/
noncomputable def
    profiledRawJointHybridMegaGuardedLinkedContinueLeftReceiverOne
    (key : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (receiver : ProfiledRawJointHybridMegaLeftReceiver A strategy hwin
      initialBank key)
    (front : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    Out₁ × OneControl A strategy hwin controllers initialBank := by
  classical
  cases hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
        initialBank front with
  | none => exact (default, .leftReceiver key receiver)
  | some root =>
      by_cases hkey : root.1 = key
      · subst key
        let source := profiledRawJointHybridMegaChildSource A strategy hwin
          initialBank root.1
        let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
          initialBank root.1
        let bank := profiledRawJointHybridMegaChildControllerBank A strategy
          hwin initialBank root.1
        let owner := initialProfiledRawJointUnitLeftPolicyOwner A strategy
          source policy bank root.2
        let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
          source policy bank receiver owner (inputOne, inputTwo)
        exact (next.1, .leftReceiver root.1 next.2)
      · exact (default, .leftReceiver key receiver)

/-- Process-two mixed-row mirror. -/
noncomputable def
    profiledRawJointHybridMegaGuardedLinkedContinueRightReceiverTwo
    (key : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (receiver : ProfiledRawJointHybridMegaRightReceiver A strategy hwin
      initialBank key)
    (front : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    Out₂ × TwoControl A strategy hwin controllers initialBank := by
  classical
  cases hroot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
        initialBank front with
  | none => exact (default, .rightReceiver key receiver)
  | some root =>
      by_cases hkey : root.1 = key
      · subst key
        let source := profiledRawJointHybridMegaChildSource A strategy hwin
          initialBank root.1
        let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
          initialBank root.1
        let bank := profiledRawJointHybridMegaChildControllerBank A strategy
          hwin initialBank root.1
        let owner := initialProfiledRawJointUnitRightPolicyOwner A strategy
          source policy bank root.2
        let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
          source policy bank receiver owner (inputTwo, inputOne)
        exact (next.1, .rightReceiver root.1 next.2)
      · exact (default, .rightReceiver key receiver)

noncomputable def profiledRawJointHybridMegaGuardedLinkedRecvOne
    (fallbackTag : RetainedTag A strategy hwin)
    (one : OneControl A strategy hwin controllers initialBank)
    (inputOne : In₁)
    (two : TwoControl A strategy hwin controllers initialBank)
    (inputTwo : In₂) :
    Out₁ × OneControl A strategy hwin controllers initialBank := by
  classical
  match one, two with
  | .exceptional (.inl (.inl (.inr (.inl _shadowOne)))),
      .exceptional (.inl (.inl (.inr (.inl shadowTwo)))) =>
      let oldNext := profiledRawJointHybridMegaInitialToCoupledOne A strategy
        hwin controllers shadowTwo inputOne inputTwo
      let installation :
          ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin :=
        .inl oldNext.2.1
      let guarded := initialProfiledRawJointHybridGuardedCoupledOne A strategy
        hwin installation
      exact (oldNext.1, .exceptional (.inr (.inl guarded)))
  | .exceptional (.inr (.inl _coupledOne)),
      .exceptional (.inr (.inl coupledTwo)) =>
      let next := startProfiledRawJointHybridGuardedLeftReceiver A strategy
        hwin coupledTwo inputOne inputTwo
      exact (next.1, .exceptional (.inr (.inr (.inr next.2))))
  | .exceptional (.inr (.inr (.inl _rightOwner))),
      .exceptional (.inr (.inr (.inl rightReceiver))) =>
      match profiledRawJointHybridMegaGuardedRightCloseReceiverOne? A strategy
          hwin initialBank rightReceiver inputOne inputTwo with
      | none => exact (default, one)
      | some installed =>
          exact (installed.1, .leftReceiver installed.2.1 installed.2.2)
  | .exceptional (.inr (.inr (.inr leftReceiver))),
      .exceptional (.inr (.inr (.inr leftOwner))) =>
      let next := stepProfiledRawJointHybridGuardedLeftReceiver A strategy
        hwin leftReceiver leftOwner inputOne inputTwo
      exact (next.1, .exceptional (.inr (.inr (.inr next.2))))
  | .exceptional (.inr (.inr (.inr _leftReceiver))),
      .exceptional (.inr (.inr (.inl rightReceiver))) =>
      match
          profiledRawJointHybridMegaGuardedRightCloseReceiverOneBoth? A
            strategy hwin initialBank rightReceiver inputOne inputTwo with
      | none => exact (default, one)
      | some installed =>
          exact (installed.1, .leftReceiver installed.2.1 installed.2.2)
  | .leftReceiver key receiver,
      .exceptional (.inr (.inr (.inl rightReceiver))) =>
      exact
        profiledRawJointHybridMegaGuardedLinkedContinueLeftReceiverOne A
          strategy hwin controllers initialBank key receiver rightReceiver
            inputOne inputTwo
  | .exceptional (.inr (.inr (.inr _leftReceiver))),
      .rightReceiver key receiver =>
      let next :=
        profiledRawJointHybridMegaLinkedStartLeftReceiverFromRightReceiverOne A
          strategy hwin controllers initialBank key receiver inputOne inputTwo
      exact (next.1,
        profiledRawJointHybridMegaGuardedLinkedLiftOldOne A strategy hwin
          controllers initialBank
            (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
              controllers initialBank next.2))
  | _, _ =>
      match profiledRawJointHybridMegaGuardedLinkedOldOne? A strategy hwin
          controllers initialBank one,
        profiledRawJointHybridMegaGuardedLinkedOldTwo? A strategy hwin
          controllers initialBank two with
      | some oldOne, some oldTwo =>
          let old :=
            profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A
              strategy hwin controllers initialBank
                fallbackTag
          let next := old.otherRecvOne oldOne inputOne oldTwo inputTwo
          exact (next.1,
            profiledRawJointHybridMegaGuardedLinkedLiftOldOne A strategy hwin
              controllers initialBank next.2)
      | _, _ => exact (default, one)

noncomputable def profiledRawJointHybridMegaGuardedLinkedRecvTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (two : TwoControl A strategy hwin controllers initialBank)
    (inputTwo : In₂)
    (one : OneControl A strategy hwin controllers initialBank)
    (inputOne : In₁) :
    Out₂ × TwoControl A strategy hwin controllers initialBank := by
  classical
  match two, one with
  | .exceptional (.inl (.inl (.inr (.inl _shadowTwo)))),
      .exceptional (.inl (.inl (.inr (.inl shadowOne)))) =>
      let oldNext := profiledRawJointHybridMegaInitialToCoupledTwo A strategy
        hwin controllers shadowOne inputTwo inputOne
      let installation :
          ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin :=
        .inl oldNext.2.1
      let guarded := initialProfiledRawJointHybridGuardedCoupledTwo A strategy
        hwin installation
      exact (oldNext.1, .exceptional (.inr (.inl guarded)))
  | .exceptional (.inr (.inl _coupledTwo)),
      .exceptional (.inr (.inl coupledOne)) =>
      let next := startProfiledRawJointHybridGuardedRightReceiver A strategy
        hwin coupledOne inputTwo inputOne
      exact (next.1, .exceptional (.inr (.inr (.inl next.2))))
  | .exceptional (.inr (.inr (.inl rightReceiver))),
      .exceptional (.inr (.inr (.inl rightOwner))) =>
      let next := stepProfiledRawJointHybridGuardedRightReceiver A strategy
        hwin rightReceiver rightOwner inputTwo inputOne
      exact (next.1, .exceptional (.inr (.inr (.inl next.2))))
  | .exceptional (.inr (.inr (.inr _leftOwner))),
      .exceptional (.inr (.inr (.inr leftReceiver))) =>
      match profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo? A strategy
          hwin initialBank leftReceiver inputTwo inputOne with
      | none => exact (default, two)
      | some installed =>
          exact (installed.1, .rightReceiver installed.2.1 installed.2.2)
  | .exceptional (.inr (.inr (.inl rightReceiver))),
      .exceptional (.inr (.inr (.inr _leftReceiver))) =>
      match
          profiledRawJointHybridMegaGuardedRightCloseReceiverTwoBoth? A
            strategy hwin initialBank rightReceiver inputTwo inputOne with
      | none => exact (default, two)
      | some installed =>
          exact (installed.1, .rightReceiver installed.2.1 installed.2.2)
  | .exceptional (.inr (.inr (.inl _rightReceiver))),
      .leftReceiver key receiver =>
      let next :=
        profiledRawJointHybridMegaLinkedStartRightReceiverFromLeftReceiverTwo A
          strategy hwin controllers initialBank key receiver inputTwo inputOne
      exact (next.1,
        profiledRawJointHybridMegaGuardedLinkedLiftOldTwo A strategy hwin
          controllers initialBank
            (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
              controllers initialBank next.2))
  | .rightReceiver key receiver,
      .exceptional (.inr (.inr (.inr leftReceiver))) =>
      exact
        profiledRawJointHybridMegaGuardedLinkedContinueRightReceiverTwo A
          strategy hwin controllers initialBank key receiver leftReceiver
            inputTwo inputOne
  | _, _ =>
      match profiledRawJointHybridMegaGuardedLinkedOldTwo? A strategy hwin
          controllers initialBank two,
        profiledRawJointHybridMegaGuardedLinkedOldOne? A strategy hwin
          controllers initialBank one with
      | some oldTwo, some oldOne =>
          let old :=
            profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A
              strategy hwin controllers initialBank
                fallbackTag
          let next := old.otherRecvTwo oldTwo inputTwo oldOne inputOne
          exact (next.1,
            profiledRawJointHybridMegaGuardedLinkedLiftOldTwo A strategy hwin
              controllers initialBank next.2)
      | _, _ => exact (default, two)

/-! ## Closed extended adapter and kernel -/

/-- The old closed adapter with only the guarded reachable rows overridden.
All ordinary recurrent transitions are still supplied by the same seven-way
indexed mega family. -/
noncomputable def
    profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter
    (fallbackTag : RetainedTag A strategy hwin) :
    ProfiledRawJointHybridMegaExceptionalAdapter A strategy hwin initialBank
      Unit Unit
      (ExceptionalOne A strategy hwin controllers initialBank)
      (ExceptionalTwo A strategy hwin controllers initialBank) := by
  classical
  let old :=
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag
  exact
    { initialOne := old.initialOne
      initialTwo := old.initialTwo
      initialOutputOne := old.initialOutputOne
      initialOutputTwo := old.initialOutputTwo
      initialNoRecvOne := fun state input =>
        let next := old.initialNoRecvOne state input
        (next.1,
          profiledRawJointHybridMegaGuardedLinkedLiftOldOne A strategy hwin
            controllers initialBank next.2)
      exceptionalNoRecvOne := fun state input =>
        match state with
        | .inl oldState =>
            let next := old.exceptionalNoRecvOne oldState input
            (next.1,
              profiledRawJointHybridMegaGuardedLinkedLiftOldOne A strategy
                hwin controllers initialBank next.2)
        | .inr guarded =>
            profiledRawJointHybridMegaGuardedLinkedNoRecvOne A strategy hwin
              controllers initialBank guarded input
      initialNoRecvTwo := fun state input =>
        let next := old.initialNoRecvTwo state input
        (next.1,
          profiledRawJointHybridMegaGuardedLinkedLiftOldTwo A strategy hwin
            controllers initialBank next.2)
      exceptionalNoRecvTwo := fun state input =>
        match state with
        | .inl oldState =>
            let next := old.exceptionalNoRecvTwo oldState input
            (next.1,
              profiledRawJointHybridMegaGuardedLinkedLiftOldTwo A strategy
                hwin controllers initialBank next.2)
        | .inr guarded =>
            profiledRawJointHybridMegaGuardedLinkedNoRecvTwo A strategy hwin
              controllers initialBank guarded input
      otherRecvOne :=
        profiledRawJointHybridMegaGuardedLinkedRecvOne A strategy hwin
          controllers initialBank fallbackTag
      otherRecvTwo :=
        profiledRawJointHybridMegaGuardedLinkedRecvTwo A strategy hwin
          controllers initialBank fallbackTag }

/-- Closed leader-free kernel with the guarded recurrent common front. -/
noncomputable def profiledRawJointHybridMegaGuardedLinkedLeaderFreeKernel
    (fallbackTag : RetainedTag A strategy hwin) :=
  profiledRawJointHybridMegaLeaderFreeKernel A strategy hwin initialBank
    (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag)

abbrev MegaGuardedLinkedPhysicalController
    (fallbackTag : RetainedTag A strategy hwin) :=
  (profiledRawJointHybridMegaGuardedLinkedLeaderFreeKernel A strategy hwin
    controllers initialBank fallbackTag).physicalController

/-! ## Reachable adapter equations -/

/-- Embed a state of the original finite mega front through the linked and
guarded extension layers. -/
def profiledRawJointHybridMegaGuardedLinkedLiftFrontOne
    (state : ProfiledRawJointHybridMegaOneControl A strategy hwin initialBank
      Unit (ProfiledRawJointHybridMegaExceptionalOne A strategy hwin
        controllers initialBank)) :
    OneControl A strategy hwin controllers initialBank :=
  profiledRawJointHybridMegaGuardedLinkedLiftOldOne A strategy hwin
    controllers initialBank
      (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
        initialBank state)

def profiledRawJointHybridMegaGuardedLinkedLiftFrontTwo
    (state : ProfiledRawJointHybridMegaTwoControl A strategy hwin initialBank
      Unit (ProfiledRawJointHybridMegaExceptionalTwo A strategy hwin
        controllers initialBank)) :
    TwoControl A strategy hwin controllers initialBank :=
  profiledRawJointHybridMegaGuardedLinkedLiftOldTwo A strategy hwin
    controllers initialBank
      (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
        initialBank state)

@[simp] theorem
    profiledRawJointHybridMegaGuardedLinked_initialShadows_recvOne
    (fallbackTag : RetainedTag A strategy hwin)
    (shadowOne : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (shadowTwo : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag).otherRecvOne
        (profiledRawJointHybridMegaGuardedLinkedLiftFrontOne A strategy hwin
          controllers initialBank
            (.exceptional
              (profiledRawJointHybridMegaExceptionalOneOfInitialShadow A
                strategy hwin controllers initialBank shadowOne))) inputOne
        (profiledRawJointHybridMegaGuardedLinkedLiftFrontTwo A strategy hwin
          controllers initialBank
            (.exceptional
              (profiledRawJointHybridMegaExceptionalTwoOfInitialShadow A
                strategy hwin controllers initialBank shadowTwo))) inputTwo =
      let oldNext := profiledRawJointHybridMegaInitialToCoupledOne A strategy
        hwin controllers shadowTwo inputOne inputTwo
      let installation :
          ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin :=
        .inl oldNext.2.1
      (oldNext.1,
        .exceptional (.inr (.inl
          (initialProfiledRawJointHybridGuardedCoupledOne A strategy hwin
            installation)))) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaGuardedLinked_initialShadows_recvTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (shadowTwo : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (shadowOne : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag).otherRecvTwo
        (profiledRawJointHybridMegaGuardedLinkedLiftFrontTwo A strategy hwin
          controllers initialBank
            (.exceptional
              (profiledRawJointHybridMegaExceptionalTwoOfInitialShadow A
                strategy hwin controllers initialBank shadowTwo))) inputTwo
        (profiledRawJointHybridMegaGuardedLinkedLiftFrontOne A strategy hwin
          controllers initialBank
            (.exceptional
              (profiledRawJointHybridMegaExceptionalOneOfInitialShadow A
                strategy hwin controllers initialBank shadowOne))) inputOne =
      let oldNext := profiledRawJointHybridMegaInitialToCoupledTwo A strategy
        hwin controllers shadowOne inputTwo inputOne
      let installation :
          ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin :=
        .inl oldNext.2.1
      (oldNext.1,
        .exceptional (.inr (.inl
          (initialProfiledRawJointHybridGuardedCoupledTwo A strategy hwin
            installation)))) :=
  rfl

@[simp] theorem profiledRawJointHybridMegaGuardedLinked_coupled_recvOne
    (fallbackTag : RetainedTag A strategy hwin)
    (one : ProfiledRawJointHybridGuardedCoupledOne A strategy hwin)
    (two : ProfiledRawJointHybridGuardedCoupledTwo A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag).otherRecvOne
        (.exceptional (.inr (.inl one))) inputOne
        (.exceptional (.inr (.inl two))) inputTwo =
      let next := startProfiledRawJointHybridGuardedLeftReceiver A strategy
        hwin two inputOne inputTwo
      (next.1, .exceptional (.inr (.inr (.inr next.2)))) :=
  rfl

@[simp] theorem profiledRawJointHybridMegaGuardedLinked_coupled_recvTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (two : ProfiledRawJointHybridGuardedCoupledTwo A strategy hwin)
    (one : ProfiledRawJointHybridGuardedCoupledOne A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag).otherRecvTwo
        (.exceptional (.inr (.inl two))) inputTwo
        (.exceptional (.inr (.inl one))) inputOne =
      let next := startProfiledRawJointHybridGuardedRightReceiver A strategy
        hwin one inputTwo inputOne
      (next.1, .exceptional (.inr (.inr (.inl next.2)))) :=
  rfl

@[simp] theorem profiledRawJointHybridMegaGuardedLinked_coupled_noRecvOne
    (fallbackTag : RetainedTag A strategy hwin)
    (one : ProfiledRawJointHybridGuardedCoupledOne A strategy hwin)
    (input : In₁) :
    (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag).exceptionalNoRecvOne
        (.inr (.inl one)) input =
      let next := startProfiledRawJointHybridGuardedRightOwner A strategy hwin
        one input
      (next.1, .exceptional (.inr (.inr (.inl next.2)))) :=
  rfl

@[simp] theorem profiledRawJointHybridMegaGuardedLinked_coupled_noRecvTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (two : ProfiledRawJointHybridGuardedCoupledTwo A strategy hwin)
    (input : In₂) :
    (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag).exceptionalNoRecvTwo
        (.inr (.inl two)) input =
      let next := startProfiledRawJointHybridGuardedLeftOwner A strategy hwin
        two input
      (next.1, .exceptional (.inr (.inr (.inr next.2)))) :=
  rfl

end


end DetParityAutomaton

end DistributedSynthesis
