/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailHandoff

/-!
# A complete local adapter on the guarded-common tail core

This is the first concrete six-map adapter for the occurrence-sensitive
common tail.  Its reachable core covers the forever-common branch and both
eventually fixed strict sides:

* equal bare roots enter equal common shadows on a receive;
* common/common receives advance the selected rational policy;
* a first local non-receive starts the corresponding blind guarded owner;
* delivery of that owner resolves the opposite receiver; and
* the resolved owner/receiver pair continues locally forever.

The staged close is also installed on a receiver-side no-receive, preparing
the later alternating/recurrent extension.  Mixed switching receive pairs are
totalized by a fixed root fallback and are not claimed correct in this file.
Thus this module is an executable positive core, not yet the final alternating
adapter.

No transition takes a graph, orientation, leader bit, semantic world, or
history.
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

/-! ## Total fallbacks outside the stated core invariant -/

private def profiledRawJointGuardedCommonTailFallbackOne
    (root : InitialOne A strategy hwin) : Out₁ ×
      OneControl A strategy hwin initialBank :=
  (default, .initial root)

private def profiledRawJointGuardedCommonTailFallbackTwo
    (root : InitialTwo A strategy hwin) : Out₂ ×
      TwoControl A strategy hwin initialBank :=
  (default, .initial root)

/-! ## Exceptional non-receive maps -/

noncomputable def profiledRawJointGuardedCommonTailCoreNoRecvOne
    (state : ExceptionalOne A strategy hwin) (input : In₁) :
    Out₁ × OneControl A strategy hwin initialBank := by
  rcases state with common | rest
  · exact profiledRawJointGuardedCommonTailCommonNoRecvOne A strategy hwin
      initialBank common input
  · rcases rest with owner | receiver
    · exact
        profiledRawJointGuardedCommonTailRightOwnerNoRecvOne A strategy hwin
          initialBank owner input
    · exact
        profiledRawJointGuardedCommonLeftStagedStartRightOwner A strategy hwin
          initialBank receiver.close input

noncomputable def profiledRawJointGuardedCommonTailCoreNoRecvTwo
    (state : ExceptionalTwo A strategy hwin) (input : In₂) :
    Out₂ × TwoControl A strategy hwin initialBank := by
  rcases state with common | rest
  · exact profiledRawJointGuardedCommonTailCommonNoRecvTwo A strategy hwin
      initialBank common input
  · rcases rest with receiver | owner
    · exact
        profiledRawJointGuardedCommonRightStagedStartLeftOwner A strategy hwin
          initialBank receiver.close input
    · exact profiledRawJointGuardedCommonTailLeftOwnerNoRecvTwo A strategy
        hwin initialBank owner input

/-! ## Receive maps on the common and fixed-side core -/

noncomputable def profiledRawJointGuardedCommonTailCoreRecvOne
    (root : InitialOne A strategy hwin)
    (one : OneControl A strategy hwin initialBank) (inputOne : In₁)
    (two : TwoControl A strategy hwin initialBank) (inputTwo : In₂) :
    Out₁ × OneControl A strategy hwin initialBank := by
  classical
  cases one with
  | initial oneRoot =>
      cases two with
      | initial _ =>
          exact profiledRawJointGuardedCommonTailInitialRecvOne A strategy hwin
            initialBank oneRoot inputOne inputTwo
      | exceptional _ =>
          exact profiledRawJointGuardedCommonTailFallbackOne A strategy hwin
            initialBank root
      | rightReceiver _ _ =>
          exact profiledRawJointGuardedCommonTailFallbackOne A strategy hwin
            initialBank root
      | leftOwner _ _ =>
          exact profiledRawJointGuardedCommonTailFallbackOne A strategy hwin
            initialBank root
  | exceptional oneState =>
      rcases oneState with oneCommon | oneRest
      · cases two with
        | exceptional twoState =>
            rcases twoState with twoCommon | twoRest
            · exact
                profiledRawJointGuardedCommonTailCommonRecvOne A strategy hwin
                  initialBank oneCommon twoCommon inputOne inputTwo
            · rcases twoRest with _rightReceiver | leftOwner
              · exact
                  profiledRawJointGuardedCommonTailFallbackOne A strategy hwin
                    initialBank root
              · exact
                  profiledRawJointGuardedCommonTailResolveLeftOne A strategy
                    hwin initialBank oneCommon leftOwner inputOne inputTwo
        | initial _ =>
            exact profiledRawJointGuardedCommonTailFallbackOne A strategy hwin
              initialBank root
        | rightReceiver _ _ =>
            exact profiledRawJointGuardedCommonTailFallbackOne A strategy hwin
              initialBank root
        | leftOwner _ _ =>
            exact profiledRawJointGuardedCommonTailFallbackOne A strategy hwin
              initialBank root
      · rcases oneRest with _rightOwner | leftReceiver
        · exact profiledRawJointGuardedCommonTailFallbackOne A strategy hwin
            initialBank root
        · cases two with
          | exceptional twoState =>
              rcases twoState with _twoCommon | twoRest
              · exact
                  profiledRawJointGuardedCommonTailFallbackOne A strategy hwin
                    initialBank root
              · rcases twoRest with _rightReceiver | leftOwner
                · exact
                    profiledRawJointGuardedCommonTailFallbackOne A strategy
                      hwin initialBank root
                · exact
                    profiledRawJointGuardedCommonTailContinueLeftOne A strategy
                      hwin initialBank leftReceiver leftOwner inputOne inputTwo
          | initial _ =>
              exact profiledRawJointGuardedCommonTailFallbackOne A strategy
                hwin initialBank root
          | rightReceiver _ _ =>
              exact profiledRawJointGuardedCommonTailFallbackOne A strategy
                hwin initialBank root
          | leftOwner _ _ =>
              exact profiledRawJointGuardedCommonTailFallbackOne A strategy
                hwin initialBank root
  | rightOwner _ _ =>
      exact profiledRawJointGuardedCommonTailFallbackOne A strategy hwin
        initialBank root
  | leftReceiver _ _ =>
      exact profiledRawJointGuardedCommonTailFallbackOne A strategy hwin
        initialBank root

noncomputable def profiledRawJointGuardedCommonTailCoreRecvTwo
    (root : InitialTwo A strategy hwin)
    (two : TwoControl A strategy hwin initialBank) (inputTwo : In₂)
    (one : OneControl A strategy hwin initialBank) (inputOne : In₁) :
    Out₂ × TwoControl A strategy hwin initialBank := by
  classical
  cases two with
  | initial twoRoot =>
      cases one with
      | initial _ =>
          exact profiledRawJointGuardedCommonTailInitialRecvTwo A strategy hwin
            initialBank twoRoot inputTwo inputOne
      | exceptional _ =>
          exact profiledRawJointGuardedCommonTailFallbackTwo A strategy hwin
            initialBank root
      | rightOwner _ _ =>
          exact profiledRawJointGuardedCommonTailFallbackTwo A strategy hwin
            initialBank root
      | leftReceiver _ _ =>
          exact profiledRawJointGuardedCommonTailFallbackTwo A strategy hwin
            initialBank root
  | exceptional twoState =>
      rcases twoState with twoCommon | twoRest
      · cases one with
        | exceptional oneState =>
            rcases oneState with oneCommon | oneRest
            · exact
                profiledRawJointGuardedCommonTailCommonRecvTwo A strategy hwin
                  initialBank twoCommon oneCommon inputTwo inputOne
            · rcases oneRest with rightOwner | _leftReceiver
              · exact
                  profiledRawJointGuardedCommonTailResolveRightTwo A strategy
                    hwin initialBank twoCommon rightOwner inputTwo inputOne
              · exact
                  profiledRawJointGuardedCommonTailFallbackTwo A strategy hwin
                    initialBank root
        | initial _ =>
            exact profiledRawJointGuardedCommonTailFallbackTwo A strategy hwin
              initialBank root
        | rightOwner _ _ =>
            exact profiledRawJointGuardedCommonTailFallbackTwo A strategy hwin
              initialBank root
        | leftReceiver _ _ =>
            exact profiledRawJointGuardedCommonTailFallbackTwo A strategy hwin
              initialBank root
      · rcases twoRest with rightReceiver | _leftOwner
        · cases one with
          | exceptional oneState =>
              rcases oneState with _oneCommon | oneRest
              · exact
                  profiledRawJointGuardedCommonTailFallbackTwo A strategy hwin
                    initialBank root
              · rcases oneRest with rightOwner | _leftReceiver
                · exact
                    profiledRawJointGuardedCommonTailContinueRightTwo A strategy
                      hwin initialBank rightReceiver rightOwner inputTwo
                        inputOne
                · exact
                    profiledRawJointGuardedCommonTailFallbackTwo A strategy
                      hwin initialBank root
          | initial _ =>
              exact profiledRawJointGuardedCommonTailFallbackTwo A strategy
                hwin initialBank root
          | rightOwner _ _ =>
              exact profiledRawJointGuardedCommonTailFallbackTwo A strategy
                hwin initialBank root
          | leftReceiver _ _ =>
              exact profiledRawJointGuardedCommonTailFallbackTwo A strategy
                hwin initialBank root
        · exact profiledRawJointGuardedCommonTailFallbackTwo A strategy hwin
            initialBank root
  | rightReceiver _ _ =>
      exact profiledRawJointGuardedCommonTailFallbackTwo A strategy hwin
        initialBank root
  | leftOwner _ _ =>
      exact profiledRawJointGuardedCommonTailFallbackTwo A strategy hwin
        initialBank root

/-! ## The concrete six-map adapter and kernel -/

/-- Complete local adapter at one fixed common-policy tail root.  Its mixed
receive fallbacks are outside the core invariant documented above. -/
noncomputable def profiledRawJointGuardedCommonTailCoreAdapter
    (root : ProfiledRawJointGuardedInitialCommonControl A strategy hwin) :
    ProfiledRawJointGuardedHybridCombinedExceptionalAdapter A strategy hwin
      initialBank (InitialOne A strategy hwin) (InitialTwo A strategy hwin)
        (ExceptionalOne A strategy hwin) (ExceptionalTwo A strategy hwin)
    where
  initialOne := root
  initialTwo := root
  initialOutputOne := default
  initialOutputTwo := default
  initialNoRecvOne :=
    profiledRawJointGuardedCommonTailInitialNoRecvOne A strategy hwin
      initialBank
  exceptionalNoRecvOne :=
    profiledRawJointGuardedCommonTailCoreNoRecvOne A strategy hwin initialBank
  initialNoRecvTwo :=
    profiledRawJointGuardedCommonTailInitialNoRecvTwo A strategy hwin
      initialBank
  exceptionalNoRecvTwo :=
    profiledRawJointGuardedCommonTailCoreNoRecvTwo A strategy hwin initialBank
  otherRecvOne :=
    profiledRawJointGuardedCommonTailCoreRecvOne A strategy hwin initialBank
      root
  otherRecvTwo :=
    profiledRawJointGuardedCommonTailCoreRecvTwo A strategy hwin initialBank
      root

/-- Indexed physical kernel on the guarded-common tail core. -/
noncomputable def profiledRawJointGuardedCommonTailCoreKernel
    (root : ProfiledRawJointGuardedInitialCommonControl A strategy hwin) :=
  profiledRawJointGuardedHybridCombinedLeaderFreeKernel A strategy hwin
    initialBank
      (profiledRawJointGuardedCommonTailCoreAdapter A strategy hwin initialBank
        root)

end

end DetParityAutomaton

end DistributedSynthesis
