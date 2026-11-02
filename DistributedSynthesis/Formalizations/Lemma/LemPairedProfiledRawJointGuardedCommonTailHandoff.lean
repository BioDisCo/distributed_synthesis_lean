/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailFront

/-!
# Installing a staged guarded close in the combined recurrent family

A resolved guarded strict receiver stores an orientation-refined root package
for its latest checked target.  This file embeds that target in the combined
old-initial/guarded recurrent alphabet and exposes the four local restart
operations needed at a communication switch.

All definitions inspect only the finite staged payload and current local
inputs.  The right/left orientation in their names is the type of the stored
payload; it is not a graph or leader argument supplied at runtime.
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

private abbrev CombinedKey :=
  ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin initialBank

private abbrev OneInitial :=
  ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin

private abbrev TwoInitial :=
  ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin

private abbrev OneExceptional :=
  ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin

private abbrev TwoExceptional :=
  ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin

private abbrev OneControl :=
  ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin initialBank
    (OneInitial A strategy hwin) (OneExceptional A strategy hwin)

private abbrev TwoControl :=
  ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin initialBank
    (TwoInitial A strategy hwin) (TwoExceptional A strategy hwin)

/-! ## The exact combined keys -/

/-- Combined recurrent key selected by a staged strict-right close. -/
def profiledRawJointGuardedCommonRightStagedCombinedKey
    (close : ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin) :
    CombinedKey A strategy hwin initialBank :=
  profiledRawJointGuardedHybridCombinedChildOfGuarded A strategy hwin
    initialBank
    (profiledRawJointGuardedCommonTargetOfRight A strategy hwin close.handoff)

/-- Strict-left mirror. -/
def profiledRawJointGuardedCommonLeftStagedCombinedKey
    (close : ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin) :
    CombinedKey A strategy hwin initialBank :=
  profiledRawJointGuardedHybridCombinedChildOfGuarded A strategy hwin
    initialBank
    (profiledRawJointGuardedCommonTargetOfLeft A strategy hwin close.handoff)

/-! ## Literal recurrent roots carried by the stage -/

/-- Choose the checked left-oriented root stored by a right close. -/
private noncomputable def profiledRawJointGuardedCommonRightStagedPackage
    (close : ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin) :
    ProfiledRawJointGuardedCommonRightHandoffRootPackage A strategy hwin
      close.handoff :=
  Classical.choice close.root

/-- Choose the checked right-oriented root stored by a left close. -/
private noncomputable def profiledRawJointGuardedCommonLeftStagedPackage
    (close : ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin) :
    ProfiledRawJointGuardedCommonLeftHandoffRootPackage A strategy hwin
      close.handoff :=
  Classical.choice close.root

/-- Initial left owner at the combined key selected by a right close. -/
noncomputable def profiledRawJointGuardedCommonRightStagedInitialLeftOwner
    (close : ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin) :
    ProfiledRawJointGuardedHybridCombinedLeftOwner A strategy hwin initialBank
      (profiledRawJointGuardedCommonRightStagedCombinedKey A strategy hwin
        initialBank close) := by
  exact profiledRawJointGuardedCommonRightTargetInitialLeftOwner A strategy
    hwin close.handoff
      (profiledRawJointGuardedCommonRightStagedPackage A strategy hwin close)

/-- Initial left receiver at the same key and stored entry row. -/
noncomputable def profiledRawJointGuardedCommonRightStagedInitialLeftReceiver
    (close : ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin) :
    ProfiledRawJointGuardedHybridCombinedLeftReceiver A strategy hwin
      initialBank
      (profiledRawJointGuardedCommonRightStagedCombinedKey A strategy hwin
        initialBank close) := by
  exact profiledRawJointGuardedCommonRightTargetInitialLeftReceiver A strategy
    hwin close.handoff
      (profiledRawJointGuardedCommonRightStagedPackage A strategy hwin close)
      close.row

/-- Initial right owner selected by a staged left close. -/
noncomputable def profiledRawJointGuardedCommonLeftStagedInitialRightOwner
    (close : ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin) :
    ProfiledRawJointGuardedHybridCombinedRightOwner A strategy hwin initialBank
      (profiledRawJointGuardedCommonLeftStagedCombinedKey A strategy hwin
        initialBank close) := by
  exact profiledRawJointGuardedCommonLeftTargetInitialRightOwner A strategy
    hwin close.handoff
      (profiledRawJointGuardedCommonLeftStagedPackage A strategy hwin close)

/-- Initial right receiver at the same key and row. -/
noncomputable def profiledRawJointGuardedCommonLeftStagedInitialRightReceiver
    (close : ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin) :
    ProfiledRawJointGuardedHybridCombinedRightReceiver A strategy hwin
      initialBank
      (profiledRawJointGuardedCommonLeftStagedCombinedKey A strategy hwin
        initialBank close) := by
  exact profiledRawJointGuardedCommonLeftTargetInitialRightReceiver A strategy
    hwin close.handoff
      (profiledRawJointGuardedCommonLeftStagedPackage A strategy hwin close)
      close.row

/-! ## Execute the switching physical round -/

/-- Process two observes no receive after a right block, installs the staged
left owner, and executes its current input. -/
noncomputable def profiledRawJointGuardedCommonRightStagedStartLeftOwner
    (close : ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin)
    (input : In₂) : Out₂ × TwoControl A strategy hwin initialBank :=
  let key := profiledRawJointGuardedCommonRightStagedCombinedKey A strategy
    hwin initialBank close
  let next := stepProfiledRawJointUnitLeftPolicyOwner A strategy
    (profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
      initialBank key)
    (profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
      initialBank key)
    (profiledRawJointGuardedHybridCombinedControllerBank A strategy hwin
      initialBank key)
    (profiledRawJointGuardedCommonRightStagedInitialLeftOwner A strategy hwin
      initialBank close) input
  (next.1, .leftOwner key next.2)

/-- Process one installs the same staged left root and executes its current
receive. -/
noncomputable def profiledRawJointGuardedCommonRightStagedStartLeftReceiver
    (close : ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × OneControl A strategy hwin initialBank :=
  let key := profiledRawJointGuardedCommonRightStagedCombinedKey A strategy
    hwin initialBank close
  let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
    (profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
      initialBank key)
    (profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
      initialBank key)
    (profiledRawJointGuardedHybridCombinedControllerBank A strategy hwin
      initialBank key)
    (profiledRawJointGuardedCommonRightStagedInitialLeftReceiver A strategy
      hwin initialBank close)
    (profiledRawJointGuardedCommonRightStagedInitialLeftOwner A strategy hwin
      initialBank close) (own, delivered)
  (next.1, .leftReceiver key next.2)

/-- Strict-left close: process one starts the staged right owner. -/
noncomputable def profiledRawJointGuardedCommonLeftStagedStartRightOwner
    (close : ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin)
    (input : In₁) : Out₁ × OneControl A strategy hwin initialBank :=
  let key := profiledRawJointGuardedCommonLeftStagedCombinedKey A strategy hwin
    initialBank close
  let next := stepProfiledRawJointUnitRightPolicyOwner A strategy
    (profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
      initialBank key)
    (profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
      initialBank key)
    (profiledRawJointGuardedHybridCombinedControllerBank A strategy hwin
      initialBank key)
    (profiledRawJointGuardedCommonLeftStagedInitialRightOwner A strategy hwin
      initialBank close) input
  (next.1, .rightOwner key next.2)

/-- Strict-left close: process two starts the same staged right receiver. -/
noncomputable def profiledRawJointGuardedCommonLeftStagedStartRightReceiver
    (close : ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × TwoControl A strategy hwin initialBank :=
  let key := profiledRawJointGuardedCommonLeftStagedCombinedKey A strategy hwin
    initialBank close
  let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
    (profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
      initialBank key)
    (profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
      initialBank key)
    (profiledRawJointGuardedHybridCombinedControllerBank A strategy hwin
      initialBank key)
    (profiledRawJointGuardedCommonLeftStagedInitialRightReceiver A strategy
      hwin initialBank close)
    (profiledRawJointGuardedCommonLeftStagedInitialRightOwner A strategy hwin
      initialBank close) (own, delivered)
  (next.1, .rightReceiver key next.2)

end

end DetParityAutomaton

end DistributedSynthesis
