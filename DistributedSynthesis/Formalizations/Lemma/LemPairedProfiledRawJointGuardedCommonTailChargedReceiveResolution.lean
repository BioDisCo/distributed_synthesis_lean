/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailChargedCarrier

/-!
# Receive-side resolution of the charged one-bit carrier

On a receive, a process sees both finite local controls.  An ordinary partner
control identifies the preceding one-way case; the same charged shadow on both
sides identifies the preceding simultaneous close.  This file decodes every
pair of enlarged controls to one pair of ordinary controls.  The meaningful
reachable equations are stated separately; mismatched shadows are totalized
by their one-way interpretations.

The decoder takes the two delivered finite controls only.  It receives no
graph, orientation, leader bit, environment round, or semantic history.
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

/-! ## Local decoding -/

inductive ProfiledRawJointGuardedCommonTailChargedDecodedOne where
  | old (control : OldOne A strategy hwin initialBank)
  | right (shadow : RightShadow A strategy hwin)
  | left (shadow : LeftShadow A strategy hwin)

inductive ProfiledRawJointGuardedCommonTailChargedDecodedTwo where
  | old (control : OldTwo A strategy hwin initialBank)
  | right (shadow : RightShadow A strategy hwin)
  | left (shadow : LeftShadow A strategy hwin)

noncomputable def profiledRawJointGuardedCommonTailDecodeChargedOne
    (control : ProfiledRawJointGuardedCommonTailChargedOneControl A strategy
      hwin initialBank) :
    ProfiledRawJointGuardedCommonTailChargedDecodedOne A strategy hwin
      initialBank :=
  match control with
  | .initial state => .old (.initial state)
  | .exceptional (.inl state) => .old (.exceptional state)
  | .exceptional (.inr (.inl shadow)) => .right shadow
  | .exceptional (.inr (.inr shadow)) => .left shadow
  | .rightOwner key state => .old (.rightOwner key state)
  | .leftReceiver key state => .old (.leftReceiver key state)

noncomputable def profiledRawJointGuardedCommonTailDecodeChargedTwo
    (control : ProfiledRawJointGuardedCommonTailChargedTwoControl A strategy
      hwin initialBank) :
    ProfiledRawJointGuardedCommonTailChargedDecodedTwo A strategy hwin
      initialBank :=
  match control with
  | .initial state => .old (.initial state)
  | .exceptional (.inl state) => .old (.exceptional state)
  | .exceptional (.inr (.inl shadow)) => .right shadow
  | .exceptional (.inr (.inr shadow)) => .left shadow
  | .rightReceiver key state => .old (.rightReceiver key state)
  | .leftOwner key state => .old (.leftOwner key state)

@[simp] theorem profiledRawJointGuardedCommonTailDecodeLiftOldOne
    (control : OldOne A strategy hwin initialBank) :
    profiledRawJointGuardedCommonTailDecodeChargedOne A strategy hwin
        initialBank
        (profiledRawJointGuardedCommonTailLiftOldOne A strategy hwin
          initialBank control) =
      .old control := by
  cases control <;> rfl

@[simp] theorem profiledRawJointGuardedCommonTailDecodeLiftOldTwo
    (control : OldTwo A strategy hwin initialBank) :
    profiledRawJointGuardedCommonTailDecodeChargedTwo A strategy hwin
        initialBank
        (profiledRawJointGuardedCommonTailLiftOldTwo A strategy hwin
          initialBank control) =
      .old control := by
  cases control <;> rfl

/-! ## One canonical pair resolver -/

/-- Resolve the charged bit whenever both finite controls are available.
Same-orientation equal shadows select the simultaneous interpretation.  Every
other shadow combination selects the corresponding one-way candidate, which
also totalizes unreachable mismatches. -/
noncomputable def profiledRawJointGuardedCommonTailResolveChargedPair
    (one : ProfiledRawJointGuardedCommonTailChargedOneControl A strategy hwin
      initialBank)
    (two : ProfiledRawJointGuardedCommonTailChargedTwoControl A strategy hwin
      initialBank) :
    OldOne A strategy hwin initialBank × OldTwo A strategy hwin initialBank := by
  classical
  let decodedOne := profiledRawJointGuardedCommonTailDecodeChargedOne A
    strategy hwin initialBank one
  let decodedTwo := profiledRawJointGuardedCommonTailDecodeChargedTwo A
    strategy hwin initialBank two
  exact match decodedOne, decodedTwo with
  | .old oldOne, .old oldTwo => (oldOne, oldTwo)
  | .right shadow, .old oldTwo =>
      (shadow.oneCandidate A strategy hwin initialBank false, oldTwo)
  | .left shadow, .old oldTwo =>
      (shadow.oneCandidate A strategy hwin initialBank false, oldTwo)
  | .old oldOne, .right shadow =>
      (oldOne, shadow.twoCandidate A strategy hwin initialBank false)
  | .old oldOne, .left shadow =>
      (oldOne, shadow.twoCandidate A strategy hwin initialBank false)
  | .right oneShadow, .right twoShadow =>
      if twoShadow = oneShadow then
        (oneShadow.oneCandidate A strategy hwin initialBank true,
          oneShadow.twoCandidate A strategy hwin initialBank true)
      else
        (oneShadow.oneCandidate A strategy hwin initialBank false,
          twoShadow.twoCandidate A strategy hwin initialBank false)
  | .left oneShadow, .left twoShadow =>
      if twoShadow = oneShadow then
        (oneShadow.oneCandidate A strategy hwin initialBank true,
          oneShadow.twoCandidate A strategy hwin initialBank true)
      else
        (oneShadow.oneCandidate A strategy hwin initialBank false,
          twoShadow.twoCandidate A strategy hwin initialBank false)
  | .right oneShadow, .left twoShadow =>
      (oneShadow.oneCandidate A strategy hwin initialBank false,
        twoShadow.twoCandidate A strategy hwin initialBank false)
  | .left oneShadow, .right twoShadow =>
      (oneShadow.oneCandidate A strategy hwin initialBank false,
        twoShadow.twoCandidate A strategy hwin initialBank false)

/-! ## Exact reachable equations -/

@[simp] theorem profiledRawJointGuardedCommonTailResolveChargedPair_old
    (one : OldOne A strategy hwin initialBank)
    (two : OldTwo A strategy hwin initialBank) :
    profiledRawJointGuardedCommonTailResolveChargedPair A strategy hwin
        initialBank
        (profiledRawJointGuardedCommonTailLiftOldOne A strategy hwin
          initialBank one)
        (profiledRawJointGuardedCommonTailLiftOldTwo A strategy hwin
          initialBank two) =
      (one, two) := by
  simp [profiledRawJointGuardedCommonTailResolveChargedPair]

@[simp] theorem
    profiledRawJointGuardedCommonTailResolveChargedPair_right_same
    (shadow : RightShadow A strategy hwin) :
    profiledRawJointGuardedCommonTailResolveChargedPair A strategy hwin
        initialBank
        (.exceptional
          (profiledRawJointGuardedCommonTailChargedRightOne A strategy hwin
            shadow))
        (.exceptional
          (profiledRawJointGuardedCommonTailChargedRightTwo A strategy hwin
            shadow)) =
      (shadow.oneCandidate A strategy hwin initialBank true,
        shadow.twoCandidate A strategy hwin initialBank true) := by
  simp [profiledRawJointGuardedCommonTailResolveChargedPair,
    profiledRawJointGuardedCommonTailDecodeChargedOne,
    profiledRawJointGuardedCommonTailDecodeChargedTwo,
    profiledRawJointGuardedCommonTailChargedRightOne,
    profiledRawJointGuardedCommonTailChargedRightTwo]

@[simp] theorem
    profiledRawJointGuardedCommonTailResolveChargedPair_left_same
    (shadow : LeftShadow A strategy hwin) :
    profiledRawJointGuardedCommonTailResolveChargedPair A strategy hwin
        initialBank
        (.exceptional
          (profiledRawJointGuardedCommonTailChargedLeftOne A strategy hwin
            shadow))
        (.exceptional
          (profiledRawJointGuardedCommonTailChargedLeftTwo A strategy hwin
            shadow)) =
      (shadow.oneCandidate A strategy hwin initialBank true,
        shadow.twoCandidate A strategy hwin initialBank true) := by
  simp [profiledRawJointGuardedCommonTailResolveChargedPair,
    profiledRawJointGuardedCommonTailDecodeChargedOne,
    profiledRawJointGuardedCommonTailDecodeChargedTwo,
    profiledRawJointGuardedCommonTailChargedLeftOne,
    profiledRawJointGuardedCommonTailChargedLeftTwo]

@[simp] theorem
    profiledRawJointGuardedCommonTailResolveChargedPair_right_oneWayOne
    (shadow : RightShadow A strategy hwin)
    (two : OldTwo A strategy hwin initialBank) :
    profiledRawJointGuardedCommonTailResolveChargedPair A strategy hwin
        initialBank
        (.exceptional
          (profiledRawJointGuardedCommonTailChargedRightOne A strategy hwin
            shadow))
        (profiledRawJointGuardedCommonTailLiftOldTwo A strategy hwin
          initialBank two) =
      (shadow.oneCandidate A strategy hwin initialBank false, two) := by
  simp [profiledRawJointGuardedCommonTailResolveChargedPair,
    profiledRawJointGuardedCommonTailDecodeChargedOne,
    profiledRawJointGuardedCommonTailChargedRightOne]

@[simp] theorem
    profiledRawJointGuardedCommonTailResolveChargedPair_right_oneWayTwo
    (one : OldOne A strategy hwin initialBank)
    (shadow : RightShadow A strategy hwin) :
    profiledRawJointGuardedCommonTailResolveChargedPair A strategy hwin
        initialBank
        (profiledRawJointGuardedCommonTailLiftOldOne A strategy hwin
          initialBank one)
        (.exceptional
          (profiledRawJointGuardedCommonTailChargedRightTwo A strategy hwin
            shadow)) =
      (one, shadow.twoCandidate A strategy hwin initialBank false) := by
  simp [profiledRawJointGuardedCommonTailResolveChargedPair,
    profiledRawJointGuardedCommonTailDecodeChargedTwo,
    profiledRawJointGuardedCommonTailChargedRightTwo]

@[simp] theorem
    profiledRawJointGuardedCommonTailResolveChargedPair_left_oneWayOne
    (shadow : LeftShadow A strategy hwin)
    (two : OldTwo A strategy hwin initialBank) :
    profiledRawJointGuardedCommonTailResolveChargedPair A strategy hwin
        initialBank
        (.exceptional
          (profiledRawJointGuardedCommonTailChargedLeftOne A strategy hwin
            shadow))
        (profiledRawJointGuardedCommonTailLiftOldTwo A strategy hwin
          initialBank two) =
      (shadow.oneCandidate A strategy hwin initialBank false, two) := by
  simp [profiledRawJointGuardedCommonTailResolveChargedPair,
    profiledRawJointGuardedCommonTailDecodeChargedOne,
    profiledRawJointGuardedCommonTailChargedLeftOne]

@[simp] theorem
    profiledRawJointGuardedCommonTailResolveChargedPair_left_oneWayTwo
    (one : OldOne A strategy hwin initialBank)
    (shadow : LeftShadow A strategy hwin) :
    profiledRawJointGuardedCommonTailResolveChargedPair A strategy hwin
        initialBank
        (profiledRawJointGuardedCommonTailLiftOldOne A strategy hwin
          initialBank one)
        (.exceptional
          (profiledRawJointGuardedCommonTailChargedLeftTwo A strategy hwin
            shadow)) =
      (one, shadow.twoCandidate A strategy hwin initialBank false) := by
  simp [profiledRawJointGuardedCommonTailResolveChargedPair,
    profiledRawJointGuardedCommonTailDecodeChargedTwo,
    profiledRawJointGuardedCommonTailChargedLeftTwo]

end


end DetParityAutomaton

end DistributedSynthesis
