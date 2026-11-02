/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailChargedReceiveResolution

/-!
# One graph-blind receive dispatcher for the charged common tail

The enlarged finite carrier has two receive duties.  An ordinary
owner/common pair at a strict cross must enter the charged table, while an
already charged pair must first resolve its one hidden bit and then execute
the resulting ordinary receive.  This module combines those duties into one
total local map for each process.

The only orientation tests below inspect the constructors of stored finite
phase tags.  No executable map accepts a graph, a leader bit, a hierarchy
side, an environment round, or a semantic history.
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

private abbrev ChargedOne :=
  ProfiledRawJointGuardedCommonTailChargedOneControl A strategy hwin
    initialBank

private abbrev ChargedTwo :=
  ProfiledRawJointGuardedCommonTailChargedTwoControl A strategy hwin
    initialBank

/-! ## Recover the two represented pending shapes -/

/-- The stored phase tags determine whether an ordinary pair is exactly a
right-pending owner/common pair. -/
noncomputable def
    profiledRawJointGuardedCommonTailRightPendingOfOldPair?
    (one : OldOne A strategy hwin initialBank)
    (two : OldTwo A strategy hwin initialBank) :
    Option (ProfiledRawJointGuardedCommonRightPending A strategy hwin) :=
  match one, two with
  | .exceptional (.inr (.inl owner)), .exceptional (.inl receiver) =>
      profiledRawJointGuardedRightLocalFactorizationPendingOf? A strategy hwin
        owner receiver
  | _, _ => none

/-- Strict-left mirror. -/
noncomputable def
    profiledRawJointGuardedCommonTailLeftPendingOfOldPair?
    (one : OldOne A strategy hwin initialBank)
    (two : OldTwo A strategy hwin initialBank) :
    Option (ProfiledRawJointGuardedCommonLeftPending A strategy hwin) :=
  match one, two with
  | .exceptional (.inl receiver), .exceptional (.inr (.inr owner)) =>
      profiledRawJointGuardedLeftLocalFactorizationPendingOf? A strategy hwin
        receiver owner
  | _, _ => none

@[simp] theorem
    profiledRawJointGuardedCommonTailRightPendingOfOldPair?_components
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin) :
    profiledRawJointGuardedCommonTailRightPendingOfOldPair? A strategy hwin
        initialBank
        (.exceptional
          (profiledRawJointGuardedCommonTailOneOfRightOwner A strategy hwin
            pending.owner))
        (.exceptional
          (profiledRawJointGuardedCommonTailTwoOfCommon A strategy hwin
            pending.receiver)) =
      some pending := by
  simp [profiledRawJointGuardedCommonTailRightPendingOfOldPair?,
    profiledRawJointGuardedCommonTailOneOfRightOwner,
    profiledRawJointGuardedCommonTailTwoOfCommon]

@[simp] theorem
    profiledRawJointGuardedCommonTailLeftPendingOfOldPair?_components
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin) :
    profiledRawJointGuardedCommonTailLeftPendingOfOldPair? A strategy hwin
        initialBank
        (.exceptional
          (profiledRawJointGuardedCommonTailOneOfCommon A strategy hwin
            pending.receiver))
        (.exceptional
          (profiledRawJointGuardedCommonTailTwoOfLeftOwner A strategy hwin
            pending.owner)) =
      some pending := by
  simp [profiledRawJointGuardedCommonTailLeftPendingOfOldPair?,
    profiledRawJointGuardedCommonTailOneOfCommon,
    profiledRawJointGuardedCommonTailTwoOfLeftOwner]

/-! ## Ordinary-pair dispatch with charged crosses -/

/-- Process one's receive on an ordinary pair.  A represented pending pair
enters its charged cross response; every other pair uses the verified old
core receive and is embedded into the enlarged carrier. -/
noncomputable def profiledRawJointGuardedCommonTailChargedOldRecvOne
    (root : ProfiledRawJointGuardedInitialCommonControl A strategy hwin)
    (one : OldOne A strategy hwin initialBank) (own : In₁)
    (two : OldTwo A strategy hwin initialBank) (delivered : In₂) :
    Out₁ × ChargedOne A strategy hwin initialBank :=
  match profiledRawJointGuardedCommonTailRightPendingOfOldPair? A strategy hwin
      initialBank one two with
  | some pending =>
      let next :=
        (profiledRawJointGuardedCommonTailRightChargedCrossResponse A strategy
          hwin pending (own, delivered)).1
      (next.1,
        profiledRawJointGuardedCommonTailLiftRightNextOne A strategy hwin
          initialBank (.inr next.2))
  | none =>
      match profiledRawJointGuardedCommonTailLeftPendingOfOldPair? A strategy
          hwin initialBank one two with
      | some pending =>
          let next :=
            (profiledRawJointGuardedCommonTailLeftChargedCrossResponse A
              strategy hwin pending (own, delivered)).1
          (next.1,
            profiledRawJointGuardedCommonTailLiftLeftNextOne A strategy hwin
              initialBank (.inr next.2))
      | none =>
          let next := profiledRawJointGuardedCommonTailCoreRecvOne A strategy
            hwin initialBank root one own two delivered
          (next.1,
            profiledRawJointGuardedCommonTailLiftOldOne A strategy hwin
              initialBank next.2)

/-- Process-two mirror, using the same reconstructed pending keys. -/
noncomputable def profiledRawJointGuardedCommonTailChargedOldRecvTwo
    (root : ProfiledRawJointGuardedInitialCommonControl A strategy hwin)
    (two : OldTwo A strategy hwin initialBank) (own : In₂)
    (one : OldOne A strategy hwin initialBank) (delivered : In₁) :
    Out₂ × ChargedTwo A strategy hwin initialBank :=
  match profiledRawJointGuardedCommonTailRightPendingOfOldPair? A strategy hwin
      initialBank one two with
  | some pending =>
      let next :=
        (profiledRawJointGuardedCommonTailRightChargedCrossResponse A strategy
          hwin pending (delivered, own)).2
      (next.1,
        profiledRawJointGuardedCommonTailLiftRightNextTwo A strategy hwin
          initialBank (.inr next.2))
  | none =>
      match profiledRawJointGuardedCommonTailLeftPendingOfOldPair? A strategy
          hwin initialBank one two with
      | some pending =>
          let next :=
            (profiledRawJointGuardedCommonTailLeftChargedCrossResponse A
              strategy hwin pending (delivered, own)).2
          (next.1,
            profiledRawJointGuardedCommonTailLiftLeftNextTwo A strategy hwin
              initialBank (.inr next.2))
      | none =>
          let next := profiledRawJointGuardedCommonTailCoreRecvTwo A strategy
            hwin initialBank root two own one delivered
          (next.1,
            profiledRawJointGuardedCommonTailLiftOldTwo A strategy hwin
              initialBank next.2)

/-! ## Total charged receive maps -/

/-- Resolve any existing charged bit, then run the ordinary-pair dispatcher.
In particular, an immediately following receive may itself start the next
charged cross; ambiguity is replaced, never multiplied. -/
noncomputable def profiledRawJointGuardedCommonTailChargedRecvOne
    (root : ProfiledRawJointGuardedInitialCommonControl A strategy hwin)
    (one : ChargedOne A strategy hwin initialBank) (own : In₁)
    (two : ChargedTwo A strategy hwin initialBank) (delivered : In₂) :
    Out₁ × ChargedOne A strategy hwin initialBank :=
  let resolved := profiledRawJointGuardedCommonTailResolveChargedPair A
    strategy hwin initialBank one two
  profiledRawJointGuardedCommonTailChargedOldRecvOne A strategy hwin
    initialBank root resolved.1 own resolved.2 delivered

/-- Process-two mirror. -/
noncomputable def profiledRawJointGuardedCommonTailChargedRecvTwo
    (root : ProfiledRawJointGuardedInitialCommonControl A strategy hwin)
    (two : ChargedTwo A strategy hwin initialBank) (own : In₂)
    (one : ChargedOne A strategy hwin initialBank) (delivered : In₁) :
    Out₂ × ChargedTwo A strategy hwin initialBank :=
  let resolved := profiledRawJointGuardedCommonTailResolveChargedPair A
    strategy hwin initialBank one two
  profiledRawJointGuardedCommonTailChargedOldRecvTwo A strategy hwin
    initialBank root resolved.2 own resolved.1 delivered

/-! ## Exact represented-cross equations -/

@[simp] theorem profiledRawJointGuardedCommonTailChargedOldRecvOne_right
    (root : ProfiledRawJointGuardedInitialCommonControl A strategy hwin)
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonTailChargedOldRecvOne A strategy hwin
        initialBank root
        (.exceptional
          (profiledRawJointGuardedCommonTailOneOfRightOwner A strategy hwin
            pending.owner)) input.1
        (.exceptional
          (profiledRawJointGuardedCommonTailTwoOfCommon A strategy hwin
            pending.receiver)) input.2 =
      let next :=
        (profiledRawJointGuardedCommonTailRightChargedCrossResponse A strategy
          hwin pending input).1
      (next.1,
        profiledRawJointGuardedCommonTailLiftRightNextOne A strategy hwin
          initialBank (.inr next.2)) := by
  simp [profiledRawJointGuardedCommonTailChargedOldRecvOne]

@[simp] theorem profiledRawJointGuardedCommonTailChargedOldRecvTwo_right
    (root : ProfiledRawJointGuardedInitialCommonControl A strategy hwin)
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonTailChargedOldRecvTwo A strategy hwin
        initialBank root
        (.exceptional
          (profiledRawJointGuardedCommonTailTwoOfCommon A strategy hwin
            pending.receiver)) input.2
        (.exceptional
          (profiledRawJointGuardedCommonTailOneOfRightOwner A strategy hwin
            pending.owner)) input.1 =
      let next :=
        (profiledRawJointGuardedCommonTailRightChargedCrossResponse A strategy
          hwin pending input).2
      (next.1,
        profiledRawJointGuardedCommonTailLiftRightNextTwo A strategy hwin
          initialBank (.inr next.2)) := by
  simp [profiledRawJointGuardedCommonTailChargedOldRecvTwo]

@[simp] theorem profiledRawJointGuardedCommonTailChargedOldRecvOne_left
    (root : ProfiledRawJointGuardedInitialCommonControl A strategy hwin)
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonTailChargedOldRecvOne A strategy hwin
        initialBank root
        (.exceptional
          (profiledRawJointGuardedCommonTailOneOfCommon A strategy hwin
            pending.receiver)) input.1
        (.exceptional
          (profiledRawJointGuardedCommonTailTwoOfLeftOwner A strategy hwin
            pending.owner)) input.2 =
      let next :=
        (profiledRawJointGuardedCommonTailLeftChargedCrossResponse A strategy
          hwin pending input).1
      (next.1,
        profiledRawJointGuardedCommonTailLiftLeftNextOne A strategy hwin
          initialBank (.inr next.2)) := by
  simp [profiledRawJointGuardedCommonTailChargedOldRecvOne,
    profiledRawJointGuardedCommonTailRightPendingOfOldPair?,
    profiledRawJointGuardedCommonTailLeftPendingOfOldPair?,
    profiledRawJointGuardedCommonTailOneOfCommon,
    profiledRawJointGuardedCommonTailTwoOfLeftOwner]

@[simp] theorem profiledRawJointGuardedCommonTailChargedOldRecvTwo_left
    (root : ProfiledRawJointGuardedInitialCommonControl A strategy hwin)
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonTailChargedOldRecvTwo A strategy hwin
        initialBank root
        (.exceptional
          (profiledRawJointGuardedCommonTailTwoOfLeftOwner A strategy hwin
            pending.owner)) input.2
        (.exceptional
          (profiledRawJointGuardedCommonTailOneOfCommon A strategy hwin
            pending.receiver)) input.1 =
      let next :=
        (profiledRawJointGuardedCommonTailLeftChargedCrossResponse A strategy
          hwin pending input).2
      (next.1,
        profiledRawJointGuardedCommonTailLiftLeftNextTwo A strategy hwin
          initialBank (.inr next.2)) := by
  simp [profiledRawJointGuardedCommonTailChargedOldRecvTwo,
    profiledRawJointGuardedCommonTailRightPendingOfOldPair?,
    profiledRawJointGuardedCommonTailLeftPendingOfOldPair?,
    profiledRawJointGuardedCommonTailOneOfCommon,
    profiledRawJointGuardedCommonTailTwoOfLeftOwner]

end

end DetParityAutomaton

end DistributedSynthesis
