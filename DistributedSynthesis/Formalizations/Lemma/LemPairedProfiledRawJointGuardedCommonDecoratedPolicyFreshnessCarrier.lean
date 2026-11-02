/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossMismatchPhase

/-!
# Leader-free freshness of the decorated common-policy state

During a strict right phase process two is the receiving endpoint and hence
owns the current decorated-policy state; during a strict left phase process
one owns it.  A blind endpoint is allowed to retain an older copy.  This is
enough: at a strict switch the newly receiving endpoint is delivered the
other process's complete finite control, while at a simultaneous round both
receivers start from the same current copy.

The executable maps below implement exactly that rule.  They see only the
endpoint's stored phase, its local input, and, on a receive, the delivered
partner state and input.  No map accepts a graph, orientation, leader bit,
strict-leader bit, semantic world, or history.  `freshnessLocalStep` is only a
proof-side product of the four local maps.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev PolicyState (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin initial
    (CrossValid A strategy hwin)

/-! ## Finite local freshness controls -/

/-- Process one's Boolean is `false` in the right-sender phase and `true` in
the left-receiver phase.  It is a constructor tag in local memory, not an
orientation observation. -/
abbrev ProfiledRawJointGuardedCommonDecoratedFreshnessOneState
    (initial : CommonPoint A strategy) :=
  PolicyState A strategy hwin initial × Bool

/-- Process-two mirror: `false` is the right-receiver phase and `true` the
left-sender phase. -/
abbrev ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState
    (initial : CommonPoint A strategy) :=
  PolicyState A strategy hwin initial × Bool

noncomputable instance
    profiledRawJointGuardedCommonDecoratedFreshnessOneStateFintype :
    Fintype
      (ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial) := by
  infer_instance

noncomputable instance
    profiledRawJointGuardedCommonDecoratedFreshnessTwoStateFintype :
    Fintype
      (ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial) := by
  infer_instance

/-- Install equal current copies in the receiver/receiver phase reached by a
simultaneous round. -/
def decoratedFreshnessBothInitial
    (state : PolicyState A strategy hwin initial) :
    ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial ×
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial :=
  ((state, true), (state, false))

/-! ## Four genuinely local transitions -/

/-- A process-one nonreceive enters the right-sender phase and retains its
finite policy copy. -/
def decoratedFreshnessNoRecvOne
    (state :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (_input : In₁) :
    ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
      initial :=
  (state.1, false)

/-- Process-two nonreceive enters the left-sender phase. -/
def decoratedFreshnessNoRecvTwo
    (state :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (_input : In₂) :
    ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
      initial :=
  (state.1, true)

/-- Process one already has the fresh copy when it is a left receiver.  When
it was a right sender, the delivered process-two control has the fresh copy.
In either case it advances that copy by the fully observed input pair. -/
def decoratedFreshnessRecvOne
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (own : In₁)
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (delivered : In₂) :
    ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
      initial :=
  let source := if one.2 then one.1 else two.1
  (package.policy.successor source (own, delivered), true)

/-- Process-two mirror.  A right receiver uses its own fresh copy; a left
sender takes the delivered process-one copy. -/
def decoratedFreshnessRecvTwo
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (own : In₂)
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (delivered : In₁) :
    ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
      initial :=
  let source := if two.2 then one.1 else two.1
  (package.policy.successor source (delivered, own), false)

@[simp] theorem decoratedFreshnessRecvOne_of_rightSender
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (oneState twoState : PolicyState A strategy hwin initial)
    (own : In₁) (delivered : In₂) :
    decoratedFreshnessRecvOne A strategy hwin package (oneState, false) own
        (twoState, false) delivered =
      (package.policy.successor twoState (own, delivered), true) := by
  rfl

@[simp] theorem decoratedFreshnessRecvOne_of_leftReceiver
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (oneState twoState : PolicyState A strategy hwin initial)
    (own : In₁) (delivered : In₂) :
    decoratedFreshnessRecvOne A strategy hwin package (oneState, true) own
        (twoState, true) delivered =
      (package.policy.successor oneState (own, delivered), true) := by
  rfl

@[simp] theorem decoratedFreshnessRecvTwo_of_rightReceiver
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (twoState oneState : PolicyState A strategy hwin initial)
    (own : In₂) (delivered : In₁) :
    decoratedFreshnessRecvTwo A strategy hwin package (twoState, false) own
        (oneState, false) delivered =
      (package.policy.successor twoState (delivered, own), false) := by
  rfl

@[simp] theorem decoratedFreshnessRecvTwo_of_leftSender
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (twoState oneState : PolicyState A strategy hwin initial)
    (own : In₂) (delivered : In₁) :
    decoratedFreshnessRecvTwo A strategy hwin package (twoState, true) own
        (oneState, true) delivered =
      (package.policy.successor oneState (delivered, own), false) := by
  rfl

/-! ## The one freshness invariant -/

/-- The impossible phase is sender/sender.  In a matched strict phase only
the receiving endpoint is required to carry the fresh state.  In the
receiver/receiver phase the two fresh copies are equal. -/
def DecoratedFreshnessAligned
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial) : Prop :=
  match one.2, two.2 with
  | false, false => True
  | true, true => True
  | true, false => one.1 = two.1
  | false, true => False

/-- Read the unique current common-policy copy without asking which process is
the strict leader: process one is current exactly in its receiver phase;
otherwise process two is current. -/
def decoratedFreshnessCurrent
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial) : PolicyState A strategy hwin initial :=
  if one.2 then one.1 else two.1

@[simp] theorem decoratedFreshnessBothInitial_aligned
    (state : PolicyState A strategy hwin initial) :
    DecoratedFreshnessAligned A strategy hwin
      (decoratedFreshnessBothInitial A strategy hwin state).1
      (decoratedFreshnessBothInitial A strategy hwin state).2 := by
  rfl

/-! ## Proof-side physical product -/

/-- Couple the four local maps according to a proof-side physical graph.  The
graph is not passed to either endpoint map. -/
def decoratedFreshnessLocalStep
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (input : In₁ × In₂) (graph : Graph) :
    ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial ×
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial :=
  match graph with
  | .right =>
      (decoratedFreshnessNoRecvOne A strategy hwin one input.1,
        decoratedFreshnessRecvTwo A strategy hwin package two input.2 one
          input.1)
  | .left =>
      (decoratedFreshnessRecvOne A strategy hwin package one input.1 two
          input.2,
        decoratedFreshnessNoRecvTwo A strategy hwin two input.2)
  | .both =>
      (decoratedFreshnessRecvOne A strategy hwin package one input.1 two
          input.2,
        decoratedFreshnessRecvTwo A strategy hwin package two input.2 one
          input.1)

/-- The honest event pair alone fixes the post-round phase tags. -/
theorem decoratedFreshnessLocalStep_sides
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (input : In₁ × In₂) (graph : Graph) :
    let next := decoratedFreshnessLocalStep A strategy hwin package one two
      input graph
    (next.1.2, next.2.2) =
      match graph with
      | .right => (false, false)
      | .left => (true, true)
      | .both => (true, false) := by
  cases graph <;> rfl

/-- Freshness is preserved for every physical graph.  This is the finite
leader-free state-transfer law used by the literal-cross trace induction. -/
theorem decoratedFreshnessLocalStep_aligned
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (haligned : DecoratedFreshnessAligned A strategy hwin one two)
    (input : In₁ × In₂) (graph : Graph) :
    let next := decoratedFreshnessLocalStep A strategy hwin package one two
      input graph
    DecoratedFreshnessAligned A strategy hwin next.1 next.2 := by
  rcases one with ⟨oneState, oneSide⟩
  rcases two with ⟨twoState, twoSide⟩
  cases oneSide <;> cases twoSide
  · cases graph <;> simp [decoratedFreshnessLocalStep,
      DecoratedFreshnessAligned, decoratedFreshnessRecvOne,
      decoratedFreshnessRecvTwo, decoratedFreshnessNoRecvOne,
      decoratedFreshnessNoRecvTwo]
  · exact False.elim haligned
  · change oneState = twoState at haligned
    subst twoState
    cases graph <;> simp [decoratedFreshnessLocalStep,
      DecoratedFreshnessAligned, decoratedFreshnessRecvOne,
      decoratedFreshnessRecvTwo, decoratedFreshnessNoRecvOne,
      decoratedFreshnessNoRecvTwo]
  · cases graph <;> simp [decoratedFreshnessLocalStep,
      DecoratedFreshnessAligned, decoratedFreshnessRecvOne,
      decoratedFreshnessRecvTwo, decoratedFreshnessNoRecvOne,
      decoratedFreshnessNoRecvTwo]

/-- Whichever physical graph occurs, the unique fresh copy advances by
exactly one decorated-policy successor.  This is the operational reason the
finite policy can be threaded without a leader detector. -/
theorem decoratedFreshnessLocalStep_current_eq_successor
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (haligned : DecoratedFreshnessAligned A strategy hwin one two)
    (input : In₁ × In₂) (graph : Graph) :
    let next := decoratedFreshnessLocalStep A strategy hwin package one two
      input graph
    decoratedFreshnessCurrent A strategy hwin next.1 next.2 =
      package.policy.successor
        (decoratedFreshnessCurrent A strategy hwin one two) input := by
  rcases one with ⟨oneState, oneSide⟩
  rcases two with ⟨twoState, twoSide⟩
  cases oneSide <;> cases twoSide
  · cases graph <;> rfl
  · exact False.elim haligned
  · change oneState = twoState at haligned
    subst twoState
    cases graph <;> rfl
  · cases graph <;> rfl

/-- Reachability of the current copy is consequently invariant under every
honest physical event. -/
theorem decoratedFreshnessLocalStep_current_reachable
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (haligned : DecoratedFreshnessAligned A strategy hwin one two)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy
          (decoratedFreshnessCurrent A strategy hwin one two))
    (input : In₁ × In₂) (graph : Graph) :
    let next := decoratedFreshnessLocalStep A strategy hwin package one two
      input graph
    ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
      initial (CrossValid A strategy hwin) package.policy
        (decoratedFreshnessCurrent A strategy hwin next.1 next.2) := by
  dsimp only
  rw [decoratedFreshnessLocalStep_current_eq_successor A strategy hwin package
    one two haligned input graph]
  exact package.successor_reachable A strategy hwin hreachable input

/-- The finite annotation at the new current copy is exactly the package's
preselected successor annotation, for all three physical graphs. -/
theorem decoratedFreshnessLocalStep_currentExtra_eq_nextExtraAt
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (haligned : DecoratedFreshnessAligned A strategy hwin one two)
    (input : In₁ × In₂) (graph : Graph) :
    let next := decoratedFreshnessLocalStep A strategy hwin package one two
      input graph
    package.extraAt A strategy hwin
        (decoratedFreshnessCurrent A strategy hwin next.1 next.2) =
      package.nextExtraAt A strategy hwin
        (decoratedFreshnessCurrent A strategy hwin one two) input := by
  dsimp only
  rw [decoratedFreshnessLocalStep_current_eq_successor A strategy hwin package
    one two haligned input graph]
  rfl

/-- The guarded pair attached to the new current copy is likewise the one
selected by the same successor lookup. -/
theorem decoratedFreshnessLocalStep_currentPair_eq_nextPairAt
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (haligned : DecoratedFreshnessAligned A strategy hwin one two)
    (input : In₁ × In₂) (graph : Graph) :
    let next := decoratedFreshnessLocalStep A strategy hwin package one two
      input graph
    package.pairAt A strategy hwin
        (decoratedFreshnessCurrent A strategy hwin next.1 next.2) =
      package.nextPairAt A strategy hwin
        (decoratedFreshnessCurrent A strategy hwin one two) input := by
  dsimp only
  rw [decoratedFreshnessLocalStep_current_eq_successor A strategy hwin package
    one two haligned input graph]
  rfl

/-- On a simultaneous round the two receiver copies are not merely related:
they are exactly the same policy successor. -/
theorem decoratedFreshnessLocalStep_both_states_eq
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (haligned : DecoratedFreshnessAligned A strategy hwin one two)
    (input : In₁ × In₂) :
    let next := decoratedFreshnessLocalStep A strategy hwin package one two
      input .both
    next.1.1 = next.2.1 := by
  have hnext := decoratedFreshnessLocalStep_aligned A strategy hwin package
    one two haligned input .both
  simpa [DecoratedFreshnessAligned,
    decoratedFreshnessLocalStep] using hnext

/-- Therefore the two annotations visible after a simultaneous round are
literally the same refreshed literal-table ID. -/
theorem decoratedFreshnessLocalStep_both_extra_eq
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (haligned : DecoratedFreshnessAligned A strategy hwin one two)
    (input : In₁ × In₂) :
    let next := decoratedFreshnessLocalStep A strategy hwin package one two
      input .both
    package.extraAt A strategy hwin next.1.1 =
      package.extraAt A strategy hwin next.2.1 := by
  intro next
  exact congrArg (package.extraAt A strategy hwin)
    (decoratedFreshnessLocalStep_both_states_eq A strategy hwin package one two
      haligned input)

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
