/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossBothPhysical
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralRightFreshPendingReencapsulation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralLeftDeferredStageFork

/-!
# Same-occurrence fresh receive handoff

A simultaneous receive does two logically different things.  It resolves the
old delayed member, and it creates the next delayed member.  The latter must
be installed from the literal child of the *same* semantic occurrence whose
physical output is emitted in the current round.

This file packages that edge without exposing a hierarchy side.  The fresh
seam key is the successor decorated-policy state paired with the current
input.  Its blind endpoint is a fresh table-vs-table fork, and its informed
endpoint is the matching true-member staged receiver.  The physical output of
the current receive is read from the two old literal tables and is proved to
be exactly the guarded successor cut.  Thus neither coordinate can be taken
from an unrelated representative.

All executable controls below are finite.  No runtime map receives a graph,
orientation, leader bit, history, or view.
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

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev State :=
  ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev Key (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin package

private abbrev RightPending
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate A
    strategy hwin package

private abbrev RightReceiver
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A strategy
    hwin package

private abbrev LeftPending
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate A
    strategy hwin package

private abbrev LeftReceiver
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A strategy
    hwin package

/-! ## The fresh edge key -/

/-- The child created by the current simultaneous input.  The first component
is the one decorated successor lookup used by `nextPairAt`; the second is the
current input whose literal child becomes the next seam occurrence. -/
noncomputable def successorLiteralCrossFreshSeamKey
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) : Key A strategy hwin package :=
  package.literalRightSeamFreshKey A strategy hwin
    (package.policy.successor state incoming) blockInput

/-- The parent stored in the fresh key is reachable whenever the pre-round
decorated state is reachable. -/
theorem successorLiteralCrossFreshSeamKey_parent_reachable
    (package : Package A strategy hwin initial)
    {state : State A strategy hwin (initial := initial)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂) :
    ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
      initial (CrossValid A strategy hwin) package.policy
        (package.successorLiteralCrossFreshSeamKey A strategy hwin state
          incoming blockInput).1 := by
  exact package.successor_reachable A strategy hwin hreachable incoming

/-- The representative at the fresh key's parent is exactly the operational
successor pair and annotation selected by the one decorated lookup. -/
theorem successorLiteralCrossFreshSeamKey_parent_spec
    (package : Package A strategy hwin initial)
    {state : State A strategy hwin (initial := initial)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂) :
    let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
      incoming blockInput
    let point := package.literalRightSeamPointAt A strategy hwin key.1
    point.move A strategy hwin =
        package.nextPairAt A strategy hwin state incoming ∧
      profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
          point = package.nextExtraAt A strategy hwin state incoming := by
  dsimp only [successorLiteralCrossFreshSeamKey]
  have hsucc := package.successor_reachable A strategy hwin hreachable incoming
  have hspec := package.literalRightSeamPointAt_spec A strategy hwin
    (package.policy.successor state incoming) hsucc
  exact ⟨hspec.2.1, hspec.2.2⟩

/-- The fresh seam child code is the literal child of that same successor
pair.  This is the poststate half of the same-occurrence edge equation. -/
theorem successorLiteralCrossFreshSeamKey_child_code
    (package : Package A strategy hwin initial)
    {state : State A strategy hwin (initial := initial)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂) :
    let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
      incoming blockInput
    (package.literalRightSeamChildPoint A strategy hwin key).code A strategy =
      (package.nextPairAt A strategy hwin state incoming).bothNextCode A
        strategy hwin blockInput := by
  let current := package.policy.successor state incoming
  have hcurrent := package.successor_reachable A strategy hwin hreachable
    incoming
  calc
    _ = (package.policy.successor current blockInput).1 :=
      package.literalRightSeamFreshKey_childCode A strategy hwin current
        hcurrent blockInput
    _ = (package.nextPairAt A strategy hwin state incoming).bothNextCode A
          strategy hwin blockInput := by
      exact congrArg Prod.fst
        (package.successor_eq_pairAt A strategy hwin current hcurrent
          blockInput)

/-! ## Fresh finite roots -/

/-- The blind fresh fork and the matching informed staged receiver, both at
the same exact key.  The true anchor is the semantic branch whose exact stage
is refreshed; the false member remains stored only as the unresolved local
alternative. -/
noncomputable def successorLiteralCrossFreshRightRoots
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    FiniteDelayedFork (RightPending A strategy hwin package) ×
      RightReceiver A strategy hwin package :=
  let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
    incoming blockInput
  (package.literalRightSeamFreshPendingSenderFork A strategy hwin key,
    package.literalRightSeamStagedReceiverInitial A strategy hwin key .both
      true)

@[simp] theorem successorLiteralCrossFreshRightRoots_fork
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossFreshRightRoots A strategy hwin state
      incoming blockInput).1 =
      package.literalRightSeamFreshPendingSenderFork A strategy hwin
        (package.successorLiteralCrossFreshSeamKey A strategy hwin state
          incoming blockInput) :=
  rfl

@[simp] theorem successorLiteralCrossFreshRightRoots_receiver
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossFreshRightRoots A strategy hwin state
      incoming blockInput).2 =
      package.literalRightSeamStagedReceiverInitial A strategy hwin
        (package.successorLiteralCrossFreshSeamKey A strategy hwin state
          incoming blockInput) .both true :=
  rfl

/-- Forgetting either pending member gives the one sender root aligned with
the fresh staged receiver. -/
theorem successorLiteralCrossFreshRightRoots_forget_aligned
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    let roots := package.successorLiteralCrossFreshRightRoots A strategy hwin
      state incoming blockInput
    package.LiteralRightSeamStagedTableAligned A strategy hwin roots.2
      (package.literalRightSeamMemberSenderForget A strategy hwin
        roots.1.openControl.1) := by
  dsimp only [successorLiteralCrossFreshRightRoots,
    successorLiteralCrossFreshSeamKey]
  exact package.literalRightSeamStaged_initial_aligned A strategy hwin
    (package.policy.successor state incoming, blockInput) .both

/-- Mirror closed root at the same fresh key.  This is installed in parallel;
it is not selected by an orientation bit. -/
noncomputable def successorLiteralCrossFreshLeftRoots
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    FiniteDelayedFork (LeftPending A strategy hwin package) ×
      LeftReceiver A strategy hwin package :=
  let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
    incoming blockInput
  (package.literalLeftSeamFreshDeferredSenderFork A strategy hwin key,
    package.literalLeftSeamStagedReceiverInitial A strategy hwin key .both
      true)

@[simp] theorem successorLiteralCrossFreshLeftRoots_fork
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossFreshLeftRoots A strategy hwin state
      incoming blockInput).1 =
      package.literalLeftSeamFreshDeferredSenderFork A strategy hwin
        (package.successorLiteralCrossFreshSeamKey A strategy hwin state
          incoming blockInput) :=
  rfl

@[simp] theorem successorLiteralCrossFreshLeftRoots_receiver
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossFreshLeftRoots A strategy hwin state
      incoming blockInput).2 =
      package.literalLeftSeamStagedReceiverInitial A strategy hwin
        (package.successorLiteralCrossFreshSeamKey A strategy hwin state
          incoming blockInput) .both true :=
  rfl

/-- The mirror pending closed member and its staged receiver have the same
key, true member, entry row, empty stage, and literally synchronized table
control. -/
theorem successorLiteralCrossFreshLeftRoots_closed_exact
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
      incoming blockInput
    let roots := package.successorLiteralCrossFreshLeftRoots A strategy hwin
      state incoming blockInput
    roots.1.closedControl.1.1 = key ∧
      roots.1.closedControl.1.2.1 = true ∧
      roots.1.closedControl.2 = none ∧
      roots.2.1 = key ∧ roots.2.2.1 = .both ∧
      roots.2.2.2.1.1 = true ∧ roots.2.2.2.2 = none ∧
      roots.1.closedControl.1.2.2 = roots.2.2.2.1.2.1 := by
  dsimp only [successorLiteralCrossFreshLeftRoots,
    successorLiteralCrossFreshSeamKey, literalRightSeamFreshKey]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact package.literalLeftSeamStaged_initial_controls_eq A strategy hwin
    (package.policy.successor state incoming, blockInput) .both true

/-! ## Current physical output at the same edge -/

/-- The two current literal receivers selected by the one successor
annotation.  This definition contains no fresh poststate and therefore cannot
silently mix the new fork's output with the old closing output. -/
noncomputable def successorLiteralCrossSelectedReceiveOutputs
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂)
    (rightAnchor leftAnchor : Bool) : Out₁ × Out₂ :=
  let extra := package.nextExtraAt A strategy hwin state incoming
  let rightReceiver :=
    profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A extra.1
      rightAnchor
  let leftReceiver :=
    profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
      leftAnchor
  ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
      leftReceiver blockInput.1 blockInput.2).1,
    (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
      rightReceiver blockInput.2 blockInput.1).1)

/-- The selected current outputs are exactly the two coordinates of the
guarded successor cut, while `successorLiteralCrossFreshRightRoots` stores the
literal child created by the same input.  This is the anti-mosaic receive
bridge needed by the selected-control trace invariant. -/
theorem successorLiteralCrossSelectedReceiveOutputs_eq_nextPairCut
    (package : Package A strategy hwin initial)
    {state : State A strategy hwin (initial := initial)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂)
    (rightAnchor leftAnchor : Bool) :
    package.successorLiteralCrossSelectedReceiveOutputs A strategy hwin state
        incoming blockInput rightAnchor leftAnchor =
      (((package.nextPairAt A strategy hwin state incoming).rightRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth,
        ((package.nextPairAt A strategy hwin state incoming).leftRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth) := by
  exact package.successorLiteralCross_bothPhysicalOutputs_eq_nextPairCut A
    strategy hwin hreachable incoming blockInput rightAnchor leftAnchor

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
