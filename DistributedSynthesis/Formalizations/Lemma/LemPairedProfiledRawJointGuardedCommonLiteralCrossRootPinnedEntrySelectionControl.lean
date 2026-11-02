/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBootstrapStrictHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryThreeWayHandoff

/-!
# Finite three-way selection controls below the root-pinned entry

The entry bootstrap and the parent-linked common carrier have different
finite state types.  This file puts their continuations in one endpoint-local
finite alphabet.  The bootstrap itself retains both receiver candidates.
When the next receive is evaluated, the ordinary branch selects the matching
strict seed and the exact-close branch selects the recurrent parent-linked
common state.  Those two postcontrols, not the pre-receive table bundle and a
common root, form the fresh unresolved fork.  After resolution, the strict
arm retains the exact dependent child and ordinary policy root furnished by
the literal second-record theorem, while the common arm retains the recurrent
parent-linked shadow state.

The local maps below describe the first round after a fixed entry.  A
non-receive keeps the corresponding literal sender, an ordinary receive
selects the appropriate strict policy root, and the exact joint close selects
the recurrent common state.  `ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRel`
records the four reachable pair shapes: entry, strict right, strict left, and
common.  Direction names occur only in constructors and proof theorems; none
of the local maps receives a graph or a leader bit.

This is the finite handoff alphabet, not yet the complete acknowledged
dispatcher.  The subsequent blind-no-receive module keeps each strict seed
dormant beside the shared owner controller of the common successor pair and
proves arbitrary-depth local output coherence.  The remaining step is to
integrate those owner-backed controls with receive resolution and the
recurrent selected-pair relation before the maps can be packaged as
`ExactClosingBlindForkLaws`.
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

private abbrev EntryOne :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneControl A

private abbrev EntryTwo :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoControl A

private abbrev CommonOne (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
    A strategy hwin initial

private abbrev CommonTwo (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
    A strategy hwin initial

private abbrev CommonRoot (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
    strategy hwin initial

/-! ## Exact finite strict seeds -/

/-- All exact right-oriented handoff roots below one guarded occurrence.
The finite tag stores the two inputs and the hidden table member that justify
the dependent child; the two proof fields do not add executable data. -/
structure
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeed
    (initial : CommonPoint A strategy) where
  entry : In₁ × In₂
  input : In₁ × In₂
  member : Bool
  child :
    let installed :=
      profiledRawJointGuardedCommonPointInstalled A strategy initial
    let source := installed.world.oneSidedState A .right
    let predicate := profiledRawJointHybridExactRightRootPredicate A installed
    let package := profiledRawJointHybridExactRightPolicy A hwin installed
    let selected := profiledRawJointRootPinnedSelectedSource A strategy source
      predicate package
    ProfiledRawJointOneSidedLiteralChildCode A strategy selected
  target :
    let installed :=
      profiledRawJointGuardedCommonPointInstalled A strategy initial
    let source := installed.world.oneSidedState A .right
    let predicate := profiledRawJointHybridExactRightRootPredicate A installed
    let package := profiledRawJointHybridExactRightPolicy A hwin installed
    let selected := profiledRawJointRootPinnedSelectedSource A strategy source
      predicate package
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hwin source predicate package
    ProfiledRawJointUnitLeftPolicyMacro A strategy child.1 (bank child)
  target_eq :
    child.1 =
      let two :=
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
          strategy hwin initial entry member
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
        (two.2.2.candidate two.1) input.2 input.1).1.target .both
  target_root :
    let installed :=
      profiledRawJointGuardedCommonPointInstalled A strategy initial
    let source := installed.world.oneSidedState A .right
    let predicate := profiledRawJointHybridExactRightRootPredicate A installed
    let package := profiledRawJointHybridExactRightPolicy A hwin installed
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hwin source predicate package
    target.state = (bank child).run []

/-- Left-oriented mirror. -/
structure
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeed
    (initial : CommonPoint A strategy) where
  entry : In₁ × In₂
  input : In₁ × In₂
  member : Bool
  child :
    let installed :=
      profiledRawJointGuardedCommonPointInstalled A strategy initial
    let source := installed.world.oneSidedState A .left
    let predicate := profiledRawJointHybridExactLeftRootPredicate A installed
    let package := profiledRawJointHybridExactLeftPolicy A hwin installed
    let selected := profiledRawJointRootPinnedSelectedSource A strategy source
      predicate package
    ProfiledRawJointOneSidedLiteralChildCode A strategy selected
  target :
    let installed :=
      profiledRawJointGuardedCommonPointInstalled A strategy initial
    let source := installed.world.oneSidedState A .left
    let predicate := profiledRawJointHybridExactLeftRootPredicate A installed
    let package := profiledRawJointHybridExactLeftPolicy A hwin installed
    let selected := profiledRawJointRootPinnedSelectedSource A strategy source
      predicate package
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hwin source predicate package
    ProfiledRawJointUnitRightPolicyMacro A strategy child.1 (bank child)
  target_eq :
    child.1 =
      let one :=
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
          strategy hwin initial entry member
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
        (one.2.2.candidate one.1) input.1 input.2).1.target .both
  target_root :
    let installed :=
      profiledRawJointGuardedCommonPointInstalled A strategy initial
    let source := installed.world.oneSidedState A .left
    let predicate := profiledRawJointHybridExactLeftRootPredicate A installed
    let package := profiledRawJointHybridExactLeftPolicy A hwin installed
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hwin source predicate package
    target.state = (bank child).run []

private abbrev StrictRightSeedData (initial : CommonPoint A strategy) :=
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy initial
  let source := installed.world.oneSidedState A .right
  let predicate := profiledRawJointHybridExactRightRootPredicate A installed
  let package := profiledRawJointHybridExactRightPolicy A hwin installed
  let selected := profiledRawJointRootPinnedSelectedSource A strategy source
    predicate package
  let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin
    source predicate package
  Σ child : ProfiledRawJointOneSidedLiteralChildCode A strategy selected,
    ProfiledRawJointUnitLeftPolicyMacro A strategy child.1 (bank child)

private abbrev StrictLeftSeedData (initial : CommonPoint A strategy) :=
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy initial
  let source := installed.world.oneSidedState A .left
  let predicate := profiledRawJointHybridExactLeftRootPredicate A installed
  let package := profiledRawJointHybridExactLeftPolicy A hwin installed
  let selected := profiledRawJointRootPinnedSelectedSource A strategy source
    predicate package
  let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin
    source predicate package
  Σ child : ProfiledRawJointOneSidedLiteralChildCode A strategy selected,
    ProfiledRawJointUnitRightPolicyMacro A strategy child.1 (bank child)

set_option synthInstance.maxHeartbeats 1000000 in
noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeedFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeed A
        strategy hwin initial) := by
  classical
  let encode := fun seed :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeed A
        strategy hwin initial ↦
    (seed.entry, seed.input, seed.member,
      (⟨seed.child, seed.target⟩ : StrictRightSeedData A strategy hwin initial))
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨entry, input, member, child, target, htarget, hroot⟩
    rcases right with ⟨entry', input', member', child', target', htarget',
      hroot'⟩
    change (entry, input, member,
        (⟨child, target⟩ : StrictRightSeedData A strategy hwin initial)) =
      (entry', input', member',
        (⟨child', target'⟩ : StrictRightSeedData A strategy hwin initial)) at heq
    have hentry := congrArg Prod.fst heq
    have htail := congrArg Prod.snd heq
    have hinput := congrArg Prod.fst htail
    have htail' := congrArg Prod.snd htail
    have hmember := congrArg Prod.fst htail'
    have hseed := congrArg Prod.snd htail'
    change entry = entry' at hentry
    change input = input' at hinput
    change member = member' at hmember
    subst entry'
    subst input'
    subst member'
    cases hseed
    rfl)

set_option synthInstance.maxHeartbeats 1000000 in
noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeedFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeed A
        strategy hwin initial) := by
  classical
  let encode := fun seed :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeed A
        strategy hwin initial ↦
    (seed.entry, seed.input, seed.member,
      (⟨seed.child, seed.target⟩ : StrictLeftSeedData A strategy hwin initial))
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨entry, input, member, child, target, htarget, hroot⟩
    rcases right with ⟨entry', input', member', child', target', htarget',
      hroot'⟩
    change (entry, input, member,
        (⟨child, target⟩ : StrictLeftSeedData A strategy hwin initial)) =
      (entry', input', member',
        (⟨child', target'⟩ : StrictLeftSeedData A strategy hwin initial)) at heq
    have hentry := congrArg Prod.fst heq
    have htail := congrArg Prod.snd heq
    have hinput := congrArg Prod.fst htail
    have htail' := congrArg Prod.snd htail
    have hmember := congrArg Prod.fst htail'
    have hseed := congrArg Prod.snd htail'
    change entry = entry' at hentry
    change input = input' at hinput
    change member = member' at hmember
    subst entry'
    subst input'
    subst member'
    cases hseed
    rfl)

/-- Select the exact strict-right dependent root exposed by the retained
second receiver record. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeedAt
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeed A
      strategy hwin initial := by
  classical
  let hexists :=
    exists_profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_strictRight_policyRoot
      A strategy hwin initial entry input member .both
  let child := Classical.choose hexists
  let target := Classical.choose (Classical.choose_spec hexists)
  have hspec := Classical.choose_spec (Classical.choose_spec hexists)
  exact ⟨entry, input, member, child, target, hspec.1, hspec.2⟩

/-- Strict-left mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeedAt
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeed A
      strategy hwin initial := by
  classical
  let hexists :=
    exists_profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_strictLeft_policyRoot
      A strategy hwin initial entry input member .both
  let child := Classical.choose hexists
  let target := Classical.choose (Classical.choose_spec hexists)
  have hspec := Classical.choose_spec (Classical.choose_spec hexists)
  exact ⟨entry, input, member, child, target, hspec.1, hspec.2⟩

/-! ## One finite alphabet for every handoff arm -/

/-- Process one can still be in the literal bootstrap, can have entered the
recurrent common shadow, or can carry either exact strict seed. -/
abbrev ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneControl
    (initial : CommonPoint A strategy) :=
  EntryOne A ⊕
    (CommonRoot A strategy hwin initial ⊕
      (CommonOne A strategy hwin initial ⊕
        (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeed A
            strategy hwin initial ⊕
          ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeed A
            strategy hwin initial)))

/-- Process-two mirror.  The summand order is deliberately identical so a
delivered partner control exposes the selected semantic arm. -/
abbrev ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoControl
    (initial : CommonPoint A strategy) :=
  EntryTwo A ⊕
    (CommonRoot A strategy hwin initial ⊕
      (CommonTwo A strategy hwin initial ⊕
        (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeed A
            strategy hwin initial ⊕
          ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeed A
            strategy hwin initial)))

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneControlFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneControl
        A strategy hwin initial) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoControlFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoControl
        A strategy hwin initial) := by
  classical
  infer_instance

private abbrev SelectionOne (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneControl
    A strategy hwin initial

private abbrev SelectionTwo (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoControl
    A strategy hwin initial

def profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionOneOfEntry
    {initial : CommonPoint A strategy} (state : EntryOne A) :
    SelectionOne A strategy hwin initial :=
  .inl state

def profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionTwoOfEntry
    {initial : CommonPoint A strategy} (state : EntryTwo A) :
    SelectionTwo A strategy hwin initial :=
  .inl state

def profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionOneOfCommonRoot
    {initial : CommonPoint A strategy}
    (state : CommonRoot A strategy hwin initial) :
    SelectionOne A strategy hwin initial :=
  .inr (.inl state)

def profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionTwoOfCommonRoot
    {initial : CommonPoint A strategy}
    (state : CommonRoot A strategy hwin initial) :
    SelectionTwo A strategy hwin initial :=
  .inr (.inl state)

def profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionOneOfCommon
    {initial : CommonPoint A strategy}
    (state : CommonOne A strategy hwin initial) :
    SelectionOne A strategy hwin initial :=
  .inr (.inr (.inl state))

def profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionTwoOfCommon
    {initial : CommonPoint A strategy}
    (state : CommonTwo A strategy hwin initial) :
    SelectionTwo A strategy hwin initial :=
  .inr (.inr (.inl state))

def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionOneOfStrictRight
    {initial : CommonPoint A strategy}
    (seed :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeed A
        strategy hwin initial) : SelectionOne A strategy hwin initial :=
  .inr (.inr (.inr (.inl seed)))

def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionTwoOfStrictRight
    {initial : CommonPoint A strategy}
    (seed :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeed A
        strategy hwin initial) : SelectionTwo A strategy hwin initial :=
  .inr (.inr (.inr (.inl seed)))

def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionOneOfStrictLeft
    {initial : CommonPoint A strategy}
    (seed :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeed A
        strategy hwin initial) : SelectionOne A strategy hwin initial :=
  .inr (.inr (.inr (.inr seed)))

def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionTwoOfStrictLeft
    {initial : CommonPoint A strategy}
    (seed :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeed A
        strategy hwin initial) : SelectionTwo A strategy hwin initial :=
  .inr (.inr (.inr (.inr seed)))

/-! ## Exact first-round local choices -/

/-- A process-one non-receive advances only its retained right sender. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionNoRecvOne
    (initial : CommonPoint A strategy) (entry : In₁ × In₂)
    (member : Bool) (input : In₁) :
    SelectionOne A strategy hwin initial × Out₁ :=
  let next :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne A
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
        strategy hwin initial entry member) input
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionOneOfEntry
    (initial := initial) A strategy hwin next.1, next.2)

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionNoRecvTwo
    (initial : CommonPoint A strategy) (entry : In₁ × In₂)
    (member : Bool) (input : In₂) :
    SelectionTwo A strategy hwin initial × Out₂ :=
  let next :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo A
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
        strategy hwin initial entry member) input
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionTwoOfEntry
    (initial := initial) A strategy hwin next.1, next.2)

/-- A process-one receive takes the ordinary strict-left arm.  Its output is
still read from the local literal table; the selected dependent seed is the
finite postcontrol. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOpenRecvOne
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) : SelectionOne A strategy hwin initial × Out₁ :=
  let one :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
      strategy hwin initial entry member
  let two :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
      strategy hwin initial entry member
  let next :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne A one
      input.1 two input.2
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionOneOfStrictLeft
    A strategy hwin
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeedAt A
        strategy hwin initial entry input member), next.2)

/-- Process-two receive takes the ordinary strict-right arm. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOpenRecvTwo
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) : SelectionTwo A strategy hwin initial × Out₂ :=
  let one :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
      strategy hwin initial entry member
  let two :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
      strategy hwin initial entry member
  let next :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo A two
      input.2 one input.1
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionTwoOfStrictRight
    A strategy hwin
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeedAt A
        strategy hwin initial entry input member), next.2)

/-- The exact simultaneous close starts process one's recurrent common
shadow and retains the successor key in that state. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCloseOne
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    SelectionOne A strategy hwin initial × Out₁ :=
  let next :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartOne
      A strategy hwin initial entry input
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionOneOfCommon
    A strategy hwin next.2, next.1)

/-- Process-two close mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCloseTwo
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    SelectionTwo A strategy hwin initial × Out₂ :=
  let next :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartTwo
      A strategy hwin initial entry input
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionTwoOfCommon
    A strategy hwin next.2, next.1)

/-! ## Fresh strict/common forks created by the resolving receive -/

/-- Process one's receive-created fork.  The open postcontrol is the exact
strict-left seed selected by the ordinary receive; the closed postcontrol is
the recurrent common state selected by interpreting the same receive as
simultaneous.  These are the two histories which form a process-one
`left`/`both` pending overlap during a following right block. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionReceiveOneFork
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    FiniteDelayedFork (SelectionOne A strategy hwin initial) :=
  ⟨(profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOpenRecvOne
      A strategy hwin initial entry input member).1,
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCloseOne
      A strategy hwin initial entry input).1⟩

/-- Process-two mirror: the ordinary branch is strict-right and the closed
branch is simultaneous, hence the relevant blind relation is the
process-two `right`/`both` pending overlap. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionReceiveTwoFork
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    FiniteDelayedFork (SelectionTwo A strategy hwin initial) :=
  ⟨(profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOpenRecvTwo
      A strategy hwin initial entry input member).1,
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCloseTwo
      A strategy hwin initial entry input).1⟩

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionReceiveOneFork_open
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionReceiveOneFork
      A strategy hwin initial entry input member).openControl =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOpenRecvOne
        A strategy hwin initial entry input member).1 :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionReceiveOneFork_closed
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionReceiveOneFork
      A strategy hwin initial entry input member).closedControl =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCloseOne
        A strategy hwin initial entry input).1 :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionReceiveTwoFork_open
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionReceiveTwoFork
      A strategy hwin initial entry input member).openControl =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOpenRecvTwo
        A strategy hwin initial entry input member).1 :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionReceiveTwoFork_closed
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionReceiveTwoFork
      A strategy hwin initial entry input member).closedControl =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCloseTwo
        A strategy hwin initial entry input).1 :=
  rfl

/-! ## Proof-side selected-pair relation -/

/-- The exact pair shapes reachable at the entry handoff.  In a strict-right
round process one remains in its blind sender while process two exposes the
right seed; strict-left is symmetric.  A simultaneous close installs the two
agreeing recurrent common states. -/
inductive
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRel
    (initial : CommonPoint A strategy) (entry : In₁ × In₂) :
    SelectionOne A strategy hwin initial →
      SelectionTwo A strategy hwin initial → Prop
  | entry (member : Bool) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRel
        initial entry
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionOneOfEntry
          (initial := initial) A strategy hwin
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
            strategy hwin initial entry member))
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionTwoOfEntry
          (initial := initial) A strategy hwin
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
            strategy hwin initial entry member))
  | commonRoot :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRel
        initial entry
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionOneOfCommonRoot
          A strategy hwin
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryKey
            A strategy hwin initial entry))
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedSelectionTwoOfCommonRoot
          A strategy hwin
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryKey
            A strategy hwin initial entry))
  | strictRight (member : Bool) (input : In₁ × In₂) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRel
        initial entry
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionNoRecvOne
          A strategy hwin initial entry member input.1).1
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOpenRecvTwo
          A strategy hwin initial entry input member).1
  | strictLeft (member : Bool) (input : In₁ × In₂) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRel
        initial entry
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOpenRecvOne
          A strategy hwin initial entry input member).1
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionNoRecvTwo
          A strategy hwin initial entry member input.2).1
  | common (input : In₁ × In₂) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRel
        initial entry
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCloseOne
          A strategy hwin initial entry input).1
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCloseTwo
          A strategy hwin initial entry input).1

/-- The common constructor really installs two copies of the same successor
key; this exposes the existing recurrent common-state agreement theorem from
the sum-level relation. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelection_common_states_agree
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
      A strategy hwin
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartOne
        A strategy hwin initial entry input).2
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartTwo
        A strategy hwin initial entry input).2 :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStart_states_agree
    A strategy hwin initial entry input

/-- Strict-right outputs are still exactly the second literal record; adding
the finite seed postcontrol changes no physical output. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelection_strictRight_outputs
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    ((profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionNoRecvOne
        A strategy hwin initial entry member input.1).2,
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOpenRecvTwo
        A strategy hwin initial entry input member).2) =
      (pairedRightSenderStrategy
          (profiledRawJointHybridExactRightUniformActivation A strategy hwin
            (profiledRawJointGuardedCommonPointInstalled A strategy initial)
            ).lambda
          [entry.1] input.1,
        profiledRawJointTargetRightReceiverBothPhysicalOutput
          (profiledRawJointTargetRightReceiverStrategy A
            (profiledRawJointHybridExactRightUniformActivation A strategy
              hwin
              (profiledRawJointGuardedCommonPointInstalled A strategy initial))
            [(entry.2, entry.1)] (input.2, input.1))) := by
  simpa [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionNoRecvOne,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOpenRecvTwo]
    using
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_strictRight_outputs
        A strategy hwin initial entry input member)

/-- Strict-left output mirror. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelection_strictLeft_outputs
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    ((profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOpenRecvOne
        A strategy hwin initial entry input member).2,
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionNoRecvTwo
        A strategy hwin initial entry member input.2).2) =
      (profiledRawJointTargetLeftReceiverBothPhysicalOutput
          (profiledRawJointTargetLeftReceiverStrategy A
            (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
              (profiledRawJointGuardedCommonPointInstalled A strategy initial))
            [entry] input),
        pairedLeftSenderStrategy
          (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
            (profiledRawJointGuardedCommonPointInstalled A strategy initial)
            ).lambda
          [entry.2] input.2) := by
  simpa [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOpenRecvOne,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionNoRecvTwo]
    using
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_strictLeft_outputs
        A strategy hwin initial entry input member)

/-- The common sum arm emits the exact literal simultaneous output. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelection_common_outputs_literal
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCloseOne
        A strategy hwin initial entry input).2,
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCloseTwo
        A strategy hwin initial entry input).2) =
      ((profiledRawJointGuardedCommonPointInstalled A strategy
          (initial.step A strategy entry)).bothOutputOne A input,
        (profiledRawJointGuardedCommonPointInstalled A strategy
          (initial.step A strategy entry)).bothOutputTwo A input) := by
  simpa [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCloseOne,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCloseTwo]
    using
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStart_outputs_literal
        A strategy hwin initial entry input)

end

end DetParityAutomaton

end DistributedSynthesis
