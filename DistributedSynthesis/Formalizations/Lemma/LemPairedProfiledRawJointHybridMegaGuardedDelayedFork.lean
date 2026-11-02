/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteDelayedBitResolver
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedFirstBothAlignment

/-!
# The delayed local fork at the first simultaneous guarded close

The first receive after a guarded-right strict prefix is locally identical at
process one on a strict-left round and on a simultaneous round.  The former
must retain the old target child, whereas the latter must retain the refreshed
target child computed from the current occurrence.  Thus process one cannot
select either child at that receive.

This file audits one finite delayed-fork candidate.  The uninformed endpoint
stores both continuations in a
`FiniteDelayedFork`.  The other endpoint distinguishes receive from
non-receive locally and stores the corresponding `FiniteDelayedTagged` bit.
The fork endpoint selects the actual continuation when it next receives the
tag.  The informed endpoint retains the tag until a non-receive or a delivered
base control acknowledges that the fork endpoint has received it.  The mirror
construction handles guarded-left prefixes.

The tag/acknowledgement mechanism is sound, but the particular closed member
constructed below is not a production continuation: it is an unconsumed
ordinary receiver whose pending target is `none`.  A hidden strict step from
that member consequently enters the unit kernel's arbitrary totalization
fallback.  The reachability-audit equations below expose this obstruction.
The production construction must retain the delayed mechanism while replacing
this raw closed receiver by an honest finite recurrent carrier.
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

private abbrev Mega (fallbackTag : RetainedTag A strategy hwin) :=
  MegaGuardedLinkedPhysicalController A strategy hwin controllers initialBank
    fallbackTag

/-! ## Finite pending controls -/

/-- At a right/`both` ambiguity, process one stores the strict-left and
simultaneous continuations in this order. -/
abbrev ProfiledRawJointHybridMegaGuardedRightPendingOne
    (fallbackTag : RetainedTag A strategy hwin) :=
  FiniteDelayedFork
    (Mega A strategy hwin controllers initialBank fallbackTag).OneControl

/-- Process two knows whether the ambiguous round was strict-left or
simultaneous and tags its actual continuation. -/
abbrev ProfiledRawJointHybridMegaGuardedRightPendingTwo
    (fallbackTag : RetainedTag A strategy hwin) :=
  FiniteDelayedTagged
    (Mega A strategy hwin controllers initialBank fallbackTag).TwoControl

/-- Guarded-left mirror: process one carries the resolved tag. -/
abbrev ProfiledRawJointHybridMegaGuardedLeftPendingOne
    (fallbackTag : RetainedTag A strategy hwin) :=
  FiniteDelayedTagged
    (Mega A strategy hwin controllers initialBank fallbackTag).OneControl

/-- Guarded-left mirror: process two retains the two candidates. -/
abbrev ProfiledRawJointHybridMegaGuardedLeftPendingTwo
    (fallbackTag : RetainedTag A strategy hwin) :=
  FiniteDelayedFork
    (Mega A strategy hwin controllers initialBank fallbackTag).TwoControl

/-! ## Right-prefix local constructors -/

/-- Process one's graph-blind receive constructs both locally possible
continuations.  Both candidates store the old checked close output; only the
child and receiver control differ. -/
noncomputable def
    profiledRawJointHybridMegaGuardedRightPendingForkOne?
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    Option (Out₁ ×
      ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
        controllers initialBank fallbackTag) :=
  match profiledRawJointHybridMegaGuardedRightCloseReceiverOne? A strategy hwin
      initialBank state inputOne inputTwo with
  | none => none
  | some opened =>
      let nextRight := stepProfiledRawJointHybridGuardedRightReceiver A
        strategy hwin state owner inputTwo inputOne
      match profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy
          hwin initialBank nextRight.2 with
      | none => none
      | some root =>
          let source := profiledRawJointHybridMegaChildSource A strategy hwin
            initialBank root.1
          let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
            initialBank root.1
          let closedReceiver := initialProfiledRawJointUnitLeftPolicyReceiver A
            strategy source policy root.2 .both
          let openControl :
              (Mega A strategy hwin controllers initialBank
                fallbackTag).OneControl :=
            (.leftReceiver opened.2.1 opened.2.2, opened.1)
          let closedControl :
              (Mega A strategy hwin controllers initialBank
                fallbackTag).OneControl :=
            (.leftReceiver root.1 closedReceiver, opened.1)
          some (opened.1, ⟨openControl, closedControl⟩)

/-- On the strict-left alternative, process two observes no receive and tags
the ordinary old-child left owner as the open continuation. -/
noncomputable def
    profiledRawJointHybridMegaGuardedRightPendingOpenTaggedTwo?
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (inputTwo : In₂) :
    Option (Out₂ ×
      ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
        controllers initialBank fallbackTag) :=
  match profiledRawJointHybridMegaGuardedRightCloseOwnerTwo? A strategy hwin
      initialBank state inputTwo with
  | none => none
  | some opened =>
      let control :
          (Mega A strategy hwin controllers initialBank fallbackTag).TwoControl
          := (.leftOwner opened.2.1 opened.2.2, opened.1)
      some (opened.1, FiniteDelayedTagged.openBranch control)

/-- On the simultaneous alternative, process two observes a receive, advances
the guarded receiver to the refreshed occurrence, and tags that continuation
as closed. -/
noncomputable def
    profiledRawJointHybridMegaGuardedRightPendingClosedTaggedTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    Out₂ × ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
      controllers initialBank fallbackTag :=
  let next := stepProfiledRawJointHybridGuardedRightReceiver A strategy hwin
    state owner inputTwo inputOne
  let control :
      (Mega A strategy hwin controllers initialBank fallbackTag).TwoControl :=
    (.exceptional (.inr (.inr (.inl next.2))), next.1)
  (next.1, FiniteDelayedTagged.closedBranch control)

/-! ## Exact right-prefix fork equation -/

/-- On a certified prefix, the open candidate is exactly the old-child
strict-left receiver and the raw closed candidate is the unconsumed refreshed-
child `.both` receiver.  Their stored Moore outputs are definitionally equal;
the fallback audit below shows why the latter is not a complete continuation. -/
theorem profiledRawJointHybridMegaGuardedRightPendingForkOne?_eq
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input nextInput : In₂ × In₁)
    (oldRoot : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (holdRoot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some oldRoot)
    (refreshedRoot :
      ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
        initialBank)
    (hrefreshedRoot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation (past ++ [input]) nextInput) =
        some refreshedRoot) :
    let oldSource := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank oldRoot.1
    let oldPolicy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank oldRoot.1
    let oldBank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank oldRoot.1
    let oldRestart := profiledRawJointUnitRestartLeft A strategy oldSource
      oldPolicy oldBank oldRoot.2 .first
    let openNext := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
      oldSource oldPolicy oldBank oldRestart.2 oldRestart.1
        (nextInput.2, nextInput.1)
    let refreshedSource := profiledRawJointHybridMegaChildSource A strategy
      hwin initialBank refreshedRoot.1
    let refreshedPolicy := profiledRawJointHybridMegaChildPolicy A strategy
      hwin initialBank refreshedRoot.1
    let closedReceiver := initialProfiledRawJointUnitLeftPolicyReceiver A
      strategy refreshedSource refreshedPolicy refreshedRoot.2 .both
    profiledRawJointHybridMegaGuardedRightPendingForkOne? A strategy hwin
        controllers initialBank fallbackTag
        (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
          installation past input)
        (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
          installation (past ++ [input])) nextInput.2 nextInput.1 =
      some (openNext.1,
        ⟨(.leftReceiver oldRoot.1 openNext.2, openNext.1),
          (.leftReceiver refreshedRoot.1 closedReceiver, openNext.1)⟩) := by
  dsimp only
  let state :=
    profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
      installation past input
  have hclose :=
    profiledRawJointHybridMegaGuardedRightCloseReceiverOne?_some A strategy
      hwin initialBank state oldRoot holdRoot nextInput.2 nextInput.1
  unfold profiledRawJointHybridMegaGuardedRightPendingForkOne?
  rw [hclose]
  dsimp only
  rw [profiledRawJointHybridGuardedRightPrefixReceiverAfter_step A strategy
    hwin installation past input nextInput, hrefreshedRoot]

/-! ## Left-prefix local constructors -/

/-- Process two's graph-blind receive stores the old-child strict-right
continuation and the refreshed simultaneous continuation. -/
noncomputable def
    profiledRawJointHybridMegaGuardedLeftPendingForkTwo?
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    Option (Out₂ ×
      ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
        controllers initialBank fallbackTag) :=
  match profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo? A strategy hwin
      initialBank state inputTwo inputOne with
  | none => none
  | some opened =>
      let nextLeft := stepProfiledRawJointHybridGuardedLeftReceiver A strategy
        hwin state owner inputOne inputTwo
      match profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy
          hwin initialBank nextLeft.2 with
      | none => none
      | some root =>
          let source := profiledRawJointHybridMegaChildSource A strategy hwin
            initialBank root.1
          let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
            initialBank root.1
          let closedReceiver :=
            initialProfiledRawJointUnitRightPolicyReceiver A strategy source
              policy root.2 .both
          let openControl :
              (Mega A strategy hwin controllers initialBank
                fallbackTag).TwoControl :=
            (.rightReceiver opened.2.1 opened.2.2, opened.1)
          let closedControl :
              (Mega A strategy hwin controllers initialBank
                fallbackTag).TwoControl :=
            (.rightReceiver root.1 closedReceiver, opened.1)
          some (opened.1, ⟨openControl, closedControl⟩)

/-- On the strict-right alternative, process one observes no receive and tags
the ordinary old-child right owner as open. -/
noncomputable def
    profiledRawJointHybridMegaGuardedLeftPendingOpenTaggedOne?
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (inputOne : In₁) :
    Option (Out₁ ×
      ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
        controllers initialBank fallbackTag) :=
  match profiledRawJointHybridMegaGuardedLeftCloseOwnerOne? A strategy hwin
      initialBank state inputOne with
  | none => none
  | some opened =>
      let control :
          (Mega A strategy hwin controllers initialBank fallbackTag).OneControl
          := (.rightOwner opened.2.1 opened.2.2, opened.1)
      some (opened.1, FiniteDelayedTagged.openBranch control)

/-- On the simultaneous alternative, process one observes a receive, advances
the guarded-left receiver, and tags the refreshed continuation as closed. -/
noncomputable def
    profiledRawJointHybridMegaGuardedLeftPendingClosedTaggedOne
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    Out₁ × ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
      controllers initialBank fallbackTag :=
  let next := stepProfiledRawJointHybridGuardedLeftReceiver A strategy hwin
    state owner inputOne inputTwo
  let control :
      (Mega A strategy hwin controllers initialBank fallbackTag).OneControl :=
    (.exceptional (.inr (.inr (.inr next.2))), next.1)
  (next.1, FiniteDelayedTagged.closedBranch control)

/-! ## Exact left-prefix fork equation -/

/-- On a certified guarded-left prefix, process two's two raw candidates are
the old-child strict-right receiver and the unconsumed refreshed-child `.both`
receiver, with one definitionally shared Moore output. -/
theorem profiledRawJointHybridMegaGuardedLeftPendingForkTwo?_eq
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input nextInput : In₁ × In₂)
    (oldRoot : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (holdRoot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input) = some oldRoot)
    (refreshedRoot :
      ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
        initialBank)
    (hrefreshedRoot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation (past ++ [input]) nextInput) =
        some refreshedRoot) :
    let oldSource := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank oldRoot.1
    let oldPolicy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank oldRoot.1
    let oldBank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank oldRoot.1
    let oldRestart := profiledRawJointUnitRestartRight A strategy oldSource
      oldPolicy oldBank oldRoot.2 .first
    let openNext := continueProfiledRawJointUnitRightPolicyReceiver A strategy
      oldSource oldPolicy oldBank oldRestart.2 oldRestart.1
        (nextInput.2, nextInput.1)
    let refreshedSource := profiledRawJointHybridMegaChildSource A strategy
      hwin initialBank refreshedRoot.1
    let refreshedPolicy := profiledRawJointHybridMegaChildPolicy A strategy
      hwin initialBank refreshedRoot.1
    let closedReceiver := initialProfiledRawJointUnitRightPolicyReceiver A
      strategy refreshedSource refreshedPolicy refreshedRoot.2 .both
    profiledRawJointHybridMegaGuardedLeftPendingForkTwo? A strategy hwin
        controllers initialBank fallbackTag
        (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
          installation past input)
        (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
          installation (past ++ [input])) nextInput.1 nextInput.2 =
      some (openNext.1,
        ⟨(.rightReceiver oldRoot.1 openNext.2, openNext.1),
          (.rightReceiver refreshedRoot.1 closedReceiver, openNext.1)⟩) := by
  dsimp only
  let state :=
    profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
      installation past input
  have hclose :=
    profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo?_some A strategy hwin
      initialBank state oldRoot holdRoot nextInput.2 nextInput.1
  unfold profiledRawJointHybridMegaGuardedLeftPendingForkTwo?
  rw [hclose]
  dsimp only
  rw [profiledRawJointHybridGuardedLeftPrefixReceiverAfter_step A strategy
    hwin installation past input nextInput, hrefreshedRoot]

/-! ## Immediate Moore-output coherence of a newly created fork -/

/-! ### Reachability audit for a hidden strict continuation

The closed member constructed above is an unconsumed ordinary receiver.  Its
pending target is therefore `none`.  If the fork remains hidden for one more
strict round, the indexed unit kernel does not follow a represented child: it
totalizes the transition with `profiledRawJointUnitPolicyFallbackRight` (or
its mirror).  The following equations make that obstruction explicit.  They
are intentionally stated before any output-coherence claim so that a later
proof cannot silently treat this totalization branch as reachable semantic
data.
-/

/-- A strict-right step from the freshly installed closed right-seam member
uses the unit kernel's arbitrary fallback right target. -/
theorem
    profiledRawJointHybridMegaGuardedClosedInitialLeft_noRecvOne_eq_fallback
    (fallbackTag : RetainedTag A strategy hwin)
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (root : ProfiledRawJointHybridMegaLeftMacro A strategy hwin initialBank
      child)
    (oldOutput : Out₁) (input : In₁) :
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank child
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank child
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank child
    let receiver := initialProfiledRawJointUnitLeftPolicyReceiver A strategy
      source policy root .both
    let target := profiledRawJointUnitPolicyFallbackRight A strategy source
      policy bank root
    let restart := profiledRawJointUnitRestartRight A strategy source policy
      bank target .both
    let next := stepProfiledRawJointUnitRightPolicyOwner A strategy source
      policy bank restart.1 input
    (Mega A strategy hwin controllers initialBank fallbackTag).noRecvOne
        ((.leftReceiver child receiver, oldOutput)) input =
      (.rightOwner child next.2, next.1) := by
  classical
  simp [Mega, MegaGuardedLinkedPhysicalController,
    profiledRawJointHybridMegaGuardedLinkedLeaderFreeKernel,
    profiledRawJointHybridMegaLeaderFreeKernel,
    profiledRawJointIndexedPolicyLeaderFreeKernel,
    profiledRawJointUnitPolicyStartRightOwner,
    profiledRawJointUnitPolicyLeftReceiverTarget,
    initialProfiledRawJointUnitLeftPolicyReceiver]

/-- A strict-left step from the freshly installed closed left-seam member
uses the mirrored arbitrary fallback left target. -/
theorem
    profiledRawJointHybridMegaGuardedClosedInitialRight_noRecvTwo_eq_fallback
    (fallbackTag : RetainedTag A strategy hwin)
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (root : ProfiledRawJointHybridMegaRightMacro A strategy hwin initialBank
      child)
    (oldOutput : Out₂) (input : In₂) :
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank child
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank child
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank child
    let receiver := initialProfiledRawJointUnitRightPolicyReceiver A strategy
      source policy root .both
    let target := profiledRawJointUnitPolicyFallbackLeft A strategy source
      policy bank root
    let restart := profiledRawJointUnitRestartLeft A strategy source policy
      bank target .both
    let next := stepProfiledRawJointUnitLeftPolicyOwner A strategy source
      policy bank restart.1 input
    (Mega A strategy hwin controllers initialBank fallbackTag).noRecvTwo
        ((.rightReceiver child receiver, oldOutput)) input =
      (.leftOwner child next.2, next.1) := by
  classical
  simp [Mega, MegaGuardedLinkedPhysicalController,
    profiledRawJointHybridMegaGuardedLinkedLeaderFreeKernel,
    profiledRawJointHybridMegaLeaderFreeKernel,
    profiledRawJointIndexedPolicyLeaderFreeKernel,
    profiledRawJointUnitPolicyStartLeftOwner,
    profiledRawJointUnitPolicyRightReceiverTarget,
    initialProfiledRawJointUnitRightPolicyReceiver]

/-- The exact invariant needed to emit from a pending right-seam fork. -/
def ProfiledRawJointHybridMegaGuardedRightPendingOutputCoherent
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag) : Prop :=
  (Mega A strategy hwin controllers initialBank fallbackTag).outputOne
      fork.openControl =
    (Mega A strategy hwin controllers initialBank fallbackTag).outputOne
      fork.closedControl

/-- The process-two mirror invariant for a guarded-left pending fork. -/
def ProfiledRawJointHybridMegaGuardedLeftPendingOutputCoherent
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag) : Prop :=
  (Mega A strategy hwin controllers initialBank fallbackTag).outputTwo
      fork.openControl =
    (Mega A strategy hwin controllers initialBank fallbackTag).outputTwo
      fork.closedControl

/-- Every successfully created right-seam fork is immediately output
coherent: its two controls deliberately carry the same stored Moore output. -/
theorem
    profiledRawJointHybridMegaGuardedRightPendingForkOne?_outputCoherent
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) (outputOne : Out₁)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (hfork :
      profiledRawJointHybridMegaGuardedRightPendingForkOne? A strategy hwin
          controllers initialBank fallbackTag state owner inputOne inputTwo =
        some (outputOne, fork)) :
    ProfiledRawJointHybridMegaGuardedRightPendingOutputCoherent A strategy hwin
      controllers initialBank fallbackTag fork := by
  unfold ProfiledRawJointHybridMegaGuardedRightPendingOutputCoherent
  unfold profiledRawJointHybridMegaGuardedRightPendingForkOne? at hfork
  split at hfork
  · simp_all
  · dsimp only at hfork
    split at hfork
    · simp_all
    · simp only [Option.some.injEq, Prod.mk.injEq] at hfork
      rcases hfork with ⟨rfl, rfl⟩
      rfl

/-- Every successfully created guarded-left fork has the mirrored immediate
Moore-output coherence property. -/
theorem
    profiledRawJointHybridMegaGuardedLeftPendingForkTwo?_outputCoherent
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) (outputTwo : Out₂)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (hfork :
      profiledRawJointHybridMegaGuardedLeftPendingForkTwo? A strategy hwin
          controllers initialBank fallbackTag state owner inputOne inputTwo =
        some (outputTwo, fork)) :
    ProfiledRawJointHybridMegaGuardedLeftPendingOutputCoherent A strategy hwin
      controllers initialBank fallbackTag fork := by
  unfold ProfiledRawJointHybridMegaGuardedLeftPendingOutputCoherent
  unfold profiledRawJointHybridMegaGuardedLeftPendingForkTwo? at hfork
  split at hfork
  · simp_all
  · dsimp only at hfork
    split at hfork
    · simp_all
    · simp only [Option.some.injEq, Prod.mk.injEq] at hfork
      rcases hfork with ⟨rfl, rfl⟩
      rfl

/-- Conditional coherence interface for one further strict-right round while
process one still cannot receive the tag.  The canonical raw fork above does
not supply this property: its closed member enters the audited fallback. -/
def ProfiledRawJointHybridMegaGuardedRightPendingNoRecvOutputCoherent
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) : Prop :=
  (Mega A strategy hwin controllers initialBank fallbackTag).outputOne
      ((Mega A strategy hwin controllers initialBank
        fallbackTag).noRecvOne fork.openControl inputOne) =
    (Mega A strategy hwin controllers initialBank fallbackTag).outputOne
      ((Mega A strategy hwin controllers initialBank
        fallbackTag).noRecvOne fork.closedControl inputOne)

/-- Guarded-left conditional mirror.  This is not a proof obligation for the
canonical raw fork, whose closed member has the mirrored fallback defect. -/
def ProfiledRawJointHybridMegaGuardedLeftPendingNoRecvOutputCoherent
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputTwo : In₂) : Prop :=
  (Mega A strategy hwin controllers initialBank fallbackTag).outputTwo
      ((Mega A strategy hwin controllers initialBank
        fallbackTag).noRecvTwo fork.openControl inputTwo) =
    (Mega A strategy hwin controllers initialBank fallbackTag).outputTwo
      ((Mega A strategy hwin controllers initialBank
        fallbackTag).noRecvTwo fork.closedControl inputTwo)

/-- One-step no-receive coherence is exactly immediate output coherence of
the advanced right fork. -/
theorem
    profiledRawJointHybridMegaGuardedRightPendingNoRecvOutputCoherent_iff
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) :
    ProfiledRawJointHybridMegaGuardedRightPendingNoRecvOutputCoherent A
        strategy hwin controllers initialBank fallbackTag fork inputOne ↔
      ProfiledRawJointHybridMegaGuardedRightPendingOutputCoherent A strategy
        hwin controllers initialBank fallbackTag
          ⟨(Mega A strategy hwin controllers initialBank
              fallbackTag).noRecvOne fork.openControl inputOne,
            (Mega A strategy hwin controllers initialBank
              fallbackTag).noRecvOne fork.closedControl inputOne⟩ :=
  Iff.rfl

/-- One-step no-receive coherence is exactly immediate output coherence of
the advanced left fork. -/
theorem
    profiledRawJointHybridMegaGuardedLeftPendingNoRecvOutputCoherent_iff
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputTwo : In₂) :
    ProfiledRawJointHybridMegaGuardedLeftPendingNoRecvOutputCoherent A strategy
        hwin controllers initialBank fallbackTag fork inputTwo ↔
      ProfiledRawJointHybridMegaGuardedLeftPendingOutputCoherent A strategy
        hwin controllers initialBank fallbackTag
          ⟨(Mega A strategy hwin controllers initialBank
              fallbackTag).noRecvTwo fork.openControl inputTwo,
            (Mega A strategy hwin controllers initialBank
              fallbackTag).noRecvTwo fork.closedControl inputTwo⟩ :=
  Iff.rfl

/-! ## Physical indistinguishability at the seam -/

/-- No physical controller can choose different process-one controls for the
strict-left and simultaneous interpretations of one local receive. -/
theorem profiledRawJointHybridMegaGuarded_left_both_one_indistinguishable
    (fallbackTag : RetainedTag A strategy hwin)
    (controls :
      (Mega A strategy hwin controllers initialBank fallbackTag).OneControl ×
      (Mega A strategy hwin controllers initialBank fallbackTag).TwoControl)
    (inputOne : In₁) (inputTwo : In₂) :
    ((Mega A strategy hwin controllers initialBank fallbackTag).advanceControls
      controls ⟨inputOne, inputTwo, .left⟩).1 =
    ((Mega A strategy hwin controllers initialBank fallbackTag).advanceControls
      controls ⟨inputOne, inputTwo, .both⟩).1 :=
  rfl

/-- Process-two mirror of the preceding local indistinguishability. -/
theorem profiledRawJointHybridMegaGuarded_right_both_two_indistinguishable
    (fallbackTag : RetainedTag A strategy hwin)
    (controls :
      (Mega A strategy hwin controllers initialBank fallbackTag).OneControl ×
      (Mega A strategy hwin controllers initialBank fallbackTag).TwoControl)
    (inputOne : In₁) (inputTwo : In₂) :
    ((Mega A strategy hwin controllers initialBank fallbackTag).advanceControls
      controls ⟨inputOne, inputTwo, .right⟩).2 =
    ((Mega A strategy hwin controllers initialBank fallbackTag).advanceControls
      controls ⟨inputOne, inputTwo, .both⟩).2 :=
  rfl

/-! ## An outer finite controller carrying the unresolved bit -/

/-- The enlarged process-one alphabet.  The two pending summands correspond
to the two possible strict-prefix orientations. -/
abbrev ProfiledRawJointHybridMegaGuardedDelayedOneControl
    (fallbackTag : RetainedTag A strategy hwin) :=
  (Mega A strategy hwin controllers initialBank fallbackTag).OneControl ⊕
    (ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
        controllers initialBank fallbackTag ⊕
      ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
        controllers initialBank fallbackTag)

/-- The enlarged process-two alphabet. -/
abbrev ProfiledRawJointHybridMegaGuardedDelayedTwoControl
    (fallbackTag : RetainedTag A strategy hwin) :=
  (Mega A strategy hwin controllers initialBank fallbackTag).TwoControl ⊕
    (ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
        controllers initialBank fallbackTag ⊕
      ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
        controllers initialBank fallbackTag)

private noncomputable def profiledRawJointHybridMegaGuardedDelayedBaseOne
    (fallbackTag : RetainedTag A strategy hwin)
    (control : ProfiledRawJointHybridMegaGuardedDelayedOneControl A strategy
      hwin controllers initialBank fallbackTag) :
    (Mega A strategy hwin controllers initialBank fallbackTag).OneControl :=
  match control with
  | .inl base => base
  | .inr (.inl fork) => fork.openControl
  | .inr (.inr tagged) => tagged.control

private noncomputable def profiledRawJointHybridMegaGuardedDelayedBaseTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (control : ProfiledRawJointHybridMegaGuardedDelayedTwoControl A strategy
      hwin controllers initialBank fallbackTag) :
    (Mega A strategy hwin controllers initialBank fallbackTag).TwoControl :=
  match control with
  | .inl base => base
  | .inr (.inl tagged) => tagged.control
  | .inr (.inr fork) => fork.openControl

private noncomputable def profiledRawJointHybridMegaGuardedDelayedNoRecvOne
    (fallbackTag : RetainedTag A strategy hwin)
    (control : ProfiledRawJointHybridMegaGuardedDelayedOneControl A strategy
      hwin controllers initialBank fallbackTag)
    (input : In₁) :
    ProfiledRawJointHybridMegaGuardedDelayedOneControl A strategy hwin
      controllers initialBank fallbackTag := by
  let base := Mega A strategy hwin controllers initialBank fallbackTag
  match control with
  | .inl baseControl =>
      match baseControl.1 with
      | .exceptional (.inr (.inr (.inr leftReceiver))) =>
          match profiledRawJointHybridMegaGuardedLeftPendingOpenTaggedOne? A
              strategy hwin controllers initialBank fallbackTag leftReceiver
                input with
          | none => exact .inl (base.noRecvOne baseControl input)
          | some tagged => exact .inr (.inr tagged.2)
      | _ => exact .inl (base.noRecvOne baseControl input)
  | .inr (.inl fork) =>
      exact .inr (.inl
        ⟨base.noRecvOne fork.openControl input,
          base.noRecvOne fork.closedControl input⟩)
  | .inr (.inr tagged) =>
      exact .inl (base.noRecvOne tagged.control input)

private noncomputable def profiledRawJointHybridMegaGuardedDelayedNoRecvTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (control : ProfiledRawJointHybridMegaGuardedDelayedTwoControl A strategy
      hwin controllers initialBank fallbackTag)
    (input : In₂) :
    ProfiledRawJointHybridMegaGuardedDelayedTwoControl A strategy hwin
      controllers initialBank fallbackTag := by
  let base := Mega A strategy hwin controllers initialBank fallbackTag
  match control with
  | .inl baseControl =>
      match baseControl.1 with
      | .exceptional (.inr (.inr (.inl rightReceiver))) =>
          match profiledRawJointHybridMegaGuardedRightPendingOpenTaggedTwo? A
              strategy hwin controllers initialBank fallbackTag rightReceiver
                input with
          | none => exact .inl (base.noRecvTwo baseControl input)
          | some tagged => exact .inr (.inl tagged.2)
      | _ => exact .inl (base.noRecvTwo baseControl input)
  | .inr (.inl tagged) =>
      exact .inl (base.noRecvTwo tagged.control input)
  | .inr (.inr fork) =>
      exact .inr (.inr
        ⟨base.noRecvTwo fork.openControl input,
          base.noRecvTwo fork.closedControl input⟩)

private noncomputable def profiledRawJointHybridMegaGuardedDelayedRecvOne
    (fallbackTag : RetainedTag A strategy hwin)
    (one : ProfiledRawJointHybridMegaGuardedDelayedOneControl A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁)
    (two : ProfiledRawJointHybridMegaGuardedDelayedTwoControl A strategy hwin
      controllers initialBank fallbackTag)
    (inputTwo : In₂) :
    ProfiledRawJointHybridMegaGuardedDelayedOneControl A strategy hwin
      controllers initialBank fallbackTag := by
  let base := Mega A strategy hwin controllers initialBank fallbackTag
  match one, two with
  | .inl baseOne, .inl baseTwo =>
      match baseOne.1, baseTwo.1 with
      | .exceptional (.inr (.inr (.inl rightOwner))),
          .exceptional (.inr (.inr (.inl rightReceiver))) =>
          match profiledRawJointHybridMegaGuardedRightPendingForkOne? A
              strategy hwin controllers initialBank fallbackTag rightReceiver
                rightOwner inputOne inputTwo with
          | none => exact .inl (base.recvOne baseOne inputOne baseTwo inputTwo)
          | some fork => exact .inr (.inl fork.2)
      | .exceptional (.inr (.inr (.inr leftReceiver))),
          .exceptional (.inr (.inr (.inr leftOwner))) =>
          exact .inr (.inr
            (profiledRawJointHybridMegaGuardedLeftPendingClosedTaggedOne A
              strategy hwin controllers initialBank fallbackTag leftReceiver
                leftOwner inputOne inputTwo).2)
      | _, _ => exact .inl (base.recvOne baseOne inputOne baseTwo inputTwo)
  | .inr (.inl fork), .inr (.inl tagged) =>
      exact .inl (base.recvOne (fork.resolve tagged) inputOne tagged.control
        inputTwo)
  | .inr (.inr tagged), .inr (.inr fork) =>
      exact .inr (.inr
        ⟨tagged.bit,
          base.recvOne tagged.control inputOne (fork.resolve tagged) inputTwo⟩)
  | _, _ =>
      exact .inl (base.recvOne
        (profiledRawJointHybridMegaGuardedDelayedBaseOne A strategy hwin
          controllers initialBank fallbackTag one) inputOne
        (profiledRawJointHybridMegaGuardedDelayedBaseTwo A strategy hwin
          controllers initialBank fallbackTag two) inputTwo)

private noncomputable def profiledRawJointHybridMegaGuardedDelayedRecvTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (two : ProfiledRawJointHybridMegaGuardedDelayedTwoControl A strategy hwin
      controllers initialBank fallbackTag)
    (inputTwo : In₂)
    (one : ProfiledRawJointHybridMegaGuardedDelayedOneControl A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) :
    ProfiledRawJointHybridMegaGuardedDelayedTwoControl A strategy hwin
      controllers initialBank fallbackTag := by
  let base := Mega A strategy hwin controllers initialBank fallbackTag
  match two, one with
  | .inl baseTwo, .inl baseOne =>
      match baseTwo.1, baseOne.1 with
      | .exceptional (.inr (.inr (.inl rightReceiver))),
          .exceptional (.inr (.inr (.inl rightOwner))) =>
          exact .inr (.inl
            (profiledRawJointHybridMegaGuardedRightPendingClosedTaggedTwo A
              strategy hwin controllers initialBank fallbackTag rightReceiver
                rightOwner inputOne inputTwo).2)
      | .exceptional (.inr (.inr (.inr leftOwner))),
          .exceptional (.inr (.inr (.inr leftReceiver))) =>
          match profiledRawJointHybridMegaGuardedLeftPendingForkTwo? A strategy
              hwin controllers initialBank fallbackTag leftReceiver leftOwner
                inputOne inputTwo with
          | none => exact .inl (base.recvTwo baseTwo inputTwo baseOne inputOne)
          | some fork => exact .inr (.inr fork.2)
      | _, _ => exact .inl (base.recvTwo baseTwo inputTwo baseOne inputOne)
  | .inr (.inl tagged), .inr (.inl fork) =>
      exact .inr (.inl
        ⟨tagged.bit,
          base.recvTwo tagged.control inputTwo (fork.resolve tagged) inputOne⟩)
  | .inr (.inr fork), .inr (.inr tagged) =>
      exact .inl (base.recvTwo (fork.resolve tagged) inputTwo tagged.control
        inputOne)
  | _, _ =>
      exact .inl (base.recvTwo
        (profiledRawJointHybridMegaGuardedDelayedBaseTwo A strategy hwin
          controllers initialBank fallbackTag two) inputTwo
        (profiledRawJointHybridMegaGuardedDelayedBaseOne A strategy hwin
          controllers initialBank fallbackTag one) inputOne)

set_option synthInstance.maxHeartbeats 1000000 in
/-- The finite local controller that retains the unresolved strict/simultaneous
bit instead of prematurely selecting the old or refreshed target child. -/
noncomputable def profiledRawJointHybridMegaGuardedDelayedPhysicalController
    (fallbackTag : RetainedTag A strategy hwin) :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ where
  OneControl := ProfiledRawJointHybridMegaGuardedDelayedOneControl A strategy
    hwin controllers initialBank fallbackTag
  TwoControl := ProfiledRawJointHybridMegaGuardedDelayedTwoControl A strategy
    hwin controllers initialBank fallbackTag
  oneFinite := by infer_instance
  twoFinite := by infer_instance
  initialOne := .inl
    (Mega A strategy hwin controllers initialBank fallbackTag).initialOne
  initialTwo := .inl
    (Mega A strategy hwin controllers initialBank fallbackTag).initialTwo
  noRecvOne := profiledRawJointHybridMegaGuardedDelayedNoRecvOne A strategy
    hwin controllers initialBank fallbackTag
  noRecvTwo := profiledRawJointHybridMegaGuardedDelayedNoRecvTwo A strategy
    hwin controllers initialBank fallbackTag
  recvOne := profiledRawJointHybridMegaGuardedDelayedRecvOne A strategy hwin
    controllers initialBank fallbackTag
  recvTwo := profiledRawJointHybridMegaGuardedDelayedRecvTwo A strategy hwin
    controllers initialBank fallbackTag
  outputOne := fun control =>
    (Mega A strategy hwin controllers initialBank fallbackTag).outputOne
      (profiledRawJointHybridMegaGuardedDelayedBaseOne A strategy hwin
        controllers initialBank fallbackTag control)
  outputTwo := fun control =>
    (Mega A strategy hwin controllers initialBank fallbackTag).outputTwo
      (profiledRawJointHybridMegaGuardedDelayedBaseTwo A strategy hwin
        controllers initialBank fallbackTag control)

/-! The following field equations keep later trace proofs from unfolding the
whole dependent controller record. -/

@[simp] theorem profiledRawJointHybridMegaGuardedDelayedPhysicalController_noRecvOne
    (fallbackTag : RetainedTag A strategy hwin)
    (control : ProfiledRawJointHybridMegaGuardedDelayedOneControl A strategy
      hwin controllers initialBank fallbackTag)
    (inputOne : In₁) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).noRecvOne control inputOne =
    profiledRawJointHybridMegaGuardedDelayedNoRecvOne A strategy hwin
      controllers initialBank fallbackTag control inputOne :=
  rfl

@[simp] theorem profiledRawJointHybridMegaGuardedDelayedPhysicalController_noRecvTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (control : ProfiledRawJointHybridMegaGuardedDelayedTwoControl A strategy
      hwin controllers initialBank fallbackTag)
    (inputTwo : In₂) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).noRecvTwo control inputTwo =
    profiledRawJointHybridMegaGuardedDelayedNoRecvTwo A strategy hwin
      controllers initialBank fallbackTag control inputTwo :=
  rfl

@[simp] theorem profiledRawJointHybridMegaGuardedDelayedPhysicalController_recvOne
    (fallbackTag : RetainedTag A strategy hwin)
    (one : ProfiledRawJointHybridMegaGuardedDelayedOneControl A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁)
    (two : ProfiledRawJointHybridMegaGuardedDelayedTwoControl A strategy hwin
      controllers initialBank fallbackTag)
    (inputTwo : In₂) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).recvOne one inputOne two inputTwo =
    profiledRawJointHybridMegaGuardedDelayedRecvOne A strategy hwin controllers
      initialBank fallbackTag one inputOne two inputTwo :=
  rfl

@[simp] theorem profiledRawJointHybridMegaGuardedDelayedPhysicalController_recvTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (two : ProfiledRawJointHybridMegaGuardedDelayedTwoControl A strategy hwin
      controllers initialBank fallbackTag)
    (inputTwo : In₂)
    (one : ProfiledRawJointHybridMegaGuardedDelayedOneControl A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).recvTwo two inputTwo one inputOne =
    profiledRawJointHybridMegaGuardedDelayedRecvTwo A strategy hwin controllers
      initialBank fallbackTag two inputTwo one inputOne :=
  rfl

/-! ## Exact seam transitions of the enlarged controller -/

@[simp] theorem profiledRawJointHybridMegaGuardedDelayed_outputOne_rightPending
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).outputOne (.inr (.inl fork)) =
    (Mega A strategy hwin controllers initialBank fallbackTag).outputOne
      fork.openControl :=
  rfl

@[simp] theorem profiledRawJointHybridMegaGuardedDelayed_outputTwo_rightPending
    (fallbackTag : RetainedTag A strategy hwin)
    (tagged : ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
      controllers initialBank fallbackTag) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).outputTwo (.inr (.inl tagged)) =
    (Mega A strategy hwin controllers initialBank fallbackTag).outputTwo
      tagged.control :=
  rfl

@[simp] theorem profiledRawJointHybridMegaGuardedDelayed_outputOne_leftPending
    (fallbackTag : RetainedTag A strategy hwin)
    (tagged : ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
      controllers initialBank fallbackTag) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).outputOne (.inr (.inr tagged)) =
    (Mega A strategy hwin controllers initialBank fallbackTag).outputOne
      tagged.control :=
  rfl

@[simp] theorem profiledRawJointHybridMegaGuardedDelayed_outputTwo_leftPending
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).outputTwo (.inr (.inr fork)) =
    (Mega A strategy hwin controllers initialBank fallbackTag).outputTwo
      fork.openControl :=
  rfl

/-- Process one's receive handler enters the right pending fork whenever its
local constructor succeeds.  This one equation is shared by strict-left and
simultaneous rounds. -/
theorem profiledRawJointHybridMegaGuardedDelayedRecvOne_rightSeam
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂)
    (outputOne : Out₁)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (hfork :
      profiledRawJointHybridMegaGuardedRightPendingForkOne? A strategy hwin
          controllers initialBank fallbackTag state owner inputOne inputTwo =
        some (outputOne, fork)) :
    profiledRawJointHybridMegaGuardedDelayedRecvOne A strategy hwin controllers
        initialBank fallbackTag
        (.inl
          ((.exceptional (.inr (.inr (.inl owner))), oldOutputOne) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).OneControl))
        inputOne
        (.inl
          ((.exceptional (.inr (.inr (.inl state))), oldOutputTwo) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).TwoControl))
        inputTwo = .inr (.inl fork) := by
  unfold profiledRawJointHybridMegaGuardedDelayedRecvOne
  simp only [hfork]

/-- Process two's simultaneous receive records the closed tag. -/
@[simp] theorem profiledRawJointHybridMegaGuardedDelayedRecvTwo_rightSeam
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledRawJointHybridMegaGuardedDelayedRecvTwo A strategy hwin controllers
        initialBank fallbackTag
        (.inl
          ((.exceptional (.inr (.inr (.inl state))), oldOutputTwo) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).TwoControl))
        inputTwo
        (.inl
          ((.exceptional (.inr (.inr (.inl owner))), oldOutputOne) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).OneControl))
        inputOne =
      .inr (.inl
        (profiledRawJointHybridMegaGuardedRightPendingClosedTaggedTwo A strategy
          hwin controllers initialBank fallbackTag state owner inputOne
            inputTwo).2) := by
  rfl

/-- Process two's strict-left non-receive records the open tag whenever the
old-child close succeeds. -/
theorem profiledRawJointHybridMegaGuardedDelayedNoRecvTwo_rightSeam
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (oldOutputTwo : Out₂) (inputTwo : In₂)
    (outputTwo : Out₂)
    (tagged : ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (htagged :
      profiledRawJointHybridMegaGuardedRightPendingOpenTaggedTwo? A strategy
          hwin controllers initialBank fallbackTag state inputTwo =
        some (outputTwo, tagged)) :
    profiledRawJointHybridMegaGuardedDelayedNoRecvTwo A strategy hwin
        controllers initialBank fallbackTag
        (.inl
          ((.exceptional (.inr (.inr (.inl state))), oldOutputTwo) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).TwoControl))
        inputTwo = .inr (.inl tagged) := by
  unfold profiledRawJointHybridMegaGuardedDelayedNoRecvTwo
  simp only [htagged]

set_option maxHeartbeats 1000000 in
/-- A strict-left round at the guarded-right seam installs the common fork at
process one and the open tag at process two. -/
theorem profiledRawJointHybridMegaGuardedDelayed_rightSeam_advance_left
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂)
    (outputOne : Out₁)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (outputTwo : Out₂)
    (tagged : ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (hfork :
      profiledRawJointHybridMegaGuardedRightPendingForkOne? A strategy hwin
          controllers initialBank fallbackTag state owner inputOne inputTwo =
        some (outputOne, fork))
    (htagged :
      profiledRawJointHybridMegaGuardedRightPendingOpenTaggedTwo? A strategy
          hwin controllers initialBank fallbackTag state inputTwo =
        some (outputTwo, tagged)) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).advanceControls
        (.inl
          ((.exceptional (.inr (.inr (.inl owner))), oldOutputOne) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).OneControl),
         .inl
          ((.exceptional (.inr (.inr (.inl state))), oldOutputTwo) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).TwoControl))
        ⟨inputOne, inputTwo, .left⟩ =
      (.inr (.inl fork), .inr (.inl tagged)) := by
  rw [FinitePairedPhysicalController.advanceControls_left]
  rw [profiledRawJointHybridMegaGuardedDelayedPhysicalController_recvOne,
    profiledRawJointHybridMegaGuardedDelayedPhysicalController_noRecvTwo,
    profiledRawJointHybridMegaGuardedDelayedRecvOne_rightSeam A strategy hwin
      controllers initialBank fallbackTag state owner oldOutputOne oldOutputTwo
        inputOne inputTwo outputOne fork hfork,
    profiledRawJointHybridMegaGuardedDelayedNoRecvTwo_rightSeam A strategy hwin
      controllers initialBank fallbackTag state oldOutputTwo inputTwo outputTwo
        tagged htagged]

set_option maxHeartbeats 1000000 in
/-- The locally indistinguishable simultaneous round installs the same fork
at process one and the closed tag at process two. -/
theorem profiledRawJointHybridMegaGuardedDelayed_rightSeam_advance_both
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂)
    (outputOne : Out₁)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (hfork :
      profiledRawJointHybridMegaGuardedRightPendingForkOne? A strategy hwin
          controllers initialBank fallbackTag state owner inputOne inputTwo =
        some (outputOne, fork)) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).advanceControls
        (.inl
          ((.exceptional (.inr (.inr (.inl owner))), oldOutputOne) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).OneControl),
         .inl
          ((.exceptional (.inr (.inr (.inl state))), oldOutputTwo) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).TwoControl))
        ⟨inputOne, inputTwo, .both⟩ =
      (.inr (.inl fork),
        .inr (.inl
          (profiledRawJointHybridMegaGuardedRightPendingClosedTaggedTwo A
            strategy hwin controllers initialBank fallbackTag state owner
              inputOne inputTwo).2)) := by
  rw [FinitePairedPhysicalController.advanceControls_both]
  rw [profiledRawJointHybridMegaGuardedDelayedPhysicalController_recvOne,
    profiledRawJointHybridMegaGuardedDelayedPhysicalController_recvTwo,
    profiledRawJointHybridMegaGuardedDelayedRecvOne_rightSeam A strategy hwin
      controllers initialBank fallbackTag state owner oldOutputOne oldOutputTwo
        inputOne inputTwo outputOne fork hfork,
    profiledRawJointHybridMegaGuardedDelayedRecvTwo_rightSeam]

/-- Process two's receive handler enters the left pending fork whenever its
local constructor succeeds.  The same equation governs strict-right and
simultaneous rounds. -/
theorem profiledRawJointHybridMegaGuardedDelayedRecvTwo_leftSeam
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂)
    (outputTwo : Out₂)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (hfork :
      profiledRawJointHybridMegaGuardedLeftPendingForkTwo? A strategy hwin
          controllers initialBank fallbackTag state owner inputOne inputTwo =
        some (outputTwo, fork)) :
    profiledRawJointHybridMegaGuardedDelayedRecvTwo A strategy hwin controllers
        initialBank fallbackTag
        (.inl
          ((.exceptional (.inr (.inr (.inr owner))), oldOutputTwo) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).TwoControl))
        inputTwo
        (.inl
          ((.exceptional (.inr (.inr (.inr state))), oldOutputOne) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).OneControl))
        inputOne = .inr (.inr fork) := by
  unfold profiledRawJointHybridMegaGuardedDelayedRecvTwo
  simp only [hfork]

/-- Process one's simultaneous receive at a guarded-left seam records the
closed tag. -/
@[simp] theorem profiledRawJointHybridMegaGuardedDelayedRecvOne_leftSeam
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledRawJointHybridMegaGuardedDelayedRecvOne A strategy hwin controllers
        initialBank fallbackTag
        (.inl
          ((.exceptional (.inr (.inr (.inr state))), oldOutputOne) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).OneControl))
        inputOne
        (.inl
          ((.exceptional (.inr (.inr (.inr owner))), oldOutputTwo) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).TwoControl))
        inputTwo =
      .inr (.inr
        (profiledRawJointHybridMegaGuardedLeftPendingClosedTaggedOne A strategy
          hwin controllers initialBank fallbackTag state owner inputOne
            inputTwo).2) := by
  rfl

/-- Process one's strict-right non-receive records the open tag whenever the
old-child close succeeds. -/
theorem profiledRawJointHybridMegaGuardedDelayedNoRecvOne_leftSeam
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (oldOutputOne : Out₁) (inputOne : In₁)
    (outputOne : Out₁)
    (tagged : ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (htagged :
      profiledRawJointHybridMegaGuardedLeftPendingOpenTaggedOne? A strategy
          hwin controllers initialBank fallbackTag state inputOne =
        some (outputOne, tagged)) :
    profiledRawJointHybridMegaGuardedDelayedNoRecvOne A strategy hwin
        controllers initialBank fallbackTag
        (.inl
          ((.exceptional (.inr (.inr (.inr state))), oldOutputOne) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).OneControl))
        inputOne = .inr (.inr tagged) := by
  unfold profiledRawJointHybridMegaGuardedDelayedNoRecvOne
  simp only [htagged]

set_option maxHeartbeats 1000000 in
/-- A strict-right round at the guarded-left seam installs the open tag at
process one and the common fork at process two. -/
theorem profiledRawJointHybridMegaGuardedDelayed_leftSeam_advance_right
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂)
    (outputOne : Out₁)
    (tagged : ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (outputTwo : Out₂)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (htagged :
      profiledRawJointHybridMegaGuardedLeftPendingOpenTaggedOne? A strategy
          hwin controllers initialBank fallbackTag state inputOne =
        some (outputOne, tagged))
    (hfork :
      profiledRawJointHybridMegaGuardedLeftPendingForkTwo? A strategy hwin
          controllers initialBank fallbackTag state owner inputOne inputTwo =
        some (outputTwo, fork)) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).advanceControls
        (.inl
          ((.exceptional (.inr (.inr (.inr state))), oldOutputOne) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).OneControl),
         .inl
          ((.exceptional (.inr (.inr (.inr owner))), oldOutputTwo) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).TwoControl))
        ⟨inputOne, inputTwo, .right⟩ =
      (.inr (.inr tagged), .inr (.inr fork)) := by
  rw [FinitePairedPhysicalController.advanceControls_right]
  rw [profiledRawJointHybridMegaGuardedDelayedPhysicalController_noRecvOne,
    profiledRawJointHybridMegaGuardedDelayedPhysicalController_recvTwo,
    profiledRawJointHybridMegaGuardedDelayedNoRecvOne_leftSeam A strategy hwin
      controllers initialBank fallbackTag state oldOutputOne inputOne outputOne
        tagged htagged,
    profiledRawJointHybridMegaGuardedDelayedRecvTwo_leftSeam A strategy hwin
      controllers initialBank fallbackTag state owner oldOutputOne oldOutputTwo
        inputOne inputTwo outputTwo fork hfork]

set_option maxHeartbeats 1000000 in
/-- The simultaneous guarded-left seam installs the closed tag at process one
and the same locally forced fork at process two. -/
theorem profiledRawJointHybridMegaGuardedDelayed_leftSeam_advance_both
    (fallbackTag : RetainedTag A strategy hwin)
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂)
    (outputTwo : Out₂)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (hfork :
      profiledRawJointHybridMegaGuardedLeftPendingForkTwo? A strategy hwin
          controllers initialBank fallbackTag state owner inputOne inputTwo =
        some (outputTwo, fork)) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).advanceControls
        (.inl
          ((.exceptional (.inr (.inr (.inr state))), oldOutputOne) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).OneControl),
         .inl
          ((.exceptional (.inr (.inr (.inr owner))), oldOutputTwo) :
            (Mega A strategy hwin controllers initialBank
              fallbackTag).TwoControl))
        ⟨inputOne, inputTwo, .both⟩ =
      (.inr (.inr
        (profiledRawJointHybridMegaGuardedLeftPendingClosedTaggedOne A strategy
          hwin controllers initialBank fallbackTag state owner inputOne
            inputTwo).2),
       .inr (.inr fork)) := by
  rw [FinitePairedPhysicalController.advanceControls_both]
  rw [profiledRawJointHybridMegaGuardedDelayedPhysicalController_recvOne,
    profiledRawJointHybridMegaGuardedDelayedPhysicalController_recvTwo,
    profiledRawJointHybridMegaGuardedDelayedRecvOne_leftSeam,
    profiledRawJointHybridMegaGuardedDelayedRecvTwo_leftSeam A strategy hwin
      controllers initialBank fallbackTag state owner oldOutputOne oldOutputTwo
        inputOne inputTwo outputTwo fork hfork]

/-! ## Resolution at the next receive -/

/-- For a pending right seam, process one resolves its fork from process two's
delivered tag before applying the base receive transition. -/
@[simp] theorem profiledRawJointHybridMegaGuardedDelayedRecvOne_resolvesRight
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (tagged : ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledRawJointHybridMegaGuardedDelayedRecvOne A strategy hwin controllers
        initialBank fallbackTag (.inr (.inl fork)) inputOne
        (.inr (.inl tagged)) inputTwo =
      .inl ((Mega A strategy hwin controllers initialBank
        fallbackTag).recvOne (fork.resolve tagged) inputOne tagged.control
          inputTwo) := by
  rfl

/-- At the same pending right seam, process two retains its tagged branch and
uses the resolved process-one candidate in the base receive transition. -/
@[simp] theorem profiledRawJointHybridMegaGuardedDelayedRecvTwo_resolvesRight
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (tagged : ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledRawJointHybridMegaGuardedDelayedRecvTwo A strategy hwin controllers
        initialBank fallbackTag (.inr (.inl tagged)) inputTwo
        (.inr (.inl fork)) inputOne =
      .inr (.inl
        ⟨tagged.bit,
          (Mega A strategy hwin controllers initialBank fallbackTag).recvTwo
            tagged.control inputTwo (fork.resolve tagged) inputOne⟩) := by
  rfl

/-- Guarded-left mirror: process one retains its tagged branch and supplies
the resolved process-two candidate to the base receive transition. -/
@[simp] theorem profiledRawJointHybridMegaGuardedDelayedRecvOne_resolvesLeft
    (fallbackTag : RetainedTag A strategy hwin)
    (tagged : ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledRawJointHybridMegaGuardedDelayedRecvOne A strategy hwin controllers
        initialBank fallbackTag (.inr (.inr tagged)) inputOne
        (.inr (.inr fork)) inputTwo =
      .inr (.inr
        ⟨tagged.bit,
          (Mega A strategy hwin controllers initialBank fallbackTag).recvOne
            tagged.control inputOne (fork.resolve tagged) inputTwo⟩) := by
  rfl

/-- Guarded-left mirror: process two resolves its fork from process one's
delivered tag before applying the base receive transition. -/
@[simp] theorem profiledRawJointHybridMegaGuardedDelayedRecvTwo_resolvesLeft
    (fallbackTag : RetainedTag A strategy hwin)
    (tagged : ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledRawJointHybridMegaGuardedDelayedRecvTwo A strategy hwin controllers
        initialBank fallbackTag (.inr (.inr fork)) inputTwo
        (.inr (.inr tagged)) inputOne =
      .inl ((Mega A strategy hwin controllers initialBank
        fallbackTag).recvTwo (fork.resolve tagged) inputTwo tagged.control
          inputOne) := by
  rfl

/-! ## Pending strict rounds and acknowledgement -/

/-- While process one does not receive, both right-seam candidates advance
under the same local no-receive event. -/
@[simp] theorem profiledRawJointHybridMegaGuardedDelayedNoRecvOne_stepsRightFork
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) :
    profiledRawJointHybridMegaGuardedDelayedNoRecvOne A strategy hwin
        controllers initialBank fallbackTag (.inr (.inl fork)) inputOne =
      .inr (.inl
        ⟨(Mega A strategy hwin controllers initialBank
            fallbackTag).noRecvOne fork.openControl inputOne,
          (Mega A strategy hwin controllers initialBank
            fallbackTag).noRecvOne fork.closedControl inputOne⟩) := by
  rfl

/-- A right-seam tag is acknowledged when process two does not receive: in
this graph model process one necessarily receives on that round. -/
@[simp] theorem profiledRawJointHybridMegaGuardedDelayedNoRecvTwo_acksRightTag
    (fallbackTag : RetainedTag A strategy hwin)
    (tagged : ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputTwo : In₂) :
    profiledRawJointHybridMegaGuardedDelayedNoRecvTwo A strategy hwin
        controllers initialBank fallbackTag (.inr (.inl tagged)) inputTwo =
      .inl ((Mega A strategy hwin controllers initialBank
        fallbackTag).noRecvTwo tagged.control inputTwo) := by
  rfl

/-- Guarded-left mirror: the unresolved process-two fork advances through a
process-two no-receive. -/
@[simp] theorem profiledRawJointHybridMegaGuardedDelayedNoRecvTwo_stepsLeftFork
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputTwo : In₂) :
    profiledRawJointHybridMegaGuardedDelayedNoRecvTwo A strategy hwin
        controllers initialBank fallbackTag (.inr (.inr fork)) inputTwo =
      .inr (.inr
        ⟨(Mega A strategy hwin controllers initialBank
            fallbackTag).noRecvTwo fork.openControl inputTwo,
          (Mega A strategy hwin controllers initialBank
            fallbackTag).noRecvTwo fork.closedControl inputTwo⟩) := by
  rfl

/-- Guarded-left mirror: a process-one non-receive acknowledges delivery of
its tag to process two. -/
@[simp] theorem profiledRawJointHybridMegaGuardedDelayedNoRecvOne_acksLeftTag
    (fallbackTag : RetainedTag A strategy hwin)
    (tagged : ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) :
    profiledRawJointHybridMegaGuardedDelayedNoRecvOne A strategy hwin
        controllers initialBank fallbackTag (.inr (.inr tagged)) inputOne =
      .inl ((Mega A strategy hwin controllers initialBank
        fallbackTag).noRecvOne tagged.control inputOne) := by
  rfl

/-- Once process one has resolved a right fork, its delivered base control
acknowledges that fact to the still-tagged process two. -/
@[simp] theorem profiledRawJointHybridMegaGuardedDelayedRecvTwo_acksRightTag
    (fallbackTag : RetainedTag A strategy hwin)
    (baseOne : (Mega A strategy hwin controllers initialBank
      fallbackTag).OneControl)
    (tagged : ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledRawJointHybridMegaGuardedDelayedRecvTwo A strategy hwin controllers
        initialBank fallbackTag (.inr (.inl tagged)) inputTwo
        (.inl baseOne) inputOne =
      .inl ((Mega A strategy hwin controllers initialBank
        fallbackTag).recvTwo tagged.control inputTwo baseOne inputOne) := by
  rfl

/-- The other endpoint may receive during the right-tag acknowledgement
round; it already has a base control and simply uses the tagged base control. -/
@[simp] theorem profiledRawJointHybridMegaGuardedDelayedRecvOne_afterRightResolve
    (fallbackTag : RetainedTag A strategy hwin)
    (baseOne : (Mega A strategy hwin controllers initialBank
      fallbackTag).OneControl)
    (tagged : ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledRawJointHybridMegaGuardedDelayedRecvOne A strategy hwin controllers
        initialBank fallbackTag (.inl baseOne) inputOne
        (.inr (.inl tagged)) inputTwo =
      .inl ((Mega A strategy hwin controllers initialBank
        fallbackTag).recvOne baseOne inputOne tagged.control inputTwo) := by
  rfl

/-- Guarded-left acknowledgement when process one receives a delivered base
control after process two has resolved its fork. -/
@[simp] theorem profiledRawJointHybridMegaGuardedDelayedRecvOne_acksLeftTag
    (fallbackTag : RetainedTag A strategy hwin)
    (tagged : ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (baseTwo : (Mega A strategy hwin controllers initialBank
      fallbackTag).TwoControl)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledRawJointHybridMegaGuardedDelayedRecvOne A strategy hwin controllers
        initialBank fallbackTag (.inr (.inr tagged)) inputOne
        (.inl baseTwo) inputTwo =
      .inl ((Mega A strategy hwin controllers initialBank
        fallbackTag).recvOne tagged.control inputOne baseTwo inputTwo) := by
  rfl

/-- The resolved process-two endpoint uses the tagged process-one base control
while the latter awaits acknowledgement. -/
@[simp] theorem profiledRawJointHybridMegaGuardedDelayedRecvTwo_afterLeftResolve
    (fallbackTag : RetainedTag A strategy hwin)
    (tagged : ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (baseTwo : (Mega A strategy hwin controllers initialBank
      fallbackTag).TwoControl)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledRawJointHybridMegaGuardedDelayedRecvTwo A strategy hwin controllers
        initialBank fallbackTag (.inl baseTwo) inputTwo
        (.inr (.inr tagged)) inputOne =
      .inl ((Mega A strategy hwin controllers initialBank
        fallbackTag).recvTwo baseTwo inputTwo tagged.control inputOne) := by
  rfl

/-! ## Exact pending-pair graph table -/

set_option maxHeartbeats 1000000 in
/-- A strict-right round is the only round that can keep a right-seam fork
unresolved: process one advances both candidates and process two advances its
actual branch while retaining the tag. -/
theorem profiledRawJointHybridMegaGuardedDelayed_rightPending_advance_right
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (tagged : ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).advanceControls
        (.inr (.inl fork), .inr (.inl tagged))
        ⟨inputOne, inputTwo, .right⟩ =
      (.inr (.inl
        ⟨(Mega A strategy hwin controllers initialBank
            fallbackTag).noRecvOne fork.openControl inputOne,
          (Mega A strategy hwin controllers initialBank
            fallbackTag).noRecvOne fork.closedControl inputOne⟩),
       .inr (.inl
        ⟨tagged.bit,
          (Mega A strategy hwin controllers initialBank fallbackTag).recvTwo
            tagged.control inputTwo (fork.resolve tagged) inputOne⟩)) := by
  rw [FinitePairedPhysicalController.advanceControls_right]
  rfl

set_option maxHeartbeats 1000000 in
/-- Under the explicit coherence obligation, the output emitted by the
unresolved endpoint on a strict-right round is the output of the actual branch
selected by process two's retained tag. -/
theorem
    profiledRawJointHybridMegaGuardedDelayed_rightPending_outputOne_eq_resolved
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (tagged : ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) (inputTwo : In₂)
    (hcoherent :
      ProfiledRawJointHybridMegaGuardedRightPendingNoRecvOutputCoherent A
        strategy hwin controllers initialBank fallbackTag fork inputOne) :
    let delayed :=
      profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy
        hwin controllers initialBank fallbackTag
    let base := Mega A strategy hwin controllers initialBank fallbackTag
    delayed.outputOne
        (delayed.advanceControls (.inr (.inl fork), .inr (.inl tagged))
          ⟨inputOne, inputTwo, .right⟩).1 =
      base.outputOne (base.noRecvOne (fork.resolve tagged) inputOne) := by
  dsimp only
  rw [profiledRawJointHybridMegaGuardedDelayed_rightPending_advance_right]
  rw [profiledRawJointHybridMegaGuardedDelayed_outputOne_rightPending]
  rcases tagged with ⟨bit, control⟩
  cases bit
  · rfl
  · exact hcoherent

set_option maxHeartbeats 1000000 in
/-- A strict-left round delivers the right-seam tag to the fork endpoint;
both endpoints leave the pending layer in that round. -/
theorem profiledRawJointHybridMegaGuardedDelayed_rightPending_advance_left
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (tagged : ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).advanceControls
        (.inr (.inl fork), .inr (.inl tagged))
        ⟨inputOne, inputTwo, .left⟩ =
      (.inl ((Mega A strategy hwin controllers initialBank
          fallbackTag).recvOne (fork.resolve tagged) inputOne tagged.control
            inputTwo),
       .inl ((Mega A strategy hwin controllers initialBank
          fallbackTag).noRecvTwo tagged.control inputTwo)) := by
  rw [FinitePairedPhysicalController.advanceControls_left]
  rfl

set_option maxHeartbeats 1000000 in
/-- On `.both`, process one resolves a right-seam fork.  Process two must keep
the advanced tag because its local receive cannot tell `.both` from
strict-right; the delivered base control acknowledges it later. -/
theorem profiledRawJointHybridMegaGuardedDelayed_rightPending_advance_both
    (fallbackTag : RetainedTag A strategy hwin)
    (fork : ProfiledRawJointHybridMegaGuardedRightPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (tagged : ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).advanceControls
        (.inr (.inl fork), .inr (.inl tagged))
        ⟨inputOne, inputTwo, .both⟩ =
      (.inl ((Mega A strategy hwin controllers initialBank
          fallbackTag).recvOne (fork.resolve tagged) inputOne tagged.control
            inputTwo),
       .inr (.inl
        ⟨tagged.bit,
          (Mega A strategy hwin controllers initialBank fallbackTag).recvTwo
            tagged.control inputTwo (fork.resolve tagged) inputOne⟩)) := by
  rw [FinitePairedPhysicalController.advanceControls_both]
  rfl

set_option maxHeartbeats 1000000 in
/-- Guarded-left mirror: only strict-left can keep the process-two fork
unresolved. -/
theorem profiledRawJointHybridMegaGuardedDelayed_leftPending_advance_left
    (fallbackTag : RetainedTag A strategy hwin)
    (tagged : ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).advanceControls
        (.inr (.inr tagged), .inr (.inr fork))
        ⟨inputOne, inputTwo, .left⟩ =
      (.inr (.inr
        ⟨tagged.bit,
          (Mega A strategy hwin controllers initialBank fallbackTag).recvOne
            tagged.control inputOne (fork.resolve tagged) inputTwo⟩),
       .inr (.inr
        ⟨(Mega A strategy hwin controllers initialBank
            fallbackTag).noRecvTwo fork.openControl inputTwo,
          (Mega A strategy hwin controllers initialBank
            fallbackTag).noRecvTwo fork.closedControl inputTwo⟩)) := by
  rw [FinitePairedPhysicalController.advanceControls_left]
  rfl

set_option maxHeartbeats 1000000 in
/-- Guarded-left mirror: coherent blind outputs make the emitted process-two
output equal to the branch named by process one's tag. -/
theorem
    profiledRawJointHybridMegaGuardedDelayed_leftPending_outputTwo_eq_resolved
    (fallbackTag : RetainedTag A strategy hwin)
    (tagged : ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) (inputTwo : In₂)
    (hcoherent :
      ProfiledRawJointHybridMegaGuardedLeftPendingNoRecvOutputCoherent A
        strategy hwin controllers initialBank fallbackTag fork inputTwo) :
    let delayed :=
      profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy
        hwin controllers initialBank fallbackTag
    let base := Mega A strategy hwin controllers initialBank fallbackTag
    delayed.outputTwo
        (delayed.advanceControls (.inr (.inr tagged), .inr (.inr fork))
          ⟨inputOne, inputTwo, .left⟩).2 =
      base.outputTwo (base.noRecvTwo (fork.resolve tagged) inputTwo) := by
  dsimp only
  rw [profiledRawJointHybridMegaGuardedDelayed_leftPending_advance_left]
  rw [profiledRawJointHybridMegaGuardedDelayed_outputTwo_leftPending]
  rcases tagged with ⟨bit, control⟩
  cases bit
  · rfl
  · exact hcoherent

set_option maxHeartbeats 1000000 in
/-- A strict-right round resolves and acknowledges a guarded-left pending
pair immediately. -/
theorem profiledRawJointHybridMegaGuardedDelayed_leftPending_advance_right
    (fallbackTag : RetainedTag A strategy hwin)
    (tagged : ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).advanceControls
        (.inr (.inr tagged), .inr (.inr fork))
        ⟨inputOne, inputTwo, .right⟩ =
      (.inl ((Mega A strategy hwin controllers initialBank
          fallbackTag).noRecvOne tagged.control inputOne),
       .inl ((Mega A strategy hwin controllers initialBank
          fallbackTag).recvTwo (fork.resolve tagged) inputTwo tagged.control
            inputOne)) := by
  rw [FinitePairedPhysicalController.advanceControls_right]
  rfl

set_option maxHeartbeats 1000000 in
/-- On a simultaneous round, process two resolves the guarded-left fork and
process one retains the advanced tag until acknowledgement. -/
theorem profiledRawJointHybridMegaGuardedDelayed_leftPending_advance_both
    (fallbackTag : RetainedTag A strategy hwin)
    (tagged : ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (fork : ProfiledRawJointHybridMegaGuardedLeftPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy hwin
      controllers initialBank fallbackTag).advanceControls
        (.inr (.inr tagged), .inr (.inr fork))
        ⟨inputOne, inputTwo, .both⟩ =
      (.inr (.inr
        ⟨tagged.bit,
          (Mega A strategy hwin controllers initialBank fallbackTag).recvOne
            tagged.control inputOne (fork.resolve tagged) inputTwo⟩),
       .inl ((Mega A strategy hwin controllers initialBank
          fallbackTag).recvTwo (fork.resolve tagged) inputTwo tagged.control
            inputOne)) := by
  rw [FinitePairedPhysicalController.advanceControls_both]
  rfl

set_option maxHeartbeats 1000000 in
/-- Once a right-seam fork has resolved, the remaining process-two tag is an
acknowledgement wrapper.  On the next round its erasure takes exactly the base
transition.  The delayed state itself may simultaneously enter a new,
oppositely oriented seam. -/
theorem profiledRawJointHybridMegaGuardedDelayed_rightTag_acknowledges
    (fallbackTag : RetainedTag A strategy hwin)
    (key : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (receiver : ProfiledRawJointHybridMegaLeftReceiver A strategy hwin
      initialBank key)
    (outputOne : Out₁)
    (tagged : ProfiledRawJointHybridMegaGuardedRightPendingTwo A strategy hwin
      controllers initialBank fallbackTag)
    (round : EnvironmentRound In₁ In₂) :
    let baseOne : (Mega A strategy hwin controllers initialBank
      fallbackTag).OneControl := (.leftReceiver key receiver, outputOne)
    let delayedNext :=
      (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy
        hwin controllers initialBank fallbackTag).advanceControls
          (.inl baseOne, .inr (.inl tagged)) round
    let baseNext := (Mega A strategy hwin controllers initialBank
      fallbackTag).advanceControls (baseOne, tagged.control) round
    (profiledRawJointHybridMegaGuardedDelayedBaseOne A strategy hwin
        controllers initialBank fallbackTag delayedNext.1,
      profiledRawJointHybridMegaGuardedDelayedBaseTwo A strategy hwin
        controllers initialBank fallbackTag delayedNext.2) = baseNext := by
  rcases round with ⟨inputOne, inputTwo, graph⟩
  cases graph <;> rfl

set_option maxHeartbeats 1000000 in
/-- Guarded-left mirror: after process two resolves its fork, the remaining
process-one tag erases through the next exact base transition. -/
theorem profiledRawJointHybridMegaGuardedDelayed_leftTag_acknowledges
    (fallbackTag : RetainedTag A strategy hwin)
    (tagged : ProfiledRawJointHybridMegaGuardedLeftPendingOne A strategy hwin
      controllers initialBank fallbackTag)
    (key : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (receiver : ProfiledRawJointHybridMegaRightReceiver A strategy hwin
      initialBank key)
    (outputTwo : Out₂)
    (round : EnvironmentRound In₁ In₂) :
    let baseTwo : (Mega A strategy hwin controllers initialBank
      fallbackTag).TwoControl := (.rightReceiver key receiver, outputTwo)
    let delayedNext :=
      (profiledRawJointHybridMegaGuardedDelayedPhysicalController A strategy
        hwin controllers initialBank fallbackTag).advanceControls
          (.inr (.inr tagged), .inl baseTwo) round
    let baseNext := (Mega A strategy hwin controllers initialBank
      fallbackTag).advanceControls (tagged.control, baseTwo) round
    (profiledRawJointHybridMegaGuardedDelayedBaseOne A strategy hwin
        controllers initialBank fallbackTag delayedNext.1,
      profiledRawJointHybridMegaGuardedDelayedBaseTwo A strategy hwin
        controllers initialBank fallbackTag delayedNext.2) = baseNext := by
  rcases round with ⟨inputOne, inputTwo, graph⟩
  cases graph <;> rfl

end

end DetParityAutomaton

end DistributedSynthesis
