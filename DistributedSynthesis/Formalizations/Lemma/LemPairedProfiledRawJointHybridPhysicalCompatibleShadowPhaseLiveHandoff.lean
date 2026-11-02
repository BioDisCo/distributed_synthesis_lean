/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleRootPinnedPolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridLeaderFreeShadowCarrier

/-!
# Delayed phase-live selection at a leader-free strict shadow

At the first strict round the non-receiving endpoint does not know the
partner input and therefore cannot select a compatible successor target.  The
receiving endpoint does know the complete input pair, but it cannot tell the
blind endpoint which target was selected until a later receive.

This file records the positive, locality-correct seam.  A finite tag names
the common-control root, the complete input pair stored by the shadow, and
the strict orientation.  For every common control a physical-compatible
root-pinned package is selected once, before any environment.  The tag then
names a literal guarded child and its ordinary accepting tail without making
a new choice under the environment quantifier.

The executable shadow/owner receive is extended by this tag.  Its output and
old guarded receiver are definitionally unchanged.  A later receive may copy
the delivered tag to the formerly blind owner; if no such receive occurs,
the play is an eventually one-way tail and is handled by the separate fixed-
tail theorem.  No local map in this file receives a graph, hierarchy side,
leader bit, strict-leader bit, history, or semantic view.
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

private abbrev CommonControl :=
  ProfiledRawJointHybridCommonControl A strategy hwin

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointHybridCode A)
    (Annotation := PhysicalAnnotation A)

private abbrev LinkedMove :=
  SourceFreeBeliefParentLinkedMove
    (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
    (Move := ProfiledRawJointHybridMove A)
    (Annotation := PhysicalAnnotation A)

/-! ## One finite package bank, selected before the environment -/

/-- The literal common move installed at one finite leader-free common
control. -/
noncomputable def
    profiledRawJointHybridShadowPhaseLiveInstalled
    (control : CommonControl A strategy hwin) :
    ProfiledRawJointHybridCommonMoveData A strategy :=
  ProfiledRawJointHybridCommonInstalledMove.toCommonMoveData A
    (profiledRawJointHybridCommonControlInstalled A strategy hwin control)

private abbrev RootPackage
    (control : CommonControl A strategy hwin) :=
  ProfiledRawJointHybridPhysicalCompatibleRootPinnedPolicy A strategy hwin
    (profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin control
      ).world
    (profiledRawJointHybridPhysicalCompatibleInstalledRootPred A strategy
      (profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin control))

/-- The complete package bank is one function of the finite common-control
type.  Looking up an entry later is not a new rational-policy choice. -/
noncomputable def
    profiledRawJointHybridShadowPhaseLiveRootPackageBank
    (control : CommonControl A strategy hwin) :
    RootPackage A strategy hwin control :=
  profiledRawJointHybridPhysicalCompatibleInstalledRootPinnedPolicy A strategy
    hwin (profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin
      control)

/-- The package at every bank entry pins exactly the raw move already used by
the leader-free common/shadow front. -/
theorem
    profiledRawJointHybridShadowPhaseLiveRootPackageBank_move
    (control : CommonControl A strategy hwin) :
    (profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
      control).rootMove.1 =
      some (profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin
        control).rawMove := by
  exact
    profiledRawJointHybridPhysicalCompatibleInstalledRootPinnedPolicy_move A
      strategy hwin
        (profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin
          control)

/-! ## Finite delayed-selection tags -/

/-- Which literal strict child is named by a delayed handoff tag.  This is a
stored finite tag, not an observation available at the first blind step. -/
inductive ProfiledRawJointHybridShadowStrictSide where
  | right
  | left
deriving DecidableEq, Fintype

/-- All information that the informed shadow can stage and later deliver to
the formerly blind owner. -/
structure ProfiledRawJointHybridShadowPhaseLiveTag where
  origin : CommonControl A strategy hwin
  input : In₁ × In₂
  side : ProfiledRawJointHybridShadowStrictSide
deriving Fintype

/-- Canonical strict-right tag staged by process two's informed shadow. -/
def profiledRawJointHybridShadowPhaseLiveRightTag
    (origin : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin :=
  { origin := origin, input := input, side := .right }

/-- Strict-left mirror staged by process one. -/
def profiledRawJointHybridShadowPhaseLiveLeftTag
    (origin : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin :=
  { origin := origin, input := input, side := .left }

/-- The raw strict direction denoted by a delayed tag. -/
def ProfiledRawJointHybridShadowPhaseLiveTag.direction
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin) :
    HybridDirection (In₁ := In₁) (In₂ := In₂) :=
  match tag.side with
  | .right => .strict (profiledRawJointCommonOneRoundStrictRight tag.input)
  | .left => .strict (profiledRawJointCommonOneRoundStrictLeft tag.input)

/-- The parent-linked initial code of the package selected at the tag's
finite common-control index. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.initialCode
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin) :
    LinkedCode A :=
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
  ((.common ((profiledRawJointCommonWorldFamily A installed.world
      ).incidenceCode A)),
    profiledRawJointHybridInitialPhysicalAnnotation A)

/-- The exact literal child code named by the tag in its already selected
root-pinned package. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.childCode
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin) :
    LinkedCode A :=
  let package :=
    profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
      tag.origin
  sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)
    (tag.initialCode A strategy hwin) package.rootMove
    (tag.direction (A := A))

/-- Root legality contains the exact guarded successor at every tagged
literal child.  The finite-code representative disappears by the standard
`sourceFreeBeliefFiniteCodeNext_of_direction` equation. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.rootSuccessor
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin) :
    let installed :=
      profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    let package :=
      profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
        tag.origin
    let initialCode := tag.initialCode A strategy hwin
    let D := sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := PhysicalAnnotation A)
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A installed.world
          ).incidenceCode A)))
    let childCode := tag.childCode A strategy hwin
    package.policy.successor
        (true,
          (sourceFreeBeliefCodeParityRunAutomaton D initialCode
            (sourceFreeBeliefParentLinkedValid
              (ProfiledRawJointHybridProvenanceValid A strategy)
              (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A
                strategy hwin))
            (sourceFreeBeliefFiniteCodeNext
              (sourceFreeBeliefParentLinkedNext
                (profiledRawJointHybridNext A)))).initial)
        childCode =
      (false, (childCode, D.step D.initial childCode)) := by
  dsimp only
  let package :=
    profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
      tag.origin
  let initialCode := tag.initialCode A strategy hwin
  let childCode := tag.childCode A strategy hwin
  have hfinite :
      sourceFreeBeliefFiniteCodeNext
          (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
          initialCode package.rootMove childCode = childCode := by
    dsimp only [childCode, ProfiledRawJointHybridShadowPhaseLiveTag.childCode]
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
      initialCode package.rootMove (tag.direction (A := A))
  have hsuccessor := package.rootMove_realizes.2.2 childCode
  dsimp only [initialCode,
    ProfiledRawJointHybridShadowPhaseLiveTag.initialCode] at hfinite
  rw [hfinite] at hsuccessor
  exact hsuccessor

/-- The policy run at the tagged child is the exact false-bit state exposed
by `rootSuccessor`. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.childRun
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin) :
    let installed :=
      profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    let package :=
      profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
        tag.origin
    let D := sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := PhysicalAnnotation A)
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A installed.world
          ).incidenceCode A)))
    let childCode := tag.childCode A strategy hwin
    package.policy.run [childCode] =
      (false, (childCode, D.step D.initial childCode)) := by
  dsimp only
  let package :=
    profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
      tag.origin
  let childCode := tag.childCode A strategy hwin
  have hrun := package.policy.successor_at ([] : TreeNode (LinkedCode A))
    childCode
  rw [package.policy.accepts.1.1] at hrun
  exact hrun.symm.trans (tag.rootSuccessor A strategy hwin)

/-- The ordinary accepting tail named by the finite tag.  This is a
projection of the already selected bank package; there is no `choice` in this
definition. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.tailCodePolicy
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin) :=
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
  let package :=
    profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
      tag.origin
  let initialCode := tag.initialCode A strategy hwin
  let D := sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := PhysicalAnnotation A)
    (profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A installed.world
        ).incidenceCode A)))
  package.tailCodePolicy D initialCode
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy
        hwin))
    (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
    (tag.childCode A strategy hwin)

/-- State type of the re-rooted ordinary policy selected by `tag`. -/
noncomputable abbrev
    ProfiledRawJointHybridShadowPhaseLiveTailState
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin) :=
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
  let package :=
    profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
      tag.origin
  let D := sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := PhysicalAnnotation A)
    (profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A installed.world
        ).incidenceCode A)))
  let childCode := tag.childCode A strategy hwin
  (sourceFreeBeliefCodeParityRunAutomaton
    (D.withInitial (package.policy.run [childCode]).2.2)
    (package.policy.run [childCode]).2.1
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy
        hwin))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext
        (profiledRawJointHybridNext A)))).State

/-- Allowed edges of a tagged tail are literal image edges of its one
root-pinned package. -/
def ProfiledRawJointHybridShadowPhaseLiveTag.TailAllowedTarget
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin)
    (source target :
      ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag) :
    Prop :=
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
  let package :=
    profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
      tag.origin
  let initialCode := tag.initialCode A strategy hwin
  let D := sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := PhysicalAnnotation A)
    (profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A installed.world
        ).incidenceCode A)))
  package.TailAllowedTarget D initialCode
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy
        hwin))
    (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
    (tag.childCode A strategy hwin) source target

/-- Every infinite tagged tail path is accepted from the exact code-DPA
control stored at the guarded child. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.acceptsFrom_of_tailAllowedPath
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin)
    (states : Nat →
      ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag)
    (hzero : states 0 =
      (tag.tailCodePolicy A strategy hwin).run [])
    (hstep : ∀ n,
      tag.TailAllowedTarget A strategy hwin (states n) (states (n + 1))) :
    let installed :=
      profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    let package :=
      profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
        tag.origin
    let childCode := tag.childCode A strategy hwin
    let bareDPA := profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A installed.world
        ).incidenceCode A))
    bareDPA.AcceptsFrom (package.policy.run [childCode]).2.2
      (fun n ↦ (states (n + 1)).1.1) := by
  dsimp only
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
  let package :=
    profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
      tag.origin
  let initialCode := tag.initialCode A strategy hwin
  let bareDPA := profiledRawJointHybridCodeParityDPA A
    (.common ((profiledRawJointCommonWorldFamily A installed.world
      ).incidenceCode A))
  let D := sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := PhysicalAnnotation A) bareDPA
  let childCode := tag.childCode A strategy hwin
  have hlinked := package.acceptsFrom_of_tailAllowedTarget_path D initialCode
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy
        hwin))
    (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
    childCode states hzero hstep
  change (bareDPA.comap Prod.fst).AcceptsFrom
      (package.policy.run [childCode]).2.2
      (fun n ↦ (states (n + 1)).1) at hlinked
  rw [DetParityAutomaton.comap_acceptsFrom_iff] at hlinked
  simpa [OmegaWord.map] using hlinked

/-- The objective control stored at the tagged child is exactly the bare
hybrid-code DPA step on its public component.  The carried physical annotation
does not reset or otherwise modify the parity automaton. -/
theorem ProfiledRawJointHybridShadowPhaseLiveTag.childControl
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin) :
    let installed :=
      profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    let package :=
      profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
        tag.origin
    let childCode := tag.childCode A strategy hwin
    let bareDPA := profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A installed.world
        ).incidenceCode A))
    (package.policy.run [childCode]).2.2 =
      bareDPA.step bareDPA.initial childCode.1 := by
  dsimp only
  have hrun := congrArg (fun state ↦ state.2.2)
    (tag.childRun A strategy hwin)
  exact hrun

/-- The public code of the tagged right child is exactly the one-sided child
of the move installed by the leader-free front. -/
theorem profiledRawJointHybridShadowPhaseLiveRightTag_childCode_fst
    (origin : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ((profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin
      input).childCode A strategy hwin).1 =
      .oneSided (profiledRawJointOneSidedNext A
        (profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin origin
          ).incidenceCode
        (profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin origin
          ).rawMove
        (profiledRawJointCommonOneRoundStrictRight input)) := by
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin origin
  change
    profiledRawJointHybridNext A
        (.common
          ((profiledRawJointCommonWorldFamily A installed.world
            ).incidenceCode A))
        (profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
          origin).rootMove.1
        (.strict (profiledRawJointCommonOneRoundStrictRight input)) =
      .oneSided (profiledRawJointOneSidedNext A installed.incidenceCode
        installed.rawMove (profiledRawJointCommonOneRoundStrictRight input))
  rw [profiledRawJointHybridShadowPhaseLiveRootPackageBank_move A strategy
    hwin origin, installed.incidence_eq]
  rfl

/-- Left mirror. -/
theorem profiledRawJointHybridShadowPhaseLiveLeftTag_childCode_fst
    (origin : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ((profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin
      input).childCode A strategy hwin).1 =
      .oneSided (profiledRawJointOneSidedNext A
        (profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin origin
          ).incidenceCode
        (profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin origin
          ).rawMove
        (profiledRawJointCommonOneRoundStrictLeft input)) := by
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin origin
  change
    profiledRawJointHybridNext A
        (.common
          ((profiledRawJointCommonWorldFamily A installed.world
            ).incidenceCode A))
        (profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
          origin).rootMove.1
        (.strict (profiledRawJointCommonOneRoundStrictLeft input)) =
      .oneSided (profiledRawJointOneSidedNext A installed.incidenceCode
        installed.rawMove (profiledRawJointCommonOneRoundStrictLeft input))
  rw [profiledRawJointHybridShadowPhaseLiveRootPackageBank_move A strategy
    hwin origin, installed.incidence_eq]
  rfl

/-! ## The locality-correct shadow extension -/

/-- Process one's receiver state after it learns that the stored ambiguity
was a strict-left block.  The old strict receiver is retained verbatim and
the informed endpoint stages the finite tail tag. -/
structure ProfiledRawJointHybridLeftShadowPhaseLiveHandoff where
  receiver : ProfiledRawJointHybridLeftStrictReceiver A strategy hwin
  tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin
deriving Fintype

/-- Process-two strict-right mirror. -/
structure ProfiledRawJointHybridRightShadowPhaseLiveHandoff where
  receiver : ProfiledRawJointHybridRightStrictReceiver A strategy hwin
  tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin
deriving Fintype

/-- Extend the existing process-one shadow/left-owner receive.  This endpoint
has the full first-block pair in `shadow.input`, so it can stage the left
tail. -/
noncomputable def
    profiledRawJointHybridOneShadowRecvLeftOwnerPhaseLive
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ × ProfiledRawJointHybridLeftShadowPhaseLiveHandoff A strategy
      hwin :=
  let next := profiledRawJointHybridOneShadowRecvLeftOwner A strategy hwin
    shadow owner ownInput deliveredInput
  let tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin shadow.origin
      shadow.input
  (next.1, ⟨next.2, tag⟩)

/-- Process-two strict-right mirror. -/
noncomputable def
    profiledRawJointHybridTwoShadowRecvRightOwnerPhaseLive
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ × ProfiledRawJointHybridRightShadowPhaseLiveHandoff A strategy
      hwin :=
  let next := profiledRawJointHybridTwoShadowRecvRightOwner A strategy hwin
    shadow owner ownInput deliveredInput
  let tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin shadow.origin
      shadow.input
  (next.1, ⟨next.2, tag⟩)

@[simp] theorem
    profiledRawJointHybridOneShadowRecvLeftOwnerPhaseLive_output
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    (profiledRawJointHybridOneShadowRecvLeftOwnerPhaseLive A strategy hwin
      shadow owner ownInput deliveredInput).1 =
      (profiledRawJointHybridOneShadowRecvLeftOwner A strategy hwin shadow
        owner ownInput deliveredInput).1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridTwoShadowRecvRightOwnerPhaseLive_output
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    (profiledRawJointHybridTwoShadowRecvRightOwnerPhaseLive A strategy hwin
      shadow owner ownInput deliveredInput).1 =
      (profiledRawJointHybridTwoShadowRecvRightOwner A strategy hwin shadow
        owner ownInput deliveredInput).1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridOneShadowRecvLeftOwnerPhaseLive_receiver
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    (profiledRawJointHybridOneShadowRecvLeftOwnerPhaseLive A strategy hwin
      shadow owner ownInput deliveredInput).2.receiver =
      (profiledRawJointHybridOneShadowRecvLeftOwner A strategy hwin shadow
        owner ownInput deliveredInput).2 :=
  rfl

@[simp] theorem
    profiledRawJointHybridTwoShadowRecvRightOwnerPhaseLive_receiver
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    (profiledRawJointHybridTwoShadowRecvRightOwnerPhaseLive A strategy hwin
      shadow owner ownInput deliveredInput).2.receiver =
      (profiledRawJointHybridTwoShadowRecvRightOwner A strategy hwin shadow
        owner ownInput deliveredInput).2 :=
  rfl

@[simp] theorem
    profiledRawJointHybridOneShadowRecvLeftOwnerPhaseLive_tag
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    (profiledRawJointHybridOneShadowRecvLeftOwnerPhaseLive A strategy hwin
      shadow owner ownInput deliveredInput).2.tag =
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin shadow.origin
        shadow.input :=
  rfl

@[simp] theorem
    profiledRawJointHybridTwoShadowRecvRightOwnerPhaseLive_tag
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    (profiledRawJointHybridTwoShadowRecvRightOwnerPhaseLive A strategy hwin
      shadow owner ownInput deliveredInput).2.tag =
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin
        shadow.origin shadow.input :=
  rfl

/-- On the later receive, the formerly blind process can install the exact
finite tag carried by its partner.  The function has no access to a graph or
side; it merely copies delivered finite state. -/
def profiledRawJointHybridInstallDeliveredLeftShadowPhaseLiveTag
    (delivered :
      ProfiledRawJointHybridLeftShadowPhaseLiveHandoff A strategy hwin) :
    ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin :=
  delivered.tag

/-- Right mirror. -/
def profiledRawJointHybridInstallDeliveredRightShadowPhaseLiveTag
    (delivered :
      ProfiledRawJointHybridRightShadowPhaseLiveHandoff A strategy hwin) :
    ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin :=
  delivered.tag

end

end DetParityAutomaton

end DistributedSynthesis
