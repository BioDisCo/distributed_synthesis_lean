/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTrackedBootstrap
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOperationalCloseCuts

/-!
# Proof-side schedule of the one-lane tagged-tail bootstrap

A strict-right shadow creates a right tag, but the live child lane of that tag
is consumed when the tag is delivered in the opposite strict-left direction.
The left-tag case is symmetric.  This file fixes that convention explicitly
and relates it to the canonical operational-close clock.

The result is deliberately a scheduling fact, not an executable dispatcher.
No local transition receives the graph, tag side, orientation, hierarchy, or
leader bit.

There is one important index boundary.  If block `k` starts in the tag's
creation direction, then `cuts (k + 1)` is the first changed graph.  When this
new graph is strict, it is exactly the tag's bootstrap direction.  Therefore
an outer activation may consume the round at `cuts (k + 1)` with the one-lane
bootstrap.  Merely installing the fibre *after* that round does not constrain
the following round `cuts (k + 1) + 1`; that placement remains an outer trace
invariant.
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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

namespace ProfiledRawJointHybridShadowStrictSide

/-- Strict graph on which a tag's guarded child was created. -/
def creationGraph : ProfiledRawJointHybridShadowStrictSide → Graph
  | .right => .right
  | .left => .left

/-- Opposite strict graph on which the tag can be delivered to the formerly
blind endpoint and its single live child lane can be bootstrapped. -/
def bootstrapGraph : ProfiledRawJointHybridShadowStrictSide → Graph
  | .right => .left
  | .left => .right

@[simp] theorem creationGraph_right : creationGraph .right = .right := rfl

@[simp] theorem creationGraph_left : creationGraph .left = .left := rfl

@[simp] theorem bootstrapGraph_right : bootstrapGraph .right = .left := rfl

@[simp] theorem bootstrapGraph_left : bootstrapGraph .left = .right := rfl

theorem creationGraph_ne_both
    (side : ProfiledRawJointHybridShadowStrictSide) :
    side.creationGraph ≠ .both := by
  cases side <;> simp [creationGraph]

theorem bootstrapGraph_ne_both
    (side : ProfiledRawJointHybridShadowStrictSide) :
    side.bootstrapGraph ≠ .both := by
  cases side <;> simp [bootstrapGraph]

theorem bootstrapGraph_ne_creationGraph
    (side : ProfiledRawJointHybridShadowStrictSide) :
    side.bootstrapGraph ≠ side.creationGraph := by
  cases side <;> simp [creationGraph, bootstrapGraph]

end ProfiledRawJointHybridShadowStrictSide

namespace ProfiledRawJointHybridShadowPhaseLiveTag

/-- Physical graph of the literal strict child named by a tag. -/
def creationGraph (tag : Tag A strategy hwin) : Graph :=
  tag.side.creationGraph

/-- Opposite strict delivery graph that matches the tag's one-live-lane
bootstrap. -/
def bootstrapGraph (tag : Tag A strategy hwin) : Graph :=
  tag.side.bootstrapGraph

section
omit [DecidableEq In₁] [DecidableEq In₂]

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem rightTag_creationGraph
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
      ).creationGraph A strategy hwin = .right :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem rightTag_bootstrapGraph
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
      ).bootstrapGraph A strategy hwin = .left :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem leftTag_creationGraph
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
      ).creationGraph A strategy hwin = .left :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem leftTag_bootstrapGraph
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
      ).bootstrapGraph A strategy hwin = .right :=
  rfl

end

/-- The canonical process-one handoff creates a left tag, whose later strict
delivery/bootstrap direction is right. -/
@[simp] theorem oneShadowRecvLeftOwnerPhaseLive_bootstrapGraph
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    ((profiledRawJointHybridOneShadowRecvLeftOwnerPhaseLive A strategy hwin
      shadow owner ownInput deliveredInput).2.tag).bootstrapGraph A strategy
        hwin = .right :=
  rfl

/-- The canonical process-two handoff creates a right tag, whose later strict
delivery/bootstrap direction is left. -/
@[simp] theorem twoShadowRecvRightOwnerPhaseLive_bootstrapGraph
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    ((profiledRawJointHybridTwoShadowRecvRightOwnerPhaseLive A strategy hwin
      shadow owner ownInput deliveredInput).2.tag).bootstrapGraph A strategy
        hwin = .left :=
  rfl

end ProfiledRawJointHybridShadowPhaseLiveTag

/-! ## Operational cuts expose exactly the bootstrap delivery round -/

namespace OperationalCloseCutPackage

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At a strict tag-side block, the first changed cut is the tag's opposite
bootstrap graph whenever that new cut is itself strict. -/
theorem next_eq_tag_bootstrapGraph_of_strict
    {graphs : Nat → Graph} (cutPackage : OperationalCloseCutPackage graphs)
    (tag : Tag A strategy hwin) (k : Nat)
    (hcreation : graphs (cutPackage.cuts k) =
      tag.creationGraph A strategy hwin)
    (hnextStrict : graphs (cutPackage.cuts (k + 1)) ≠ .both) :
    graphs (cutPackage.cuts (k + 1)) =
      tag.bootstrapGraph A strategy hwin := by
  have hcurrentStrict : graphs (cutPackage.cuts k) ≠ .both := by
    rw [hcreation]
    exact tag.side.creationGraph_ne_both
  have hchanged := cutPackage.maximal_of_strict k hcurrentStrict
  cases hside : tag.side with
  | right =>
      have hcurrent : graphs (cutPackage.cuts k) = .right := by
        simpa [ProfiledRawJointHybridShadowPhaseLiveTag.creationGraph,
          ProfiledRawJointHybridShadowStrictSide.creationGraph, hside] using
            hcreation
      cases hnext : graphs (cutPackage.cuts (k + 1)) with
      | right =>
          exact False.elim (hchanged (hnext.trans hcurrent.symm))
      | left =>
          simpa [ProfiledRawJointHybridShadowPhaseLiveTag.bootstrapGraph,
            ProfiledRawJointHybridShadowStrictSide.bootstrapGraph, hside] using
              hnext
      | both =>
          exact False.elim (hnextStrict hnext)
  | left =>
      have hcurrent : graphs (cutPackage.cuts k) = .left := by
        simpa [ProfiledRawJointHybridShadowPhaseLiveTag.creationGraph,
          ProfiledRawJointHybridShadowStrictSide.creationGraph, hside] using
            hcreation
      cases hnext : graphs (cutPackage.cuts (k + 1)) with
      | right =>
          simpa [ProfiledRawJointHybridShadowPhaseLiveTag.bootstrapGraph,
            ProfiledRawJointHybridShadowStrictSide.bootstrapGraph, hside] using
              hnext
      | left =>
          exact False.elim (hchanged (hnext.trans hcurrent.symm))
      | both =>
          exact False.elim (hnextStrict hnext)

end OperationalCloseCutPackage

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
/-- On the persistent strict-reversal tail, every sufficiently late changed
cut from a tag's creation direction is definitionally its bootstrap delivery
direction. -/
theorem PersistentStrictReversalTail.eventually_operationalClose_next_eq_tagBootstrap
    {graphs : Nat → Graph} (hreversal : PersistentStrictReversalTail graphs) :
    let cutPackage :=
      operationalCloseCutPackageOfPersistentStrictReversalTail graphs hreversal
    ∃ threshold : Nat, ∀ (tag : Tag A strategy hwin) (k : Nat),
      threshold ≤ cutPackage.cuts (k + 1) →
        graphs (cutPackage.cuts k) = tag.creationGraph A strategy hwin →
          graphs (cutPackage.cuts (k + 1)) =
            tag.bootstrapGraph A strategy hwin := by
  dsimp only
  rcases hreversal.1 with ⟨threshold, hnoBoth⟩
  refine ⟨threshold, ?_⟩
  intro tag k hlate hcreation
  let cutPackage :=
    operationalCloseCutPackageOfPersistentStrictReversalTail graphs hreversal
  exact
    DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.next_eq_tag_bootstrapGraph_of_strict
      A strategy hwin cutPackage tag k hcreation (hnoBoth _ hlate)

end

end DetParityAutomaton

end DistributedSynthesis
