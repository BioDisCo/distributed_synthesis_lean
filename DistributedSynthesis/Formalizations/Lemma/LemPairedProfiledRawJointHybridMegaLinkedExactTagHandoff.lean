/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedPayload
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankRetainedReinstallation

/-!
# Exact marked-bank tags at the mega-front handoff

The older cast-free adapter from a phase-live tag entered the *root* of the
marked bank.  That is too early for the linked deferred tail: a phase-live tag
already denotes one concrete strict child of that root.  This file records the
correct local conversion.  It follows the stored tag's concrete direction in
the already selected finite bank and retains that exact child.

The conversion inspects only the delivered finite tag (`origin`, the finite
input pair, and its stored side).  It receives no graph, hierarchy, leader, or
strict-leader argument.  The side is construction provenance carried in the
delivered control, not a newly observed runtime bit.
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

private abbrev ShadowTag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

/-! ## The exact child, not the root -/

/-- The exact marked-bank child denoted by a delivered phase-live tag. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.markedBankChild
    (tag : ShadowTag A strategy hwin) : BankControl A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
    hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
        hwin tag.origin)
      (tag.direction (A := A))

/-- The exact retained installation tag used by the linked deferred tail.
The canonical false anchors are finite initialization data; the first fresh
receive replaces them with the appropriate `.first`/`.both` pair. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.markedRetainedChildTag
    (tag : ShadowTag A strategy hwin) : RetainedTag A strategy hwin :=
  (tag.markedBankChild A strategy hwin, (false, false))

@[simp] theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.markedRetainedChildTag_state
    (tag : ShadowTag A strategy hwin) :
    (tag.markedRetainedChildTag A strategy hwin).1 =
      tag.markedBankChild A strategy hwin :=
  rfl

@[simp] theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.markedRetainedChildTag_anchors
    (tag : ShadowTag A strategy hwin) :
    (tag.markedRetainedChildTag A strategy hwin).2 = (false, false) :=
  rfl

/-- The handoff stays in the bank entry selected at the common front. -/
@[simp] theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.markedBankChild_index
    (tag : ShadowTag A strategy hwin) :
    (tag.markedBankChild A strategy hwin).1 = tag.origin :=
  rfl

/-- The root is reachable, hence so is the exact direction-selected child
installed at the handoff. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.markedBankChild_reachable
    (tag : ShadowTag A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
      hwin (tag.markedBankChild A strategy hwin) := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
      strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
          hwin tag.origin)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_reachable A
          strategy hwin tag.origin)
        (tag.direction (A := A))

/-- The stored full linked code is exactly the code requested by the tag's
real strict direction at the marked root. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.markedBankChild_code
    (tag : ShadowTag A strategy hwin) :
    (tag.markedBankChild A strategy hwin).2.1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
        hwin tag.origin).childCode A strategy hwin (tag.direction (A := A)) := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_code A
      strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
          hwin tag.origin)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_reachable A
          strategy hwin tag.origin)
        (tag.direction (A := A))

/-! ## Delivered handoff projections -/

/-- Process-one strict-left handoff conversion. -/
noncomputable def
    profiledRawJointHybridDeliveredLeftShadowPhaseLiveMarkedRetainedChildTag
    (delivered :
      ProfiledRawJointHybridLeftShadowPhaseLiveHandoff A strategy hwin) :
    RetainedTag A strategy hwin :=
  delivered.tag.markedRetainedChildTag A strategy hwin

/-- Process-two strict-right mirror. -/
noncomputable def
    profiledRawJointHybridDeliveredRightShadowPhaseLiveMarkedRetainedChildTag
    (delivered :
      ProfiledRawJointHybridRightShadowPhaseLiveHandoff A strategy hwin) :
    RetainedTag A strategy hwin :=
  delivered.tag.markedRetainedChildTag A strategy hwin

@[simp] theorem
    profiledRawJointHybridDeliveredLeftShadowPhaseLiveMarkedRetainedChildTag_state
    (delivered :
      ProfiledRawJointHybridLeftShadowPhaseLiveHandoff A strategy hwin) :
    (profiledRawJointHybridDeliveredLeftShadowPhaseLiveMarkedRetainedChildTag A
      strategy hwin delivered).1 =
      delivered.tag.markedBankChild A strategy hwin :=
  rfl

@[simp] theorem
    profiledRawJointHybridDeliveredRightShadowPhaseLiveMarkedRetainedChildTag_state
    (delivered :
      ProfiledRawJointHybridRightShadowPhaseLiveHandoff A strategy hwin) :
    (profiledRawJointHybridDeliveredRightShadowPhaseLiveMarkedRetainedChildTag A
      strategy hwin delivered).1 =
      delivered.tag.markedBankChild A strategy hwin :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
