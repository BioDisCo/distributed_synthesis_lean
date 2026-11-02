/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalPendingOnly
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshReceiveOneHandler
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshReceiveTwoHandler

/-!
# The cross cut installs the opposite shared table

The canonical pending-only controller never enters the independently
rationalized ordinary-policy half of its phase sum.  At every receive it
instead computes one finite occurrence key from the locally selected fresh
common-policy copy and the now-known input pair.  Process one installs the
left-seam sender and both right-seam receiver interpretations at that key;
process two installs the right-seam sender and both left-seam receiver
interpretations at the same key.

This file proves the boundary equations.  Under the leader-free freshness
invariant, the two local source selectors agree.  Consequently both fresh
shared controls retain the same exact occurrence key, their freshness copies
are aligned again, and the key unfolds to the literal child of the semantic
occurrence already attached to that policy state.  No equality with an
independently selected ordinary controller occurs.

No executable function below accepts a graph, orientation, hierarchy side,
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

private abbrev OneShared (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
    package

private abbrev TwoShared (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
    package

/-! ## One leader-free boundary source and key -/

/-- The proof-side name of the unique current finite policy copy.  Each
endpoint computes this value from its own phase and the delivered partner
copy; it is not an executable argument. -/
def literalCombinedFreshPendingBoundarySource
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) :
    State A strategy hwin (initial := initial) :=
  decoratedFreshnessCurrent A strategy hwin one.1 two.1

/-- The exact finite occurrence installed at the boundary. -/
def literalCombinedFreshPendingBoundaryKey
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) (input : In₁ × In₂) :
    Key A strategy hwin package :=
  (package.literalCombinedFreshPendingBoundarySource A strategy hwin one two,
    input)

/-- Process one's local source selector is definitionally the boundary
source. -/
@[simp] theorem literalCombinedFreshOneReceiveSource_eq_boundary
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) :
    package.literalCombinedFreshOneReceiveSource A strategy hwin one two =
      package.literalCombinedFreshPendingBoundarySource A strategy hwin one
        two :=
  rfl

/-- Process two selects the same source whenever the two finite freshness
copies satisfy their leader-free alignment invariant. -/
theorem literalCombinedFreshTwoReceiveSource_eq_boundary_of_aligned
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package)
    (haligned : DecoratedFreshnessAligned A strategy hwin one.1 two.1) :
    package.literalCombinedFreshTwoReceiveSource A strategy hwin two one =
      package.literalCombinedFreshPendingBoundarySource A strategy hwin one
        two := by
  exact decoratedFreshnessRecvTwoSource_eq_current_of_aligned A strategy hwin
    one.1 two.1 haligned

/-- Hence process one's fresh sender key is exactly the common boundary key. -/
@[simp] theorem literalCombinedFreshOneReceiveKey_eq_boundary
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) (input : In₁ × In₂) :
    package.literalCombinedFreshOneReceiveKey A strategy hwin one input.1 two
        input.2 =
      package.literalCombinedFreshPendingBoundaryKey A strategy hwin one two
        input :=
  rfl

/-- Process two's freshly installed opposite sender has the same key. -/
theorem literalCombinedFreshTwoReceiveShared_key_eq_boundary_of_aligned
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) (input : In₁ × In₂)
    (haligned : DecoratedFreshnessAligned A strategy hwin one.1 two.1) :
    (package.literalCombinedFreshTwoReceiveShared A strategy hwin two input.2
      one input.1).2.1.1 =
      package.literalCombinedFreshPendingBoundaryKey A strategy hwin one two
        input := by
  rw [package.literalCombinedFreshTwoReceiveShared_sender_key A strategy hwin]
  rw [package.literalCombinedFreshTwoReceiveSource_eq_boundary_of_aligned A
    strategy hwin one two haligned]
  cases input
  rfl

/-! ## The two opposite tables are installed together -/

/-- Process one's new pending shared value, written directly at the common
boundary key. -/
noncomputable def literalCombinedFreshPendingBoundaryOneShared
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) (input : In₁ × In₂) :
    OneShared A strategy hwin package :=
  package.literalCrossCombinedFreshOneSharedAt A strategy hwin
    (package.literalCombinedFreshOneReceiveFreshness A strategy hwin one
      input.1 two input.2)
    (package.literalCombinedFreshPendingBoundaryKey A strategy hwin one two
      input)

/-- Process two's opposite-table shared value at that same key. -/
noncomputable def literalCombinedFreshPendingBoundaryTwoShared
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) (input : In₁ × In₂) :
    TwoShared A strategy hwin package :=
  package.literalCrossCombinedFreshTwoSharedAt A strategy hwin
    (decoratedFreshnessRecvTwo A strategy hwin package two.1 input.2 one.1
      input.1)
    (package.literalCombinedFreshPendingBoundaryKey A strategy hwin one two
      input)

/-- The process-one pending receive installs exactly the boundary shared
table, before the canonical false/true fork wrapper is added. -/
@[simp] theorem literalCombinedFreshPendingBoundaryOneShared_eq_receive
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) (input : In₁ × In₂) :
    package.literalCombinedFreshPendingBoundaryOneShared A strategy hwin one
        two input =
      package.literalCrossCombinedFreshOneSharedAt A strategy hwin
        (package.literalCombinedFreshOneReceiveFreshness A strategy hwin one
          input.1 two input.2)
        (package.literalCombinedFreshOneReceiveKey A strategy hwin one input.1
          two input.2) :=
  rfl

/-- Under alignment, process two's actual receive construction is exactly the
opposite boundary shared table. -/
theorem literalCombinedFreshPendingBoundaryTwoShared_eq_receive_of_aligned
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) (input : In₁ × In₂)
    (haligned : DecoratedFreshnessAligned A strategy hwin one.1 two.1) :
    package.literalCombinedFreshPendingBoundaryTwoShared A strategy hwin one
        two input =
      package.literalCombinedFreshTwoReceiveShared A strategy hwin two input.2
        one input.1 := by
  unfold literalCombinedFreshPendingBoundaryTwoShared
    literalCombinedFreshTwoReceiveShared
  rw [package.literalCombinedFreshTwoReceiveSource_eq_boundary_of_aligned A
    strategy hwin one two haligned]
  cases input
  rfl

/-- The left-seam sender installed for process one carries the common key. -/
@[simp] theorem literalCombinedFreshPendingBoundaryOneShared_sender
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) (input : In₁ × In₂) :
    (package.literalCombinedFreshPendingBoundaryOneShared A strategy hwin one
      two input).2.1 =
      package.literalLeftSeamStagedSenderInitial A strategy hwin
        (package.literalCombinedFreshPendingBoundaryKey A strategy hwin one
          two input) :=
  rfl

/-- Simultaneously, process two carries the opposite right-seam sender at the
same key. -/
@[simp] theorem literalCombinedFreshPendingBoundaryTwoShared_sender
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) (input : In₁ × In₂) :
    (package.literalCombinedFreshPendingBoundaryTwoShared A strategy hwin one
      two input).2.1 =
      package.literalRightSeamStagedSenderInitial A strategy hwin
        (package.literalCombinedFreshPendingBoundaryKey A strategy hwin one
          two input) :=
  rfl

/-- After the boundary receive the two new finite freshness copies are aligned
again.  Thus the construction can repeat at the next reversal without learning
which endpoint was the strict leader. -/
theorem literalCombinedFreshPendingBoundary_freshness_aligned
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) (input : In₁ × In₂)
    (haligned : DecoratedFreshnessAligned A strategy hwin one.1 two.1) :
    DecoratedFreshnessAligned A strategy hwin
      (package.literalCombinedFreshPendingBoundaryOneShared A strategy hwin
        one two input).1
      (package.literalCombinedFreshPendingBoundaryTwoShared A strategy hwin
        one two input).1 := by
  rcases one with ⟨⟨oneState, onePhase⟩, oneRest⟩
  rcases two with ⟨⟨twoState, twoPhase⟩, twoRest⟩
  cases onePhase <;> cases twoPhase <;>
    simp [DecoratedFreshnessAligned,
      literalCombinedFreshPendingBoundaryOneShared,
      literalCombinedFreshPendingBoundaryTwoShared,
      literalCombinedFreshOneReceiveFreshness,
      literalCrossCombinedFreshOneSharedAt,
      literalCrossCombinedFreshTwoSharedAt,
      decoratedFreshnessRecvOne, decoratedFreshnessRecvTwo] at haligned ⊢
  case true.false => simpa [haligned]

/-! ## Exact occurrence provenance -/

/-- The boundary key does not merely retain an incidence code.  It unfolds
definitionally to the literal child of the exact semantic occurrence attached
to the selected finite source state. -/
@[simp] theorem literalCombinedFreshPendingBoundaryKey_installed
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) (input : In₁ × In₂) :
    package.literalRightSeamInstalled A strategy hwin
        (package.literalCombinedFreshPendingBoundaryKey A strategy hwin one
          two input) =
      profiledRawJointGuardedCommonPointInstalled A strategy
        ((package.literalRightSeamPointAt A strategy hwin
          (package.literalCombinedFreshPendingBoundarySource A strategy hwin
            one two)).step A strategy input) :=
  rfl

/-- On a reachable boundary source, the same literal child has exactly the
public successor code.  This is a consequence of occurrence identity, not a
same-code representative replacement. -/
theorem literalCombinedFreshPendingBoundaryKey_childCode
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) (input : In₁ × In₂)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy
          (package.literalCombinedFreshPendingBoundarySource A strategy hwin
            one two)) :
    (package.literalRightSeamChildPoint A strategy hwin
      (package.literalCombinedFreshPendingBoundaryKey A strategy hwin one two
        input)).code A strategy =
      (package.policy.successor
        (package.literalCombinedFreshPendingBoundarySource A strategy hwin one
          two) input).1 := by
  exact package.literalRightSeamFreshKey_childCode A strategy hwin
    (package.literalCombinedFreshPendingBoundarySource A strategy hwin one two)
    hreachable input

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
