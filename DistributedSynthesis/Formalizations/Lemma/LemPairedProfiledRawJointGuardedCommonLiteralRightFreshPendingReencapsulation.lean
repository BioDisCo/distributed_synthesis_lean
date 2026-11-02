/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralRightPendingForkCoherence

/-!
# Same-occurrence re-encapsulation of a fresh right seam

The finite key of a new right/`both` seam is the current decorated-policy
state together with the complete input pair delivered at that occurrence.
This module records the important semantic fact hidden by that small product:
the key denotes the literal child of the representative attached to the
*current* state.  It is not reconstructed later from a bare successor code.

The receiving endpoint can therefore create one false/true pending table fork
at the exact child occurrence.  Its two alternatives erase to the same table
sender root and remain coherent at arbitrary blind depth.  The recurrent
target retained by the table is used only after the old member is resolved;
the fresh fork itself never contains a recurrent/table mixture.
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

private abbrev Reachable
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial)) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
    initial (CrossValid A strategy hwin) package.policy state

private abbrev Key
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin package

private abbrev Pending
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate A
    strategy hwin package

/-! ## The exact fresh key -/

/-- Finite key selected at a new occurrence.  Both components are available
to the receiving endpoint: the current finite policy state is local control,
and the complete input pair is its own input plus the delivered partner input. -/
def literalRightSeamFreshKey
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (input : In₁ × In₂) : Key A strategy hwin package :=
  (state, input)

/-- Unfolding the key exposes the literal child of the representative attached
to this exact current state. -/
@[simp] theorem literalRightSeamFreshKey_childPoint
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (input : In₁ × In₂) :
    package.literalRightSeamChildPoint A strategy hwin
        (package.literalRightSeamFreshKey A strategy hwin state input) =
      (package.literalRightSeamPointAt A strategy hwin state).step A strategy
        input :=
  rfl

/-- Consequently the installed heterogeneous table is literally extracted at
that same child occurrence, rather than at an arbitrary equal-code point. -/
@[simp] theorem literalRightSeamFreshKey_installed
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (input : In₁ × In₂) :
    package.literalRightSeamInstalled A strategy hwin
        (package.literalRightSeamFreshKey A strategy hwin state input) =
      profiledRawJointGuardedCommonPointInstalled A strategy
        ((package.literalRightSeamPointAt A strategy hwin state).step A
          strategy input) :=
  rfl

/-- At a reachable current state, the exact child's incidence code is the
public successor code.  The proof passes through the current occurrence's
guarded pair; it does not choose a new successor representative. -/
theorem literalRightSeamFreshKey_childCode
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (hreachable : Reachable A strategy hwin package state)
    (input : In₁ × In₂) :
    (package.literalRightSeamChildPoint A strategy hwin
      (package.literalRightSeamFreshKey A strategy hwin state input)).code A
        strategy =
      (package.policy.successor state input).1 := by
  have hpoint :=
    package.literalRightSeamPointAt_spec A strategy hwin state hreachable
  rw [package.literalRightSeamFreshKey_childPoint A strategy hwin state input]
  rw [ProfiledRawJointGuardedCommonSemanticPoint.step_code A strategy hwin]
  rw [hpoint.2.1]
  exact (congrArg Prod.fst
    (package.successor_eq_pairAt A strategy hwin state hreachable input)).symm

/-! ## Endpoint-facing fresh fork -/

/-- Re-encapsulate both new alternatives at the same occurrence-specific
table key. -/
noncomputable def literalRightSeamFreshPendingSenderForkAt
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (input : In₁ × In₂) : FiniteDelayedFork (Pending A strategy hwin package) :=
  package.literalRightSeamFreshPendingSenderFork A strategy hwin
    (package.literalRightSeamFreshKey A strategy hwin state input)

@[simp] theorem literalRightSeamFreshPendingSenderForkAt_open_key
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (input : In₁ × In₂) :
    (package.literalRightSeamFreshPendingSenderForkAt A strategy hwin state
      input).openControl.1.1 =
      package.literalRightSeamFreshKey A strategy hwin state input :=
  rfl

@[simp] theorem literalRightSeamFreshPendingSenderForkAt_closed_key
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (input : In₁ × In₂) :
    (package.literalRightSeamFreshPendingSenderForkAt A strategy hwin state
      input).closedControl.1.1 =
      package.literalRightSeamFreshKey A strategy hwin state input :=
  rfl

@[simp] theorem literalRightSeamFreshPendingSenderForkAt_members
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (input : In₁ × In₂) :
    ((package.literalRightSeamFreshPendingSenderForkAt A strategy hwin state
        input).openControl.1.2.1,
      (package.literalRightSeamFreshPendingSenderForkAt A strategy hwin state
        input).closedControl.1.2.1) = (false, true) :=
  rfl

/-- The two new alternatives erase to one executable table root at this exact
key. -/
theorem literalRightSeamFreshPendingSenderForkAt_forget_pair
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (input : In₁ × In₂) :
    (package.literalRightSeamMemberSenderForget A strategy hwin
        (package.literalRightSeamFreshPendingSenderForkAt A strategy hwin
          state input).openControl.1,
      package.literalRightSeamMemberSenderForget A strategy hwin
        (package.literalRightSeamFreshPendingSenderForkAt A strategy hwin
          state input).closedControl.1) =
      (package.literalRightSeamStagedSenderInitial A strategy hwin
          (package.literalRightSeamFreshKey A strategy hwin state input),
        package.literalRightSeamStagedSenderInitial A strategy hwin
          (package.literalRightSeamFreshKey A strategy hwin state input)) := by
  exact package.literalRightSeamFreshPendingSenderFork_forget_pair A strategy
    hwin (package.literalRightSeamFreshKey A strategy hwin state input)

/-- The same-occurrence fork is immediately blind-output coherent. -/
theorem literalRightSeamFreshPendingSenderForkAt_noRecvOutputCoherent
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (input : In₁ × In₂) (nextInput : In₂) :
    (package.literalRightSeamFreshPendingSenderForkAt A strategy hwin state
      input).NoRecvMealyOutputCoherent
        (package.literalRightSeamPendingSenderNoRecv A strategy hwin)
        nextInput := by
  exact package.literalRightSeamFreshPendingSenderFork_noRecvOutputCoherent A
    strategy hwin
      (package.literalRightSeamFreshKey A strategy hwin state input) nextInput

/-- And it remains coherent after every further blind table step. -/
theorem
    literalRightSeamFreshPendingSenderForkAt_noRecv_preserves_coherent
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (input : In₁ × In₂) (blindInput nextInput : In₂) :
    ((package.literalRightSeamFreshPendingSenderForkAt A strategy hwin state
      input).noRecvMealy
        (package.literalRightSeamPendingSenderNoRecv A strategy hwin)
        blindInput).1.NoRecvMealyOutputCoherent
      (package.literalRightSeamPendingSenderNoRecv A strategy hwin)
      nextInput := by
  exact
    package.literalRightSeamFreshPendingSenderFork_noRecv_preserves_coherent A
      strategy hwin
        (package.literalRightSeamFreshKey A strategy hwin state input)
        blindInput nextInput

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
