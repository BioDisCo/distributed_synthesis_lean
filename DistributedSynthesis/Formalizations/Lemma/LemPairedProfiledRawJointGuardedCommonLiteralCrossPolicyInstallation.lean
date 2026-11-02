/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedAnnotatedShadowStart
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossLocalCarrier

/-!
# Installing retained literal cross tables at a common-policy successor

The decorated policy already exposes its successor annotation by a total
finite lookup.  Here that annotation is installed into the concrete right and
left local carrier roots.  This is the operational handoff from
"the table ID survives rationalization" to "both processes actually store
and execute that ID".

The executable installations use only a finite policy state, the current
input pair, and a private Boolean anchor supplied by the resolving local
phase.  Reachability is used solely to prove that the installed ID came from
the exact semantic occurrence selected at this successor.
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

/-! ## Tables already stored at the current occurrence -/

/-- Install the right outgoing table already decorating the current policy
state.  In particular this needs no partner input: the table was selected
before the policy was rationalized. -/
noncomputable def currentRightLiteralCrossInitial
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossOneState A ×
      ProfiledRawJointGuardedCommonLiteralCrossTwoState A :=
  profiledRawJointGuardedCommonLiteralCrossRightInitial A
    (package.extraAt A strategy hwin state) anchor

/-- Current left table, symmetrically. -/
noncomputable def currentLeftLiteralCrossInitial
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossOneState A ×
      ProfiledRawJointGuardedCommonLiteralCrossTwoState A :=
  profiledRawJointGuardedCommonLiteralCrossLeftInitial A
    (package.extraAt A strategy hwin state) anchor

@[simp] theorem currentRightLiteralCrossInitial_eq
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (anchor : Bool) :
    package.currentRightLiteralCrossInitial A strategy hwin state anchor =
      (.inl
        (profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A
          (package.extraAt A strategy hwin state).1),
        .inl
          (profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A
            (package.extraAt A strategy hwin state).1 anchor)) := by
  rfl

@[simp] theorem currentLeftLiteralCrossInitial_eq
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (anchor : Bool) :
    package.currentLeftLiteralCrossInitial A strategy hwin state anchor =
      (.inr
        (profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A
          (package.extraAt A strategy hwin state).2 anchor),
        .inr
          (profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A
            (package.extraAt A strategy hwin state).2)) := by
  rfl

/-- Reachability reads the current finite annotation back to the exact
semantic occurrence at the current policy code and guarded pair. -/
theorem exists_point_of_currentLiteralCrossInitial
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    {state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state) :
    ∃ point : CommonPoint A strategy,
      point.code A strategy = state.1 ∧
        point.move A strategy hwin = package.pairAt A strategy hwin state ∧
        profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
          point = package.extraAt A strategy hwin state := by
  exact package.extraAt_valid A strategy hwin state hreachable

/-- Total graph-blind installation of the retained right table at the next
common-policy state. -/
noncomputable def nextRightLiteralCrossInitial
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (input : In₁ × In₂) (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossOneState A ×
      ProfiledRawJointGuardedCommonLiteralCrossTwoState A :=
  profiledRawJointGuardedCommonLiteralCrossRightInitial A
    (package.nextExtraAt A strategy hwin state input) anchor

/-- Left-oriented mirror. -/
noncomputable def nextLeftLiteralCrossInitial
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (input : In₁ × In₂) (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossOneState A ×
      ProfiledRawJointGuardedCommonLiteralCrossTwoState A :=
  profiledRawJointGuardedCommonLiteralCrossLeftInitial A
    (package.nextExtraAt A strategy hwin state input) anchor

/-- A fully observed successor installs exactly the table already decorating
that successor state; there is no second choice at the handoff. -/
theorem currentRightLiteralCrossInitial_successor
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (input : In₁ × In₂) (anchor : Bool) :
    package.currentRightLiteralCrossInitial A strategy hwin
        (package.policy.successor state input) anchor =
      package.nextRightLiteralCrossInitial A strategy hwin state input
        anchor := by
  rfl

/-- Left mirror. -/
theorem currentLeftLiteralCrossInitial_successor
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (input : In₁ × In₂) (anchor : Bool) :
    package.currentLeftLiteralCrossInitial A strategy hwin
        (package.policy.successor state input) anchor =
      package.nextLeftLiteralCrossInitial A strategy hwin state input
        anchor := by
  rfl

/-! ## Exact installed IDs -/

/-- Unfolding the right installation exposes exactly the retained right table
ID in both endpoint roots. -/
@[simp] theorem nextRightLiteralCrossInitial_eq
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (input : In₁ × In₂) (anchor : Bool) :
    package.nextRightLiteralCrossInitial A strategy hwin state input anchor =
      (.inl
        (profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A
          (package.nextExtraAt A strategy hwin state input).1),
        .inl
          (profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A
            (package.nextExtraAt A strategy hwin state input).1 anchor)) := by
  rfl

/-- Left installation exposes the retained left table ID symmetrically. -/
@[simp] theorem nextLeftLiteralCrossInitial_eq
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (input : In₁ × In₂) (anchor : Bool) :
    package.nextLeftLiteralCrossInitial A strategy hwin state input anchor =
      (.inr
        (profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A
          (package.nextExtraAt A strategy hwin state input).2 anchor),
        .inr
          (profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A
            (package.nextExtraAt A strategy hwin state input).2)) := by
  rfl

/-! ## Initial synchronization -/

theorem nextRightLiteralCrossInitial_controls_eq
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (input : In₁ × In₂) (anchor : Bool) :
    (profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A
      (package.nextExtraAt A strategy hwin state input).1).2 =
        (profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A
          (package.nextExtraAt A strategy hwin state input).1 anchor).2.2.1 := by
  exact profiledRawJointGuardedCommonRightLiteralCross_initial_controls_eq A
    (package.nextExtraAt A strategy hwin state input).1 anchor

theorem nextLeftLiteralCrossInitial_controls_eq
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (input : In₁ × In₂) (anchor : Bool) :
    (profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A
      (package.nextExtraAt A strategy hwin state input).2).2 =
        (profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A
          (package.nextExtraAt A strategy hwin state input).2 anchor).2.2.1 := by
  exact profiledRawJointGuardedCommonLeftLiteralCross_initial_controls_eq A
    (package.nextExtraAt A strategy hwin state input).2 anchor

/-! ## Proof-only exact-occurrence readback -/

/-- At a reachable policy state the locally installed table IDs are exactly
those extracted at one semantic occurrence whose code and guarded pair are
the successor code and successor pair used by the two annotated shadows. -/
theorem exists_point_of_nextLiteralCrossInitial
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    {state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (input : In₁ × In₂) :
    ∃ point : CommonPoint A strategy,
      point.code A strategy =
          (package.pairAt A strategy hwin state).bothNextCode A strategy hwin
            input ∧
        point.move A strategy hwin =
          package.nextPairAt A strategy hwin state input ∧
        profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
          point = package.nextExtraAt A strategy hwin state input := by
  exact package.nextExtraAt_valid_at_currentChildCode A strategy hwin
    hreachable input

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
