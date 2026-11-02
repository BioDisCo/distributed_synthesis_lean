/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTreeRationalization

/-!
# Feeding the rational common policy into the local guarded carrier

The common tree rationalization selects one complete guarded move pair at
each reachable finite policy state.  After the full current input pair is
received, the policy successor state selects the next complete pair.  This
file packages that next pair as the coherent child label required by the
local shadow carrier.

All data passed to the local transitions are finite: the rational-policy
state, the current and next guarded move pairs, and the current input pair.
Semantic occurrences occur only in proof fields establishing the child
incidence equation.  No function accepts a graph, orientation, leader bit, or
semantic history.
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

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

/-! ## The coherent child selected at the policy successor -/

/-- The package-selected pair at the successor policy state is an allowed
complete child of the current guarded pair. -/
noncomputable def
    ProfiledRawJointGuardedCommonPolicyPackage.successorChild
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    (state : ProfiledRawJointGuardedCommonPolicyState A strategy hwin initial)
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial package.policy state)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonSuccessor A strategy hwin
      (package.pairAt state) input := by
  let nextPair := package.nextPairAt A strategy hwin state input
  refine ⟨nextPair, ?_⟩
  have hvalid := package.nextPairAt_valid A strategy hwin hreachable input
  rcases hvalid with ⟨point, hcode, hpair⟩
  refine ⟨point.parent, point.incoming, ?_, ?_, ?_⟩
  · have h := congrArg (fun pair : CommonPair A strategy hwin ↦ pair.1.1)
      hpair
    simpa [nextPair,
      ProfiledRawJointGuardedCommonSemanticPoint.move,
      profiledRawJointGuardedCommonPairOfWorld] using h.symm
  · have h := congrArg (fun pair : CommonPair A strategy hwin ↦ pair.1.2)
      hpair
    simpa [nextPair,
      ProfiledRawJointGuardedCommonSemanticPoint.move,
      profiledRawJointGuardedCommonPairOfWorld] using h.symm
  · calc
      (profiledRawJointCommonWorldFamily A
        (profiledRawJointCommonWorldAfterBoth A point.parent point.incoming)
        ).incidenceCode A = point.code A strategy := rfl
      _ = (package.policy.successor state input).1 := hcode
      _ = (package.pairAt state).bothNextCode A strategy hwin input :=
        package.successor_code_eq_currentPair A strategy hwin hreachable input
      _ = profiledRawJointBothTargetMerge A input
          (((package.pairAt state).rightRootRecord A strategy hwin input
            ).2.1.target .both)
          (((package.pairAt state).leftRootRecord A strategy hwin input
            ).2.1.target .both) := rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonPolicyPackage.successorChild_pair
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    (state : ProfiledRawJointGuardedCommonPolicyState A strategy hwin initial)
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial package.policy state)
    (input : In₁ × In₂) :
    (package.successorChild A strategy hwin state hreachable input).1 =
      package.nextPairAt A strategy hwin state input :=
  rfl

/-- Exact proof-side source-incidence equation carried by the selected child
label. -/
theorem
    ProfiledRawJointGuardedCommonPolicyPackage.successorChild_source_incidence
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    (state : ProfiledRawJointGuardedCommonPolicyState A strategy hwin initial)
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial package.policy state)
    (input : In₁ × In₂) :
    ∃ world : ProfiledRawJointCommonBaseWorld A strategy,
      ∃ current : In₁ × In₂,
        (package.nextPairAt A strategy hwin state input).1.1 =
            profiledRawJointGuardedCommonRightMoveOfWorld A strategy hwin world
              current ∧
          (package.nextPairAt A strategy hwin state input).1.2 =
            profiledRawJointGuardedCommonLeftMoveOfWorld A strategy hwin world
              current ∧
          (profiledRawJointCommonWorldFamily A
            (profiledRawJointCommonWorldAfterBoth A world current)
            ).incidenceCode A =
          (package.pairAt state).bothNextCode A strategy hwin input := by
  have hchild := (package.successorChild A strategy hwin state hreachable
    input).property
  simpa only [package.successorChild_pair A strategy hwin state hreachable
    input] using hchild

/-! ## The two local receive transitions at one reachable policy state -/

noncomputable def
    ProfiledRawJointGuardedCommonPolicyPackage.startOneShadow
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    (state : ProfiledRawJointGuardedCommonPolicyState A strategy hwin initial)
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial package.policy state)
    (input : In₁ × In₂) :
    Out₁ × ProfiledRawJointGuardedCommonOneShadow A strategy hwin :=
  profiledRawJointGuardedCommonStartOneShadowOfSuccessor A strategy hwin
    (package.pairAt state) input
    (package.successorChild A strategy hwin state hreachable input)

noncomputable def
    ProfiledRawJointGuardedCommonPolicyPackage.startTwoShadow
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    (state : ProfiledRawJointGuardedCommonPolicyState A strategy hwin initial)
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial package.policy state)
    (input : In₁ × In₂) :
    Out₂ × ProfiledRawJointGuardedCommonTwoShadow A strategy hwin :=
  profiledRawJointGuardedCommonStartTwoShadowOfSuccessor A strategy hwin
    (package.pairAt state) input
    (package.successorChild A strategy hwin state hreachable input)

@[simp] theorem
    ProfiledRawJointGuardedCommonPolicyPackage.startOneShadow_source
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    (state : ProfiledRawJointGuardedCommonPolicyState A strategy hwin initial)
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial package.policy state)
    (input : In₁ × In₂) :
    (package.startOneShadow A strategy hwin state hreachable input).2.source =
      package.pairAt state :=
  rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonPolicyPackage.startTwoShadow_source
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    (state : ProfiledRawJointGuardedCommonPolicyState A strategy hwin initial)
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial package.policy state)
    (input : In₁ × In₂) :
    (package.startTwoShadow A strategy hwin state hreachable input).2.source =
      package.pairAt state :=
  rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonPolicyPackage.startOneShadow_common
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    (state : ProfiledRawJointGuardedCommonPolicyState A strategy hwin initial)
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial package.policy state)
    (input : In₁ × In₂) :
    (package.startOneShadow A strategy hwin state hreachable input).2.common =
      package.nextPairAt A strategy hwin state input :=
  rfl

@[simp] theorem
    ProfiledRawJointGuardedCommonPolicyPackage.startTwoShadow_common
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    (state : ProfiledRawJointGuardedCommonPolicyState A strategy hwin initial)
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial package.policy state)
    (input : In₁ × In₂) :
    (package.startTwoShadow A strategy hwin state hreachable input).2.common =
      package.nextPairAt A strategy hwin state input :=
  rfl

/-- Both local transitions install definitionally the same next guarded pair. -/
theorem ProfiledRawJointGuardedCommonPolicyPackage.startShadows_agree
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    (state : ProfiledRawJointGuardedCommonPolicyState A strategy hwin initial)
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial package.policy state)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonShadowsAgree A strategy hwin
      (package.startOneShadow A strategy hwin state hreachable input).2
      (package.startTwoShadow A strategy hwin state hreachable input).2 :=
  rfl

/-- Receiver-side dangerous-pair equation at the selected occurrence. -/
theorem ProfiledRawJointGuardedCommonPolicyPackage.startShadows_outputs
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    (state : ProfiledRawJointGuardedCommonPolicyState A strategy hwin initial)
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial package.policy state)
    (input : In₁ × In₂) :
    ((package.startOneShadow A strategy hwin state hreachable input).1,
      (package.startTwoShadow A strategy hwin state hreachable input).1) =
      (((package.pairAt state).rightRootRecord A strategy hwin input
        ).2.1.physical.closingBoth,
        ((package.pairAt state).leftRootRecord A strategy hwin input
          ).2.1.physical.closingBoth) :=
  profiledRawJointGuardedCommonStartSuccessorShadows_outputs A strategy hwin
    (package.pairAt state) input
    (package.successorChild A strategy hwin state hreachable input)

end


end DetParityAutomaton

end DistributedSynthesis
