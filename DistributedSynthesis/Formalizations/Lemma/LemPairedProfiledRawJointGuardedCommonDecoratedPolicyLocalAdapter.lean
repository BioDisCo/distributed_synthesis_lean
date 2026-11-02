/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedPolicyPackage

/-!
# Feeding the finitely decorated common policy into the local carrier

This is the decorated analogue of the guarded common-policy local adapter.
The successor policy state exposes one total same-occurrence readout
`(guarded pair, extra)`.  Its guarded-pair projection drives exactly the old
two local shadow transitions, while its finite annotation remains available
to later operational layers through `nextExtraAt`.

All executable arguments are finite and source-free: a fixed package, a
finite policy state, and the current input pair.  No executable map accepts a
graph, orientation, leader bit, or semantic history.
-/

namespace DistributedSynthesis

universe u v x y s b

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

variable {Extra : Type b} [Fintype Extra]

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

private abbrev CommonCode :=
  ProfiledRawJointIncidenceCode A (I := Unit)

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable
  {initial : CommonPoint A strategy}
  {ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop}

/-! ## Same-occurrence successor readout -/

/-- The complete decorated move selected at the successor policy state. -/
noncomputable def nextMoveAt
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (input : In₁ × In₂) : CommonPair A strategy hwin × Extra :=
  package.moveAt (package.policy.successor state input)

/-- Guarded pair projected from the successor's one decorated lookup. -/
noncomputable def nextPairAt
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (input : In₁ × In₂) : CommonPair A strategy hwin :=
  package.pairAt A strategy hwin (package.policy.successor state input)

/-- Finite annotation projected from that same successor lookup. -/
noncomputable def nextExtraAt
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (input : In₁ × In₂) : Extra :=
  package.extraAt A strategy hwin (package.policy.successor state input)

section
omit [Fintype Extra]

/-- The two projections are definitionally tied to one successor lookup. -/
theorem nextMoveAt_eq_pair_extra
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (input : In₁ × In₂) :
    package.nextMoveAt A strategy hwin state input =
      (package.nextPairAt A strategy hwin state input,
        package.nextExtraAt A strategy hwin state input) := by
  simp only [nextMoveAt, nextPairAt, nextExtraAt, pairAt, extraAt]

/-- Exact finite handoff: the successor code is the merge advertised by the
current selected guarded roots. -/
theorem successor_code_eq_currentPair
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    {state}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.policy.successor state input).1 =
      (package.pairAt A strategy hwin state).bothNextCode A strategy hwin
        input := by
  exact congrArg Prod.fst
    (package.successor_eq_pairAt A strategy hwin state hreachable input)

/-- The complete successor readout satisfies both its guarded-pair and finite
annotation obligations. -/
theorem nextMoveAt_valid
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    {state}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin ExtraValid
      (package.policy.successor state input).1
      (package.nextMoveAt A strategy hwin state input) :=
  package.moveAt_valid _
    (package.successor_reachable A strategy hwin hreachable input)

/-- The successor guarded pair is valid at its exact successor code. -/
theorem nextPairAt_valid
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    {state}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonMoveValid A strategy hwin
      (package.policy.successor state input).1
      (package.nextPairAt A strategy hwin state input) :=
  package.pairAt_valid A strategy hwin _
    (package.successor_reachable A strategy hwin hreachable input)

/-- The successor annotation belongs to the very same guarded-pair lookup. -/
theorem nextExtraAt_valid
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    {state}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    ExtraValid (package.policy.successor state input).1
      (package.nextPairAt A strategy hwin state input)
      (package.nextExtraAt A strategy hwin state input) :=
  package.extraAt_valid A strategy hwin _
    (package.successor_reachable A strategy hwin hreachable input)

/-- Source-facing form of annotation validity, rewritten to the exact child
code advertised by the current pair. -/
theorem nextExtraAt_valid_at_currentChildCode
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    {state}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    ExtraValid
      ((package.pairAt A strategy hwin state).bothNextCode A strategy hwin
        input)
      (package.nextPairAt A strategy hwin state input)
      (package.nextExtraAt A strategy hwin state input) := by
  rw [← package.successor_code_eq_currentPair A strategy hwin hreachable
    input]
  exact package.nextExtraAt_valid A strategy hwin hreachable input

end

/-! ## The coherent child selected at the policy successor -/

/-- The successor's guarded-pair projection is an allowed complete child of
the current pair.  The sibling annotation remains accessible independently
through `nextExtraAt`. -/
noncomputable def successorChild
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonSuccessor A strategy hwin
      (package.pairAt A strategy hwin state) input := by
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
      _ = (package.pairAt A strategy hwin state).bothNextCode A strategy hwin
          input :=
        package.successor_code_eq_currentPair A strategy hwin hreachable input
      _ = profiledRawJointBothTargetMerge A input
          (((package.pairAt A strategy hwin state).rightRootRecord A strategy
            hwin input).2.1.target .both)
          (((package.pairAt A strategy hwin state).leftRootRecord A strategy
            hwin input).2.1.target .both) := rfl

omit [Fintype Extra] in
@[simp] theorem successorChild_pair
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.successorChild A strategy hwin state hreachable input).1 =
      package.nextPairAt A strategy hwin state input :=
  rfl

omit [Fintype Extra] in
/-- Exact proof-side source-incidence equation carried by the selected child
label. -/
theorem successorChild_source_incidence
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
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
          (package.pairAt A strategy hwin state).bothNextCode A strategy hwin
            input := by
  have hchild :=
    (package.successorChild A strategy hwin state hreachable input).property
  simpa only [package.successorChild_pair A strategy hwin state hreachable
    input] using hchild

/-! ## The two source-free local receive transitions -/

noncomputable def startOneShadow
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    Out₁ × ProfiledRawJointGuardedCommonOneShadow A strategy hwin :=
  profiledRawJointGuardedCommonStartOneShadowOfSuccessor A strategy hwin
    (package.pairAt A strategy hwin state) input
    (package.successorChild A strategy hwin state hreachable input)

noncomputable def startTwoShadow
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    Out₂ × ProfiledRawJointGuardedCommonTwoShadow A strategy hwin :=
  profiledRawJointGuardedCommonStartTwoShadowOfSuccessor A strategy hwin
    (package.pairAt A strategy hwin state) input
    (package.successorChild A strategy hwin state hreachable input)

section
omit [Fintype Extra]

@[simp] theorem startOneShadow_source
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.startOneShadow A strategy hwin state hreachable input).2.source =
      package.pairAt A strategy hwin state :=
  rfl

@[simp] theorem startTwoShadow_source
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.startTwoShadow A strategy hwin state hreachable input).2.source =
      package.pairAt A strategy hwin state :=
  rfl

@[simp] theorem startOneShadow_common
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.startOneShadow A strategy hwin state hreachable input).2.common =
      package.nextPairAt A strategy hwin state input :=
  rfl

@[simp] theorem startTwoShadow_common
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.startTwoShadow A strategy hwin state hreachable input).2.common =
      package.nextPairAt A strategy hwin state input :=
  rfl

/-- Both local transitions install definitionally the same next guarded pair.
The annotation paired with it is `nextExtraAt`. -/
theorem startShadows_agree
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonShadowsAgree A strategy hwin
      (package.startOneShadow A strategy hwin state hreachable input).2
      (package.startTwoShadow A strategy hwin state hreachable input).2 :=
  rfl

/-- Receiver-side dangerous-pair equation at the selected occurrence. -/
theorem startShadows_outputs
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    ((package.startOneShadow A strategy hwin state hreachable input).1,
      (package.startTwoShadow A strategy hwin state hreachable input).1) =
      (((package.pairAt A strategy hwin state).rightRootRecord A strategy hwin
        input).2.1.physical.closingBoth,
        ((package.pairAt A strategy hwin state).leftRootRecord A strategy hwin
          input).2.1.physical.closingBoth) :=
  profiledRawJointGuardedCommonStartSuccessorShadows_outputs A strategy hwin
    (package.pairAt A strategy hwin state) input
    (package.successorChild A strategy hwin state hreachable input)

end

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
