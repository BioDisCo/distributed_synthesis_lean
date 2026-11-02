/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonInstalledMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedInitialState
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedProvenancePolicy

/-!
# Replacing one common round by either strict shadow

After a simultaneous common-policy transition, install the provenance source
at the finite successor control.  Projecting that common source to either
singleton lane gives exactly the one-sided code that the preceding installed
move would have produced on the locally indistinguishable strict alternative.

This is a proof-side replacement statement.  The selected side is not a
field of either process's controller and no process is told the graph or a
strict leader.
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

/-! ## The purely finite projection calculation -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Keeping only the left lane of a common world with a prescribed full
incidence code is the right-actual projection of that prescribed code. -/
theorem ProfiledRawJointCommonBaseWorld.leftSingleton_code_eq_rightActual
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : (profiledRawJointCommonWorldFamily A world).incidenceCode A =
      code) :
    (world.oneSidedState A .left).code A =
      { family :=
          { right := fun _ => none
            left := code.family.left
            rightPattern := fun _ _ => false
            leftPattern := code.family.leftPattern }
        cross := fun _ _ => false } := by
  have hleft := congrArg
    (fun current : ProfiledRawJointIncidenceCode A (I := Unit) ↦
      current.family.left) hcode
  have hleftPattern := congrArg
    (fun current : ProfiledRawJointIncidenceCode A (I := Unit) ↦
      current.family.leftPattern) hcode
  apply ProfiledRawJointIncidenceCode.eq_of_fields A
  · apply ProfiledRawJointFamilyCode.eq_of_fields A
    · rfl
    · simpa [ProfiledRawJointSemanticFamily.incidenceCode] using hleft
    · rfl
    · simpa [ProfiledRawJointSemanticFamily.incidenceCode] using hleftPattern
  · rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Keeping only the right lane is the left-actual mirror. -/
theorem ProfiledRawJointCommonBaseWorld.rightSingleton_code_eq_leftActual
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : (profiledRawJointCommonWorldFamily A world).incidenceCode A =
      code) :
    (world.oneSidedState A .right).code A =
      { family :=
          { right := code.family.right
            left := fun _ => none
            rightPattern := code.family.rightPattern
            leftPattern := fun _ _ => false }
        cross := fun _ _ => false } := by
  have hright := congrArg
    (fun current : ProfiledRawJointIncidenceCode A (I := Unit) ↦
      current.family.right) hcode
  have hrightPattern := congrArg
    (fun current : ProfiledRawJointIncidenceCode A (I := Unit) ↦
      current.family.rightPattern) hcode
  apply ProfiledRawJointIncidenceCode.eq_of_fields A
  · apply ProfiledRawJointFamilyCode.eq_of_fields A
    · simpa [ProfiledRawJointSemanticFamily.incidenceCode] using hright
    · rfl
    · simpa [ProfiledRawJointSemanticFamily.incidenceCode] using hrightPattern
    · rfl
  · rfl

/-! ## Installed one-round replacement package -/

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {initialCode : ProfiledRawJointHybridCode A}
variable {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
  initialCode}
variable {key : ProfiledRawJointHybridCommonPolicyKey A strategy initialCode
  policy}

/-- Install the provenance source at the actual simultaneous finite-policy
successor. -/
noncomputable def ProfiledRawJointHybridCommonInstalledMove.nextInstalled
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridCommonInstalledMove A strategy initialCode policy
      (ProfiledRawJointHybridCommonInstalledMove.simultaneousSuccessorKey A
        installed input) :=
  Classical.choice
    (nonempty_profiledRawJointHybridCommonInstalledMove A strategy initialCode
      policy
      (ProfiledRawJointHybridCommonInstalledMove.simultaneousSuccessorKey A
        installed input))

/-- Strict-right proof-side direction with the common pivot, empty past, and
the right-block input order. -/
def profiledRawJointCommonOneRoundStrictRight
    (input : In₁ × In₂) :
    ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) :=
  profiledRawJointCommonActualDirection
    { side := .right
      direction := profiledRawJointBothRestartDirection input }

/-- Strict-left mirror. -/
def profiledRawJointCommonOneRoundStrictLeft
    (input : In₁ × In₂) :
    ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) :=
  profiledRawJointCommonActualDirection
    { side := .left
      direction := profiledRawJointBothRestartDirection input }

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The left singleton installed after the simultaneous round has exactly
the strict-right child code of the preceding installed common move. -/
theorem ProfiledRawJointHybridCommonInstalledMove.oneRound_leftReplacement_code
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    let next := installed.nextInstalled A input
    (next.world.oneSidedState A .left).code A =
      profiledRawJointOneSidedNext A key.incidenceCode installed.rawMove
        (profiledRawJointCommonOneRoundStrictRight input) := by
  dsimp only
  let next := installed.nextInstalled A input
  have hprojection := next.world.leftSingleton_code_eq_rightActual A
    (ProfiledRawJointHybridCommonInstalledMove.simultaneousSuccessorKey A
      installed input).incidenceCode
    next.incidence_eq
  simpa [ProfiledRawJointHybridCommonInstalledMove.simultaneousSuccessorKey,
    ProfiledRawJointHybridCommonInstalledMove.simultaneousChildCode,
    profiledRawJointCommonOneRoundStrictRight,
    profiledRawJointCommonActualDirection,
    profiledRawJointForceBothPivots,
    profiledRawJointOneSidedNext,
    profiledRawJointRightActualIncidenceNext,
    profiledRawJointRightActualFamilyNext] using hprojection

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The right singleton is the strict-left mirror. -/
theorem ProfiledRawJointHybridCommonInstalledMove.oneRound_rightReplacement_code
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    let next := installed.nextInstalled A input
    (next.world.oneSidedState A .right).code A =
      profiledRawJointOneSidedNext A key.incidenceCode installed.rawMove
        (profiledRawJointCommonOneRoundStrictLeft input) := by
  dsimp only
  let next := installed.nextInstalled A input
  have hprojection := next.world.rightSingleton_code_eq_leftActual A
    (ProfiledRawJointHybridCommonInstalledMove.simultaneousSuccessorKey A
      installed input).incidenceCode
    next.incidence_eq
  simpa [ProfiledRawJointHybridCommonInstalledMove.simultaneousSuccessorKey,
    ProfiledRawJointHybridCommonInstalledMove.simultaneousChildCode,
    profiledRawJointCommonOneRoundStrictLeft,
    profiledRawJointCommonActualDirection,
    profiledRawJointForceBothPivots,
    profiledRawJointOneSidedNext,
    profiledRawJointLeftActualIncidenceNext,
    profiledRawJointLeftActualFamilyNext] using hprojection

/-! ## Fresh recurrent-policy handoff -/

/-- Canonical left-singleton replacement source installed at the common
successor control. -/
noncomputable def ProfiledRawJointHybridCommonInstalledMove.leftReplacementState
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  ((ProfiledRawJointHybridCommonInstalledMove.nextInstalled A installed
    input).world).oneSidedState A .left

/-- Canonical right-singleton mirror. -/
noncomputable def ProfiledRawJointHybridCommonInstalledMove.rightReplacementState
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  ((ProfiledRawJointHybridCommonInstalledMove.nextInstalled A installed
    input).world).oneSidedState A .right

/-- The complete one-round replacement handoff.  Both recurrent policies are
freshly rationalized from literal singleton semantic sources; no policy is
spliced from an independently selected predecessor. -/
structure ProfiledRawJointHybridCommonOneRoundReplacementPackage
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) where
  leftState : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)
  rightState : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)
  leftState_eq : leftState = installed.leftReplacementState A input
  rightState_eq : rightState = installed.rightReplacementState A input
  left_code : leftState.code A =
    profiledRawJointOneSidedNext A key.incidenceCode installed.rawMove
      (profiledRawJointCommonOneRoundStrictRight input)
  right_code : rightState.code A =
    profiledRawJointOneSidedNext A key.incidenceCode installed.rawMove
      (profiledRawJointCommonOneRoundStrictLeft input)
  leftPolicy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (leftState.code A)
  rightPolicy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (rightState.code A)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A winning original strategy supplies both fresh recurrent policies at
every reachable common control and every simultaneous input pair. -/
theorem nonempty_profiledRawJointHybridCommonOneRoundReplacementPackage
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    Nonempty (ProfiledRawJointHybridCommonOneRoundReplacementPackage A
      installed input) := by
  let leftState := installed.leftReplacementState A input
  let rightState := installed.rightReplacementState A input
  let leftPolicy := Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy
      hwin leftState)
  let rightPolicy := Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy
      hwin rightState)
  refine ⟨{
    leftState := leftState
    rightState := rightState
    leftState_eq := rfl
    rightState_eq := rfl
    left_code := ?_
    right_code := ?_
    leftPolicy := leftPolicy
    rightPolicy := rightPolicy }⟩
  · simpa [leftState,
      ProfiledRawJointHybridCommonInstalledMove.leftReplacementState] using
      ProfiledRawJointHybridCommonInstalledMove.oneRound_leftReplacement_code
        A installed input
  · simpa [rightState,
      ProfiledRawJointHybridCommonInstalledMove.rightReplacementState] using
      ProfiledRawJointHybridCommonInstalledMove.oneRound_rightReplacement_code
        A installed input

end

end DetParityAutomaton

end DistributedSynthesis
