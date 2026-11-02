/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridProvenancePolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedInitialState
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefRootPinnedRationalPolicy

/-!
# Exact root pinning for the initial hybrid semantic tree

Finite-code rationalization need not forget which complete move occurs at the
fresh hybrid root.  The generic root guard can pin the literal common semantic
move once, while all descendants immediately use the ordinary finite-code
transition predicate.

For every finite first input pair this file selects such a guarded policy,
recovers its literal semantic source, and exposes the exact simultaneous and
strict child-code equations.  The pinned move is proof-side root data; no
graph, orientation, or leader field is supplied to a runtime process.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

/-! ## Reusable hybrid root pinning -/

/-- A provenance-strengthened hybrid finite-code policy with one predicate
checked only at the fresh semantic root. -/
noncomputable abbrev ProfiledRawJointHybridRootPinnedProvenancePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (RootPred : ProfiledRawJointHybridMove A → Prop) :=
  SourceFreeBeliefFiniteCodeRootPinnedPolicy
    (profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)))
    (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridNext A) RootPred

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Any predicate true of the literal common semantic move survives
finite-code rationalization at that root. -/
theorem nonempty_profiledRawJointHybridRootPinnedProvenancePolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (RootPred : ProfiledRawJointHybridMove A → Prop)
    (hroot : RootPred
      ((ProfiledRawJointHybridSemanticState.common initial).move A)) :
    Nonempty (ProfiledRawJointHybridRootPinnedProvenancePolicy A strategy
      initial RootPred) := by
  let raw := profiledRawJointHybridSemanticTree A initial
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  let certificate :=
    profiledRawJointHybridSemanticTree_codeParityCertificate A strategy hwin
      initial
  exact certificate.nonempty_finiteCodeDirectionRootPinnedRationalPolicy
    (profiledRawJointHybridCodeParityDPA A initialCode)
    initialCode (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridNext A) raw RootPred hroot

/-- Semantic provenance inverts the guarded root move into one literal hybrid
state. -/
noncomputable def profiledRawJointHybridRootPinnedSelectedSource
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (RootPred : ProfiledRawJointHybridMove A → Prop)
    (package : ProfiledRawJointHybridRootPinnedProvenancePolicy A strategy
      initial RootPred) :
    ProfiledRawJointHybridSemanticState A strategy :=
  Classical.choose package.rootMove_realizes.1

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The selected semantic source has the advertised fresh-root code. -/
theorem profiledRawJointHybridRootPinnedSelectedSource_code
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (RootPred : ProfiledRawJointHybridMove A → Prop)
    (package : ProfiledRawJointHybridRootPinnedProvenancePolicy A strategy
      initial RootPred) :
    (profiledRawJointHybridRootPinnedSelectedSource A strategy initial RootPred
      package).code A =
      .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A) :=
  (Classical.choose_spec package.rootMove_realizes.1).1

/-- Its complete semantic move is exactly the move installed by the guarded
policy. -/
theorem profiledRawJointHybridRootPinnedSelectedSource_move
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (RootPred : ProfiledRawJointHybridMove A → Prop)
    (package : ProfiledRawJointHybridRootPinnedProvenancePolicy A strategy
      initial RootPred) :
    (profiledRawJointHybridRootPinnedSelectedSource A strategy initial RootPred
      package).move A = package.rootMove :=
  (Classical.choose_spec package.rootMove_realizes.1).2

/-- Every literal raw direction of the selected source is represented by the
exact finite child-code successor at the guarded root. -/
theorem profiledRawJointHybridRootPinned_successor_eq_selectedChild
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (RootPred : ProfiledRawJointHybridMove A → Prop)
    (package : ProfiledRawJointHybridRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (direction : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂)) :
    let initialCode : ProfiledRawJointHybridCode A :=
      .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
    let selected := profiledRawJointHybridRootPinnedSelectedSource A strategy
      initial RootPred package
    let childCode := profiledRawJointHybridNext A (selected.code A)
      (selected.move A) direction
    package.policy.successor
        (true,
          (sourceFreeBeliefCodeParityRunAutomaton
            (profiledRawJointHybridCodeParityDPA A initialCode)
            initialCode (ProfiledRawJointHybridProvenanceValid A strategy)
            (profiledRawJointHybridFiniteCodeNext A)).initial)
        childCode =
      (false,
        (childCode,
          (profiledRawJointHybridCodeParityDPA A initialCode).step
            (profiledRawJointHybridCodeParityDPA A initialCode).initial
            childCode)) := by
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  let selected := profiledRawJointHybridRootPinnedSelectedSource A strategy
    initial RootPred package
  let childCode := profiledRawJointHybridNext A (selected.code A)
    (selected.move A) direction
  have hcode : selected.code A = initialCode :=
    profiledRawJointHybridRootPinnedSelectedSource_code A strategy initial
      RootPred package
  have hmove : selected.move A = package.rootMove :=
    profiledRawJointHybridRootPinnedSelectedSource_move A strategy initial
      RootPred package
  have hfinite :
      profiledRawJointHybridFiniteCodeNext A initialCode package.rootMove
          childCode = childCode := by
    dsimp only [childCode]
    rw [hcode, hmove]
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (profiledRawJointHybridNext A) initialCode package.rootMove direction
  have hsuccessor := package.rootMove_realizes.2.2 childCode
  have hfinite' :
      sourceFreeBeliefFiniteCodeNext (profiledRawJointHybridNext A)
          initialCode package.rootMove childCode = childCode := hfinite
  rw [hfinite'] at hsuccessor
  exact hsuccessor

end

/-! ## Exact policy at every first input pair -/

/-- The literal common world reached by the physical first simultaneous
round with this input pair. -/
abbrev ProfiledRawJointHybridInitialRootPinnedWorld
    (input : In₁ × In₂) :=
  profiledRawJointInitialCommonBaseWorld A strategy input.1 input.2

/-- Its tagged finite code. -/
abbrev ProfiledRawJointHybridInitialRootPinnedCode
    (input : In₁ × In₂) : ProfiledRawJointHybridCode A :=
  .common ((profiledRawJointCommonWorldFamily A
    (ProfiledRawJointHybridInitialRootPinnedWorld A strategy input)
    ).incidenceCode A)

/-- The complete literal hybrid move at that root. -/
abbrev ProfiledRawJointHybridInitialLiteralMove
    (input : In₁ × In₂) : ProfiledRawJointHybridMove A :=
  (ProfiledRawJointHybridSemanticState.common
    (ProfiledRawJointHybridInitialRootPinnedWorld A strategy input)).move A

/-- The underlying complete two-lane move before the live/dead option tag. -/
abbrev ProfiledRawJointHybridInitialLiteralRawMove
    (input : In₁ × In₂) :
    ProfiledRawJointLambdaFamilyMove A (I := Unit) :=
  (profiledRawJointCommonWorldFamily A
    (ProfiledRawJointHybridInitialRootPinnedWorld A strategy input)).move A

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂]

@[simp] theorem profiledRawJointHybridInitialLiteralMove_eq_some
    (input : In₁ × In₂) :
    ProfiledRawJointHybridInitialLiteralMove A strategy input =
      some (ProfiledRawJointHybridInitialLiteralRawMove A strategy input) :=
  rfl

/-- The right lane of the common move is exactly the literal right one-sided
root lane.  This is an equality of proof-side data, not a side signal exposed
to either process. -/
@[simp] theorem profiledRawJointHybridInitialLiteralRawMove_rightLane
    (input : In₁ × In₂) :
    (ProfiledRawJointHybridInitialLiteralRawMove A strategy input
      ).rightLambda () =
      (((ProfiledRawJointHybridInitialRootPinnedWorld A strategy input
        ).oneSidedState A .right).move A).rightLambda () :=
  rfl

/-- Left-lane mirror. -/
@[simp] theorem profiledRawJointHybridInitialLiteralRawMove_leftLane
    (input : In₁ × In₂) :
    (ProfiledRawJointHybridInitialLiteralRawMove A strategy input
      ).leftLambda () =
      (((ProfiledRawJointHybridInitialRootPinnedWorld A strategy input
        ).oneSidedState A .left).move A).leftLambda () :=
  rfl

end

/-- Exact one-shot root predicate. -/
def profiledRawJointHybridInitialExactRootPredicate
    (input : In₁ × In₂) (move : ProfiledRawJointHybridMove A) : Prop :=
  move = ProfiledRawJointHybridInitialLiteralMove A strategy input

/-- The exact root-pinned policy type at one first input pair. -/
noncomputable abbrev ProfiledRawJointHybridInitialRootPinnedPolicy
    (input : In₁ × In₂) :=
  ProfiledRawJointHybridRootPinnedProvenancePolicy A strategy
    (ProfiledRawJointHybridInitialRootPinnedWorld A strategy input)
    (profiledRawJointHybridInitialExactRootPredicate A strategy input)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The hybrid code-parity certificate unconditionally supplies the exact
root-pinned policy. -/
theorem nonempty_profiledRawJointHybridInitialRootPinnedPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (input : In₁ × In₂) :
    Nonempty (ProfiledRawJointHybridInitialRootPinnedPolicy A strategy input) :=
  nonempty_profiledRawJointHybridRootPinnedProvenancePolicy A strategy hwin
    (ProfiledRawJointHybridInitialRootPinnedWorld A strategy input)
    (profiledRawJointHybridInitialExactRootPredicate A strategy input) rfl

/-- Select the exact root-pinned policy once for this finite input pair. -/
noncomputable def profiledRawJointHybridInitialRootPinnedPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (input : In₁ × In₂) :
    ProfiledRawJointHybridInitialRootPinnedPolicy A strategy input :=
  Classical.choice
    (nonempty_profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin
      input)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The selected guarded policy installs the complete literal common move. -/
theorem profiledRawJointHybridInitialRootPinnedPolicy_rootMove
    (input : In₁ × In₂) :
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin input
      ).rootMove =
      ProfiledRawJointHybridInitialLiteralMove A strategy input :=
  (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin input
    ).rootMove_realizes.2.1

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Expanded form: the selected policy pins the complete two-lane literal
move, rather than merely one of its projections. -/
theorem profiledRawJointHybridInitialRootPinnedPolicy_rootMove_eq_some
    (input : In₁ × In₂) :
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin input
      ).rootMove =
      some (ProfiledRawJointHybridInitialLiteralRawMove A strategy input) :=
  profiledRawJointHybridInitialRootPinnedPolicy_rootMove A strategy hwin input

/-- Literal semantic source selected by the exact guarded root. -/
noncomputable def profiledRawJointHybridInitialRootPinnedSelectedSource
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (input : In₁ × In₂) :
    ProfiledRawJointHybridSemanticState A strategy :=
  profiledRawJointHybridRootPinnedSelectedSource A strategy
    (ProfiledRawJointHybridInitialRootPinnedWorld A strategy input)
    (profiledRawJointHybridInitialExactRootPredicate A strategy input)
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin input)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridInitialRootPinnedSelectedSource_code
    (input : In₁ × In₂) :
    (profiledRawJointHybridInitialRootPinnedSelectedSource A strategy hwin
      input).code A =
      ProfiledRawJointHybridInitialRootPinnedCode A strategy input :=
  profiledRawJointHybridRootPinnedSelectedSource_code A strategy
    (ProfiledRawJointHybridInitialRootPinnedWorld A strategy input)
    (profiledRawJointHybridInitialExactRootPredicate A strategy input)
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin input)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridInitialRootPinnedSelectedSource_move
    (input : In₁ × In₂) :
    (profiledRawJointHybridInitialRootPinnedSelectedSource A strategy hwin
      input).move A =
      ProfiledRawJointHybridInitialLiteralMove A strategy input := by
  unfold profiledRawJointHybridInitialRootPinnedSelectedSource
  rw [profiledRawJointHybridRootPinnedSelectedSource_move A strategy]
  exact profiledRawJointHybridInitialRootPinnedPolicy_rootMove A strategy hwin
    input

/-! ## Exact first-child code equations -/

/-- The finite code of one literal simultaneous continuation. -/
noncomputable def profiledRawJointHybridInitialSimultaneousChildCode
    (first current : In₁ × In₂) : ProfiledRawJointHybridCode A :=
  profiledRawJointHybridNext A
    (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
    (ProfiledRawJointHybridInitialLiteralMove A strategy first)
    (.simultaneous current)

/-- The finite code of one literal first strict continuation. -/
noncomputable def profiledRawJointHybridInitialStrictChildCode
    (first : In₁ × In₂)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridCode A :=
  profiledRawJointHybridNext A
    (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
    (ProfiledRawJointHybridInitialLiteralMove A strategy first)
    (.strict actual)

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂]

/-- The strict child is definitionally the exact one-sided transition of the
complete common move. -/
theorem profiledRawJointHybridInitialStrictChildCode_eq_oneSidedNext
    (first : In₁ × In₂)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridInitialStrictChildCode A strategy first actual =
      .oneSided (profiledRawJointOneSidedNext A
        ((profiledRawJointCommonWorldFamily A
          (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first)
          ).incidenceCode A)
        (ProfiledRawJointHybridInitialLiteralRawMove A strategy first)
        (profiledRawJointCommonActualDirection actual)) :=
  rfl

/-- The named simultaneous child is the literal semantic successor code. -/
theorem profiledRawJointHybridInitialSimultaneousChildCode_eq_semantic
    (first current : In₁ × In₂) :
    profiledRawJointHybridInitialSimultaneousChildCode A strategy first
        current =
      ((ProfiledRawJointHybridSemanticState.common
        (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first)
        ).step A (.simultaneous current)).code A := by
  exact (ProfiledRawJointHybridSemanticState.step_code A
    (.common
      (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first))
    (.simultaneous current)).symm

/-- The named strict child is likewise the literal semantic successor code. -/
theorem profiledRawJointHybridInitialStrictChildCode_eq_semantic
    (first : In₁ × In₂)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridInitialStrictChildCode A strategy first actual =
      ((ProfiledRawJointHybridSemanticState.common
        (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first)
        ).step A (.strict actual)).code A := by
  exact (ProfiledRawJointHybridSemanticState.step_code A
    (.common
      (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first))
    (.strict actual)).symm

end

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The guarded root table contains the exact simultaneous child code. -/
theorem profiledRawJointHybridInitialRootPinnedPolicy_successor_simultaneous
    (first current : In₁ × In₂) :
    let package :=
      profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
    let initialCode :=
      ProfiledRawJointHybridInitialRootPinnedCode A strategy first
    let childCode := profiledRawJointHybridInitialSimultaneousChildCode A
      strategy first current
    package.policy.successor
        (true,
          (sourceFreeBeliefCodeParityRunAutomaton
            (profiledRawJointHybridCodeParityDPA A initialCode)
            initialCode (ProfiledRawJointHybridProvenanceValid A strategy)
            (profiledRawJointHybridFiniteCodeNext A)).initial)
        childCode =
      (false,
        (childCode,
          (profiledRawJointHybridCodeParityDPA A initialCode).step
            (profiledRawJointHybridCodeParityDPA A initialCode).initial
            childCode)) := by
  simpa only [profiledRawJointHybridInitialSimultaneousChildCode,
    profiledRawJointHybridInitialRootPinnedSelectedSource,
    profiledRawJointHybridRootPinnedSelectedSource_code,
    profiledRawJointHybridRootPinnedSelectedSource_move,
    profiledRawJointHybridInitialRootPinnedPolicy_rootMove] using
    (profiledRawJointHybridRootPinned_successor_eq_selectedChild A strategy
      (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first)
      (profiledRawJointHybridInitialExactRootPredicate A strategy first)
      (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first)
      (.simultaneous current))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Strict-child mirror. -/
theorem profiledRawJointHybridInitialRootPinnedPolicy_successor_strict
    (first : In₁ × In₂)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    let package :=
      profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
    let initialCode :=
      ProfiledRawJointHybridInitialRootPinnedCode A strategy first
    let childCode := profiledRawJointHybridInitialStrictChildCode A strategy
      first actual
    package.policy.successor
        (true,
          (sourceFreeBeliefCodeParityRunAutomaton
            (profiledRawJointHybridCodeParityDPA A initialCode)
            initialCode (ProfiledRawJointHybridProvenanceValid A strategy)
            (profiledRawJointHybridFiniteCodeNext A)).initial)
        childCode =
      (false,
        (childCode,
          (profiledRawJointHybridCodeParityDPA A initialCode).step
            (profiledRawJointHybridCodeParityDPA A initialCode).initial
            childCode)) := by
  simpa only [profiledRawJointHybridInitialStrictChildCode,
    profiledRawJointHybridInitialRootPinnedSelectedSource,
    profiledRawJointHybridRootPinnedSelectedSource_code,
    profiledRawJointHybridRootPinnedSelectedSource_move,
    profiledRawJointHybridInitialRootPinnedPolicy_rootMove] using
    (profiledRawJointHybridRootPinned_successor_eq_selectedChild A strategy
      (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first)
      (profiledRawJointHybridInitialExactRootPredicate A strategy first)
      (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first)
      (.strict actual))

end


end DetParityAutomaton

end DistributedSynthesis
