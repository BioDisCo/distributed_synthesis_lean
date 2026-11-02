/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedSemanticParity
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefFiniteCodeDirection

/-!
# Provenance-strengthened finite-code policy for the one-sided raw joint tree

The finite raw legality predicate alone does not say that the lambda family
selected by a rational policy is the move of any literal semantic state.  In
particular, the local-view lemmas for the original distributed strategy cannot
be applied to a merely syntactically legal move.

This file strengthens legality by retaining, in `Prop`, one one-sided semantic
state with exactly the advertised code and move.  The exact semantic tree
satisfies this strengthened predicate at every node.  We then replace the
possibly infinite raw direction alphabet by the finite child-code alphabet and
apply the checked finite-direction rational-run theorem.

At every reachable policy state, legality inversion consequently installs one
selected move together with a literal semantic source witness.  This is a
source installation theorem only.  The independently installed witness at a
successor code is not asserted to be the literal semantic child of the source;
that edge-continuity/local-representation theorem remains a separate model
obligation.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-! ## Semantic provenance in the legality predicate -/

/-- Raw legality together with one literal one-sided semantic state having
exactly the advertised finite code and raw joint move.  The witness is
proof-erased and adds no runtime state. -/
def ProfiledRawJointOneSidedProvenanceValid
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (code : ProfiledRawJointIncidenceCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I)) : Prop :=
  ProfiledRawJointIncidenceMoveValid A code move ∧
    ∃ source : ProfiledRawJointOneSidedSemanticState A strategy (I := I),
      source.code A = code ∧ source.move A = move

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The exact semantic unfolding satisfies the provenance-strengthened
code-parity certificate. -/
theorem profiledRawJointOneSidedSemanticTree_provenanceCodeParityCertificate
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I)) :
    let raw := profiledRawJointOneSidedSemanticTree A initial
    SourceFreeBeliefCodeParityCertificate
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
      (initial.code A)
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedNext A)
      raw := by
  let raw := profiledRawJointOneSidedSemanticTree A initial
  refine {
    initial_code := rfl
    valid := ?_
    next_code := ?_
    accepts := ?_ }
  · intro node
    refine ⟨profiledRawJointOneSidedSemanticTree_valid A hwin initial node,
      raw.stateAt node, rfl, rfl⟩
  · intro node direction
    exact profiledRawJointOneSidedSemanticTree_next_code A initial node
      direction
  · intro branch
    exact profiledRawJointOneSidedSemanticTree_accepts A strategy hwin initial
      branch

/-! ## Finite child-code policy -/

/-- The raw actual-direction type is inhabited from the finite model data.
The chosen value is used only as the fallback representative of an
unrealizable child-code tag. -/
noncomputable instance profiledRawJointActualDirectionNonempty :
    Nonempty (ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :=
  ⟨{
    side := .right
    direction := {
      rightPivot := (default, .first)
      rightTaggedPast := []
      rightInput := (default, default)
      leftPivot := (default, .first)
      leftTaggedPast := []
      leftInput := (default, default) } }⟩

/-- Finite child-code successor used by the rational policy.  The explicit
signature fixes the raw direction parameters before typeclass synthesis asks
for their `Nonempty` instance. -/
noncomputable def profiledRawJointOneSidedFiniteCodeNext
    (code : ProfiledRawJointIncidenceCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (childCode : ProfiledRawJointIncidenceCode A (I := I)) :
    ProfiledRawJointIncidenceCode A (I := I) :=
  sourceFreeBeliefFiniteCodeNext
    (Direction := ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (profiledRawJointOneSidedNext A) code move childCode

/-- Rational policy obtained from the provenance-strengthened semantic tree
after replacing raw directions by finite child-code tags. -/
noncomputable abbrev ProfiledRawJointOneSidedProvenanceRationalPolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := I)) :=
  SourceFreeBeliefCodeParityRationalPolicy
    (profiledRawJointOneSidedCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointOneSidedProvenanceValid A strategy)
    (profiledRawJointOneSidedFiniteCodeNext A)

/-- Complete finite state of the provenance-strengthened policy. -/
noncomputable abbrev ProfiledRawJointOneSidedProvenancePolicyState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := I)) :=
  (sourceFreeBeliefCodeParityRunAutomaton
    (profiledRawJointOneSidedCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointOneSidedProvenanceValid A strategy)
    (profiledRawJointOneSidedFiniteCodeNext A)).State

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The finite-child-code policy exists unconditionally from the original
winner.  The only rational basis used here is the checked finite-direction
basis inside `nonempty_finiteCodeDirectionRationalPolicy`. -/
theorem nonempty_profiledRawJointOneSidedProvenanceRationalPolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I)) :
    Nonempty
      (ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
        (initial.code A)) := by
  let raw := profiledRawJointOneSidedSemanticTree A initial
  let certificate :=
    profiledRawJointOneSidedSemanticTree_provenanceCodeParityCertificate A
      strategy hwin initial
  exact certificate.nonempty_finiteCodeDirectionRationalPolicy
    (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
    (initial.code A)
    (ProfiledRawJointOneSidedProvenanceValid A strategy)
    (profiledRawJointOneSidedNext A)
    raw

/-! ## Reachable selected-move installation -/

/-- A move realizes the complete finite-child-code successor table at one
policy state. -/
def ProfiledRawJointOneSidedProvenanceMoveRealizesAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := I))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (move : ProfiledRawJointLambdaFamilyMove A (I := I)) : Prop :=
  SourceFreeBeliefCodeParityRationalPolicy.MoveRealizesAt
    (profiledRawJointOneSidedCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointOneSidedProvenanceValid A strategy)
    (profiledRawJointOneSidedFiniteCodeNext A)
    policy state move

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- At every reachable finite policy state, the selected move is installed
on one literal one-sided semantic source with exactly the policy code. -/
theorem exists_profiledRawJointOneSidedProvenanceInstalledMove
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := I))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledRawJointOneSidedCodeParityDPA A initialCode)
      initialCode
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedFiniteCodeNext A)
      policy state) :
    ∃ move : ProfiledRawJointLambdaFamilyMove A (I := I),
      ∃ source : ProfiledRawJointOneSidedSemanticState A strategy (I := I),
        ProfiledRawJointOneSidedProvenanceMoveRealizesAt A strategy
            initialCode policy state move ∧
          source.code A = state.1 ∧ source.move A = move := by
  obtain ⟨move, hmove⟩ :=
    SourceFreeBeliefCodeParityRationalPolicy.exists_sourceFreeMove
      (profiledRawJointOneSidedCodeParityDPA A initialCode)
      initialCode
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedFiniteCodeNext A)
      policy state hreachable
  rcases hmove.1.2 with ⟨source, hcode, hsourceMove⟩
  exact ⟨move, source, hmove, hcode, hsourceMove⟩

/-- Root-specialized installation. -/
theorem exists_profiledRawJointOneSidedProvenanceInitialInstalledMove
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := I))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode) :
    ∃ move : ProfiledRawJointLambdaFamilyMove A (I := I),
      ∃ source : ProfiledRawJointOneSidedSemanticState A strategy (I := I),
        ProfiledRawJointOneSidedProvenanceMoveRealizesAt A strategy
            initialCode policy (policy.run []) move ∧
          source.code A = (policy.run []).1 ∧ source.move A = move := by
  exact exists_profiledRawJointOneSidedProvenanceInstalledMove A strategy
    initialCode policy (policy.run []) ⟨[], rfl⟩

/-- For a literal raw direction from the installed source, use its actual
child code as the finite policy tag.  The policy successor is then exactly
the raw one-sided child code and the corresponding code-DPA step. -/
theorem ProfiledRawJointOneSidedProvenanceMoveRealizesAt.successor_eq_raw
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := I))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (hmove : ProfiledRawJointOneSidedProvenanceMoveRealizesAt A strategy
      initialCode policy state move)
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    let childCode := profiledRawJointOneSidedNext A state.1 move actual
    policy.successor state childCode =
      (childCode,
        (profiledRawJointOneSidedCodeParityDPA A initialCode).step state.2
          childCode) := by
  let childCode := profiledRawJointOneSidedNext A state.1 move actual
  have hsuccessor := hmove.2 childCode
  have hfinite :
      profiledRawJointOneSidedFiniteCodeNext A state.1 move childCode =
        childCode := by
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (profiledRawJointOneSidedNext A) state.1 move actual
  rw [hfinite] at hsuccessor
  exact hsuccessor

end

end

end DetParityAutomaton

end DistributedSynthesis
