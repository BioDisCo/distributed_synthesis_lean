/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefEpochAbstractions
import DistributedSynthesis.Formalizations.Lemma.LemReversalregulartransduction

/-!
# Handoff soundness as a finite regular check
-/

namespace DistributedSynthesis

universe u v w x y z

/-- The successor test for a tuple and target atom is nonempty. -/
def HandoffSuccessorNonempty
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂)
    (d : Proc)
    (tuple : DirectReversalTuple Atom In₁ In₂ Out₁ Out₂ d)
    (target : Atom d.other) :
    Prop :=
  ∃ oldPath, oldPath ∈ tests.successorTest d tuple target

/--
Semantic handoff invariant: for every old tuple, all realized successor tests
land in the atom returned by the handoff map.
-/
def HandoffSemanticInvariant
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂)
    (handoff :
      (d : Proc) ->
        DirectReversalTuple Atom In₁ In₂ Out₁ Out₂ d ->
        Atom d.other) :
    Prop :=
  ∀ d tuple target oldPath,
    oldPath ∈ tests.successorTest d tuple target ->
      target = handoff d tuple

/-- Construct the paper's finite handoff object from a map and its semantic invariant. -/
def finiteDirectReversalHandoffOf
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂)
    (handoff :
      (d : Proc) ->
        DirectReversalTuple Atom In₁ In₂ Out₁ Out₂ d ->
        Atom d.other) :
    FiniteDirectReversalHandoff Atom In₁ In₂ Out₁ Out₂ where
  handoff := handoff
  invariant := HandoffSemanticInvariant tests handoff

/--
Finite exclusion checks used by `prop:handoffregularcheck`: every atom different
from the proposed target has empty successor test.
-/
def HandoffExclusionCheck
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂)
    (handoff :
      (d : Proc) ->
        DirectReversalTuple Atom In₁ In₂ Out₁ Out₂ d ->
        Atom d.other) :
    Prop :=
  ∀ d tuple target,
    target ≠ handoff d tuple ->
      ∀ oldPath, oldPath ∉ tests.successorTest d tuple target

/--
Proposition `prop:handoffregularcheck`, semantic core: the finite family of
regular emptiness checks is exactly what is needed to prove a proposed handoff
map sound.
-/
theorem handoff_exclusion_check_implies_invariant
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂)
    (handoff :
      (d : Proc) ->
        DirectReversalTuple Atom In₁ In₂ Out₁ Out₂ d ->
        Atom d.other)
    (hcheck : HandoffExclusionCheck tests handoff) :
    (finiteDirectReversalHandoffOf tests handoff).invariant := by
  intro d tuple target oldPath hmem
  by_cases htarget : target = handoff d tuple
  · exact htarget
  · exact False.elim ((hcheck d tuple target htarget oldPath) hmem)

/--
Paper-facing form: after the finite regular-language checks succeed, the
proposed family is a finite direct-reversal handoff, and its invariant is
decidable by the exhibited proof.
-/
theorem handoff_regular_check_sound
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂)
    (handoff :
      (d : Proc) ->
        DirectReversalTuple Atom In₁ In₂ Out₁ Out₂ d ->
        Atom d.other)
    (hcheck : HandoffExclusionCheck tests handoff) :
    Nonempty (FiniteDirectReversalHandoff Atom In₁ In₂ Out₁ Out₂) ∧
      Nonempty (Decidable (finiteDirectReversalHandoffOf tests handoff).invariant) := by
  refine ⟨⟨finiteDirectReversalHandoffOf tests handoff⟩, ?_⟩
  exact ⟨isTrue (handoff_exclusion_check_implies_invariant tests handoff hcheck)⟩

end DistributedSynthesis
