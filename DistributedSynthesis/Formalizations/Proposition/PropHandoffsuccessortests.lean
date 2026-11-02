/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Proposition.PropHandoffregularcheck

/-!
# Handoff from successor-test atoms
-/

namespace DistributedSynthesis

open Classical

universe u v w x y z

/-- For every tuple, at most one target atom has a nonempty successor test. -/
def AtMostOneHandoffSuccessor
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂) :
    Prop :=
  ∀ d tuple target₁ target₂,
    HandoffSuccessorNonempty tests d tuple target₁ ->
      HandoffSuccessorNonempty tests d tuple target₂ ->
        target₁ = target₂

/-- A finite separating witness: one tuple has two distinct realized target atoms. -/
structure HandoffSeparatingWitness
    (EdgeType : Proc -> Type u)
    (Atom : Proc -> Type v)
    (In₁ : Type w) (In₂ : Type x) (Out₁ : Type y) (Out₂ : Type z)
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂) where
  d : Proc
  tuple : DirectReversalTuple Atom In₁ In₂ Out₁ Out₂ d
  target₁ : Atom d.other
  target₂ : Atom d.other
  distinct : target₁ ≠ target₂
  oldPath₁ : TypedPath (EdgeType d)
  oldPath₂ : TypedPath (EdgeType d)
  realizes₁ : oldPath₁ ∈ tests.successorTest d tuple target₁
  realizes₂ : oldPath₂ ∈ tests.successorTest d tuple target₂

/-- The canonical handoff map when every tuple has at most one realized successor. -/
noncomputable def handoffMapFromUniqueSuccessors
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    [∀ d, Inhabited (Atom d)]
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂) :
    (d : Proc) ->
      DirectReversalTuple Atom In₁ In₂ Out₁ Out₂ d ->
      Atom d.other :=
  fun d tuple =>
    if h : ∃ target, HandoffSuccessorNonempty tests d tuple target then
      Classical.choose h
    else
      default

/--
If the successor set is single-valued, the canonical map passes the finite
exclusion checks from `prop:handoffregularcheck`.
-/
theorem unique_successors_give_exclusion_check
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    [∀ d, Inhabited (Atom d)]
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂)
    (hunique : AtMostOneHandoffSuccessor tests) :
    HandoffExclusionCheck tests (handoffMapFromUniqueSuccessors tests) := by
  intro d tuple target hneq oldPath hmem
  by_cases hexists : ∃ target', HandoffSuccessorNonempty tests d tuple target'
  · have hchosen :
        HandoffSuccessorNonempty tests d tuple (Classical.choose hexists) :=
      Classical.choose_spec hexists
    have htarget : HandoffSuccessorNonempty tests d tuple target := ⟨oldPath, hmem⟩
    have heq : target = Classical.choose hexists :=
      hunique d tuple target (Classical.choose hexists) htarget hchosen
    apply hneq
    simpa [handoffMapFromUniqueSuccessors, hexists] using heq
  · exact hexists ⟨target, oldPath, hmem⟩

/--
Proposition `prop:handoffsuccessortests`, positive branch: if the finite
successor tests are single-valued on every tuple, they construct a finite
direct-reversal handoff.
-/
theorem handoff_successor_tests_construct_handoff
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    [∀ d, Inhabited (Atom d)]
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂)
    (hunique : AtMostOneHandoffSuccessor tests) :
    Nonempty (FiniteDirectReversalHandoff Atom In₁ In₂ Out₁ Out₂) ∧
      (finiteDirectReversalHandoffOf tests
        (handoffMapFromUniqueSuccessors tests)).invariant := by
  exact
    ⟨(handoff_regular_check_sound tests (handoffMapFromUniqueSuccessors tests)
        (unique_successors_give_exclusion_check tests hunique)).1,
      handoff_exclusion_check_implies_invariant tests
        (handoffMapFromUniqueSuccessors tests)
        (unique_successors_give_exclusion_check tests hunique)⟩

/-- Non-single-valued successor tests give the finite separating witness. -/
theorem not_unique_successors_give_witness
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂)
    (hnot : ¬ AtMostOneHandoffSuccessor tests) :
    Nonempty (HandoffSeparatingWitness EdgeType Atom In₁ In₂ Out₁ Out₂ tests) := by
  classical
  unfold AtMostOneHandoffSuccessor at hnot
  push Not at hnot
  rcases hnot with ⟨d, tuple, target₁, target₂, hnonempty₁, hnonempty₂, hne⟩
  rcases hnonempty₁ with ⟨oldPath₁, hmem₁⟩
  rcases hnonempty₂ with ⟨oldPath₂, hmem₂⟩
  exact
    ⟨{
      d := d
      tuple := tuple
      target₁ := target₁
      target₂ := target₂
      distinct := hne
      oldPath₁ := oldPath₁
      oldPath₂ := oldPath₂
      realizes₁ := hmem₁
      realizes₂ := hmem₂
    }⟩

/--
Paper-facing dichotomy: successor-test enumeration either constructs a handoff
or returns a finite separating witness.
-/
theorem handoff_successor_tests_dichotomy
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    [∀ d, Inhabited (Atom d)]
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂) :
    (Nonempty (FiniteDirectReversalHandoff Atom In₁ In₂ Out₁ Out₂) ∧
        (finiteDirectReversalHandoffOf tests
          (handoffMapFromUniqueSuccessors tests)).invariant) ∨
      Nonempty (HandoffSeparatingWitness EdgeType Atom In₁ In₂ Out₁ Out₂ tests) := by
  by_cases hunique : AtMostOneHandoffSuccessor tests
  · exact Or.inl (handoff_successor_tests_construct_handoff tests hunique)
  · exact Or.inr (not_unique_successors_give_witness tests hunique)

end DistributedSynthesis
