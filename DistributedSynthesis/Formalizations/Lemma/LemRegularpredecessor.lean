/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemReversalregulartransduction

/-!
# Regular predecessor for one-round substitution
-/

namespace DistributedSynthesis

universe u v w x z

/--
The one-round predecessor of a regular successor language under locally
uniform finite substitution.
-/
def OneRoundRegularPredecessor
    {OldEdge : Type u} {NewEdge : Type v} {Label : Type w}
    [Fintype Label]
    (scheme : FiniteSubstitutionScheme.{u, v, w, z} OldEdge NewEdge Label)
    (target : WordDFA.{v, x} NewEdge) :
    Set (List OldEdge) :=
  { oldPath |
    ∃ successor,
      successor ∈ scheme.SuccessorWords oldPath ∧
        target.Accepts successor }

/--
Lemma `lem:regularpredecessor`: the old words that have some locally uniform
one-round substitution into a DFA-recognized successor language are
recognized by an explicitly constructed finite NFA.
-/
theorem regular_predecessor_for_one_round_substitution
    {OldEdge : Type u} {NewEdge : Type v} {Label : Type w}
    [Fintype Label]
    (scheme : FiniteSubstitutionScheme.{u, v, w, z} OldEdge NewEdge Label)
    (target : WordDFA.{v, x} NewEdge) :
    ∃ oldRecognizer : WordNFA.{u, max w x} OldEdge,
      ∀ oldPath,
        oldRecognizer.Accepts oldPath ↔
          oldPath ∈ OneRoundRegularPredecessor scheme target := by
  refine
    ⟨transducerPreimageNFA (substitutionTransducer scheme) target, ?_⟩
  intro oldPath
  rw [transducerPreimageNFA_accepts_iff]
  constructor
  · intro h
    rcases h with ⟨successor, htransducer, htarget⟩
    have hsuccessor :
        successor ∈ scheme.SuccessorWords oldPath := by
      have hmem :
          successor ∈
            ({ output |
              (substitutionTransducer scheme).Accepts oldPath output } :
                Set (List NewEdge)) := htransducer
      simpa [finite_transducer_form_of_one_round_substitution scheme oldPath]
        using hmem
    exact ⟨successor, hsuccessor, htarget⟩
  · intro h
    rcases h with ⟨successor, hsuccessor, htarget⟩
    have htransducer :
        (substitutionTransducer scheme).Accepts oldPath successor := by
      have hmem :
          successor ∈
            ({ output |
              (substitutionTransducer scheme).Accepts oldPath output } :
                Set (List NewEdge)) := by
        simpa [finite_transducer_form_of_one_round_substitution scheme oldPath]
          using hsuccessor
      exact hmem
    exact ⟨successor, htransducer, htarget⟩

end DistributedSynthesis
