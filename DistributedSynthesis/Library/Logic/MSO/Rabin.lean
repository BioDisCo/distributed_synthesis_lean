/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.ToTreeAutomaton
import DistributedSynthesis.Library.Logic.MSO.FromTreeAutomaton

/-! # Rabin's MSO/tree-automata equivalence

For a finite nonempty direction set and a finite alphabet, a language of full
infinite labelled trees is MSO-definable exactly when it is recognized by a
nondeterministic parity tree automaton. This is the semantic language
characterization; the noncomputable translations are not an executable compiler.
-/
namespace DistributedSynthesis.MSO.Tree

variable {Branch Alphabet : Type*} [Fintype Branch] [Nonempty Branch] [Fintype Alphabet]

/-- Semantic Rabin equivalence, with no compiler or determinacy certificate
supplied as a hypothesis. -/
theorem definable_iff_recognizable (L : Set (LabeledTree Branch Alphabet)) :
    (∃ φ : Sentence (language Branch Alphabet), ∀ tree, Satisfies tree φ ↔ tree ∈ L) ↔
      ∃ A : RunParityTreeAutomaton.{_, _, 0} Branch Alphabet,
        ∀ tree, A.acceptsTree tree ↔ tree ∈ L := by
  constructor
  · rintro ⟨φ,correct⟩
    exact ⟨sentenceAutomaton φ,fun tree => (sentenceAutomaton_correct φ tree).trans (correct tree)⟩
  · rintro ⟨A,correct⟩
    exact ⟨ofAutomaton A,fun tree => (ofAutomaton_correct A tree).trans (correct tree)⟩

/-- Translating an automaton to MSO and back preserves its entire language. -/
theorem automaton_roundtrip (A : RunParityTreeAutomaton Branch Alphabet)
    (tree : LabeledTree Branch Alphabet) :
    (sentenceAutomaton (ofAutomaton A)).acceptsTree tree ↔ A.acceptsTree tree :=
  (sentenceAutomaton_correct (ofAutomaton A) tree).trans (ofAutomaton_correct A tree)

/-- Translating a sentence to an automaton and back preserves its meaning. -/
theorem sentence_roundtrip (φ : Sentence (language Branch Alphabet))
    (tree : LabeledTree Branch Alphabet) :
    Satisfies tree (ofAutomaton (sentenceAutomaton φ)) ↔ Satisfies tree φ :=
  (ofAutomaton_correct (sentenceAutomaton φ) tree).trans (sentenceAutomaton_correct φ tree)

end DistributedSynthesis.MSO.Tree
