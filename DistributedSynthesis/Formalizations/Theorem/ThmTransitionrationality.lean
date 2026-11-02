/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefTreeAutomata

/-!
# Transition-rational regular-tree theorem

This file isolates the controller-exposing regular-tree rationality interface.
For an input-free parity tree automaton, nonemptiness of its accepted tree
language yields an accepted rational tree with an explicit finite transition
graph.
-/

namespace DistributedSynthesis

universe u v w

/--
External regular-tree rationality theorem in transition form.

The mathematical content is packaged as the `transitionRationality` field of
`InputFreeParityTreeAutomaton`; this theorem is the standalone module-level
form used by the Bérard finite-memory interface.
-/
theorem inputFreeParityTreeAutomaton_transitionRationality
    {Branch : Type u} {Alphabet : Type v}
    (A : InputFreeParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (haccepts : ∃ tree : LabeledTree Branch Alphabet, A.acceptsTree tree) :
    TransitionRationalAcceptedBy A := by
  exact A.transitionRationality haccepts

/--
Existential form of the transition-rational theorem, exposing the witness
directly.
-/
theorem inputFreeParityTreeAutomaton_transitionRationality_exists
    {Branch : Type u} {Alphabet : Type v}
    (A : InputFreeParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (haccepts : ∃ tree : LabeledTree Branch Alphabet, A.acceptsTree tree) :
    ∃ rationalTree : TransitionRationalTree.{u, v, w} Branch Alphabet,
      A.acceptsTree rationalTree.labeledTree := by
  exact A.transitionRationality haccepts

end DistributedSynthesis
