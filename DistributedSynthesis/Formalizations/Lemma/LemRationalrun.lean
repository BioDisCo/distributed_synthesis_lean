/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmTransitionrationality

/-!
# Rational-run lemma

This file packages the external regular-tree rationality theorem in the form
used by the paper.
-/

namespace DistributedSynthesis

universe u v w

/--
Lemma `lem:rationalrun`: an input-free parity tree automaton with a finite
alphabet accepts a rational tree whenever it accepts some tree.
-/
theorem rational_run
    {Branch : Type u} {Alphabet : Type v}
    (A : InputFreeParityTreeAutomaton Branch Alphabet)
    (haccepts : ∃ tree : LabeledTree Branch Alphabet, A.acceptsTree tree) :
    RationalAcceptedBy A := by
  exact A.rationality haccepts

/--
Transition-rational strengthening of `rational_run`.

This is the controller-exposing form needed by the reachable finite-memory
construction: the accepted rational tree comes with an initial finite control
state and a branch successor function.
-/
theorem transition_rational_run
    {Branch : Type u} {Alphabet : Type v}
    (A : InputFreeParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (haccepts : ∃ tree : LabeledTree Branch Alphabet, A.acceptsTree tree) :
    TransitionRationalAcceptedBy A := by
  exact inputFreeParityTreeAutomaton_transitionRationality A haccepts

end DistributedSynthesis
