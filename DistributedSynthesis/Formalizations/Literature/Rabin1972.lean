/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmParityTreeEmptinessGame

/-!
# Rabin (1972): the regular-tree basis theorem

**Source.**  M. O. Rabin, *Automata on Infinite Objects and Church's
Problem*, AMS Regional Conference Series 13, 1972 (basis theorem for tree
automata; the underlying tree-automata theory is Rabin 1969).

**Statement.**  A tree automaton with a nonempty language accepts a regular
(finitely generated) tree.

**Status: PROVEN.**  Machine-checked in this development
(`ThmParityTreeEmptinessGame.lean`) for run-based parity tree automata,
via the checked Zielonka determinacy of the emptiness game: a positional
Even strategy of the emptiness game is literally a transition-rational
tree.  This theorem is the sole source of finite-memory in the journal
plan machinery (`t.Control`); no finite-memory import from synthesis
literature is used for it.  This file only re-exports it under its
literature name.
-/

namespace DistributedSynthesis

namespace Literature

namespace Rabin

universe u v w

/-- The regular-tree basis theorem: nonempty run-based parity tree automata
accept a transition-rational tree.  Re-export of the checked
`exists_transitionRational_accepted`. -/
theorem regular_basis {Branch : Type u} {Alphabet : Type v}
    [Fintype Branch] [Fintype Alphabet]
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (haccepts : ∃ tree : LabeledTree Branch Alphabet, A.acceptsTree tree) :
    ∃ rationalTree : TransitionRationalTree.{u, v, w} Branch Alphabet,
      A.acceptsTree rationalTree.labeledTree :=
  A.exists_transitionRational_accepted haccepts

end Rabin

end Literature

end DistributedSynthesis
