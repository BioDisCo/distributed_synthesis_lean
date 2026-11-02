/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedTreeNonemptiness

namespace DistributedSynthesis.Tests.EncodedTreeNonemptiness
open DistributedSynthesis.EncodedTreeNonemptiness

#guard solve (0, 1, 1, [0], [0], 0)
#guard !(solve (0, 1, 1, [0], [1], 0))
-- No branch means no infinite branch to reject. A root still needs a label.
#guard solve (0, 1, 0, [], [1], 0)
#guard !(solve (0, 0, 1, [], [0], 0))
#guard !(solve (0, 0, 0, [], [0], 0))
-- A transient priority is irrelevant; the eventual component determines parity.
#guard solve (1, 1, 1, [1, 1], [1, 2], 0)
#guard !(solve (1, 1, 1, [1, 1], [0, 1], 0))
-- Controllable and adversarial choices, respectively.
#guard solve (1, 2, 1, [0, 1, 0, 1], [1, 0], 0)
#guard !(solve (1, 1, 2, [0, 1, 0, 1], [0, 1], 0))
-- A winner needs different labels at states zero and one.
#guard solve (2, 2, 1, [1, 0, 1, 2, 2, 2], [1, 1, 0], 0)

def matching : Data := (1, 2, 2, [0, 1, 1, 0, 0, 1, 1, 0], [0, 1], 0)

/-- Deliberately incorrect quantifier order, for a regression comparison only. -/
def reversedOrder (d : Data) : Bool := decide
  (∀ bs ∈ FiniteSearch.tables (branches d) (bound d),
    ∃ ls ∈ FiniteSearch.tables (labels d) (bound d),
      EncodedOrbitParity.Passes (orbitData d ls bs))

#guard !(solve matching)
#guard reversedOrder matching

-- Missing entries and out-of-range state indices follow the specified normalization.
#guard solve (1, 1, 1, [99, 99], [1, 2], 98)
#guard !(solve (1, 1, 1, [99, 99], [2, 1], 98))
#guard solve (0, 1, 1, [], [], 123)

example : Primrec solve := solve_primrec
example : ComputablePred DistributedSynthesis.EncodedTreeNonemptiness.Nonempty := nonempty_computable

example (d : Data) : solve d = true ↔ ∃ tree, (monitor d).toRunAutomaton.acceptsTree tree :=
  solve_correct d

end DistributedSynthesis.Tests.EncodedTreeNonemptiness
