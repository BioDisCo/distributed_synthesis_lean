/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Executable
import DistributedSynthesis.Library.Logic.MSO.ExecutableFromAutomaton

/-! # Effective MSO/parity-tree-automaton translations

`Executable.compile` and `Automaton.Ordered.ofAutomaton` are executable
constructors with correctness theorems. `Executable.satisfiable` and
`Executable.valid` are executable decision procedures. Finite orders in the
reverse interface provide enumeration, not an acceptance oracle.
-/
namespace DistributedSynthesis.MSO.Tree.Executable

variable {Branch Alphabet : Type} [Fintype Branch] [LinearOrder Branch] [Nonempty Branch]
variable [Fintype Alphabet] [LinearOrder Alphabet]

/-- The two executable translations preserve the automaton's language. -/
theorem automaton_roundtrip (A : RunParityTreeAutomaton.{0,0,0} Branch Alphabet)
    [LinearOrder A.State] [∀ q a next, Decidable (A.delta q a next)]
    (tree : LabeledTree Branch Alphabet) :
    (sentenceAutomaton (Automaton.Ordered.ofAutomaton A)).Accepts tree ↔ A.acceptsTree tree :=
  (sentenceAutomaton_correct (Automaton.Ordered.ofAutomaton A) tree).trans
    (Automaton.Ordered.ofAutomaton_correct A tree)

end DistributedSynthesis.MSO.Tree.Executable
