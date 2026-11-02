/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefNondeterministicOmegaAutomata
import DistributedSynthesis.Formalizations.Definition.DefMullerAutomata
import DistributedSynthesis.Formalizations.Definition.DefAlternatingAutomata
import DistributedSynthesis.Formalizations.Theorem.ThmDPACombinators
import DistributedSynthesis.Formalizations.Theorem.ThmMullerToDPA

/-! # Word automata
Deterministic parity, nondeterministic Büchi/Streett/Muller, and alternating
automata, with language semantics and the existing combinators/conversions.
Importing a definition does not supply every possible conversion algorithm. -/
