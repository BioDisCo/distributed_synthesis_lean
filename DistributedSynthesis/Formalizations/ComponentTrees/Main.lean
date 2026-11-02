/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.BoundedRepresentation
import DistributedSynthesis.Formalizations.ComponentTrees.RankMinimal
import DistributedSynthesis.Formalizations.ComponentTrees.CompressedEquivalence
import DistributedSynthesis.Formalizations.ComponentTrees.SynthesisAutomaton
import DistributedSynthesis.Formalizations.ComponentTrees.FiniteRunMSO
import DistributedSynthesis.Formalizations.ComponentTrees.FiniteAlphabet
import DistributedSynthesis.Formalizations.ComponentTrees.GeneratingEncode
import DistributedSynthesis.Formalizations.ComponentTrees.Synthesis

/-! Component-tree proofs corresponding to the current `main.tex`.

Exports view-complex maps and extensions, the broadcaster proof of bounded
common views, state-preserving reductions, endpoint-table compression,
unique coverage by uncompressed nodes, and the complete bounded-
representation equivalence. Both recursive constructions follow the paper;
the reverse direction also has a verified executable implementation.

The full LTL equivalence, finite-alphabet MSO characterization, both recursive
model/tree transports, and finite model extraction are checked. The executable
`Effective.solve` and `Effective.synthesize` implement the complete tree-based
decision and synthesis route. See README.md for the statement-by-statement
correspondence and representation details.
-/
