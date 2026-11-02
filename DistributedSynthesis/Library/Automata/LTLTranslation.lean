/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmLTLAPASemanticBridge

/-! # Canonical LTL-to-parity translation
`DistributedSynthesis.PositiveLTL.canonicalLTLToDPACompiler` has a checked language-correctness
field, through the weak alternating-automaton route. It is currently declared
`noncomputable`; this API does not assert a primitive-recursive encoded
LTL-to-DPA algorithm. General APA conversion certificates retain their premises.
The pipeline imports generic automata/support/game modules, not the mixed synthesis backend. This dependency boundary is checked transitively. -/
