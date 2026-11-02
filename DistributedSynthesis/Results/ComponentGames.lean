/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.Main

/-! Constructive decidability through the Paper component games.

`Characterisation.ComponentGames.solve_correct` decides the original
`WithInputs.Realizable` predicate. `synthesize_complete` and `synthesize_sound`
certify actual returned `WithInputs.Strategies`, with arbitrary perfect recall
and full LTL including next-time. Both the adversary table and formula are inputs.

The model has three communication graphs and finite nonempty input/output
alphabets. The adversary is supplied as an encoded deterministic parity automaton
whose geometric language image is nowhere dense. That promise is used only to
prove termination of the consensus-bound search and is erased from execution.

The implementation is executable and its semantic correctness is proved.
This entry point does not assert a new numeric `Primrec` theorem or an efficiency
bound. The existing independent PeriodicBlocks decision route remains available.
-/
