/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.Synthesis

/-! The component-game proof of constructive decidability.

The public namespace is `Characterisation.ComponentGames`:
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration Characterisation.ComponentGames.Representation.FiniteArena
* `solve` and `solve_correct`: uniform decision from an encoded adversary and LTL instance;
* `synthesize`, `synthesize_complete`, and `synthesize_sound`: executable local
  strategies, existence exactly when realizable, and correctness of the returned strategy;
* `Consensus.encodedConsensusBound_correct`: the computed positive bound works
  for every live residual language;
* `HistoryGame` and `Representation`: literal component games, their finite
  representations, and both strategy transfers.

All model types and automata infrastructure are reused from the library.
The new game definitions describe the manuscript's replacement-before-extension
moves. They do not redefine finite sets, views, LTL, or distributed executions.
See README.md in this directory for the paper correspondence and use examples.
-/
