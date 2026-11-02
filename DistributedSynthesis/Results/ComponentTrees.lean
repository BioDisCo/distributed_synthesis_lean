/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.Main

/-! Component-tree proofs corresponding to the current `main.tex`.

Public declarations live in `Characterisation.ComponentTrees`. The API
includes the local view-complex and compression lemmas and the complete
bounded-representation equivalence, with effective reverse construction.
The full LTL equivalence, MSO characterization, recursive model/tree transports,
and finite model extraction are checked. `Effective.solve_correct` decides
original realizability. `Effective.synthesize_complete` and
`Effective.synthesize_sound` certify the returned local output functions.
Both the adversary table and LTL formula are inputs; the nowhere-dense promise
justifies the terminating consensus search. No finite-state implementation
of the distributed strategy is claimed. The independent game APIs remain in
`DistributedSynthesis.Results.ComponentGames`.
-/
