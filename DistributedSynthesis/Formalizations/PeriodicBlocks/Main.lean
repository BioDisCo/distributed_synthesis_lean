/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.Decidability

/-! Independent fixed-block reduction for the positive synthesis theorem.

The principal endpoints are:

* `holes_periodic_primitive_recursive_solver`: a primitive-recursive Boolean
  solver on the original LTL-instance encoding, constructed by this route;
* `holes_periodic_realizable_computable`: decidability under precisely the
  original omega-regularity and graph-hole hypotheses;

* `periodic_block_game_iff`: exact equivalence between the new finite block
  game and distributed realizability of a guarded parity objective;
* `holes_periodic_LTL_characterization`: the corresponding equivalence for
  the paper's original finite-input LTL instances;
* `holes_periodic_LTL_finite_controller`: realizability is equivalent to the
  existence of a finite public controller for the new game.

The construction uses fixed positive-length blocks and bounded compressed
families. It does not assume a bound on the original input-history component.
Soundness constructs local distributed strategies. Completeness constructs
all game moves and proves parity for every compatible compressed thread.

The numeric solver and its correctness proof are also separate. The old
distributed synthesis solver and its correctness theorem are not used.
Generic finite-table, automata, and parity-game algorithms are reused.
-/
