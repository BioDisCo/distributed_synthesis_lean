# Fixed-length block reduction

`Main.lean` imports the complete fixed-length block reduction.

## Main statements

All declarations below are in namespace `Characterisation.PeriodicBlocks`.

- `holes_periodic_primitive_recursive_solver` in `Decidability.lean` constructs
  a primitive-recursive Boolean solver, uniform in the original LTL instance
  and its four finite alphabets, for each fixed omega-regular adversary with
  graph-only holes.
- `holes_periodic_realizable_computable` proves computable realizability under
  the same hypotheses as the original positive theorem. No additional
  compression, game-solving, or encoding hypothesis is assumed.

- `periodic_block_game_iff` in `Reduction.lean` proves that the new finite
  block game has a winning strategy exactly when the guarded parity objective
  has a distributed realizing strategy.
- `holes_periodic_LTL_characterization` in `LTL.lean` specializes that
  equivalence to the original finite-input LTL model, including next-time
  formulas and nonclosed adversaries.
- `holes_periodic_LTL_finite_controller` in `LTL.lean` proves the same
  equivalence with a finite public controller for the block game.

Blocks have one fixed positive length `D`. The uniform width bounds retained
representatives. The original input-dependent components need not be bounded.

## Construction and proof

`BlockArena.lean` defines finite boundary states, output policies, compression
responses, and environment outcomes. Its legality checks are computable finite
predicates. Each response lists retained endpoints and maps every endpoint in
the chosen component to one of them. The checks enforce preservation of
local-view equality, graph-recognizer states, and objective states. No process
is given the hidden source index.

`BlockGame.lean` combines these moves with the universal hidden-thread parity
monitor. Environment chooses an ending component. Every compatible sequence
of source and target slots must satisfy parity. The finite-controller theorem
uses the existing rational-run result for finite automata.

`BlockReadback.lean`, `BlockStrategy.lean`, and `BlockExecution.lean` reconstruct
the public game history from actual executions. Equal local views yield the
same public history and equal represented local views. The chosen outputs
therefore define a distributed strategy. Its objective states and block
minima agree with the game. `BlockSoundness.lean` proves acceptance of every
live execution. The guarded objective accepts executions leaving the live
prefix language.

For completeness, source roots are classified by their graph-recognizer
state, objective state, complete `D`-round output rule, and suffix set in the
selected ending component. One representative of each type suffices.
`PartialCompression.lean` handles components reached from only some source
roots and permits repeated entries when padding the retained family.
`BlockMoveCompleteness.lean` constructs the legal moves.

Representatives minimize a lexicographic ordinal rank at the source of each
block. The rank is constructed from the original winning strategy's tree.
`BlockCompleteness.lean` recursively constructs the entire winning game
strategy and proves acceptance of every compatible hidden thread, including
threads that do not form an original execution. Ordinal ranks are proof
witnesses and are not part of the game state or its legality checks.

The priority convention is source-inclusive and endpoint-exclusive.
Consecutive blocks partition the original priority sequence.

## Scope

The semantic reduction, both realizability implications, and the uniform
numeric implementation are proved.
The construction reuses the existing common-past-view theorem, LTL frontend,
finite-thread determinization, and finite rational-run theorem.

`EncodedBlockData.lean` and `EncodedBlockSolver.lean` define the numeric
arena and solver. `BlockPresentation.lean` enumerates its typed moves and
outcomes exactly. The table, guard, priority, and game encoding proofs culminate
in `encoded_block_solve_correct`. `EncodedBlockFrontend.lean` generates the
tables uniformly from a block length, a fixed graph recognizer, and an encoded
objective. `BlockFrontendCorrect.lean` proves the correspondence, including
the conversion between the two graph-numbering conventions.

`ComputableBounds.lean` supplies one block length for all input alphabets and
a primitive-recursive compression-width bound. `Decidability.lean` combines
these results with the existing guarded LTL frontend.

As in the original theorem, the adversary is fixed. The result is uniform in
the formula, truth table, and alphabet sizes. It does not assert a practical
running-time bound.

## Verification

From the repository root:

```sh
lake --wfail build DistributedSynthesis.Formalizations.PeriodicBlocks.Main DistributedSynthesis.Results.HolesCharacterization
python3 scripts/check_library.py --axioms DistributedSynthesis/Formalizations/PeriodicBlocks/Audit.lean
```
