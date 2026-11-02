# Next-free LTL with four output symbols per process

[Repository README](../../README.md).

The closed endpoint is
`NextFreeUndecidability.four_symbol_nextFree_ltl_synthesis_undecidable` in
`DistributedSynthesis.Results.NextFreeUndecidability`.
It proves `¬ ComputablePred EncodedNextFreeReduction.Realizable`.
The target predicate explicitly conjoins `LTL.NextFree (decode c)` with
realizability of that decoded formula; it is not unrestricted LTL realizability.

## Model and scope

The original full-view perfect-recall model is unchanged: two named processes,
singleton external inputs, reception before output, no acknowledgements, and
all infinite sequences of the three communication graphs. Each output is
`Bool × Bool`, with first coordinate data and second coordinate clock. Thus
there are four symbols **per process**, not four joint symbols. The seven
atomic propositions test the graph, the two data bits, and the two clock bits.
LTL can test graphs, but strategies are not given a graph oracle.

## Reduction

Write `c₁,c₂` for the clock propositions. The clock formula requires
`G(c₁ ↔ c₂)` and, for each graph test `g` and phase literal `p ∈ {c₁,¬c₁}`,

```text
G ((g ∧ p) → ((g ∧ p) U ¬p)).
```

These requirements contain no next operator. Agreement on every history edge
makes the clock constant across all reachable local views at each positive
depth, by connectedness of the existing view path. If two consecutive depths
had equal clock values, choose an environment whose graphs differ in those
rounds. The until requirement would force those graphs to agree, a contradiction.
Consequently every winning strategy alternates its clock every physical round.
This argument is about winning over **all environments**; the clock formula
does not force alternation on every individual satisfying word.

The structural translation preserves atoms and every operator except next:

```text
tr(X ψ) = (c₁ ∧ (c₁ U (¬c₁ ∧ tr(ψ))))
        ∨ (¬c₁ ∧ (¬c₁ U (c₁ ∧ tr(ψ)))).
```

Under alternation, each relevant until witnesses exactly the next position.
The compiled formula is the conjunction of the clock formula and `tr(φ)`.
A binary winning strategy lifts by appending the parity of its local view
depth. Conversely, dropping the clock coordinates from a compiled winner
gives a binary winner. Views do not depend on outputs, so these transformations
preserve the original views and every physical round; no padding is introduced.

## Checked interfaces

- `LTL.NextFreeTranslation.correct`: generic word/suffix theorem, assuming an
  alternating proposition. Independent of the distributed reduction.
- `NextFreeClock.winning_alternates`: discharges alternation from universal
  winning of the next-free clock protocol in the actual model.
- `NextFreeReduction.realizable_iff`: exact strategy-level equivalence.
- `EncodedNextFreeReduction.compile_primrec`, `compile_nextFree`, and
  `compile_correct`: total postfix compiler, next-free target, and realizability
  equivalence. Malformed source codes retain the existing decoder's semantics.
- `EncodedNextFreeReduction.binary_manyOneReducible`: reusable reduction,
  importing no undecidability result.
- `NextFreeUndecidability.four_symbol_nextFree_ltl_synthesis_undecidable`:
  composition with the established unconditional binary-output theorem.

`Tests.NextFreeReduction` checks public statements and executable examples,
including malformed codes. The main axiom audit includes the new endpoint and
its key intermediate certificates. All previous proofs and theorem statements
are unchanged. The two-symbol, next-free case is not claimed here.

## Check

From the repository root:

```sh
lake build DistributedSynthesis.Results.NextFreeUndecidability DistributedSynthesis.Tests.NextFreeReduction
python3 scripts/check_library.py --axioms
```
