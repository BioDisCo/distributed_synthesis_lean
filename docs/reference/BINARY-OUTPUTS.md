# Binary-output extension: completed encoded reduction

[Repository README](../../README.md). Commands and code paths in this note
are relative to the repository root.

The binary-output undecidability theorem is unconditional in Lean.
`SourcePort.source` discharges the original two-counter source interface. The full
realizability equivalence, primitive-recursive compiler, and many-one composition
are checked. The proofs use no `sorry` or new axioms.

## Scope

Two named processes, singleton external inputs, the original three graphs,
mandatory full prior-view messages, deterministic perfect-recall strategies,
and outputs chosen after reception. LTL may inspect graphs and both outputs.
All infinite graph sequences remain quantified. Varying external inputs are
outside the current encoding claim.

`BinaryReduction.realizable_iff` converts a finite-output instance in this model
into one using one Boolean output per process per physical round. It assumes
nonempty output types, injective codes of a common width, and exhaustive finite
alphabet lists. The codes always exist for finite alphabets.
`fin_realizable_iff` specializes the result to `Fin m₁` and `Fin m₂` for positive
sizes, with explicit one-hot codes and alphabet lists. The encoded reduction
is composed with the existing counter-machine reduction; that proof is not repeated.

The original parameterized public endpoint is
`CounterMachine.BinaryCompiler.binary_ltl_synthesis_undecidable`, imported
through `DistributedSynthesis.Results.BinaryUndecidability`. It states
`¬ ComputablePred EncodedBinaryReduction.Realizable`, with the sole explicit
argument `CounterMachine.MM2.SourceUndecidability`. The target instances are
ordinary postfix LTL strings over the five fixed atoms `Graph ⊕ Proc`, and
both output alphabets are `Bool`.
The closed endpoint is `CounterMachine.Unconditional.binary_ltl_synthesis_undecidable`,
imported through `DistributedSynthesis.Results.UnconditionalUndecidability`; it has no source
argument. See `SOURCE-UNDECIDABILITY.md` for the completed credited source port.

## Checked components

- `Library/Combinatorics/Paths.lean`: the former generic path lemmas, with
  original `ScalingRow` names preserved and a compatibility import at the old
  path. New `Path.fiber_uniform` proves agreement on fibers of a nondecreasing
  integer projection from agreement on collapsed edges. `Path.intermediate`
  supplies every intermediate integer when increments are at most one.
- `Library/Distributed/ViewPaths.lean`: paths of the existing tagged `View`
  type. `mem_row_iff` includes every graph history at its depth.
  `evaluate_graphSequence` identifies the evaluation with original history
  semantics for arbitrary past output types.
- `Library/Distributed/PaddingProjection.lean`: a locally computed projection
  for every active/padding schedule and every depth. `projected_gap` gives
  projected edge length one when all padding graphs are bidirectional, and
  zero otherwise. `core_false_iff` identifies failure with an actual earlier
  one-way padding round.
- `fiber_agreement` and `factors_through_projection`: any output labeling
  satisfying equality after such a round depends only on the projected
  coordinate, on reachable views. Equality is an explicit hypothesis of these
  generic lemmas; the `BinaryAgreement` adapter now derives it from the LTL
  protocol on actual executions.
- `coordinate_injective`, `project_surjective`, `unique_virtual_view`: each
  physical view projects to exactly one original tagged view at the number of
  active rounds. No injectivity, connectivity, or surjectivity certificates
  are assumed from the caller.
- `Library/Logic/BlockTranslation.lean`: structural LTL translation and
  semantic correctness for every constructor, including until and release.
  The explicit hypotheses are an exact marker and correct atomic tests. This
  is a semantic theorem; the encoded computability proof is provided separately
  by `EncodedBlockTranslation` and the compiler composition below.
- `Library/Logic/BinaryClock.lean`: finite LTL frame formula and `clock_exact`.
  The marker is `one ∧ X one`, not a fresh clock proposition. A satisfying
  word has markers exactly at multiples of the block length. `frame_of_pattern`
  also proves frame satisfaction from fixed headers and separators, without
  restricting data bits; it is used by the constructed strategy below.
- `Library/Distributed/BlockEmbedding.lean`: complete odd-length blocks
  restore the original process identities (`embed_projection`), and
  `phase_view_iff` identifies the exact original tagged view at every output
  offset. `binary_stream_data_view_iff` proves the owner-swapped identification
  for every data bit along one embedded infinite environment. The embedding,
  prefix correspondence, virtual round count, and absence of padding faults
  in embedded finite histories are all proved, not certificate premises.
- `Library/Distributed/GraphExecutions.lean`: connects graph prefixes to the
  original `execution` for arbitrary output types. An output at position `t`
  uses views of depth `t+1`. Every nonempty finite graph history is extended
  to an actual infinite execution, without assumptions on the strategy.
- `Library/Distributed/BinaryAgreement.lean`: defines a literal LTL protocol
  consisting of the frame and permanent-equality formulas. Its five atoms
  inspect the graph or either Boolean output. `finite_history_agreement`
  derives agreement from universal protocol satisfaction, including the fault
  round itself. `winning_iff` also proves the reverse implication under the
  frame. `winning_factors_through_projection` removes the separate echo/clock
  premises, and `serialized_bit_local` shows that equal original local views
  give equal serialized bits, even on different global histories.
  Here `Winning` refers only to this frame/equality protocol, not to the full
  target formula with code validity and the translated original objective.
- `Library/Logic/BinaryWords.lean`: injective binary codes, executable one-hot
  `finCode`, common positive-width codes for arbitrary finite alphabets, and
  finite LTL word/code-validity tests. `valid_iff` gives their exact meaning;
  `wordTest_unique` proves decoding uniqueness. One-hot codes are intentionally
  not size-optimal. The compiler constructors take explicit alphabet lists.
- `Library/Distributed/BinaryStrategy.lean`: constructs a genuine local
  Boolean strategy from any original strategy and two common-width codes.
  `encode_stream_data` proves exact bitwise reproduction of original outputs.
  `encode_protocol_and_validity` proves the frame/equality protocol on every
  environment and code validity at every block start on every core execution,
  not just a selected family of embedded environments. No protocol-winning
  certificate is assumed. This endpoint covers protocol/code validity;
  `BinaryReduction.encode_wins` adds the translated original objective.
- `Library/Distributed/BinaryReduction.lean`: literal source-letter tests,
  complete target formula, and `translate_correct` for the original objective.
  `encode_wins` proves the whole forward direction on every environment.
  `localWord_stream` recovers each data bit from the original tagged view;
  `decoded_represents` and `decode_wins` prove the converse for an actual
  original strategy. `realizable_iff` composes both directions without
  coherence, frame, or decoding certificates. `finCompile` is the executable
  finite-index specialization. The encoded route below handles the existing
  raw structured letters directly, avoiding a separate alphabet-renaming step.
- `Library/Logic/EncodedBlockTranslation.lean`: primitive-recursive stack
  compilation into ordinary postfix LTL. `translate_rep` proves exact agreement
  with the structural block translation for every source string, including
  underflow and surplus-stack cases. `translate_primrec` accounts for varying
  lengths and atomic substitutions, not just fixed parameters.
- `Library/Logic/EncodedBinarySyntax.lean`: encoded frame, word, validity,
  and complete guarded-protocol formulas, with representation and
  primitive-recursive proofs for all parameter-dependent loops.
- `Library/Distributed/EncodedBinaryReduction.lean`: fixed-alphabet encoded
  target predicate, generic primitive-recursive compiler, and semantic
  composition through an explicit atomic interface. It imports no source
  machine theorem; the next adapter proves that interface.
- `Formalizations/Theorem/ThmCounterMachineBinaryUndecidability.lean`: numeric
  encoding of the existing structured output labels, atomic correctness,
  `compileInstance_primrec`, and `compiled_realizable_iff` for all existing
  finite-output instances. `compileProgram_primrec` and
  `compileProgram_realizable_iff` compose with the old compiler;
  `binary_ltl_synthesis_undecidable` transfers the agreed source theorem.

The arbitrary-strategy transformation `encode` is `noncomputable`: it uses
the proved unique virtual-view correspondence to form the original strategy's
coordinate table. This supplies no new observation to either process and is
legitimate for arbitrary perfect-recall strategies. It is separate from
computability of the finite instance compiler, which is now proved separately.
The reverse transformation `decode` likewise uses classical choice to form a
strategy table; its argument at run time is only the original local view.
Arbitrary-type `finiteCode` uses an enumeration; `finCode` for explicit finite
indices is executable and does not use that enumeration choice.

The library APIs import neither counter-machine results nor result umbrellas. Their
project dependency boundaries are checked. The execution adapters inherit the
existing `Execution` API's coupling; lightweight projection and
logic modules remain independent of it. Public clients are in
`DistributedSynthesis/Tests/BinaryEncoding.lean`, `DistributedSynthesis/Tests/BinaryAgreement.lean`,
`DistributedSynthesis/Tests/BinaryStrategy.lean`, and `DistributedSynthesis/Tests/BinaryReduction.lean`.
`DistributedSynthesis/Tests/EncodedBinaryReduction.lean` also checks the encoded compiler.
Thirty-five binary-development endpoints are included in the axiom audit.

## The local projection argument

Let `active t` select whether physical round `t+1` is simulated or padding.
The projection `P` starts at 0 and 1 on the two empty tagged views. Given prior
self view `v` and sender view `u`, it is computed locally as follows:

| Round | No reception | Reception |
| --- | --- | --- |
| active | `3 P(v)` | `P(v) + 2 P(u)` |
| padding | `P(v)` | `P(u)` |

Time comes from local-view depth. No graph oracle, whole history, or global
fault flag is supplied to either strategy. The recursion is total even on
unreachable views; the theorems concern reachable ones.

The depth row is a path, and its projected increments are zero or one. Thus
each fiber is a connected interval. Precisely the edges with an earlier
one-way padding round collapse. Equality of the two outputs on those histories
therefore makes a physical output constant on each fiber, despite the extra
history revealed during padding.

With every round active there are no collapsed edges. Applying the same
theorem to the identity labeling proves that coordinates uniquely identify
reachable tagged views. The projected boundaries are 0 and `3^m`, where `m`
counts active rounds. The intermediate-value lemma supplies every integer in
that interval. These facts prove `unique_virtual_view` without an assumed
view-class correspondence.

## Block construction and complete formula

Choose injective `K`-bit codes for the two nonempty finite output alphabets.
Use blocks of odd length `L = 2*K+3`:

```
11 0 b1 0 b2 ... 0 bK 0
```

Only the first round of each block is active. All other rounds are padding.
On histories with bidirectional padding, odd data offsets swap physical
owners: decode original process 1 from physical process 2, and conversely.
The even number of padding rounds restores ownership before the next block.
These embedding and ownership claims are now proved in `BlockEmbedding`.
For zero-based source round `n` and bit `j < K`, the physical output offset is
`2*j+3`; its view is evaluated after `(2*K+3)*n+1+(2*j+3)` physical rounds.
The projected original view is that of the other process after source round
`n+1`. The extra `+1` accounts for reception before output in our model.

Let `A` be the `11` marker and `B` the bidirectional graph test. The compiled
target formula is

```
Frame ∧ G((¬A ∧ ¬B) → G(out1 ↔ out2))
      ∧ (G(A ∨ B) → (G(A → ValidCodes) ∧ Translate(φ))).
```

Non-core environments still have to satisfy the frame and permanent-agreement
obligations. `BinaryAgreement.finite_history_agreement` now proves that these
obligations supply the hypotheses of `fiber_agreement`; the guard is not an
external restriction on allowed graph sequences.

## Reverse decoding

For an original tagged view `v` of positive depth `m`, let `k` be its path
coordinate. To recover bit `j < K`, choose a reachable physical view at depth
`(2*K+3)*(m-1)+1+(2*j+3)` whose padding projection is `k`, and read the binary
strategy's label there. `winning_fiber_agreement` makes this choice irrelevant.
`localWord_stream` proves that on every embedded source play the resulting
word is exactly the serialized output for `v`. Thus this definition does not
give either process the additional observations received during padding.

The complete target formula requires code validity on every embedded play.
Consequently the recovered word at each encountered original view is a codeword
and determines a unique source output. `decode` uses that output; arbitrary
defaults only make the strategy total outside these valid cases. The graph and
both decoded outputs then agree with the target block tests at every source
round. `translate_correct`, including its until and release cases, transfers
the original objective. This proves `decode_wins`, not merely pointwise
consistency on selected histories.

## Encoded compilation and source boundary

Write `C` for the cardinality of the fixed payload type `Output Unit`. A source
instance with control bound `n` uses `K = C*(n+1)` data bits. Fix an enumeration
`e` of the payloads. The numeric code index of a label with payload `p` and
control `q ≤ n` is `q + (n+1)*e(p)`. `outputFin` proves this is a bijection
with `Fin K`; the code is its one-hot word. The list of valid indices is
`List.range K`. A source atom whose control numbers exceed the bound translates
to false; all other atoms translate to the graph test and the two word tests.

The enumeration is fixed independently of the input instance. The definitions
using it are `noncomputable` Lean definitions, but their primitive-recursive
certificates are proved: fixed finite lookup tables are constant data, and
every operation depending on `n` or the input string is included in the proof.
This establishes encoded effectivity, not merely semantic correctness. No
efficiency or polynomial-size claim is made for the one-hot construction.

`compileInstance_rep` ensures every emitted string represents an ordinary LTL
formula. `compiled_realizable_iff` needs no source well-formedness assumption.
The full `compileProgram` map is primitive recursive and its output is realizable
exactly when the source program does not halt from its zero initial state.

There are no remaining source- or target-side proof obligations for this result.
The Rocq-to-Lean source port is complete and provides `SourcePort.source`, without
introducing a new axiom.

## Paper presentation and credits

The final main-text section of `undecidable.tex`, “Reduction to binary
outputs,” gives the generic reduction, local projection, permanent-agreement
constraint, both strategy transformations, and effective composition with the
finite-output theorem. The original finite-output argument remains intact.

The section credits Demri and Schnoebelen, *The Complexity of Propositional
Linear Temporal Logics in Simple Cases* (Information and Computation 174(1),
2002), Propositions 3.3–3.4 and Section 3.1, for the bit-block, consecutive-one
marker, and marker-relativized temporal techniques. Their word-level reductions
do not by themselves prove preservation of distributed realizability; the
local-projection and agreement argument establishes that additional property
here. The view-path subdivision is credited to Godard and Perdereau, Section 4,
as in the original path lemma.

## Verification

Use the [overview's verification commands](../../README.md#build-audit-and-maintain).
The audit includes the composed primitive-recursive compiler, realizability
equivalence, and final binary-output undecidability endpoint.
The public reduction clients cover unequal finite alphabet sizes, temporal
formulas containing until/release, evaluation of the finite syntax compiler,
and the zero-width edge case for singleton output alphabets. Encoded regression
tests cover empty strings, stack underflow, surplus stack entries, recovery
after underflow, word/frame evaluation, and the final source-interface client.
