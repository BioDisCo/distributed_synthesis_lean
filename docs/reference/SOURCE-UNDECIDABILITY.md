# Exact source theorem and verification boundary

[Repository README](../../README.md). Commands and code paths in this note
are relative to the repository root.

The development proves source undecidability and both unconditional encoded
LTL synthesis undecidability theorems.
`CounterMachine.SourcePort.source` proves `MM2.SourceUndecidability` through an
explicit primitive-recursive reduction from Mathlib's code halting problem.
`DistributedSynthesis.Results.UnconditionalUndecidability` applies it to the finite-output
and binary-output synthesis results. There is no source premise, new axiom,
global instance, or proof placeholder.

The modular chain is Mathlib → binary TM2 → BSM → MM → regular FRACTRAN →
MMA2 → MM2 → zero-initialized MM2. The manual Rocq adaptations and Mario
Carneiro's Mathlib development are credited separately in
[`Library/Computability/CounterMachines`](../../DistributedSynthesis/Library/Computability/CounterMachines/README.md),
with MPL-2.0 and Apache-2.0 notices respectively. The original conditional
target APIs remain unchanged; the new unconditional result module supplies
their source parameter explicitly.

## Stable interface

`LemMM2SourceSemantics` isolates the source model without any dependency on
distributed synthesis. `LemMM2SourceInterface` fixes a primitive-recursive
encoding of instructions by `Bool × Option Nat` and programs by lists.
Its single source proposition, now proved by `SourcePort.source`, is:

```lean
structure SourceUndecidability : Prop where
  zeroHalting_not_computable : ¬ ComputablePred ZeroHalts
```

The reusable conditional consumers take `(source : SourceUndecidability)`
explicitly. The proved constant `SourcePort.source` supplies it; there is no
source axiom, typeclass instance, or proof hole. `SourceUndecidability.transfer` derives target undecidability from this
parameter and a Mathlib `ManyOneReducible` proof from source nonhalting.
That reduction must include actual `Computable` evidence for the compiler.

`CounterMachine.Compiler.encoded_ltl_synthesis_undecidable` now applies this
interface to the encoded LTL problem itself, not just a predicate on source
programs. `compileInstance_primrec` proves the compiler primitive recursive,
and `nonhalting_manyOneReducible` packages its computability with the exact
realizability equivalence. The target instance is an alphabet bound and a
postfix formula string; its interpretation contains no source-program
interpreter. This supersedes the weaker source-indexed endpoint for the
undecidability claim.
For the port, `SourceUndecidability.of_halting_reduction` constructs the
interface from a computable reduction of Mathlib's fixed-input halting problem
to `ZeroHalts`. `SourcePort.halting_manyOneReducible_zeroHalting` now provides
that reduction. The unconditional endpoints are
`CounterMachine.Unconditional.encoded_ltl_synthesis_undecidable` and
`CounterMachine.Unconditional.binary_ltl_synthesis_undecidable`.

## Implemented source-port components

Import `DistributedSynthesis.Library.Computability.CounterMachines`. This library has no
distributed-synthesis dependency and preserves the existing source interface.

- **Zero initialization:** `MM2.ZeroInitialization.compile_correct` proves
  exact equivalence between halting with arbitrary initial counter values and
  halting of the compiled program from zero. The compiler prepends increments
  and shifts positive addresses, leaving zero fixed. `reduce_primrec` and
  `halting_manyOneReducible_zeroHalting` certify its actual effectivity. This
  ports Andrej Dudenhefner's `MM2_HALTING_to_MM2_ZERO_HALTING.v`.
- **MMA2 representation change:** `MMA2ToMM2.terminates_correct` proves the
  correspondence between the two-register vector model and the fixed MM2
  model. `toZero_primrec` and `toZero_correct` certify the composed reduction
  from MMA2 halting to zero-initialized MM2 halting. This ports Dominique
  Larchey-Wendling's `MMA2_to_MM2.v`.
- **Mathlib starting point:** `MathlibBridge.wordHalting_not_computable` proves
  unconditional undecidability of `WordHalts universalCode`. This is one fixed
  finite-control machine with four stacks, four symbols, and five local-store
  values. Its halting predicate is equivalent to finite reachability of a halted
  configuration. `halting_manyOneReducible` reduces `Nat.Partrec.Code.eval` at
  input zero to this predicate; `InputEncoding.inputWord_primrec` certifies the
  varying-input map. `universalCode` is chosen once, not compiled separately for
  each input. No effectivity claim is inferred from that choice. The bridge
  imports neither MM2 nor its source interface.
- **Binary alphabet:** `MathlibBridge.BinaryStacks.stepAux_correct` proves
  exact execution of every translated TM2 statement on two-bit encoded stacks.
  `halts_iff` gives halting equivalence in both directions, including empty-stack
  cases and peek restoration. `BinaryUniversal.inputWord_primrec` and
  `wordHalting_not_computable` provide the effective binary-input reduction and
  unconditional binary-stack source theorem. This still uses structured TM2
  control, with 15 finite local-store values; this intermediate model is not Rocq BSM.
- **Rocq BSM control blocks:** `BSM` adapts Dominique Larchey-Wendling's binary
  instruction semantics, including arbitrary base addresses, true-fall-through
  POP, and halting outside the program interval. `BSMMacros` proves jump, push,
  pop, and peek blocks with exact positive step counts under explicit placement
  hypotheses. The jump preserves an arbitrary existing stack; no empty scratch
  stack is assumed. These local block proofs do not constitute a whole-program
  control compiler by themselves; the next components supply it.
- **Whole-program control compilation:** `BSMGraph.block_placed` discharges the
  block hypotheses for a finite instruction list with seven slots per graph
  node, an entry jump, and halting at address zero. `TM2ToBSM` represents each
  supported substatement and local-store value by a finite control location.
  `statement_progress` proves strict simulation, and `compile_correct` proves
  halting equivalence for the actual BSM program from base address one. No
  placement or empty-scratch assumption remains.
- **Unconditional Rocq BSM source:** `BSMSource.halting_manyOneReducible` reduces
  Mathlib's fixed-input code halting predicate to `@BSM.Halts 4`.
  `reduce_primrec` certifies the reduction, and `halting_not_computable` proves
  BSM halting undecidable without a source parameter. One fixed BSM program
  suffices: only its initial word changes. The selected finite enumeration and
  compiled program are constants; no uniformly effective syntax compiler is
  inferred from classical choice.

- **BSM-to-MM register simulation:** `MM.StackEncoding` represents the empty
  stack by one and Boolean cons by doubling plus the bit. `MM.Arithmetic` and
  `MM.StackMacros` prove actual transfer, doubling, division, push, and pop
  instruction sequences, including positive progress and preservation of
  untouched registers. `BSMToMM.compile_correct` proves whole-program halting
  equivalence at source base one. It discharges placement obligations for a
  sixteen-slot layout and restores both temporary registers to zero after
  every simulated step. MM jumps on zero, unlike MMA; these are separate models.
- **Unconditional MM source:** `MMSource.halting_manyOneReducible` reduces
  Mathlib's fixed-input code halting predicate to `@MM.Halts 6`.
  `reduce_primrec` proves this reduction primitive recursive, and
  `halting_not_computable` establishes unconditional six-register halting
  undecidability. The program is fixed, and `BSMToMM.state_primrec` certifies
  the varying stack-to-register input encoding. No uniform primitive-recursive
  program-compiler theorem is assumed or claimed.

- **MM-to-FRACTRAN simulation:** `MMToFRACTRAN` encodes counter values as prime
  exponents and separates instruction entry from execution with distinct
  control primes. `instruction_two_steps` proves exactly two FRACTRAN steps per
  MM step. `compile_regular_correct` proves whole-program halting equivalence
  and nonzero denominators, without a self-jump restriction. This adapts
  Larchey-Wendling and Forster's prime-power construction; the private phase
  replaces upstream self-loop elimination. `FRACTRAN.step_eq_some_iff` and
  `halts_iff_relStep` prove agreement with the original relational semantics
  on regular programs, including cancellation and first-applicable priority.
- **Unconditional regular FRACTRAN source:** `FRACTRANSource` proves ordinary
  and regular halting undecidable, even with the program fixed and only the
  initial encoded word varying. `reduce_primrec` certifies every input-dependent
  operation. `program_regular` and `input_positive` establish the concrete
  target conditions. Prime enumeration and the universal program are fixed
  constants, not presumed uniformly effective compilers.

- **FRACTRAN-to-MMA2 simulation:** `MMA.Arithmetic`, `MMA.Subtract`, and
  `MMA.Division` port Larchey-Wendling's actual two-register arithmetic blocks.
  `FRACTRANToMMA.one_success` computes the quotient and restarts the scan;
  `one_failure` restores both registers and advances to the next fraction.
  The latter derives positivity of the numerator from failure; zero numerators
  remain supported. `compile_correct` proves halting equivalence for every
  regular fraction list and every natural input, including zero. Placement and
  ordered-priority obligations are discharged for the concrete program. This
  port omits the upstream final register-zeroing postlude, since ordinary
  MMA2 halting suffices.
- **Two-counter source and final composition:** `MMA2Source` proves
  unconditional two-register halting undecidability. `SourcePort.reduce`
  composes its fixed-program input reduction with `MMA2ToMM2.toZero`.
  `reduce_primrec` proves the actual map primitive recursive; `reduce_correct`
  proves equivalence with Mathlib code halting. `SourcePort.source` therefore
  inhabits the stable interface. The separate `Results.UnconditionalUndecidability`
  module applies it to both existing encoded synthesis reductions.

The source snapshots, file-level credits, theorem correspondence, licensing,
and dependency boundaries are in the directory's
[README](../../DistributedSynthesis/Library/Computability/CounterMachines/README.md).
The Rocq reductions are manual Lean adaptations, not an automatic Rocq
import. Their composition now proves MM2 halting undecidability without an
undecidability premise. The Mathlib bridge directly imports Carneiro's checked
compiler and adds finite-control restriction and the effective fixed-program
reduction. The whole-program compilers connect that model to the exact BSM
and MM instruction conventions, then regular FRACTRAN and MMA2, with explicit input reductions.

No simulation remains open in this chain. MM's zero-branch and MMA/MM2's
positive-branch decrement conventions are kept distinct. The fixed universal
programs and their primes are constants; every input-dependent map is proved
primitive recursive. No uniformly effective compiler from function-bearing TM2
syntax or uniformly effective prime enumeration is inferred from classical
choice. These uniform compilation claims are not needed for the proved
fixed-program reduction. Rocq's synthetic `undecidable` is not used as a
substitute for Mathlib's `ComputablePred`: the chain starts at Mathlib's checked
halting theorem and every link is proved in Lean.

Use the [overview's verification commands](../../README.md#build-audit-and-maintain).
Runtime regressions cover
empty programs, zero-length prefixes, zero and out-of-range jump targets,
both decrement branches, the complete instruction representation change, and
the stack input encoder's zero, carry, and symbol-order cases; binary push/pop/
peek, scratch reset, and other-stack preservation; and all BSM control-block
branches, arbitrary base addresses, nonempty jump stacks, and self-jumps.
Whole-program regressions check nonzero entry nodes, cross-block execution,
unreachable padding, actual termination, and formally proved nontermination of
a compiled self-loop.
MM regressions additionally check the sentinel encoding, transfer/doubling/
division, all three pop branches, restored temporary registers, and preservation
of a fourth register. Whole BSM-to-MM programs test push/pop composition,
invalid targets, repeated pop, the six-register input map, and a compiled
empty-pop loop formally proved not to halt.
FRACTRAN regressions check product divisibility, fraction cancellation, ordered
priority, increment/decrement execution, inactive control primes, and a compiled
zero-counter self-jump formally proved not to halt. Concrete fraction lists are
proved equal to compiler outputs; tests do not substitute another compiler.
MMA tests cover zero multipliers, both bounded-subtraction branches, remainder
handling, untouched-register preservation, cancellation, failed-test restoration,
first-applicable priority, and zero numerators/inputs. The compiled identity
fraction loop is formally proved not to halt. Public clients check the closed
source theorem and both unconditional synthesis endpoints.

## The source problem

The Coq library of undecidability proofs exports `MM2_ZERO_HALTING_undec`
in [MM2_undec.v](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/MinskyMachines/MM2_undec.v).
Its predicate is defined in [MM2.v](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/MinskyMachines/MM2.v):
start at address one with both counters zero; increment falls through to
the next address; conditional decrement jumps on a positive counter and
falls through on zero; execution halts exactly when no instruction occurs
at the current address. In particular, zero and every address above the
program length are halting addresses.

The selected revision is `11c41e0637f0c5219ad1c4c92d11609b7e072c31`.
The published matching result is Bell and Potapov, section 2.1,
Proposition 1, [Periodic and Infinite Traces in Matrix Semigroups](https://www.csc.liv.ac.uk/~igor/papers/sofsem2008.pdf).
For the machine-instruction distinction and mechanization, see Dudenhefner,
[Certified Decision Procedures for Two-Counter Machines](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2022.16).

## What the Lean adapter proves

`LemMM2SourceSemantics.lean` defines the six source instruction transitions
independently of the target monitor's operations. Together with the adapter
in `LemCounterMachineMM2.lean`, it proves:

- `lookup_iff_instrAt`: executable lookup agrees with the source's list-prefix
  definition of instruction occurrence, including its one-based indexing;
- `zeroHalts_iff_run`: reaching a stuck state by the reflexive-transitive
  step relation agrees with hitting a missing instruction in the functional run;
- `compile_step` and `compile_run`: exact configuration simulation by our
  machine with finite control type `Fin (P.length + 1)`;
- `compile_nonhalting_iff`: the compiled machine is nonhalting exactly when
  the source program does not satisfy the relational zero-halting predicate;
- `ltl_realizable_iff_not_zeroHalts`: the corresponding literal LTL formula
  is realizable exactly when the source program does not halt.

The compiler retains addresses `1,...,length P` and sends every missing
address to the finite sink zero. Thus arbitrary jump targets and the empty
program require no extra well-formedness assumption. Initialization is already
zero in the cited source theorem, so no counter-loading prefix is needed.

These are Lean proofs about our transcription of the source definitions.
They are not a mechanically checked translation of the Coq declarations.
The correspondence to those declarations has been inspected explicitly.

## Citation versus a single-kernel proof

A mathematical undecidability proof may cite the established source theorem.
It need not reprove universality of counter machines. Combined with the
effective finite-table expansion in `COUNTER-MACHINE-REDUCTION.md`, the new
reduction yields the claimed mathematical undecidability result for the
uniform finite-alphabet, graph-dependent specification problem.

A fully unconditional end-to-end Lean theorem is now available through the
manual port and `SourcePort.source`. It does not introduce an axiom named after
the Rocq theorem or identify Rocq's synthetic `undecidable` predicate with
Mathlib's `ComputablePred` without proof.

The chain starts from Mathlib's `ComputablePred.halting_problem` for partial
recursive codes. No Rocq-import plugin or external proof oracle is used.
The source parameter remains visible only in the reusable conditional APIs;
the unconditional result module supplies its proved inhabitant explicitly.
