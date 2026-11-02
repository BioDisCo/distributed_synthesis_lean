# Counter-machine source port

This directory contains a manual Lean adaptation of parts of the
[Coq library of undecidability proofs](https://github.com/uds-psl/coq-library-undecidability),
now developed with Rocq. The pinned upstream revision is
`11c41e0637f0c5219ad1c4c92d11609b7e072c31`.

`SourcePort.source` proves `MM2.SourceUndecidability`; `reduce_primrec` and
`reduce_correct` certify its explicit Mathlib-code reduction. No source premise,
new axiom, global instance, or proof placeholder remains. The existing conditional
target APIs are preserved; `DistributedSynthesis.Results.UnconditionalUndecidability` supplies
this proved source to both encoded LTL synthesis results.

## Imports and boundaries

```lean
import DistributedSynthesis.Library.Computability.CounterMachines
```

For the existing source interface alone, continue using
`DistributedSynthesis.Library.Computability.TwoCounterMachines`. That module does not import
this port or any distributed-synthesis result. Names in `CounterMachine.MM2`
and its instruction/list encoding are unchanged.

| Module in this directory | Content |
| --- | --- |
| `MM2` | Re-export of the fixed source interface, without duplicate definitions |
| `Halting` | Arbitrary-input halting and deterministic terminal-suffix facts |
| `ZeroInitialization` | Loading prefix, address relocation, exact simulation and halting equivalence |
| `ZeroInitializationComputable` | Primitive-recursive compiler, many-one reduction, conditional connection to the source interface |
| `MMA` | Independent finite-register model, with decrement jumping on a positive counter |
| `MMA2ToMM2` | Representation equivalence and primitive-recursive composition to zero-initialized MM2 |
| `MathlibBridge.FiniteControl` | Generic restriction to finite control support, preserving each step and halting |
| `MathlibBridge.InputEncoding` | Primitive-recursive four-symbol input words, with exact Mathlib representation correspondence |
| `MathlibBridge.UniversalStackMachine` | Unconditional halting undecidability for one fixed finite-control four-stack machine |
| `MathlibBridge.BinaryStacks` | Generic two-bit stack compiler; exact statement, step, evaluator, and halting correspondence |
| `MathlibBridge.BinaryUniversalStackMachine` | Unconditional binary-stack halting source with a primitive-recursive binary input encoder |
| `BSM` | Independent Rocq binary-stack instruction semantics, arbitrary base addresses, and big-step/termination equivalence |
| `BSMMacros` | Jump, push, pop, and peek control blocks with exact positive step counts and explicit placement hypotheses |
| `BSMGraph` | Whole-program finite control-graph layout, all placement proofs, strict simulation, and initial-state halting equivalence |
| `TM2ToBSM` | Finite-store elimination, supported substatement enumeration, and complete TM2-to-BSM halting equivalence |
| `BSMSource` | Primitive-recursive reduction from Mathlib halting to the Rocq four-stack BSM model; unconditional BSM undecidability |
| `MM` | Independent Rocq register-machine semantics: decrement jumps on zero, unlike MMA |
| `MM.StackEncoding` | Sentinel binary-stack encoding and its primitive recursiveness |
| `MM.Frame` | Three distinct working registers, updates, and preservation of other registers |
| `MM.Arithmetic` | Transfer, doubling, and division by two as actual MM instructions, with strict progress |
| `MM.StackMacros` | Push and three-way pop blocks, preserving other registers and restoring temporaries |
| `BSMToMM.Encoding` | Encoding n stacks in n + 2 registers, update correspondence, and primitive recursiveness |
| `BSMToMM.Compiler` | Executable program layout, discharged placement obligations, strict simulation, and halting equivalence |
| `MMSource` | Primitive-recursive Mathlib-code reduction and unconditional six-register MM halting undecidability |
| `FRACTRAN` | First-applicable fraction semantics, regularity, and agreement with the upstream relational step/halting semantics |
| `MMToFRACTRAN.Encoding` | Disjoint control/register primes, prime-power state encoding, divisibility tests, and register updates |
| `MMToFRACTRAN.Blocks` | Entry/execution phases and ordered instruction blocks, including self-jumps |
| `MMToFRACTRAN.Compiler` | Whole-program simulation, exactly two target steps per source step, regularity, and halting equivalence |
| `MMToFRACTRAN.Computable` | Primitive-recursive initial prime-power encoding for any fixed register dimension |
| `FRACTRANSource` | Unconditional regular FRACTRAN halting undecidability; fixed regular program, positive inputs, and primitive-recursive reduction |
| `MMA.Execution`, `MMA.Frame` | Executable MMA semantics, equivalence with the existing relational model, placement, and two-register frames |
| `MMA.Arithmetic` | Verified jump, repeated increment, transfer, and multiplication-by-constant instruction blocks |
| `MMA.Subtract` | Bounded subtraction with optional copying, including success and exhaustion branches |
| `MMA.Division` | Emptiness test, divisibility test with transfer, and division-by-constant loops |
| `FRACTRANToMMA.Fraction` | One fraction: quotient on success, exact input restoration on failure |
| `FRACTRANToMMA.Compiler` | Ordered scan, whole-program halting equivalence for regular FRACTRAN, and primitive-recursive initial registers |
| `MMA2Source` | Unconditional two-register MMA halting undecidability and primitive-recursive Mathlib-code reduction |
| `Source` | Final composition to zero-initialized MM2 and the proved `SourcePort.source` interface |

The generic `MMA` model imports no MM2 or distributed modules. The Mathlib bridge
imports neither the Rocq models nor the MM2 source interface. The entire port
has an explicit dependency allowlist enforced by `scripts/check_library.py`.
The parameterized target reductions do not depend on this port;
the new unconditional result module is the explicit join with the target side.

`BSM` and `BSMMacros` also have their own dependency allowlist: neither may
import the Mathlib bridge, MM2, or distributed consumers. No connecting compiler
is hidden in either independent model.
`BSMGraph` and `TM2ToBSM` depend only on the BSM side and Mathlib. `BSMSource`
is the explicit composition point with the independent universal-machine bridge;
its allowlist excludes the MM2 interface and all distributed consumers.
The MM modules and `BSMToMM` likewise cannot import MMA, MM2, or distributed
consumers. `BSMToMM` cannot import either universal source; `MMSource` alone
composes its generic compiler with `BSMSource`.
`FRACTRAN` imports no other project model. `MMToFRACTRAN` can import only MM
and FRACTRAN, not either universal source, MMA, MM2, or distributed results.
`FRACTRANSource` is the explicit composition point with `MMSource`.
The MMA arithmetic and `FRACTRANToMMA` cannot import universality sources or
MM2. `MMA2Source` composes the generic simulation with `FRACTRANSource` but
still cannot import the MM2 interface. `Source` alone joins that chain with
`MMA2ToMM2`; its allowlist excludes all distributed consumers.

## Proved reductions

For a program `P` and initial counters `a,b`, the zero-initialization compiler is

```text
replicate a incA ++ replicate b incB ++ map (shiftInstr (a+b)) P.
```

It shifts every positive address by `a+b` and leaves zero unchanged. The loading
prefix reaches address `1+a+b` with counters `(a,b)`. The remaining execution is
exactly the relocated original execution. Missing addresses, including zero,
remain missing. Hence

```lean
MM2.ZeroInitialization.compile_correct P a b :
  MM2.ZeroHalts (MM2.ZeroInitialization.compile P a b) ↔ MM2.Halts (P,a,b)
```

`reduce_primrec` proves compiler effectivity for the existing encodings, and
`halting_manyOneReducible_zeroHalting` packages `MM2.Halts ≤₀ MM2.ZeroHalts`.

The MMA2 adapter represents the two-register vector by its two coordinates;
register zero is A and register one is B. It proves instruction, step,
reachability, and halting correspondence. Its composed endpoint is

```lean
MMA2ToMM2.toZero_correct d : MM2.ZeroHalts (MMA2ToMM2.toZero d) ↔ MMA.Halts d
MMA2ToMM2.toZero_primrec : Primrec MMA2ToMM2.toZero
MMA2ToMM2.halting_manyOneReducible_zeroHalting : @MMA.Halts 2 ≤₀ MM2.ZeroHalts
```

These are reductions, not proofs that either halting predicate is undecidable.
In particular, `ZeroInitialization.source_of_halting_reduction` still requires
a computable reduction from Mathlib's fixed-input halting predicate to
`MM2.Halts`; it does not manufacture that reduction.

## Proved Mathlib starting point

Import `DistributedSynthesis.Library.Computability.CounterMachines.MathlibBridge.UniversalStackMachine`
for this independent component. Its public endpoint is

```lean
MathlibBridge.wordHalting_not_computable :
  ¬ ComputablePred (MathlibBridge.WordHalts MathlibBridge.universalCode)
```

This theorem has **no undecidability premise**. `WordHalts c w` is termination
of a finite-control instance of Mathlib's `Turing.TM2` stack machine, initialized
with the word `w : List (Fin 4)` on its main stack and empty other stacks.
`wordHalts_iff_reaches_halt` identifies termination with reaching a configuration
whose control label is `none`. The machine has four stacks, four stack symbols,
five local-store values, and finitely many control labels. All function fields
in its instructions therefore have finite domains; they are not oracle calls.

The proof uses **Mario Carneiro's** Mathlib development, not an unported Rocq
universality theorem:

1. `ToPartrec.Code.exists_code` supplies a program for the single function
   `n ↦ Nat.Partrec.Code.eval (Denumerable.ofNat _ n) 0`.
2. `PartrecToTM2.tr_eval` and `tr_supports` supply its stack-machine execution
   and finite control support. Our `FiniteControl.lift_step` restricts labels
   to that support while preserving each step exactly.
3. `InputEncoding.inputWord_primrec` certifies the only input-dependent map:
   encode the source code as a natural number, write its little-endian binary
   digits using symbols 2 and 3, and append separator 1. Zero has no digits.
4. `inputWord_correct` proves halting equivalence; `halting_manyOneReducible`
   and Mathlib's halting theorem give `wordHalting_not_computable`.

`universalCode` is chosen once and is constant across all reduction inputs.
There is no claim of a computable program compiler obtained from classical
choice. The actual varying-input reduction has an explicit `Primrec` proof.

Mathlib is pinned by `lake-manifest.json` to revision
`c5ea00351c28e24afc9f0f84379aa41082b1188f` (v4.30.0). The credited upstream
proofs are in
[`Config.lean`](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Computability/TuringMachine/Config.lean),
[`ToPartrec.lean`](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Computability/TuringMachine/ToPartrec.lean),
and [`StackTuringMachine.lean`](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Computability/TuringMachine/StackTuringMachine.lean).
We import these checked proofs; we do not reproduce their compiler.
The initial three `MathlibBridge` files add the finite-control restriction,
primitive-recursive input encoding, and fixed-program reduction, under Apache-2.0.

## Binary-stack compiler and BSM blocks

`BinaryStacks.Codec` requires a two-bit encoding and its left inverse.
`BinaryStacks.stmt` translates every TM2 statement. Push writes the second bit
before the first; pop removes both; peek pops the first, reads the second, and
restores the first. On an empty stack, peek restores nothing. A temporary
`Option Bool` in the local store is cleared before each source continuation.
`stepAux_correct` proves exact statement execution on encoded stacks, and
`halts_iff` proves halting equivalence in both directions. This is a complete
alphabet compiler, not just a proof that words can be encoded.

The specialized endpoint is

```lean
MathlibBridge.BinaryUniversal.wordHalting_not_computable :
  ¬ ComputablePred (MathlibBridge.BinaryUniversal.WordHalts MathlibBridge.universalCode)
```

It has no source premise. There are four binary stacks, the same finite label
set, and 15 local-store values. `inputWord_primrec` proves the composed
code-to-binary-word map primitive recursive. Correctness is required only on
encoded stacks; no interpretation of malformed odd-length words is assumed.
This intermediate target executes structured TM2 statements, not Rocq BSM;
the whole-program compiler below connects the two models.

`BSM.lean` separately adapts **Dominique Larchey-Wendling's**
[`BSM.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/StackMachines/BSM.v).
Its POP convention is true = fall through, false = first target, empty = second
target. `lookup_eq_none` proves that exactly the addresses outside the program
interval halt. `Eval` factors the upstream big-step cases through the explicit
instruction function `next`; `eval_iff` and `terminates_iff_eval` prove the
correspondence with deterministic reachability and termination.

The new project-specific `BSMMacros` proofs operate inside any ambient program
with the stated `Placed` hypothesis:

| Block | Number of instructions | Executed steps | Effect |
| --- | ---: | --- | --- |
| `jump` | 2 | 2 | Push false, pop it, jump; preserve every stack |
| `pushTo` | 3 | 3 | Push the specified bit, jump |
| `popTo` | 3 | 3 on true; 1 on false/empty | Pop and dispatch; empty leaves stacks unchanged |
| `peek` | 7 | 4 on true/false; 1 on empty | Dispatch without changing any stack |

These blocks use an existing stack, not an auxiliary stack assumed to be empty.
`runSteps_reaches₁` certifies strict progress, including self-jumps. The macros
are additions of this project, not claimed to reproduce a particular Rocq macro.
Runtime regressions exercise every branch, arbitrary base addresses, nonempty
jump stacks, other-stack preservation, and the alphabet compiler's scratch reset.

## Completed whole-program connection to Rocq BSM

`BSMGraph` represents a finite graph whose nodes jump, push, pop, or peek.
It reserves seven instruction slots per node, preceded by a two-instruction
entry jump. Node `q` starts at address `3 + 7*q`; address zero halts. Short
blocks are padded, but every execution from a node entry leaves by a proved
jump and never falls into padding. `block_placed` discharges the macro placement
hypotheses for the actual instruction list. `block_progress` proves a strict
simulation, and `initial_halts_iff` proves halting equivalence from the actual
BSM entry address one, including when the selected graph entry is not node zero.

`TM2ToBSM` uses a pair `(supported substatement, local-store value)` as a graph
node. These pairs form a finite type. Loads and Boolean branches are resolved
in the control graph; stack operations remain runtime instructions.
`statement_progress` proves by structural induction that every TM2 statement
executes at least one graph step before reaching its corresponding boundary
configuration. Mathlib's deterministic strict-simulation theorem supplies both
directions of halting equivalence. The resulting interface is

```lean
TM2ToBSM.compile_correct M e scratch entry v s :
  BSM.Halts (1, TM2ToBSM.compile M e scratch entry v, TM2ToBSM.mapStacks e s) ↔
    (StateTransition.eval (Turing.TM2.step M) ⟨some entry,v,s⟩).Dom
```

Here `M` has finite control and finite local store, `e` identifies its stack
indices with `Fin n`, and `scratch : Fin n` selects an existing stack whose
contents are restored by jumps. There is no empty-scratch or layout premise.

`BSMSource` specializes this to the fixed binary universal machine. It proves

```lean
BSMSource.reduce_primrec : Primrec BSMSource.reduce
BSMSource.halting_manyOneReducible :
  (fun p : Nat.Partrec.Code => (p.eval 0).Dom) ≤₀ @BSM.Halts 4
BSMSource.halting_not_computable : ¬ ComputablePred (@BSM.Halts 4)
```

Even one fixed compiled program has undecidable binary-word halting:
`BSMSource.wordHalting_not_computable`. The reduction supplies base address one,
that constant program, the encoded word on stack zero, and three empty stacks.
`reduce_primrec` certifies all input-dependent work. The chosen finite control
enumeration is fixed with the program; we do not claim a uniformly
primitive-recursive compiler on function-bearing TM2 syntax from classical
choice. These control-extraction/layout proofs are additions of this project,
using the credited Mathlib simulation API and Rocq BSM semantics.

## Completed BSM-to-MM simulation

Each binary stack is encoded in one natural-number register:

```text
code [] = 1
code (false :: s) = 2 * code s
code (true :: s) = 2 * code s + 1.
```

The two additional registers are zero at every simulated BSM boundary.
`MM.Arithmetic` proves transfer, doubling, and quotient/remainder computation
by actual increment/decrement instruction sequences. `MM.StackMacros` uses
these to implement push and pop. On pop, code one selects the empty branch
and restores one; otherwise division by two gives the tail and remainder
selects the Boolean branch. Every block takes at least one step, restores
the temporary registers to zero, and preserves all other stack registers.

`BSMToMM` places each block in sixteen slots, with a one-instruction entry
jump. Invalid source addresses map to zero. Lookup and placement proofs
discharge all local hypotheses, giving the public theorem

```lean
BSMToMM.compile_correct P s :
  MM.Halts (BSMToMM.compile P, BSMToMM.state s) ↔ BSM.Halts (1, P, s)
```

This specializes source programs to base address one, which is exactly the
interface of `BSMSource`. `MMSource` composes the compiler with that fixed
four-stack program and proves

```lean
MMSource.reduce_primrec : Primrec MMSource.reduce
MMSource.halting_manyOneReducible :
  (fun p : Nat.Partrec.Code => (p.eval 0).Dom) ≤₀ @MM.Halts 6
MMSource.halting_not_computable : ¬ ComputablePred (@MM.Halts 6)
```

The MM program is constant. `state_primrec` certifies the varying-input map;
no uniform `Primrec` theorem for the program compiler is claimed or needed for
this reduction. `wordHalting_not_computable` also gives undecidability with
that program fixed and only its initial encoded word varying.

## Completed MM-to-regular-FRACTRAN simulation

Choose pairwise distinct primes `a_i`, `b_i`, and `r_k`, for entry addresses,
private execution addresses, and registers. The encoding of `(i,v)` is
`a_i * ∏ k, r_k ^ v_k`; its execution-phase encoding replaces `a_i` by `b_i`.
For each instruction at address `i`, emit the following fractions in order:

| Instruction | Fractions |
| --- | --- |
| increment register `k` | `b_i / a_i`, then `(a_(i+1) * r_k) / b_i` |
| decrement register `k`, jump to `j` on zero | `b_i / a_i`, then `a_(i+1) / (b_i * r_k)`, then `a_j / b_i` |

FRACTRAN selects the first fraction `(p,q)` for which `q` divides `p*x`.
At either encoded phase, fractions from other addresses cannot apply: their
control-prime denominator divides neither their numerator nor the current
encoding. The entry fraction changes only the control prime. In the execution
phase, a positive counter makes the decrement fraction apply before the zero
branch; a zero counter makes it fail. The product identities in `registers_inc`
and `registers_dec` then give the next encoding.

This extra phase is important for self-jumps. In the upstream one-step encoding,
a zero-branch self-jump would yield `a_i/a_i`, applicable at every input.
Upstream first eliminates self-loops. Here the zero branch is `a_i/b_i`, whose
control primes remain distinct even when the jump returns to the same address.
`instruction_two_steps` proves exactly two target steps for every source step;
an out-of-code source address has no applicable target fraction. Thus

```lean
MMToFRACTRAN.compile_regular_correct P v :
  FRACTRAN.RegularHalts (MMToFRACTRAN.compile P, MMToFRACTRAN.state (1,v)) ↔
  MM.Halts (P,v)
```

There is no no-self-jump hypothesis. `RegularHalts (P,x)` means that all
denominators in `P` are nonzero and execution from `x` halts. On this regular
domain, `step_eq_some_iff` and `halts_iff_relStep` prove that the executable
semantics agrees with the upstream ordered relational rules. Zero denominators
are skipped outside that domain; no equivalence with upstream is claimed there.

`FRACTRANSource` specializes the construction to the fixed six-register program:

```lean
FRACTRANSource.program_regular : FRACTRAN.Regular FRACTRANSource.program
FRACTRANSource.reduce_primrec : Primrec FRACTRANSource.reduce
FRACTRANSource.regularHalting_manyOneReducible :
  (fun p : Nat.Partrec.Code => (p.eval 0).Dom) ≤₀ FRACTRAN.RegularHalts
FRACTRANSource.regularHalting_not_computable : ¬ ComputablePred FRACTRAN.RegularHalts
```

`input_positive` proves positivity of the varying initial value.
`wordHalting_not_computable` also proves undecidability with the regular program
fixed. The prime sequence uses Mathlib's `Nat.nth Nat.Prime`; it is marked
`noncomputable`. This does not supply a uniformly effective compiler or prime
enumerator. The program and the finitely many register primes are constants;
`registers_primrec` proves the finite product of their powers primitive recursive,
and `reduce_primrec` certifies all input-dependent work in the claimed reduction.

## Completed FRACTRAN-to-MMA2 simulation

The arithmetic blocks act on two registers X and Y. For a fraction `(p,q)`
with `q > 0`, the entry invariant is `(X,Y) = (x,0)`. The block uses the
following sequence, following `mma_fractran_one`:

| Stage | Registers after the stage |
| --- | --- |
| Multiply X by `p`, accumulating in Y | `(0,p*x)` |
| Test divisibility by `q`, transferring Y back to X | `(p*x,0)` on either branch |
| Success: divide X by `q`, then transfer Y back to X | `(p*x/q,0)`; restart the fraction scan |
| Failure: divide X by `p`, then transfer Y back to X | `(x,0)`; try the next fraction |

The failed test implies `p > 0`, since every positive `q` divides zero. This
discharges the recovery division's precondition; numerator zero is not excluded
from the compiler. Fractions need not be reduced, and input zero is supported.
`one_success` and `one_failure` prove positive progress through the actual
`29 + 4*p + 7*q` instructions, preserving every register outside the frame.
`MMA.Subtract` unifies the upstream subtraction and subtraction-with-copy
blocks through a Boolean flag; their instruction sequences are unchanged.

`scan_success` and `scan_failure` prove ordered selection for the assembled
fraction list. The full program restarts at address one after success; after
all tests fail, a final two-instruction jump halts at zero. In the halting
equivalence proof, `boundary` relates an immediately stuck source value to the
target after this final scan, and `initial_to_boundary` proves the connecting
execution. Its test is a finite one-step scan, not an eventual-halting oracle.
There is no empty-scratch or placement premise in the public theorem:

```lean
FRACTRANToMMA.compile_correct Q hQ x :
  MMA.Halts (FRACTRANToMMA.compile Q, FRACTRANToMMA.initial x) ↔
  FRACTRAN.Halts (Q,x)
```

The only hypothesis `hQ` is `FRACTRAN.Regular Q`. The compiler supplies the
initial register pair `(x,0)`. Unlike upstream `fractran_mma0`, this adaptation
does not zero the first register at the end: it proves ordinary halting, which
is exactly what the existing MMA2-to-MM2 reduction needs.

`MMA2Source` specializes this to `FRACTRANSource.program`, whose regularity is
already proved. Its `reduce_primrec` gives an unconditional reduction from
Mathlib code halting to `MMA.Halts` with two registers. `SourcePort.reduce`
then composes it with the previously proved `MMA2ToMM2.toZero`:

```lean
SourcePort.reduce_primrec : Primrec SourcePort.reduce
SourcePort.reduce_correct p : MM2.ZeroHalts (SourcePort.reduce p) ↔ (p.eval 0).Dom
SourcePort.source : MM2.SourceUndecidability
```

No source assumption remains. The intermediate programs are fixed constants;
all varying-input work, including the final zero-initialization loading prefix,
has explicit primitive-recursive evidence. No uniform effectivity claim for
the entire family of intermediate syntax compilers is needed or asserted.

## Credits and correspondence

The Lean adaptations, extensions, and connecting proofs in this directory are
provided by the [paper authors](../../../../AUTHORS.md). Credits below name
the authors of the original Rocq/Coq or Mathlib formalizations; they do not
attribute authorship of our Lean files to those upstream authors. The independent
`MathlibBridge` is this project's Lean development using Mathlib results, not a
Rocq port. Existing upstream copyright and license notices are retained separately.

The algorithm and correctness argument for zero initialization are adapted from
**Andrej Dudenhefner**,
[`MM2_HALTING_to_MM2_ZERO_HALTING.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/MinskyMachines/Reductions/MM2_HALTING_to_MM2_ZERO_HALTING.v).
The module preserves his loading-prefix and zero-preserving relocation
construction. In Lean, exact lookup/step reflection and Mathlib's deterministic
reachability comparison replace the upstream generic simulation/confluence
helpers. The explicit `Primrec` certification is added by this port.

The MMA2 representation-change proof is adapted from **Dominique
Larchey-Wendling**,
[`MMA2_to_MM2.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/MinskyMachines/Reductions/MMA2_to_MM2.v).
His [`MMA.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/MinskyMachines/MMA.v)
supplies the generic register-machine convention. The fixed
[`MM2.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/MinskyMachines/MM2.v)
credits **Dominique Larchey-Wendling and Andrej Dudenhefner**.

The MM model and stack simulation are adapted from **Dominique
Larchey-Wendling**'s
[`MM.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/MinskyMachines/MM.v),
[`mm_utils.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/MinskyMachines/MM/mm_utils.v),
[`mm_comp.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/MinskyMachines/MM/mm_comp.v), and
[`BSM_MM.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/MinskyMachines/Reductions/BSM_MM.v).
The sentinel encoding and transfer/doubling/division/push/pop instruction
sequences follow those sources. This port replaces their generic variable-size
layout with sixteen-slot blocks and an entry jump, specializes the source base
to one, and omits the final register-zeroing postlude: it proves ordinary MM
halting equivalence, not the stronger all-registers-zero halting result.
The explicit `Primrec` input proof and composition with Mathlib halting are
additions of this project.

The FRACTRAN semantics follows **Dominique Larchey-Wendling**'s
[`FRACTRAN.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/FRACTRAN/FRACTRAN.v).
The prime-power construction follows **Dominique Larchey-Wendling and Yannick
Forster**'s
[`mm_fractran.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/FRACTRAN/FRACTRAN/mm_fractran.v)
and [`MM_FRACTRAN.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/FRACTRAN/Reductions/MM_FRACTRAN.v).
The private execution phase replaces their self-loop-elimination pass; the
explicit Mathlib primitive-recursiveness proof and unconditional composition
are additions of this port. No claim is made that the two-phase layout itself
originated in those files or that it is a new technique.

The MMA arithmetic and fraction-scan simulation follow **Dominique
Larchey-Wendling**'s
[`mma_utils.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/MinskyMachines/MMA/mma_utils.v),
[`fractran_mma.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/MinskyMachines/MMA/fractran_mma.v), and
[`FRACTRAN_to_MMA2.v`](https://github.com/uds-psl/coq-library-undecidability/blob/11c41e0637f0c5219ad1c4c92d11609b7e072c31/theories/MinskyMachines/Reductions/FRACTRAN_to_MMA2.v).
This port preserves the arithmetic algorithms and fraction-block layout. It
uses explicit ambient placement and Mathlib's deterministic refinement API
instead of the upstream subcode/step-count comparison library, and omits the
unneeded final register-zeroing block. Primitive-recursive input certification
and the final composition with Mathlib code halting are additions of this port.

| Upstream declaration | Lean counterpart |
| --- | --- |
| `Argument.shift_instr`, `shift_state`, `M'` | `ZeroInitialization.shiftInstr`, `shiftState`, `compile` |
| `init_a0`, `init_b0`, `init_a0b0` | `initA`, `initB`, `initializes` |
| `mm2_step_sim`, `transport`, `reflection` | `step_shift`, `step_from_shift`, `compile_correct` |
| `reduction` | `halting_manyOneReducible_zeroHalting` in `ZeroInitialization` |
| `mma_mm2_instr`, `mma_mm2_state` | `MMA2ToMM2.instrEquiv`, `stateEquiv` |
| `mma_mm2_atom_equiv`, `mma_mm2_step_equiv`, `mma_mma2_reduction` | `next_correct`, `step_correct`, `terminates_correct` |
| `MMA2_MM2_HALTING` | `MMA2ToMM2.halting_manyOneReducible` |
| `mm_transfert`, `mm_mul2`, `mm_div2` and their specifications | `MM.Arithmetic.transfer_correct`, `double_correct`, `divide_correct` |
| `mm_push_Zero`, `mm_push_One`, `mm_pop` | `MM.StackMacros.pushZero`, `pushOne`, `pop` and their strict simulation proofs |
| `bsm_state_enc` | `BSMToMM.state`, `state_update`, `state_primrec` |
| BSM/MM whole-program simulation and halting reduction | `BSMToMM.compile_correct`, `MMSource.halting_manyOneReducible` (ordinary halting, as scoped above) |
| `fractran_step`, regular-program termination | `FRACTRAN.RelStep`, `step_eq_some_iff`, `halts_iff_relStep` |
| `encode_state`, `qs_encode_state`, register-product updates | `MMToFRACTRAN.state`, `reg_dvd_working`, `registers_inc`, `registers_dec` (two control phases) |
| `mm_fractran_simulation`, `MM_FRACTRAN_REG_HALTING` | `MMToFRACTRAN.compile_regular_correct`, `FRACTRANSource.regularHalting_manyOneReducible` (no self-loop preprocessing) |
| `mma_jump`, `mma_incs`, `mma_transfert`, `mma_mult_cst` | `MMA.Arithmetic.jump`, `incs`, `transfer`, `mult` and their correctness proofs |
| `mma_decs`, `mma_decs_copy` | `MMA.Arithmetic.subtract` with the copy flag false/true; `subtract_correct` |
| `mma_isempty`, `mma_mod_cst`, `mma_div_cst` | `empty_correct`, `modulo_correct`, `divide_correct` |
| `mma_fractran_one_ok_progress`, `mma_fractran_one_nok_progress` | `FRACTRANToMMA.one_success`, `one_failure` |
| `mma_fractran_step_success_progress`, `mma_fractran_step_failure_compute` | `scan_success`, `scan_failure` |
| `fractran_mma_reduction`, `FRACTRAN_REG_MMA2_HALTING` | `FRACTRANToMMA.compile_correct`, `MMA2Source.halting_manyOneReducible` (ordinary halting) |

This is a manually adapted proof checked by the Lean kernel, not an automatic
import or a kernel-checked translation of Rocq declarations. The two models use
different vector and instruction representations, as documented in `MMA.lean`.
Upstream constructive definability is not used as a substitute for Mathlib
computability: each claimed effective reduction has an explicit `Primrec`
theorem for its input-dependent map. This does not assert uniform primitive
recursiveness of every intermediate program compiler.

Relevant publications:

- Yannick Forster and Dominique Larchey-Wendling. *Certified Undecidability of
  Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines.*
  CPP 2019, pp. 104–117. [DOI: 10.1145/3293880.3294096](https://doi.org/10.1145/3293880.3294096).
  This is provenance for the broader mechanized machine-reduction development,
  not a claim that its complete reduction chain has been ported here.
- Andrej Dudenhefner. *Certified Decision Procedures for Two-Counter Machines.*
  FSCD 2022, 16:1–16:18.
  [DOI: 10.4230/LIPIcs.FSCD.2022.16](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2022.16).
  This treats the same positive-counter-jump instruction convention; the exact
  zero-initialization implementation is credited to its source file above.

## Completed source chain

The inspected suffix of the Rocq proof is:

```text
Mathlib → binary TM2 → BSM → MM → regular FRACTRAN → MMA2 → MM2 → zero-MM2
```

Every arrow is proved in Lean, with the adaptations described above.
Import `CounterMachines.Source` for `SourcePort.source`, or
`DistributedSynthesis.Results.UnconditionalUndecidability` for the closed finite-output and
binary-output encoded LTL theorems. The original conditional APIs, delayed
hierarchy, and restricted-network decidability results remain unchanged.

Validation: full `lake build` passes 4,585 jobs; 551 selected axiom endpoints
use only `propext`, `Classical.choice`, and `Quot.sound`; all 33 boundary tests
pass. Further work is optional review or optimization, not a missing source proof.

## License and source snapshots

The adapted Lean implementation files marked `SPDX-License-Identifier: MPL-2.0`
retain the upstream Mozilla Public License 2.0; the complete license is in
[`LICENSE-MPL-2.0`](LICENSE-MPL-2.0). This notice does not relicense unrelated
project files. Original credited source files are preserved in `upstream/` for
review, not imported into Lean or treated as axioms.

The independent `MathlibBridge` files use Apache-2.0, matching the credited
Mathlib development; its full license is in
[`LICENSE-APACHE-2.0`](LICENSE-APACHE-2.0). This does not change the license of
the Rocq adaptations.

The fifteen snapshots were checked byte-for-byte against the pinned upstream files.
The upstream names `MM_FRACTRAN.v` and `mm_fractran.v` differ only in case;
their local snapshots are named `MM_FRACTRAN_reduction.v` and
`mm_fractran_compiler.v` to coexist on case-insensitive filesystems. Their
contents are unchanged.
Their SHA-256 digests are:

| Snapshot | SHA-256 |
| --- | --- |
| `MM2.v` | `3054fe20af66dc1dd1a9a413802ad9c2c0df3211688a25900d28f53d895b02e9` |
| `MMA.v` | `ed57ff72ec0e96363e6657f27371a04ed7b28eaeb635c3c644235d634f71aead` |
| `MM2_HALTING_to_MM2_ZERO_HALTING.v` | `51aa6c9c899cc92d3fa9c2afa5bba7ace1c9c107fbadc8480e6d78c506264782` |
| `MMA2_to_MM2.v` | `c72a10cb9c880f3fd0aef8cb0bb7f8caaa3535dec2ab350866bbecd467f66168` |
| `BSM.v` | `f3e03edf3fc7cb2bff2abe8165d9c8a29f5272f7f661265f02203c839193a6ad` |
| `MM.v` | `d106422a057972d61c5bd410e68587f7e92781b8d2937799359da42c8d25dd22` |
| `BSM_MM.v` | `1928724c180059abeef0deb192e09a555b77758edb95649f2b0f53f5611b0929` |
| `mm_comp.v` | `be66376823b717d844cbfc8849ee0a8a4f8158235f1f45978289548141e03350` |
| `mm_utils.v` | `cab052c741c9b68225388c9a7c030bf88ea370158bd7118b589431e4f7026325` |
| `FRACTRAN.v` | `d63490b9cfa08816507f014c163879cee462a69b8d2c34e7d1f3e52b7d5680f0` |
| `MM_FRACTRAN_reduction.v` | `24a258f2e925794f39c64d70e99ce4cc4f7a4cdb50027e7d77967e089c18fd6d` |
| `mm_fractran_compiler.v` | `8afb9cbceebed83a68b126741b56cebff417a99f36c76f2bb55108359e854855` |
| `FRACTRAN_to_MMA2.v` | `311c79194173edd855b0b9fce7d46794a40328ce29f9244680e2c1828c7fc03c` |
| `fractran_mma.v` | `03d538fa672ca3442fc324f7aad114ea6048c9260b602204370a3a2b6a1b362f` |
| `mma_utils.v` | `f7971b8adf4e612a107a9d637325316b806f7e3c03ff477db8ca4dec5c585a05` |
