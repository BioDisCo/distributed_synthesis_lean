# Computation by ternary row masses

[Repository README](../../README.md). Commands and code paths in this note
are relative to the repository root.

The feasibility test yields a mathematical reduction from two-counter
nonhalting to perfect-recall realizability.
The distributed equivalence is now proved end to end in Lean:
`CounterMachine.ResidueLTL.ltl_realizable_iff_nonhalting`. It covers the
finite monitor, arbitrary perfect-recall strategy rows, exact machine
soundness, the local winning source, and the literal LTL translation.
The exact classical MM2 source adapter is also checked; see
`SOURCE-UNDECIDABILITY.md`. The source theorem is isolated as the explicit
`SourceUndecidability` parameter in the reusable API; its credited Lean port is
now complete and `SourcePort.source` proves that interface.
The **encoded compiler and undecidability composition are now checked**:
`CounterMachine.Compiler.compileInstance_primrec` proves primitive
recursiveness, and `encoded_ltl_synthesis_undecidable` derives undecidability
of the encoded LTL problem from the explicit source parameter.
`CounterMachine.Unconditional.encoded_ltl_synthesis_undecidable` supplies the
proved source and gives the unconditional single-kernel endpoint. Import
`DistributedSynthesis.Results.UnconditionalUndecidability`.

This note concerns the exact singleton-input, two-process, full-view,
no-acknowledgement model of `SCALING-COUNTEREXAMPLE.md`. No bound on process
memory or message size is assumed. LTL specifications may inspect the graph
component of a round, as permitted by the repository's LTL API; the processes
are not supplied that graph as a local input. The finite output alphabet below depends
effectively on the machine. The separate fixed binary-output reduction is
proved in [BINARY-OUTPUTS.md](BINARY-OUTPUTS.md).

## 1. Source problem and the change from tape to counters

Let a deterministic two-counter machine have a finite control set `Q`, an
initial control `q₀`, and one instruction at each control:

- `inc(r,p)`: increment counter `r∈{1,2}` and go to `p`;
- `dec(r,p₀,p₊)`: if counter `r` is zero, leave it unchanged and go to `p₀`;
  otherwise decrement it and go to `p₊`;
- `halt`.

Both counters initially equal zero. Halting for precisely this instruction
set and initialization is stated in Bell and Potapov, section 2.1,
Proposition 1, [Periodic and Infinite Traces in Matrix Semigroups](https://www.csc.liv.ac.uk/~igor/papers/sofsem2008.pdf).
For a modern mechanized reference and the importance of the instruction
set, see Dudenhefner, Definition 2 and Theorem 6,
[Certified Decision Procedures for Two-Counter Machines](https://drops.dagstuhl.de/opus/volltexte/2022/16297/pdf/LIPIcs-FSCD-2022-16.pdf).
Its increment-successor and conditional-decrement instructions are instances
of ours; a finite initial-value instance can be initialized from zero by a
finite prefix of increments. No undecidability theorem about tilings or
finite-state distributed synthesis is used in the reduction below.

Instead of representing a tape in the expanding rows, represent a counter
value `c` by density `3^(-c)`. Physical depth `n≥1` represents machine time
`n−1`. A row has length `Lₙ=3^n`; for counter `r`, let its binary edge weights
be `w⁽ʳ⁾ₙ,ⱼ` and their sum be `W⁽ʳ⁾ₙ`. The intended invariant is

```
W⁽ʳ⁾ₙ · 3^(c⁽ʳ⁾ₙ₋₁) = 3^n.                         (1)
```

When depth increases by one, the required mass multipliers are:

| Counter operation | New counter | Mass multiplier |
| --- | --- | --- |
| increment | `c+1` | `1` |
| unchanged | `c` | `3` |
| positive decrement | `c−1` | `9` |

These are fixed small integers. They fit the previously verified finite
carry-and-promised-children mechanism.

## 2. The finite zero test

Each vertex outputs two Boolean claims `z₁,z₂`, where `true` means zero.
Require endpoint claims to agree on every edge. The shared-view row is a
connected path, so each claim is common throughout the row.

For each counter impose:

1. If `zᵣ=true`, the weight of **every** edge is one.
2. If `zᵣ=false`, the weight of the **leftmost** edge is zero.

The second check is a boundary check, just like the already used carry
condition. No process is given a boundary detector; the specification checks
it along the all-`right` graph prefix.

For any binary row of positive length `L`, these rules imply

```
zᵣ=true  iff  Wᵣ=L.                                  (2)
```

Indeed, a true claim forces `L` ones. A false claim permits at most `L−1`
ones because the leftmost bit is zero. This argument applies to arbitrary
row labelings, not just the proposed source. Combining (1) and (2) gives
`zᵣ=true iff cᵣ=0`: if `Wᵣ=L>0`, (1) forces `3^cᵣ=1`; the converse follows
by substituting `cᵣ=0` in (1).

The source can satisfy the false-claim boundary check for every positive
counter, as shown in section 5. No comparison with an approximate density,
positive real number chosen without initialization, or unbounded counter
stored in the monitor is involved.

## 3. Explicit finite monitor

A plan for one counter is `P=(w,a₀,a₁,a₂)∈{0,1}⁴`. Each process emits

```
ℓ = (q, z₁,z₂, e₁,e₂, P¹_L,P¹_R,P²_L,P²_R),
q∈Q,  zᵣ∈{false,true},  eᵣ∈{0,…,8}.
```

There are `|Q|·4·9²·16⁴` labels before adding the modulo-three residue for
LTL. All components are finite and effectively enumerable.

From `(q,z₁,z₂)`, the machine instruction determines a next control
`next(q,z)` and two multipliers `mᵣ(q,z)∈{1,3,9}`. An increment uses `1`
for the incremented counter and `3` for the other. A zero decrement branch
uses `3` for both counters; a positive branch uses `9` for the decremented
counter and `3` for the other. Halting controls are rejected.

The monitor retains orientation, the two outer-boundary flags, a first-round
flag, and the previous common control, zero claims, and two edge plans.
As before, the graph determines the next child digit `d`, the new
orientation, and the surviving boundary flags. Put the current outputs in
geometric order `(ℓ,r)` and perform these finite checks:

1. Their controls and zero claims agree, and `q` is nonhalting.
2. For each counter `r`, the two incident plans match. Write their common
   plan as `Pᵣ=(wᵣ,aᵣ₀,aᵣ₁,aᵣ₂)`.
3. For each counter, check
   `aᵣ₀+aᵣ₁+aᵣ₂+eᵣ_left = mᵣ(q,z)wᵣ+eᵣ_right`.
4. A true zero claim requires `wᵣ=1`. At the left boundary require
   `eᵣ_left=0` and, for a false zero claim, `wᵣ=0`. At the right boundary
   require `eᵣ_right=0`.
5. On the first round require `q=q₀` and `w₁=w₂=1`.
6. On every later round require the current control to be the next control
   determined by the previous control and zero claims. Require each current
   weight to equal component `d` of its previous edge plan.

Failure is absorbing. Priorities zero on good states and one on failed
states turn these checks into a deterministic safety DPA. The monitor does
not contain coordinates, row lengths, row sums, or counter values.

## 4. Soundness: no spurious accepting computation

Fix an arbitrary perfect-recall strategy that wins against all environments.
At each depth, the histories form the connected shared-view path described
in section 2 of `SCALING-COUNTEREXAMPLE.md`. Outputs at shared vertices are
equal because a local strategy is a function of its local view. Therefore
check 1 gives one common `qₙ,zₙ` per row, and check 2 gives well-defined edge
weights for both counters.

Every finite history can be extended to an infinite environment. Since a
failed check remains failed forever, universal acceptance implies all six
checks at every finite history.

Fix a depth and a counter. Sum check 3 across that row. Internal carries
cancel because they belong to shared vertex labels; the two boundary carries
vanish by check 4. Check 6 identifies each promised weight with the actual
weight on its corresponding child. The three children of every edge
partition the next row. Consequently

```
W⁽ʳ⁾ₙ₊₁ = mᵣ(qₙ,zₙ) W⁽ʳ⁾ₙ.                          (3)
```

The first row has three edges, so check 5 gives `q₁=q₀` and both masses
equal to three. Thus (1) holds for the initial machine configuration.

Assume the configuration is correct at depth `n`. Section 2 proves that
both zero flags are its actual zero tests. The chosen control successor
and operations are therefore exactly those of the machine instruction.
Equation (3) preserves (1): multiplication by `1` compensates for increasing
the exponent by one; multiplication by `3` compensates for the row-length
increase alone; multiplication by `9` compensates for both row growth and
a positive decrement. For the decrement, use `c≥1` and
`9·W·3^(c−1)=3·W·3^c`. This proves the induction.

Thus the row controls and encoded counter values are the machine's unique
run, without any assumption that the arbitrary winning strategy uses the
source's spatial arrangement of bits. A halt in that run would put a
halting control in a row, violating check 1. The machine therefore never
halts. This excludes the relevant cheating possibilities:

- controls or zero claims cannot vary between histories in one row;
- fractional or all-zero mass trajectories cannot enter from the forced
  initial row;
- false zero branches contradict (1) and (2);
- mass cannot be created at an internal or outer boundary;
- promised children cannot be replaced by unrelated future weights;
- the machine cannot be paused or restarted unless its own instructions do
  so, because every next physical row must have the specified successor.

## 5. Completeness: every nonhalting run gives a local winner

Suppose the machine does not halt. Let `(qₜ,c¹ₜ,c²ₜ)` be its run from zero.
At time `t`, each counter is at most `t`. Therefore at depth `n=t+1`,
`cᵣₜ≤n−1`, and `Dᵣₙ=3^(cᵣₜ)` divides the row length `3^n`.

For counter `r` define prefix counts, edge weights, and vertex carries by

```
Fᵣₙ(j) = floor(j / Dᵣₙ),
wᵣₙ(j) = Fᵣₙ(j+1) − Fᵣₙ(j),
eᵣₙ(j) = floor(mᵣₙ j / Dᵣₙ) − mᵣₙ floor(j / Dᵣₙ).
```

Weights are zero or one. If the counter is zero then `D=1`, and all weights
are one. If it is positive then `D≥3`, and the first weight is zero.
Writing `j=Dk+s`, with `0≤s<D`, gives `e(j)=floor(ms/D)`, so
`0≤e(j)<m≤9`. Both boundary carries are zero because both boundary
coordinates are multiples of `D`.

The three operations satisfy

```
3 / Dᵣₙ₊₁ = mᵣₙ / Dᵣₙ,
Fᵣₙ₊₁(3j) = floor(mᵣₙ j / Dᵣₙ).                     (4)
```

Subtract (4) at `j` from (4) at `j+1`, and telescope the three child
weights. Substituting the definition of `e` yields exactly check 3. Choose
each plan to contain its weight and its three actual next-row weights.
Then all promised-child checks hold as well. The chosen controls and flags
follow the actual run; initialization and all remaining checks hold.

Each process computes its own depth and coordinate from its local view
using the existing recursion. At depth `n≥1`, coordinate `j`, it outputs
the common control and flags of machine time `n−1`, the two carries at `j`,
and plans for edges `j−1` and `j`. Outside-facing plans are arbitrary finite
defaults. Initial empty-view outputs are unused and may also be defaults.
These are genuinely local functions. Although the functions can use
unbounded computation and memory, this is precisely the perfect-recall
strategy class in the question. No observation of the global graph or
leader role is supplied to them.

## 6. Effective LTL translation and consequence

Add each vertex coordinate modulo three to its output. Require the same
initial residue update and global consecutive-letter residue updates as in
`LemScalingLTL`. These identify the geometric orientation from the current
letter. The rest of the specification consists of:

- finite current-letter predicates for checks 1--3 and true zero claims;
- a first-letter predicate for check 5;
- a finite consecutive-letter relation for control succession and promised
  child weights;
- the left boundary condition
  `(graph≠right) R (graph≠right ∨ B_left)`, where `B_left` asserts both
  carries are zero and every false zero claim has incident weight zero;
- the analogous right boundary condition, requiring both right carries zero.

Here `R` is release. Boundary conditions start at time zero and do not
restart on a later return to the same graph. On the all-`right` prefix,
process one is the geometric left endpoint, so `B_left` is a predicate
of its current output alone. The right case is mirrored.

All predicates and relations are decidable finite tables obtained from the
machine's finite instruction list. Enumerating the letters and expanding
these tables as finite conjunctions/disjunctions of letter atoms and `X`
is an effective construction of a finite LTL formula `φ_M`; the size need
not be small. The already proved `FiniteLetterLTL` lemmas justify that
expansion. `LemCounterMachineLTL` now proves the machine-dependent language
equivalence and both strategy transfers. An explicit recursive encoding of
the construction remains separate from this semantic theorem.

Sections 4 and 5, with the residue update argument, give the mathematical
equivalence

```
M does not halt from (q₀,0,0)
    iff φ_M has a perfect-recall winning strategy.              (5)
```

A decision procedure for perfect-recall realizability of these finite LTL
instances would decide nonhalting, and hence halting, of these machines.
Thus (5) gives undecidability for the uniform problem with finite alphabets
as part of the instance. This is a new reduction in the perfect-recall
model, not a transfer from finite-state synthesis undecidability. The
established delay-one view hierarchy remains valid in this same model.

## 7. Audit and formalization boundary

The Lean module `LemTernaryCounterSoundness` checks the exact binary-row zero
test (`guard_exact`), uniqueness of zero under the integer invariant
(`encoded_zero`), all three counter updates (`encoded_step`), and induction
over every certified operation sequence (`forced_counts`). It also checks
the source weight bounds, positive-counter boundary weight, carry bound,
three-child conservation, and total row weight. The recurrence and zero
guard are premises of `forced_counts`; this theorem does not by itself
extract them from arbitrary distributed acceptance.

`audits/check_counter_rows.py` separately implements the actual finite monitor and
tests all graph histories using interned full-view constructors. It tests
unbounded increment, growth of both counters, zero/decrement loops, and
halting rejection. It also enumerates arbitrary binary rows of widths three
and nine, not just the source rows, to test conservation and the zero guard.

An ablation produces an explicit bad construction: remove only the initial
weight-one requirement, and a machine that tests zero and otherwise
decrements back to itself admits constant all-zero labels claiming both
counters positive. All carries and plans are zero, so all remaining checks
pass, although the real zero-initialized machine halts. The full monitor
rejects this construction on the first boundary history. Initialization
is therefore an essential hypothesis, not a cosmetic convention.

The actual-model links are now complete. `LemCounterMachineMonitor` defines
the machine-dependent finite DPA; `LemCounterMachineViewRows` proves the
shared-row structure for arbitrary perfect-recall strategies;
`CounterMachine.Rows.winning_implies_nonhalting` in
`LemCounterMachineRowSoundness` forces the exact machine run. `LemCounterMachineSource`
constructs an actual local winner. `LemCounterMachineLTL` supplies the literal
formula and proves `CounterMachine.ResidueLTL.ltl_realizable_iff_nonhalting`.
These results do not assume externally supplied row certificates.

The encoded recursive compiler and its composition are now checked in
`ThmCounterMachineEncodedUndecidability`. For a source program `P`, the
compiler returns `(P.length, c_P)`, where `c_P` is a finite postfix LTL
string. The target uses output type `Output (Fin (P.length + 1))` for each
process and the original local perfect-recall execution semantics. The
proved equivalence is `EncodedRealizable (compileInstance P) ↔ ¬ ZeroHalts P`.
Consequently, the checked many-one reduction transfers the explicit source
undecidability premise to this encoded synthesis problem.

For effectivity, split each letter into two natural control numbers and a
payload in a fixed finite type. Enumerate the controls from zero to the
alphabet bound, filter letters and pairs using the machine checks, and
expand each table into disjunctions of letter atoms (with a next operator
for the second letter of a pair). The payload enumeration and its coding
are fixed constants, independent of the source program. Their definitions
use classical choice, but every program-dependent operation has a checked
primitive-recursive proof. Formula assembly uses conjunction, always, and
release, with a proved correspondence to the original five conditions.
Thus the computability obligation is discharged, not assumed.

`SourcePort.source` now supplies the source interface. The separate Boolean-
output strengthening is complete as well; see `BINARY-OUTPUTS.md`. Neither
result requires reopening finite-controller extraction or a transient-bit
information-fork argument.

Use the [overview's verification commands](../../README.md#build-audit-and-maintain).
The independent `python3 audits/check_counter_rows.py --depth 10` checks 265,755
passing literal transitions, rejects every branch of the tested first
halting rows, checks 7,680 arbitrary row-pair/multiplier cases, and reproduces
the missing-anchor cheat when that check is deliberately disabled.
These finite tests are independent sanity checks,
not a substitute for either direction of the infinite proof.
