# A scaling safety objective that requires infinite memory

[Repository README](../../README.md). Commands and code paths in this note
are relative to the repository root.

The finite-DPA and LTL counterexamples are proved in
`LemScalingNoFiniteWinner.lean` and `LemScalingLTLWinner.lean` for
the repository's two-process, no-acknowledgement model. This construction
targets the unrestricted finite-winning-replacement claim itself, not merely
preservation of a selected source strategy.

## 1. Claim and model

There are singleton input alphabets, finite output alphabets, and a finite
deterministic safety automaton over the three graphs `left,right,both` such
that a perfect-recall distributed strategy wins, but no finite distributed
controller wins. More strongly, no finite blind library has an accepting
joint prescription tree for this automaton.

The model is exactly `advanceViewsWithEnvironment`: in a strict round one
endpoint receives both pre-round views and both current inputs; the other
endpoint receives nothing. Both receive views in a simultaneous round are
the same views they would have received in the corresponding strict rounds.
There is no acknowledgement distinguishing these cases. Outputs are emitted
after the current view update. The specification constrains outputs and
graphs only, not message contents.

## 2. The interval of local views

Initially place the view of process one at coordinate 0 and that of process
two at coordinate 1. Give a local view its depth and integer coordinate by
the following recursion:

```
empty one: (0,0)                  empty two: (0,1)
noRecv(v): (depth(v)+1, 3*coord(v))
recv(v,u): (depth(v)+1, coord(v)+2*coord(u)).
```

At depth `n`, the `3^n` environment histories form the edges of one path
with vertices `0,...,3^n`. The two endpoints of an edge are precisely its two
local views. Adjacent edges have literally the same local view at their
common vertex. The vertex at an even coordinate belongs to process one; the
vertex at an odd coordinate belongs to process two.

Here is the inductive verification, including the shared-view assertion.
For a parent edge with geometric endpoints `v,u`, its three child edges in
geometric order have endpoints

```
(noRecv(v), recv(u,v)),
(recv(u,v), recv(v,u)),
(recv(v,u), noRecv(u)).
```

The coordinates are respectively `(3j,3j+1)`, `(3j+1,3j+2)`, and
`(3j+2,3j+3)`. The two internal vertices are shared by the displayed
constructors. Adjacent parent edges retain a shared outer vertex because
both apply `noRecv` to their shared parent view. This proves all assertions
by induction; the ordering is a ternary reflected ordering of graph words,
not their ordinary lexicographic ordering.

If process one is the left endpoint, the child graphs in this order are
`right,both,left`. If process one is the right endpoint, they are
`left,both,right`. Thus the current orientation is tracked by one bit,
toggled exactly on `both`. The outermost edges are the all-`right` and
all-`left` histories.

The same induction applies to a blind library's accepting prescription tree:
adjacent edges have the same shared control, and their emitted labels at a
common vertex coincide. Within a parent, this follows from the shared receive
prescription. Across parent boundaries, it follows from applying the same
blind map to the same control. The receive prescriptions need not otherwise
be uniform over histories for this argument.

## 3. Finite labels and the safety automaton

A plan is `P=(w,a₀,a₁,a₂)`, with all four coordinates in `{2,3,4}`.
An output label is

```
ℓ=(m,c,P_L,P_R),
m ∈ {2,4},    c ∈ {0,1,2,3}.
```

The two plans describe the incident edge on the left and on the right.
A plan facing outside the path is unused and can be arbitrary. Both
processes use this same finite alphabet of `2*4*81² = 52,488` labels.

The monitor keeps an orientation bit, two boundary bits, an optional previous
edge plan, and a sticky failure bit. It starts with process one on the left,
both boundary bits true, no previous plan, and no failure. Given the graph,
it computes the child number `d∈{0,1,2}` by the ordering above and toggles
orientation on `both`. The left boundary bit persists exactly for child 0;
the right boundary bit persists exactly for child 2.

Let `ℓ,r` be the two current output labels put in geometric left-to-right
order using the updated orientation. Check all the following:

1. `ℓ.m=r.m`, and `ℓ.P_R=r.P_L`. Write the common plan as
   `P=(w,a₀,a₁,a₂)` and the common multiplier as `m`.
2. `a₀+a₁+a₂ + ℓ.c = m*w + r.c`.
3. At the left boundary require `ℓ.c=0`; at the right boundary require
   `r.c=0`.
4. If the previous plan exists, require its component `a_d` to equal the
   current weight `w`.

Store `P` for the next round. Any failed check sets failure forever. Give
nonfailed states priority 0 and failed states priority 1. This is a finite
DPA: its state space has at most `2*2*2*82*2 = 1,312` elements. In particular,
it never stores a depth, a coordinate, a row, or an unbounded integer.

The test involving all three child weights is a test of a finite plan in the
current output, not a branching-time test. On every next-round graph the
monitor checks the corresponding promised weight; universal winning makes
all three promises hold. This distinction is essential to the construction.

## 4. What every winner is forced to do

Fix any winning strategy. At depth `n≥1`, adjoining edges share their vertex
labels. Equality of endpoint multipliers on every edge therefore forces one
common multiplier `m_n∈{2,4}` throughout the row. Plan matching gives an
unambiguous weight `w_{n,j}∈{2,3,4}` for each edge `j<3^n`. Set

```
W_n = Σ_{j<3^n} w_{n,j}.
```

Consequently `2*3^n ≤ W_n ≤ 4*3^n`. Sum check 2 over every edge of the row.
The carries at internal vertices cancel; the two outer carries vanish by
check 3. Check 4 identifies each promised child weight with the weight of
that actual child edge. The children partition the entire next row. Hence

```
W_{n+1} = m_n W_n                      (n≥1).                 (★)
```

Every check used here is enforced on a finite prefix: if it failed there,
any extension would remain in the rejecting sink. Thus parity acceptance
really does imply these safety checks at every tree node.

The sequence `(m_n)` cannot be eventually periodic. Suppose it had positive
period `p` beyond depth `N≥1`, and let `M=∏_{i=0}^{p-1}m_{N+i}`. Iterating
(★) gives `W_{N+kp}=M^k W_N` for all `k`. Dividing the row bounds by
`3^{N+kp}` yields

```
2 ≤ (W_N/3^N) * (M/3^p)^k ≤ 4             for every k≥0.
```

A positive geometric progression bounded both above and away from zero has
ratio 1: a ratio greater than 1 has unbounded powers, and a ratio less than
1 has unbounded reciprocal powers. Thus `M=3^p`. But every multiplier is a
power of 2, so `M` is a power of 2, whereas `p>0` makes `3^p` divisible by 3.
This contradiction proves non-eventual-periodicity for **every** winner.

Along the constant `right` environment, process one is blind forever and
is the left boundary vertex at every depth. Its output multiplier must be
`m_n`. A finite blind controller on singleton input has an eventually
periodic output stream, since repetition of a control repeats its entire
future blind orbit. Therefore no finite controller wins. The identical
argument rules out an accepting tree over any library with finite first
blind control set, even if its receive prescriptions have infinite memory.

## 5. A winning perfect-recall strategy exists

The preceding constraints are consistent. Define integers `W_n` and `m_n`
recursively, beginning at depth zero:

```
W_0=3,
m_n = 2 if W_n ≥ 3*3^n, and 4 otherwise,
W_{n+1}=m_n W_n.
```

Induction gives `2*3^n ≤ W_n ≤ 4*3^n`. In the first case,
`6*3^n ≤ W_{n+1} ≤ 8*3^n`; in the second,
`8*3^n ≤ W_{n+1} < 12*3^n`. Both ranges lie in
`[2*3^{n+1},4*3^{n+1}]`.

For `0≤j≤3^n`, define the integer prefix mass

```
S_n(j) = floor(j W_n / 3^n).
```

The edge weights and vertex carries are

```
w_{n,j} = S_n(j+1)-S_n(j),
c_{n,j} = floor(m_n j W_n / 3^n) - m_n S_n(j).
```

Writing `jW_n/3^n=S_n(j)+r` with `0≤r<1` shows
`c_{n,j}=floor(m_n r)∈{0,...,m_n-1}⊆{0,1,2,3}`. The density bounds give
`w_{n,j}∈{2,3,4}`: the difference of floors at distance
`W_n/3^n∈[2,4]` lies between 2 and 4. At `j=0` and `j=3^n`, the fractional
part vanishes, so the carries are zero.

Choose the plan

```
P_{n,j}=(w_{n,j}, w_{n+1,3j}, w_{n+1,3j+1}, w_{n+1,3j+2}).
```

At vertex `j` of depth `n`, output

```
(m_n, c_{n,j}, P_{n,j-1}, P_{n,j}),
```

using any valid default plan for a missing boundary edge. A process computes
`n,j` from its own full view by section 2, so this is a genuine local
strategy without knowledge of the current graph or the other's receipt.

Plan matching, common multipliers, boundary carries, and next-round promised
weights hold by their definitions. For the remaining conservation check,
telescope the three child weights and use `W_{n+1}=m_nW_n`:

```
Σ_{d=0}² w_{n+1,3j+d}
 = floor((j+1)m_nW_n/3^n) - floor(jm_nW_n/3^n)
 = m_n w_{n,j} + c_{n,j+1} - c_{n,j}.
```

This is exactly check 2. Therefore every safety check succeeds on every
environment history, and the strategy wins.

## 6. The counterexample can also be specified in LTL

One must not infer LTL expressibility merely from the finite DPA above:
the orientation bit tracks a parity of past graphs. To remove that issue,
augment each output label by its vertex coordinate modulo 3. This increases
the output alphabet by a factor of three. The realizing strategy outputs
`j mod 3` with the label of vertex `j`.

Require the two residues to update from `(x,y)` according to

```
right: (3x, y+2x),
left:  (x+2y, 3y),
both:  (x+2y, y+2x),
```

with all expressions taken modulo 3 and initial residues `(0,1)` before
the first round. These are an initial-letter constraint and a constraint on
each pair of consecutive letters. Induction makes the residues the true
coordinates modulo 3 on every history. For adjacent integer coordinates,
process one is on the left exactly when `y=x+1 mod 3`; the other orientation
has `x=y+1 mod 3`. These cases are distinct. Orientation is now a predicate
of the current output letter, not hidden unbounded past information.

The common-mode, matching-plan, and conservation checks are predicates of
one current letter, using this orientation. The promised-child-weight check
is a predicate of a pair of consecutive letters, using the earlier letter's
orientation and the later letter's graph to choose `d`. Every such finite
relation is expressible in LTL: for a relation `R` on the finite letter
alphabet, use

```
G (∨_{(a,b)∈R} (letter=a ∧ X(letter=b))).
```

Finally the left-boundary carry condition is
`(graph=right ∧ carryOne=0) W (graph≠right)`, and the right-boundary
condition is its `left`/`carryTwo` mirror. Here `W` is weak until,
`φ W ψ := (φ U ψ) ∨ G φ`. This checks a zero boundary carry exactly as long
as the entire graph prefix stays at that boundary. Both formulae are imposed
at time zero; they do not restart after leaving the boundary.

Conjoin these formulas with the initial residue check and the global
one-letter checks. This is a finite LTL formula over output and graph atoms.
It has the augmented perfect-recall winner. Conversely every winner has
the true residues, hence satisfies all checks used in section 4 after
forgetting residues. No finite controller can therefore win this LTL
specification either. This construction does not assume that every safety
DPA language is LTL-definable.

The formal formula is `ScalingSafety.ResidueLTL.formula : LTL Letter`, with
`Letter` the finite augmented round-record alphabet. An atom names one
current letter and is interpreted by equality. Finite disjunctions express
one-letter predicates; for each possible first letter, a finite conjunction
requires the next letter to satisfy the corresponding relation. Thus atom
interpretation never inspects future letters or monitor states.

The boundary formula is written equivalently with release:
`(graph≠right) R (graph≠right ∨ carryOne=0)`, and its left mirror. The generic
`satisfies_boundary` lemma proves that this requires zero carry exactly when
the graph prefix through the current round consists entirely of the boundary
graph. It does not restart checks after leaving the boundary.

`formula_iff_accepts` proves, for every augmented infinite word `w`,

```
w satisfies formula  ↔  ResidueValid w ∧ objective.Accepts (forget ∘ w).
```

`lifted_wins` proves that the local coordinate-residue augmentation of the
explicit source satisfies this formula. `project_word` proves that forgetting
residues changes only a finite controller's output maps, not its local states
or transition maps. Together they yield `ltl_realizable_not_finite`.

## 7. Consequences and verification boundary

Taken together, sections 4 and 5 refute unrestricted finite blind
regularization and the corresponding universal finite-controller claim for
this no-acknowledgement model. This does not by itself prove undecidability
of perfect-recall realizability, and it does not conflict with decidability
results whose processes receive direct acknowledgements. Acknowledgements
separate the shared local views used in section 2.

The scaling idea is related to multiplicative constructions of aperiodic
tilings, for example [Aubrun and Kari, *Tiling problems on Baumslag–Solitar
groups*](https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?MCU2013.12.pdf=).
No tiling theorem is a premise here: the finite monitor, realizing strategy,
and contradiction are specified above directly in the current model.

`audits/check_scaling_candidate.py` independently interns literal local-view
constructors, enumerates all graph histories, checks the exact shared-view
path, and runs a finite monitor with no access to coordinates or depth. At
depth 10 it checks 88,572 transitions and 88,584 distinct local views; every
check succeeds. It also checks the modulo-three update, reconstruction of the
orientation, and the two-letter promised-weight relation of the LTL
extension. Negative tests check rejection after corrupting a multiplier or a
boundary carry, and persistence of the rejecting sink. These finite tests
are sanity checks, not proofs of the infinite statements.

The Lean verification consists of:

- `LemScalingAperiodicity`: bounds for the constructed mass sequence,
  bounded-geometric-progression rigidity, exclusion of periodic scaling for
  **every** mass/multiplier sequence with the stated recurrence and bounds,
  and the carry bound;
- `LemScalingSafetyObjective`: the finite DPA, exact cardinalities, equivalence
  of its parity acceptance to never failing a check, the shared receive-view
  identities, and the subdivision coordinates in both orientations;
- `LemScalingSourceLabels`: the floor-based weights and carries, all their
  finite bounds, and the exact conservation identity at every depth and
  coordinate;
- `LemScalingSourceWinner`: geometric induction on the actual local views,
  alignment with the actual DPA run, and `Source.wins`, which accepts every
  infinite environment for the explicitly defined local strategy;
- `LemScalingRowPath`: path refinement, propagation of a common endpoint
  value, and telescoping of the conservation equations;
- `LemScalingPhysicalRows`: rows built from the actual three physical
  successor controls, equality of their shared endpoints, their literal DPA
  states, zero boundary carries, uniform modes, and `row_recurrence` derived
  from acceptance. Its `rowMass n` denotes depth `n+1`, so the bounds use
  `3^(1+n)`; the unmonitored initial row is not assumed to pass a check;
- `LemScalingNoFiniteWinner`: eventual periodicity of a finite blind endpoint,
  `no_finite_winner`, the combined `realizable_not_finite` theorem,
  `no_accepting_finite_blind_library`, and the negation of the positive
  development's exact `PerStrategyWinningFinitePairedPhysicalController`
  gate;
- `LemFiniteLetterLTL`: literal finite-letter LTL formulas and their exact
  semantics, including the boundary release formula;
- `LemScalingLTL`: modulo-three orientation, all-depth boundary flags, and the
  exact equivalence between LTL satisfaction and residue-valid DPA acceptance;
- `LemScalingLTLWinner`: local residue augmentation, actual execution
  projection, finite-controller projection, and `ltl_realizable_not_finite`.

In particular, `realizable_not_finite` has no source-agreement, common-mode,
row-conservation, or replacement-progress hypothesis. Its positive half
quantifies over all actual environment sequences. Its negative half
quantifies over all finite paired physical controllers, permitting different
finite types and arbitrary output replacement. The finite-library corollary
uses the existing sound accepting-tree-to-physical-controller compiler; it
assumes both library control types finite, rather than formalizing the
stronger one-finite-side variant of the direct mathematical argument.

Use the [overview's verification commands](../../README.md#build-audit-and-maintain).
The axiom audit includes source execution, physical row recurrence, LTL
language transfer, and the final endpoints. The independent finite-depth
checker, including its negative tests, is not a premise of any Lean theorem.

This separation theorem alone gives no decidability or undecidability
conclusion about unrestricted perfect-recall realizability. It settles
the universal finite-winning-replacement claim negatively for both finite
safety DPAs and LTL specifications.

## 8. Relation to the proved delay-one hierarchy

The counterexample does not invalidate `delayOneHierarchy_left/right/both`
or `summaryGameDelayOneViewHierarchy_holds`. The latter quantifies over all
alternative summary-game histories with the same pending full view and
determines the other process's settled observation prefix. This is not the
same premise as equality of finite summary-observation histories, nor does
it prove strict hierarchy of accumulated non-fringe core histories.

Consequently the established view-level delayed hierarchy and the failure
of finite winning replacement coexist in this model. This is a limitation
of using that structural property as a synthesis criterion, not a proof that
the only missing ingredient is a locally recognizable leader. The existing
`Berwanger2018` adapter requires additional settled/core hierarchy explicitly.

The separate [counter-machine reduction](COUNTER-MACHINE-REDUCTION.md) uses
counter densities, mass factors `1,3,9`, and an exact finite zero test.
Its soundness, completeness, encoded compiler, and source proof are complete;
`DistributedSynthesis.Results.UnconditionalUndecidability` exports the closed
Lean result. This is a computation encoding, not a conversion of the transient
fringe bit into a persistent private information channel.

Since the scaling formula is realizable with perfect recall but not by a
finite controller, the two existence predicates cannot be identified when
transferring a decidability or undecidability result.
