# Monadic second-order logic and tree-language operations

The development uses the project's pinned Lean/Mathlib **4.30.0**. It introduces
full MSO syntax and semantics and proves **Rabin's semantic language
characterization**: MSO-definable languages of full infinite labelled trees are
exactly the languages recognized by nondeterministic parity tree automata.
Both semantic translations have unconditional correctness theorems.
`EffectiveRabin` additionally provides **executable translations and Boolean
satisfiability/validity procedures**, reusing the existing Piterman compiler and
finite-policy nonemptiness solver. The semantic APIs remain available.

## Imports and reuse

```lean
import DistributedSynthesis.Library.Logic.MSO.Semantics
-- Generic logic over an existing Mathlib first-order structure.

import DistributedSynthesis.Library.Logic.MSO
-- Tree interpretation and both directions of Rabin's semantic equivalence.
```

The namespace is `DistributedSynthesis.MSO`. `Formula L n m` has `n` free
individual variables and `m` free set variables. Its `firstOrder` constructor
embeds Mathlib's `L.Formula (Fin n)`; its other primitive constructors are
membership, falsity, implication, and universal quantification of either sort.
Existential quantifiers and the other Boolean connectives are derived. A binder
appends its variable using `Fin.snoc`, with index `Fin.last` in the body.

`Formula.Realize φ nodes sets` uses the existing `L.Structure M`. Set variables
range over **all `Set M`**, including infinite subsets. Renaming has a semantic
correctness theorem (`Formula.realize_rename`). `Formula.realize_reachable`
identifies the formula expressing membership in every successor-closed set
with Mathlib's `Relation.ReflTransGen`.

`MSO.Tree` interprets the logic on the existing `TreeNode Branch` and
`LabeledTree Branch Alphabet`. Its signature has the root, directional successor
functions, child relation, and input-label predicates. `realize_ancestor` proves
that the MSO ancestor formula is precisely list prefix, including equality.
There is no new model of trees, finite sets, or parity acceptance.

## Checked automata constructions

All automata below are the existing `RunParityTreeAutomaton`, with the existing
run and min-even parity semantics.

| Module in `Library.Automata` | Construction and correctness theorem |
| --- | --- |
| `TreeLocal` | Node-local, root, and directional edge tests; `localTest_accepts_iff`, `rootTest_accepts_iff`, `edgeTest_accepts_iff` |
| `TreeSingleton` | Exactly one marked node, including existence; `accepts_iff` |
| `TreeProjection` | Inverse letter maps and existential label projection; `project_acceptsTree_iff` |
| `TreeAcceptanceGame` | Fixed-input-tree game; `accepts_iff_even_winning` and `rejects_iff_odd_winning` |
| `TreeComplement` | Nondeterministic tree-language complement; `accepts_iff` |
| `TreeBoolean` | Intersection and union; `inter_accepts_iff`, `union_accepts_iff` |
| `UniversalThreads` | Existing finite-thread system and universal word determinization, moved out of the application import closure with names and proofs preserved |
| `SequenceParity` | Existing finite-range recurrence lemmas, extracted without changing their statements |

Projection guesses one letter per tree node, shared by all branches through
that node. Its correctness theorem quantifies over one coherent lifted tree.
With finite source letters and decidable transition data, projection transitions
have a decidable instance.

Complementation applies to finite, nonempty branching and finite input
alphabets. It uses countable parity-game positional determinacy to obtain one
rejecting strategy. Each node is decorated with a finite table choosing a
direction for each state and proposed successor vector. The existing Piterman
construction checks every thread following those tables, then projection
forgets the tables. Missing transitions are handled by the odd sink in the
acceptance game. The complement theorem has no assumed determinization,
complementation, or rational-run certificate.

Intersection uses a synchronous product and the existing deterministic
Muller-to-parity construction for the two parity conditions. Taking a minimum
of priorities does not implement this operation. Union is obtained by De Morgan's
law using the actual tree-language complement.

`TreeComplement` and `TreeBoolean` remain the semantic APIs.
`TreeComputable` supplies executable counterparts with state-equality and
transition deciders. `UniversalThreadsComputable` uses the existing executable
Piterman compiler; `ParityPairComputable` checks both priority streams using
that universal-thread construction. The old `ThmBundleDeterminization` entry point continues to re-export the moved
finite-thread declarations and its previous application dependencies.

## MSO translation steps

`Tree.encode` decorates labels with Boolean variable markers. Individual
variables mark exactly one node; set variables mark arbitrary subsets.
`Tree.Represents A φ` states exact correctness on these encoded valuations.
It says nothing about malformed individual-variable markers.

`MSO.Compilation` proves:

- `falseAutomaton_correct`, `membershipAutomaton_correct`,
  `equalityAutomaton_correct`, and `labelAutomaton_correct`;
- `complement_represents`, `inter_represents`, `union_represents`, and
  `impAutomaton_correct`;
- `project_represents_exSet` and `allSetAutomaton_correct`.

The last two quantify over arbitrary sets. The projection proof establishes
that every lift preserving the old markers is exactly the encoding of one
additional set (`dropSet_eq_encode_iff`). Correctness of the body automaton is
an explicit induction hypothesis in these construction lemmas, not an assumed
general MSO-to-automaton theorem.

`MSO.NodeQuantification` proves `exNodeAutomaton_correct` and
`allNodeAutomaton_correct`. Before projecting an individual marker, it intersects
the body automaton with `TreeSingleton.automaton`. Its searching state follows
one child until it finds the marker; all other subtrees forbid markers. Odd
priority during the search excludes an infinite unsuccessful search. Thus no
extra assumption about malformed inputs of the body automaton is required.

`MSO.TreeAtoms` adds `rootAutomaton_correct`, `successorAutomaton_correct`,
and `childAutomaton_correct`. The child relation uses a finite union of the
directional successor automata.

## Complete translations and Rabin equivalence

The main theorems live in `DistributedSynthesis.MSO.Tree`:

| Endpoint | Exact guarantee |
| --- | --- |
| `toAutomaton_correct φ` | Every formula is recognized on its encoded free individual and set valuations |
| `sentenceAutomaton_correct φ tree` | `sentenceAutomaton φ` accepts `tree` iff `Satisfies tree φ` |
| `ofAutomaton_correct A tree` | `Satisfies tree (ofAutomaton A)` iff `A.acceptsTree tree` |
| `definable_iff_recognizable L` | Existence of an MSO sentence defining `L` iff existence of a parity tree automaton recognizing `L` |
| `automaton_roundtrip`, `sentence_roundtrip` | Translating in both directions preserves the accepted language or sentence meaning |

These results require `[Fintype Branch] [Nonempty Branch] [Fintype Alphabet]`.
No nonemptiness hypothesis is needed for the alphabet. The forward translation
produces an automaton with its finite state type in universe zero; the reverse
translation accepts the existing universe-polymorphic automaton type. The
language-equivalence statement uses universe-zero state types. In particular,
it applies to the usual full infinite binary trees.

`Terms` recognizes the graphs of arbitrary terms using witness nodes.
`FirstOrder` handles every Mathlib bounded-formula constructor, flattening free
and bound individual variables into one marker context. `ToTreeAutomaton`
then proves `formula_recognizable` by structural induction over every MSO
constructor. Correctness of the body automata is discharged by that induction,
not assumed at the public translation endpoint.

For the reverse direction, `Branches` defines complete infinite branches by
root membership, ancestor closure, and exactly one continuing child, and proves
that these sets are precisely the ranges of the existing `branchNode` paths.
`AutomatonRuns` assigns one set to each state, using a partition and the actual
local transition relation. `AutomatonParity` expresses recurring priorities as
cofinal occurrences in the ancestor order and proves equivalence to the
existing `NatSeqMinEvenParity`. `FromTreeAutomaton` existentially binds all
state sets and universally checks all branch sets. It uses Mathlib's
`Fintype.equivFin`; it does not introduce a separate finite-set representation.

`Rabin` assembles these two translations into the language characterization.
It assumes neither a compiler certificate nor a determinacy certificate.
The proofs ultimately use the existing checked positional determinacy and
Piterman constructions through tree complementation.

## Executable translations and decisions

```lean
import DistributedSynthesis.Library.Logic.MSO.EffectiveRabin
open DistributedSynthesis.MSO.Tree

-- Executable.compile φ            -- automaton for a formula with free variables
-- Executable.sentenceAutomaton φ  -- automaton over the original alphabet
-- Executable.satisfiable φ        -- Bool
-- Executable.valid φ              -- Bool
-- Automaton.Ordered.ofAutomaton A -- executable reverse translation

#eval Executable.satisfiable (Branch := Unit) (Alphabet := Unit) .falsum
-- false
```

The forward compiler takes the same `MSO.Formula` syntax, including arbitrary
embedded Mathlib first-order terms and formulas. It requires finite enumerations
and decidable equality for directions and alphabet, with nonempty directions.
The decision procedures additionally take an `Inhabited Branch` instance. With
ordinary numeric carriers such as `Fin (d+1)` and `Fin a`, these inputs are
executable without classical choices. Full powerset semantics is preserved;
the algorithm does not enumerate infinite sets or trees.

`TreeAutomatonData` wraps the existing `RunParityTreeAutomaton` with state
equality and transition deciders. `Recognition` stores this data together with
its correctness proof. The term, first-order, and MSO recursions construct those
records directly. No automaton is selected from an existential theorem.
The generic finite-thread adapter follows the library's existing
`ThreadComputable` pattern: it supplies executable enumeration and deciders,
and `buchi_eq` identifies its entire automaton record with the existing
violation Büchi automaton. `universalDPA_eq` identifies the resulting universal
monitor with the semantic one. The original thread declarations are unchanged;
there is no new finite-set representation or alternative acceptance condition.

The endpoint `Executable.compile_correct` proves correctness on every encoded
valuation. `Executable.sentenceAutomaton_correct` proves correctness on every
input tree. The existing finite-policy and finite-orbit nonemptiness search
then yields the exact decision theorems:

```lean
Executable.satisfiable φ = true ↔ ∃ tree, Satisfies tree φ
Executable.valid φ = true       ↔ ∀ tree, Satisfies tree φ
```

For the reverse translation, `Automaton.Ordered.ofAutomaton` takes finite,
linearly ordered direction, alphabet, and state carriers, and decidable
transitions. These orders supply executable enumerations; numeric finite-table
automata satisfy this interface. It reuses `FiniteOrders.functionOrder` for
successor assignments and Mathlib's `monoEquivOfFin` for state numbering.
`Automaton.Ordered.ofAutomaton_correct` proves the same language semantics as
the earlier reverse translation. `Executable.automaton_roundtrip` proves that
composing the executable reverse and forward translations preserves every input
tree's acceptance.

All these constructors and decision procedures are ordinary executable `def`s.
Classical reasoning occurs in their correctness proofs, which are erased when
code is generated, not as a decision oracle. The implementation is deliberately
exhaustive: state enumeration and repeated determinization can be prohibitively
large. There is no efficiency claim. A small additional determinization runtime
experiment was stopped before completion because of the exhaustive state-space
construction; it is not counted as a passed execution test.

## Primitive-recursive numeric procedures

```lean
import DistributedSynthesis.Library.Logic.MSO.PrimitiveRecursive
open DistributedSynthesis.MSO.Tree

#check Numeric.compile_primrec       -- Primrec Numeric.compile
#check Numeric.satisfiable_primrec   -- Primrec Numeric.satisfiable
#check Numeric.valid_primrec         -- Primrec Numeric.valid
#check Numeric.compileNat_primrec    -- Nat.Primrec Numeric.compileNat
#check Numeric.satisfiableNat_correct
#check Numeric.validNat_correct
```

The numeric interface uses explicit postfix MSO construction codes. Instructions
record the variable context and atomic predicate, negation, conjunction,
renaming, or existential projection. `Numeric.formulaInput φ` constructs this
code from the existing full formula syntax: terms use witness nodes, embedded
first-order binders are flattened, and individual quantification includes the
singleton-marker test. This follows the existing executable compiler's proof
strategy. No restriction to quantifier-free formulas, finite set witnesses, or
bounded quantifier alternation is introduced.

`NumericProgram.compile_primrec` proves primitive recursiveness of the code
interpreter by Mathlib's finite-list fold theorem. Each numeric automata
operation has its own primitive-recursion and language-correctness theorem.
`Numeric.compile_correct` connects the resulting automaton to `Tree.Realize`
for **every formula and every valuation**. The input code contains no proof,
solver, or assumed automaton witness. Evaluation is total on malformed codes;
semantic correctness is stated for codes produced from formulas.

`Numeric.Input` consists of the branch maximum, alphabet maximum, individual
and set context sizes, and postfix code. Thus the carriers are `Fin (b+1)` and
`Fin (a+1)`. `Numeric.SentenceInput` instead records the **alphabet cardinality**,
allowing zero letters. `Numeric.sentenceInput φ` handles sentences over
`Fin (b+1)` and `Fin a`, including `a = 0`. The zero-letter case has no labelled
full tree, so satisfiability is false and validity is true. Nonempty branching
is the same hypothesis used by the earlier tree-complementation theorem.

The exact decision endpoints are:

```lean
Numeric.satisfiable (Numeric.sentenceInput φ) = true ↔ ∃ tree, Satisfies tree φ
Numeric.valid (Numeric.sentenceInput φ) = true       ↔ ∀ tree, Satisfies tree φ
```

`compileNat`, `satisfiableNat`, and `validNat` use Mathlib's existing
`Encodable` representation to expose literal `Nat → Nat` functions, all with
`Nat.Primrec` proofs. The `*_encode` theorems identify their results with the
finite-data interface. `satisfiableNat_correct` and `validNat_correct` give the
same semantic equivalences directly at this natural-number interface. The
formal primitive-recursion claims concern these explicit numeric codes; they
do not install a new coding instance on Mathlib's dependent formula type.

The implementation reuses `FiniteSearch.tables`, `FiniteCodeNumbering`, the
numeric Piterman compiler, the existing parity-product/Muller construction,
and `EncodedTreeNonemptiness.solve`. `FiniteFunctionCoding` only packages the
existing table enumeration and its numbering equivalence. Generic numeric
thread definitions are in `Automata`; elementary parity modules have no
dependency on the synthesis backend.

Primitive recursiveness strengthens the computability statement; it does not
claim polynomial, elementary, or practical running time. The reverse
translation remains the existing executable, semantically verified interface;
these new numeric `Primrec` endpoints concern the forward translation and the
two decision procedures.

## Verification

`Tests.MSO` checks genuinely infinite set witnesses, ancestor semantics,
preservation of markers, both sorts of quantification and their alternation,
embedded Mathlib quantifiers with successor terms, empty and multiple individual
markers, missing transitions, the reverse translation on a rejecting automaton,
and the branch formula on an infinite path. A binary-tree regression shows that
flipping all priorities fails to complement the language while
`TreeComplement.automaton` succeeds.

`Tests.MSOExecutable` additionally evaluates the false-sentence decision and
both outcomes of membership transitions and single-versus-multiple child choices. Semantic regression proofs cover
infinite witnesses, quantifier alternation, first-order binders/terms, validity,
the executable reverse translation, and its roundtrip. Executed examples are
intentionally tiny; larger semantic regressions use the general correctness
theorems rather than attempting impractically large state enumeration.

`Tests.MSOPrimitiveRecursive` checks the three `Nat.Primrec` endpoints,
executes the numeric false-sentence solver and zero-letter cases, and proves
regressions for an infinite set witness, alternating quantifiers, embedded
first-order binders/terms, and the literal natural-number validity interface.

The new endpoint proofs are included in `Tests.Axioms`. The permitted axioms
remain `propext`, `Classical.choice`, and `Quot.sound`; no new axiom or admitted
proof is introduced. Import-boundary tests keep generic MSO semantics free of
automata and the generic finite-thread construction free of sender narrowing.
Run the ordinary project checks:

```sh
lake --wfail build
python3 scripts/check_library.py --axioms
python3 -m unittest discover -s scripts -p 'test_*.py'
```
