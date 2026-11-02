# No-direct-reversal decidability: completed encoded construction

[Repository README](../../README.md). Commands and code paths in this note
are relative to the repository root.

`EncodedNoDirectComputable.realizable_computable` proves
`ComputablePred EncodedNoDirect.Realizable` for the existing fixed instance
encoding and original perfect-recall semantics on the no-direct-reversal
fragment. `compile_primrec` and `compile_correct` supply the complete numeric
instance-to-journal-table compiler and exact realizability/nonemptiness
equivalence. `solve_primrec` and `solve_correct` prove the composed decision
procedure primitive recursive and correct. `original_solve_primrec` proves the
same effectivity guarantee for the earlier `EncodedNoDirect.solve` by equality
of Boolean answers. No compiler, checker, numbering, solver, or finite-memory
premise remains. This closes the formal target; it is not an efficiency claim.

## Classical decidability and computability

`main_result_for_ltl_noDirect_fragment_synthesis_finiteAlphabets` returns
`Decidable` but is `noncomputable`. More importantly, its data construction
`DetParityAutomaton.reversalForgivingSummaries` in `ThmReversalForgiving.lean`
tests `ReversalForgivingRealizable A`. In the positive branch it chooses a
winning `JournalReadbackWitness`; otherwise it selects default plans.

`journalSummaries` uses the chosen witness's control type and plan tables.
`summaryEpochTransformer` includes that summary carrier in the game state and
uses its transitions. The dependency therefore survives into the finite game:
building that game already uses the answer to synthesis. This is valid as a
classical existence construction, not as an effective reduction.

The downstream finite search is not the main obstruction. In
`ThmDynhiersynth.lean`, it enumerates supplied finite controller/environment
carriers and a supplied decidable winning relation. The state-loop proof in
`ThmAutomataBackend.lean` gives a bounded repeat search once the concrete finite
transition data are available. Neither step removes the upstream dependency.

## Checked replacement route

Import `DistributedSynthesis.Library.Distributed.NoDirectJournal`, or the existing result
entry point `DistributedSynthesis.Results.NoDirectReversal`.

- `NoDirectJournal.realizable_iff_nonempty_of_checkers`: arbitrary perfect-recall
  realizability under `NoDirectReversalSequence` is equivalent to nonemptiness
  of the journal tree automaton for the reversal-forgiving companion, for any
  semantically correct left, right, and chain checkers.
- `NoDirectJournal.realizable_iff_nonempty`: discharges the checker parameters
  with the existing canonical constructions. No solver or summary-winner
  premise remains in this **semantic** equivalence.
- `NoDirectJournal.realizable_iff_compiled_nonempty`: the same statement through
  executable outer journal assembly, given checker data and a label enumeration.

Forward: a fragment winner wins the companion on all environments; the existing
uniformization and `tauTree_acceptsTree` theorems produce an accepted journal
tree. Reverse: the rational-tree basis and
`journal_readback_accepts_of_accepts` produce a strategy accepted on the
fragment; on that fragment the companion and original objectives coincide.

The automaton is fixed from the objective and checkers before any strategy is
chosen. Classical witness extraction occurs only in correctness proofs, not in
the outer compiler. This removes the identified circularity without claiming
that all computational obligations are closed.

## Implemented computational components

`DistributedSynthesis.Library.Distributed.JournalCompilation` contains ordinary executable
`def`s for the priority shift, priorities, and `compile`. The compiler takes
the objective, three checker records, and a finite label enumeration, and
returns a deterministic tree monitor. `compile_toRunAutomaton` proves equality
with the semantic journal automaton. This is executable **from those data**;
it does not make the canonical checker constructors executable.

The checker dependency runs through `threadBlockMonitor`, `threadDPA`, and
`NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler`.
The semantic Piterman `stepImage` classically filters an arbitrary
proposition-valued NBW transition relation. The original `livePlan` also chose
an arbitrary fresh-node allocation certificate. It now uses the shared sorted
allocator, with classical deciders for the unrestricted semantic interface;
the executable compiler instead receives those deciders as data.

`DistributedSynthesis.Library.Distributed.ThreadComputable` now supplies executable thread
Büchi data, finite transition tests, and acceptance tests. Its `buchi_eq`
theorem proves equality with the semantic thread automaton. The receiver
input and priority-threshold quantifiers are finite; no infinite-run predicate
is tested. Only a finite receiver alphabet and decidable monitor-state equality
are required for the transition tests.

`DistributedSynthesis.Library.Automata.PitermanComputable` supplies the executable adapter:

- `Piterman.Computable.stepImage` receives the transition decider explicitly
  and performs finite successor search.
- `Piterman.Computable.stage1` updates the compact-tree labels with this search.
- `stepImage_eq` and `stage1_eq` prove exact agreement with the semantic
  operations. No new determinization-correctness premise is introduced.
- `acceptingPart` and `stage2Triggers` use the supplied acceptance decider.
- `stage2PlanOfBounds` sorts triggering nodes and inactive nodes, assigns the
  j-th trigger to the j-th inactive node, and assigns name `active.card + j`.
  It proves every field of the existing `Stage2Plan`: inactivity, injectivity,
  names above the old names, bounded consecutive names, and interval coverage.
  The domain is the existing finite pool of `2 * |A.State|` nodes.
- `stage2Plan` specializes this allocator to a well-formed tree.
- `ownerOf` searches the finite trigger list and agrees with the old owner
  relation by uniqueness. `stage2` performs the actual child creation;
  `stage2_eq` proves equality with the semantic update for the same plan.
- `transitionPlan` computes an allocation after executable stage 1 and returns
  the existing `TransitionPlan` certificate. The canonical `livePlan` now calls
  this same allocator, replacing its arbitrary certificate choice.
- `FiniteOrbits.reachable_iff_bounded` proves that a reachable value first
  occurs before the cardinality of a finite deterministic state space. Its
  executable decider handles parent-chain ancestry, including malformed cycles;
  no well-formedness premise is needed for this finite search.
- `stage3` removes duplicate states, `stage4` removes descendants of green
  nodes, `stage5` removes empty nodes, and `stage6` compacts names. Each update
  has an equality theorem with its semantic counterpart.
- `transitionWithPlan_eq` connects the full six-stage update to the semantic
  update for the same plan. `transitionWithPlan_wellFormed` reuses the existing
  invariant proof when the stage-4 root label is nonempty.
- `liveTransition` computes the sorted allocation and either returns the
  certified successor or enters the rejecting sink. It does not require an
  allocation or invariant certificate from its caller beyond a well-formed
  starting state.
- `wellFormedDecidable`, `rawFintype`, and `liveFintype` supply executable
  invariant checking and exhaustive finite enumeration. `automatonData` packages
  the complete executable deterministic parity automaton data. Enumeration is
  intentionally exhaustive and potentially enormous, not an efficient
  reachable-state exploration.

### Language correctness is now connected

The canonical proof now uses the sorted allocator. This is an intentional
change to the internal `livePlan` definition, not a claim that the previous
arbitrary choice happened to select those nodes. All existing correctness proof
bodies were preserved and rechecked with the revised definition.

`transitionPlan_eq_livePlan` identifies the executable and revised canonical
allocations: different decision procedures for the same propositions do not
change the data. `liveTransition_eq` then identifies transitions, and
`automatonData_eq` identifies the whole automaton, including its finite carrier.
`accepts_iff` transfers the existing soundness and completeness theorems:

```lean
(Piterman.Computable.automatonData A decStep decAccept).Accepts word ↔ A.Accepts word
```

`Piterman.Computable.compilation` is an ordinary executable definition returning
`NondetBuchiToDPACompilation A`, with this equivalence in its `correct` field.
It requires finite NBW data, decidable state equality, and transition/acceptance
deciders; no allocation-invariance, language-correctness, or completeness
hypothesis remains. The alphabet need not be finite: only the successor-state
search is enumerated, and the transition decider handles the supplied letter.
This executable adapter alone is not a `Computable` theorem for an encoded
end-to-end synthesis procedure; that theorem is supplied by the completed
numeric pipeline below.

To avoid an import cycle, the compact-tree machinery was physically extracted
into `Automata.PitermanTransition`, and executable allocation/stages 1--2 into
`Automata.PitermanAllocation`. The language proof imports the latter;
`Automata.PitermanComputable` imports the language proof and supplies the final
executable adapter. Public declaration names are retained.

The public regression client `DistributedSynthesis.Tests.NoDirectJournal` includes actual
evaluation of the priority shift and stage-1 labels, finite successor tests
(including empty and two-state sets), and the unrestricted-strategy equivalence.
`DistributedSynthesis.Tests.PitermanAllocation` evaluates zero-trigger and simultaneous-trigger
allocation, resulting active nodes and parent links, allocation after stage 1,
and thread tests for valid odd-threshold guesses, invalid even guesses, priority
drops, and acceptance. These checks execute the data-producing definitions.
`DistributedSynthesis.Tests.PitermanTransition` evaluates bounded orbit search, ancestor-aware
duplicate removal, green and empty-node deletion, name compaction, the invariant
checker, and complete live/sink transitions. It avoids enumerating the enormous
raw-state carrier; these finite tests are not substitutes for language correctness.
`DistributedSynthesis.Tests.PitermanCompilation` is a synthesis-independent public client of
the certified executable compiler and its full infinite-word equivalence.

## Completed end-to-end executable construction

1. `ThreadCompilation` compiles the thread NBWs with executable Piterman.
   `JournalCheckers` supplies left, right, and chain checkers and explicitly
   enumerates finite response-table labels. `realizable_iff_nonempty` proves
   the complete journal reduction without checker parameters.
2. `FiniteOrbitParity` characterizes recurrent states by bounded reachability
   and positive return. `TreeNonemptiness` enumerates state-based label policies
   and branch policies, testing the resulting deterministic orbits. Its
   correctness uses positionality for both the accepting player and any
   rejecting path. Tests include empty label/direction alphabets and transient
   priorities. `NoDirectDecision.solve_correct` completes the DPA solver.
3. `MiyanoHayashiComputable.step_iff` identifies the certified-support relation
   with finite support-table search. One table determines both frontier and
   pending updates; a regression test rejects independently chosen updates.
   `WeakComputable` gives executable parity recoloring and weak APA compilation.
   `LTLComputable` computes positive-normal-form transitions and finite
   subformula carriers, proves the weak hypothesis, and composes with Piterman.
   `LTLComputable.correct` proves full infinite-word language equivalence.
4. `NoDirectLTLDecision.solve_correct` relates the computed answer directly to
   arbitrary perfect-recall strategies satisfying the formula on every
   `NoDirectReversalSequence` environment. `EncodedNoDirect` specializes this
   algorithm to finite data; no function-valued parameter is left in its input.

`EncodedNoDirect.Instance` contains four alphabet cardinalities minus one,
a finite atom/round-record truth table, and a postfix LTL string over natural
atom names. Alphabet sizes are positive, graph codes 0/1/2 mean left/right/both,
missing table entries are false, and out-of-range entries are unused. The
existing total postfix decoder is retained, including recovery after stack
underflow. The explicit product representation supplies `Primcodable Instance`.

All these constructors are ordinary executable definitions. Classical choice
may occur in correctness proofs; it is not an oracle in the executable data.
The finite searches are exhaustive and potentially enormous, not an efficiency
claim or a tested practical synthesis implementation.

## Checked numeric components

`Computability.FiniteSearch` proves primitive recursiveness of bounded
existential/universal tests with input-dependent bounds. `tables alphabet size`
enumerates all length-`size` lists whose entries are below `alphabet`;
`tables_primrec`, `mem_tables_iff`, and `ofFn_mem_tables` establish numeric
computability, exact membership, and coverage of every finite policy. The
empty-alphabet and zero-size cases are included.

`Automata.EncodedOrbitParity` uses the fixed input type
`Nat × List Nat × List Nat × Nat`: maximum state index, successor table,
priority table, and initial index. Missing entries default to zero; successor
and initial indices are normalized modulo the positive state count. This
specifies all malformed inputs without changing valid finite systems.
`solve_primrec` proves the complete bounded orbit/parity test primitive
recursive, and `accepts_computable` proves `ComputablePred` for its actual
infinite-run semantics. `encode_correct` applies it to any deterministic
finite system with an explicitly supplied state numbering. No computability
of an input-dependent numbering is assumed or inferred from that adapter.

Runtime tests cover transient and unreachable priorities, the min-even
convention, maximal-length return cycles, malformed indices, empty tables,
and finite policy enumeration.

`Automata.EncodedTreeNonemptiness` now composes those components. Its fixed
numeric input contains the maximum state index, label and branch counts,
flattened transition table, priority table, and initial index. The transition
entry for `(q, l, b)` has index `(q * labelCount + l) * branchCount + b`.
Missing entries and out-of-range state indices use the same total convention
as the orbit checker. Labels and branches may be empty.

`orbitData_primrec` constructs the deterministic orbit table for a policy pair.
`solve_primrec` proves the complete existential-label/universal-branch search
primitive recursive. `orbitData_correct` identifies each orbit test with
the monitor's parity condition, and `passes_iff` uses
`TreeNonemptiness.nonempty_iff` to connect the search to actual accepted trees.
`nonempty_computable` is the resulting mathlib `ComputablePred` theorem;
neither a solver nor a positionality certificate is an input parameter.

The converse table-to-policy construction in `FiniteSearch` proves that all
enumerated tables represent policies, not just that every policy appears.
Regression tests cover empty alphabets, transient priorities, state-dependent
label choices, adversarial branches, and malformed tables. A quantifier-order
test rejects an instance that an incorrect universal-branch/existential-label
search accepts.

## Numeric alternating frontend

`PostfixFold.run_correct` verifies generic stack folds against the total
postfix decoder. `run_family_primrec` handles an input-dependent algebra:
its constants and operations must be uniformly primitive recursive.
`EncodedPositiveLTL` discharges this requirement for normalization and
subformula enumeration. It constructs both polarities together, retains
duplicate subformula occurrences, and injectively numbers distinct semantic
subformulas by their first occurrence. `EncodedLTLStates` computes exactly
the canonical alternating priorities from these codes.

`EncodedLTLTransitions` computes positive Boolean transition codes whose atoms
are numeric successor indices. `transition_correct` identifies their decoding
with the canonical alternating step after renaming. `transition_bounded`
proves every successor reference is in range; `name_root` fixes the initial
index at zero. `table_primrec` proves uniform construction for a finite list
of atom valuations, and `trueAtoms_primrec` obtains valuations from a finite
atom/letter truth table. Duplicate entries and absent entries are covered.

`EncodedNoDirect.alternatingTables_primrec` composes these stages from the actual
encoded synthesis instance. It also enumerates the complete valid round-record
alphabet: `mem_letters_iff` proves exact coverage, so out-of-range truth-table
entries are never used. `transitionRow_correct` identifies each row with the
existing interpretation on actual round records. This supplies numeric
alternating-automaton data; the complete parity-tree compiler is the composition
documented below.

## Numeric state semantics and exact support choices

The numbering issue is now resolved. `EncodedPositiveLTL.occurrence_number`
proves that decoding a first-occurrence index returns the original semantic
subformula. The reusable `AlternatingRetraction.accepts_iff` transfers run trees
between an automaton and a finite carrier with redundant state names.
`selfOrDecreasing` uses the measure
`2 * originalMeasure(decodedState) + redundantBit`, where representatives have
bit zero and redundant positions have bit one. This extra bit is necessary:
a duplicate `until` occurrence can point to its first occurrence without
decreasing formula size.

`EncodedLTLAutomaton.accepts_iff`, `row_correct`, and `priority_correct`
connect the finite numeric carrier to the actual compiled data and the source
LTL language. `weak` and `buchi_accepts_iff` transfer the existing weak
alternation-removal correctness theorem to this carrier. These are semantic
interpretations; they do not assert numeric computability of the NBW compiler.

`EncodedSupports.enumerate_primrec` exhaustively lists exact supports of a
decoded positive Boolean transition. `enumerate_iff` covers every satisfying
finite set contained in the syntactic atoms, in both directions; malformed
codes follow the existing decoder. `enumerate_decodeSet_iff` transfers the
result to bounded numeric state sets. `EncodedSupportTables` constructs all
simultaneous support tables with `enumerateTables_primrec`; `tables_complete`
proves exact correspondence to lists of finite supports. Empty supports,
empty frontiers, and duplicate atom occurrences are included.

The same numeric table supplies both components of `advance`: the union of
all selected supports, and the union selected by pending source states (or all
sources after a reset), filtered to odd-priority targets. Primitive
recursiveness and exact membership equations are proved. LTL discharges the
transition-decoding hypothesis in `supportTables_correct`; the actual synthesis
input has the primitive-recursive adapter `EncodedNoDirect.supportTables`.

The complete numeric breakpoint stage is now checked. `FiniteSubsets` supplies
canonical bounded subset/pair codes, normalization, semantic equality, and
complete primitive-recursive enumeration. `EncodedBreakpoints.step_primrec`
proves uniform primitive recursiveness of the entire transition search;
`Semantic.step_iff_tableStep` and `step_iff_buchiStep` identify it with the
existing construction. Both updates use the same support choice, and a pending
code normalizes to the empty list exactly when its decoded set is empty.

`EncodedLTLBreakpoints` discharges all row and priority hypotheses using the
actual LTL automaton. It proves initial-state, accepting-state, and transition
correspondence and completeness of the finite state-code list. Its `accepts_iff`
transfers runs in both directions and proves exact source LTL semantics for
the numeric-state Büchi automaton. `compile_primrec` covers the fully materialized
state, initial, accepting, and finite-alphabet edge tables; `mem_edges` connects
the generated edges to the transition predicate. `EncodedNoDirect.buchiTables`
provides the primitive-recursive adapter over all round records, with exact
edge semantics in `mem_buchiEdges`. No general parity alternation-removal
claim is used: the language theorem still uses the proved LTL weakness measure
and parity recoloring.

## Completed numeric frontend and journal

Piterman progress: `EncodedPitermanStates` enumerates numeric codes for all
raw compact trees, proves encode/decode identity, and proves enumeration
completeness. `EncodedPitermanTransition` proves stage 1 primitive recursive
and exactly equal to the executable successor-label propagation.
`EncodedPitermanAllocation` proves primitive recursiveness of numeric ranks,
child choices, and fresh names; `child_eq_plan` and `name_eq_plan` prove agreement
with the actual sorted allocation in `stage2PlanOfBounds`. That allocation
correspondence is no longer an unproved premise.

`EncodedPitermanCreation`, `EncodedPitermanPruning`, `EncodedPitermanGreen`,
and `EncodedPitermanDeletion` now implement stages 2--6 and prove exact
canonical-code correspondence. `EncodedPitermanMinima` supplies the bounded
name minima. `EncodedPitermanStep.transition_primrec` and `transition_encode`
compose all six stages, saving the stage-4 removed nodes before stage 5 and
reusing the full removed-node union during renaming. `step_primrec` and
`step_correct` include the empty-root test and agree exactly with
`Piterman.Computable.liveTransition` on well-formed input trees.

`EncodedPitermanAutomaton` now adds numeric initialization, priorities, and an
absorbing rejecting sink. It enumerates all raw trees without testing the
invariant. `run_embed` proves that every run from the initial state follows the
well-formed semantic automaton exactly, so unreachable malformed trees do not
affect the language. `EncodedPitermanCompiler.compile_primrec` materializes the
complete finite parity tables; `automaton_eq` and `accepts_iff` certify them.

`EncodedLTLNumbering` supplies the explicit list-search state numbering and
proves edge/acceptance adequacy for the LTL-generated Büchi automaton.
`EncodedLTLParity.compile_primrec` and `accepts_iff` therefore close the complete
numeric LTL-to-parity frontend. `EncodedNoDirectParity.compile_primrec` and
`realizable_iff` specialize it to the original synthesis instance encoding,
including the complete round-record alphabet and atom interpretation. No
computable choice of finite-type equivalence is assumed.

`EncodedNoDirectComputable.compile` is the uniform map
`EncodedNoDirect.Instance → EncodedTreeNonemptiness.Data`; `compile_primrec`
proves its effectivity and `compile_correct` proves its exact semantic
equivalence. The following components discharge its construction and
correctness obligations.

Numeric journal construction is closed. `EncodedJournalLabels`
enumerates all sixteen finite response tables, proves completeness, and proves
that decoding an encoded label returns exactly that label. `EncodedOrdinaryCompiler`
supplies primitive-recursive complete ordinary left/right bad-thread tables.
`EncodedOrdinaryThreadsCorrect` instantiates the generic correspondence data:
state-pair numbering, indexed priorities with exact range, existential receiver
edges, initial states, and Büchi steps/acceptance. Right-block inputs are swapped
explicitly; equal priorities retain the incumbent minimum state. These results
hold for arbitrary numeric objectives through `EncodedRoundObjectives`, whose
adapter from `EncodedNoDirectParity` is checked. `EncodedThreadBuchi` additionally
proves soundness of its state codes and injectivity of semantic encoding.

The following numeric components are now closed:

1. `EncodedReversalForgiving.compile_primrec` constructs the companion;
   `accepts_iff` proves its language exactly that of the semantic companion.
   The construction uses a separate numeric state carrier, with an absorbing
   accepting state after a forbidden reversal. A `both` round clears the
   previous one-sided direction.
2. `EncodedThreadNumbering` removes repeated state codes before assigning
   indices. `EncodedThreadCompiler` composes the verified Piterman compiler
   with parity complementation. The complete ordinary and chain table adapters
   instantiate its state, priority, edge, and initial-state contracts.
3. `EncodedThreadStream` supplies transitions without enumerating the complete
   letter alphabet at each step. `EncodedOrdinaryCheckerAssembly` uses one
   numeric carrier for all boundaries; only the initial state changes.
   `EncodedChainCheckerAssembly` uses canonical handoff-set codes and retains
   that set throughout checker execution. The journal's current thread set
   remains a separate component. All three existing checker interfaces are
   supplied, with no assumed checker-correctness premise.
4. `EncodedJournalAssembly.realizable_iff_nonempty` proves fragment realizability
   equivalent to the assembled journal built from these numeric checkers and
   the numeric companion. This transfers language equivalence, not an assumed
   equality of the companion's two state representations.
5. `EncodedJournalBoundary` supplies primitive-recursive closing, synchronizing,
   and first-reversal transitions. `EncodedJournalSubsets` supplies all opening,
   continuation, closing, and reversal set updates. Their `Correct` modules
   prove exact agreement with every corresponding semantic finite-set image.
   Closures preserve the sampled block minimum; first and repeated reversals
   update it. Set codes are normalized and remain correct for empty sets.

6. `EncodedJournalMachineSteps` proves that selecting and re-encoding a label's
   response fields preserves the complete ordered edge list. Its checker-step
   equalities therefore identify actual deterministic states, not just languages.
7. `EncodedJournalTransitions` supplies all numeric outer transitions and
   priorities with primitive-recursiveness proofs. `EncodedJournalStateCoding`
   proves injective encoding and sound/complete finite-state enumeration;
   its numbering certifies the compiler's actual duplicate-safe list search.
   `EncodedJournalTransitionsCorrect.step_correct` proves the full transition
   simulation, and `EncodedJournalPriorities.priority_correct` includes the
   even global priority shift.
8. `EncodedJournalTables.compile_primrec` constructs the complete flattened
   transition table, priorities, and initial state. `EncodedJournalAlphabetCoding`
   proves label and branch coverage. `FiniteTableLookup.lookup3` verifies the
   flattened indexing. `EncodedJournalTablesCorrect.nonempty_iff` proves exact
   journal-table nonemptiness, using the generic `TreeMonitorRetraction` theorem
   for surjective label and branch representations.
9. `EncodedNoDirectComputable` composes these checked stages with the existing
   numeric frontend and tree solver. Its `realizable_computable` theorem is the
   final mathlib `ComputablePred` endpoint. There is no remaining implementation
   or proof obligation for this encoded decision result.

The state code has a mode tag, a numeric checker state, a current
atom/chain-set code, and (only in reversed modes) the retained handoff-set code.
Boundary atoms instead store their pair index. Branches distinguish a boundary
atom from a left or right sender input. A first reversal initializes the chain
checker at the newly computed handoff set without advancing it on that round.
Its prestart state consumes its first guessed thread on the next round.
These details are covered by the transition correspondence theorem.

Do not restart the circular summary route or treat `noncomputable Decidable`
as algorithmic decidability. Effectivity here follows from explicit
primitive-recursiveness proofs, not from finiteness alone. Classical numbering
equivalences and witness choices occur in correctness certificates; the numeric
data compiler does not call them. The separate unrestricted-network
undecidability results use the completed source port through `SourcePort.source`;
they do not contradict decidability under the no-direct-reversal restriction.

## Verification

Use the [overview's verification commands](../../README.md#build-audit-and-maintain).
Numeric frontend tests cover repeated
subformulas, temporal continuation indices, literal polarity, malformed-source
decoding, duplicate/missing truth-table entries, and exact alphabet enumeration.
Additional tests cover empty versus impossible supports, duplicate occurrences,
simultaneous tables, shared frontier/pending updates, full breakpoint transitions,
normalization, impossible mixed choices, and finite Büchi tables. Numeric Piterman
tests cover simultaneous child creation, cyclic ancestor search, descendant
blocking, green/empty deletion, name compaction, and full live/sink transitions.
Additional compiler regressions execute a full one-state Büchi determinization,
absorbing-sink behavior, and the bad-thread threshold rules. Generic clients
check the complete numeric LTL frontend and its original-model realizability
equivalence without materializing the enormous full LTL carriers.
Numeric journal tests cover all sixteen table shapes, label round trips,
unequal input/output cardinalities, the right-block swap, priority ties,
missing-field decoding, receiver-edge enumeration, and complete tiny ordinary
bad-thread tables. Further tests cover duplicate-safe numbering, parity
complementation, the reversal-forgiving companion, prestart/dead/live chain
states, boundary and reversal minima, response-field orientations, normalized
set images, repeated reversals, and empty handoffs. Public clients check the
assembled numeric-checker journal's original-model equivalence.
Outer-journal tests additionally cover accepted versus unreachable boundary
branches, empty current sets, distinct retained handoff sets, absorbing sinks,
priority shifts, label/branch enumeration, and public clients of the final
computability theorem. Full enormous journal tables are not evaluated in tests.
The old no-direct-reversal endpoint retains its type and proof. Piterman's
canonical allocation uses the shared sorted construction checked by the
executable compiler's correspondence theorems.
