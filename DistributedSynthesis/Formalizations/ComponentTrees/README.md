# Component trees: proof correspondence

For the paper's statements, definitions, and proof entry files, see the
[paper guide](../Paper/README.md). This page describes the component-tree
implementation and its reusable results.

The symbolic alphabet stores `(K,q,r,λ,gen)`. The incoming generating table
belongs to the child; the root uses a dummy field. Local MSO tests check each
child's correspondence against its parent and require all successor
components exactly once. Decision and synthesis use this alphabet, including
the generating tables in the extracted model.

Public import: `DistributedSynthesis.Results.ComponentTrees`.
Namespace: `Characterisation.ComponentTrees`.

The development proves the tree-based decision and synthesis chain.
This includes both recursive MSO model/tree transports, preservation of every
compatible run, executable model decoding, finite model extraction, and the
returned distributed strategies at full original LTL strength.

Public executable endpoints:
- `Effective.solve` and `Effective.solve_correct`;
- `Effective.synthesize`, `Effective.synthesize_complete`, and `Effective.synthesize_sound`.

The inputs are the existing encoded adversary automaton and LTL instance.
The three-graph alphabet encoding is checked by `alphabet`; the nowhere-dense
promise justifies termination of the existing consensus-bound search.
The decision/synthesis theorems require no supplied consensus bound, model,
strategy, liveness certificate, or run-transport invariant.
The existing game-based results remain independent.

## Current construction

A node carries the full position `(K,q)`, an arbitrary owner-preserving,
state-preserving idempotent reduction `r : K → K` with bounded image, and a
block rule on `r(K)`. Its children carry the **full** components of the live
extensions of `r(K)`. A run satisfies `e_(n+1) = r_n(e_n) u_n`.
The bounds are `a = |Σ|^D`, `N = (1+|Q|)^a`, `B = Na`, and `b = Ba`:
`B` bounds reduction images; `b` bounds full successor components.

`CompressedNode`, `CompressedNode.Successor`, and
`CompressedNode.CompatibleStep` encode precisely these local requirements.
They do not restrict reductions to the representative-table construction.
`UncompressedTree` and `CompressedTree` reuse `LabeledTree`, public support,
and compatible runs. Validity includes every full successor component;
acceptance quantifies over every supported branch and every compatible run.

## Statement and proof correspondence

| Target in main.tex | Checked Lean declarations | Proof coverage |
| --- | --- | --- |
| `lem:tree-combined-automaton` | `blockAutomaton`, `blockAutomaton_finite_states`, `blockAutomaton_run_live`, `blockAutomaton_run_priority`, `blockAutomaton_accepts` | Product of the supplied prefix recognizer, guarded specification automaton, and priority range plus zero. Completed minima include the source and exclude the endpoint. `synthesisBlockAutomaton_language` and `synthesisBlockAutomaton_live` instantiate the actual guarded LTL objective and exact prefix recognizer, for all execution words and all finite block lists. |
| Position requirements | `StateReachable`, `PositionValid`, `initial_position_valid` | Existing `HistoryGame.Position` is only the finite history container. Validity separately requires liveness, connectivity inside the position, and individual state reachability with some output sequence. No common past strategy is required. |
| Output labelings and block successors | `ruleBlock`, `blockSuccessor`, `blockSuccessor_reachable` | The existing `ClosingPolicyCoherent` means one output per process view. The existing `closingPolicyCoherent_iff_local` proves equivalence to actual local strategies across all rounds of the block. All intermediate outputs occur in `ruleBlock`. |
| Map of view complexes | `ViewVertex`, `ViewComplexMap`, `ofEdge`, `ofVertices`, `preserves_views`, `ext`, `ext_vertices` | Vertices are the existing views occurring on edges; there are no isolated vertices. Maps have actual owner-indexed vertex functions and an incidence-preserving edge action. Both conversions are supplied. For injectively indexed histories, the vertex action uniquely determines the edge action. |
| `lem:view-extension` | `ViewComplexMap.extend`, `extend_history`, `extend_zero`, `extend_identity`, `extend_comp`, `extend_inverse` | All extensions, including nonlive ones, at arbitrary source and target rounds. Reuses the constructor induction in `append_preserves_views` and the existing `ClosingLayer` maps. No same-round, endomorphism, injectivity, or view-reflection premise is imposed on the map. |
| Reduction definition | `Reduction`, `vertex_idempotent`, `map_idempotent`, `fixes_image`, `image_connected`, `priority_preserved` | Every state-preserving idempotent view-complex map is allowed. Edge idempotence gives vertex idempotence because every vertex lies on an edge. Image connectivity is internal to the image. |
| `lem:bounded-common-view`, including its English proof | `consensus_proposal_decisions`, `consensus_selects_process`, `consensus_selected_of_blind`, `proposal_suffix_views`, `broadcaster_common_roots`, `bounded_common_view` | Follows the broadcaster argument: distinct fresh proposals; a silent process must select itself by validity; a receiving endpoint recovers the earlier history; simulated decisions and earlier views agree along shared endpoints; connectivity makes the dependent label constant. It does not use the geometric holes proof. Arbitrary connected subgraphs and singleton application input alphabets are covered. |
| Class partition and `lem:tree-compression` | `endpointTable`, `table_entry`, `endpointReduction`, `compression_reduction` | `Option Q` records exactly membership in the selected component and successor state. Arbitrary class-preserving, class-constant representatives induce an actual reduction on the full component. The current endpoint obtains the common vertex through the broadcaster proof, then extends/restricts the map. No equality of old states or of complete rules is required. |
| Compression size bounds | `endpointTable_card`, `endpointFold_image_bound`, `live_endpoints_bound`, `component_position_bound` | Exactly `N`, `B = Na`, and the source-dependent full-component bound `b = Ba`. The reduced image and full component are not conflated. |
| Full child and its reduction | `component_position`, `component_position_with_reduction`, `Reduction.reindex`, `reindex_image_card` | Constructs the full child `C`, with actual block-successor labels, state reachability, internal connectivity, and its bounded reduction. Reuses `componentEquiv` to pass from endpoint scenarios to actual history edges. |
| Reduced source | `Reduction.imagePosition`, `imagePosition_valid`, `imagePosition_card`, `imageProjection_state`, `initial_map_identity` | Constructs `r(K)` in the existing position container, proves validity and the exact image cardinality, and preserves each starting state. The singleton root forces the identity reduction. |
| `def:tree-component-tree`, local steps | `CompressedNode`, `Successor`, `successor_exists`, `successor_bound`, `CompatibleStep`, `compatible_step_state` | The source is `r(K)` and the child is the full successor component. The next edge and its automaton state satisfy the current manuscript's equation; no extra target fold is inserted into that step. The global tree definitions require all full successor components through public support. |
| Forward bounded-representation proof: ranks | `EdgeSegment`, `edgeSegment_wellFounded`, `edgeRank_le`, `edgeRank_lt` | English descending-chain/concatenation argument and ordinal ranks. Only infinite live branches must accept. Transition priorities count the target and exclude the source. |
| Forward proof: progress along a run | `rank_minimal_reduced_edges_accept` | Measures progress on `r_n(e_n)`. Uses the source reduction, actual compatible step, and next node's representative reduction in the order in main.tex. This general helper exposes the subset/state invariant as `sound`. The global endpoint `ForwardConstruction.tree_accepting` discharges that obligation through actual node inclusions and `UncompressedTree.stateOf_history`; it does not take `sound` as a hypothesis. |
| Reverse proof: local copying | `CompressedNode.copied_rule`, `copied_block_rule`, `blockSuccessor_restrict` | Compose the simulation with the source reduction and copy the block rule from its image. Distributedness and complete successor states are preserved without injectivity. `simulationEndpoint_live`, `simulation_component`, and `simulation_next` establish liveness, full-component selection, and the next simulation map. |
| Global tree definitions | `UncompressedTree.Valid`, `CompressedTree.Valid`, `UncompressedTree.Accepting`, `CompressedTree.Accepting` | Reuses `LabeledTree`, `publicSupport`, and `HistoryGame.CompatibleRun`. Unsupported addresses are ignored. All full children, arbitrary allowed reductions, every supported branch, and every compatible run are included. |
| Reverse bounded-representation proof | `ReverseConstruction.tree_valid`, `simulation_branch`, `tree_accepting`, `block_compressed_to_uncompressed` | Complete recursive simulation and acceptance transfer following the English proof. The generic helper uses `StateLiveness`; `blockAutomaton_stateLiveness` discharges it for the paper's constructed automaton, so the concrete endpoint imposes no extra liveness premise. |
| Reverse construction: effectiveness | `ExecutableReverse.tree`, `advanceData_eq`, `tree_eq`, `tree_accepting` | Executable finite searches produce exactly the semantic construction. The supplied tree, automata, finite input enumerations, state equality, and liveness test are data. No finite-memory assumption is imposed on the supplied tree; no numeric primitive-recursive encoding theorem is claimed here. |
| Unique occurrence and original labels | `UncompressedTree.nodes_equal_of_view`, `occurrence_of_live`, `stateOf_eq`, `stateOf_history`, `live_word_run`, `stateOf_accepts` | Every live block history has exactly one node at its depth. Edges sharing a vertex have the same node. Every infinite word with live prefixes yields a run, even if its infinite graph sequence is outside A. Thus q_U and its path-acceptance property are proved. |
| Recursive forward construction | `inclusion_next`, `rank_minimal_reduction`, `ForwardConstruction.tree_valid`, `atState_depth`, `original_labels`, `tree_accepting` | Restricts the original rule to r(K), associates every full child with an original child, preserves literal history inclusion and states, and selects rank-minimal table representatives. One constructed tree accepts every compatible run; no invariant or progress certificate is assumed. |
| `lem:tree-uncompressed-equivalence` | `uncompressed_equivalence`, `UncompressedTree.prescriptions_consistent`, `states_replay`, `AlgorithmTree.tree_accepting`, `executable_readback_realizes` | Complete equivalence at original LTL strength. Follows English local-view consistency and replay. Uses the stated A nonempty and D positive assumptions; no closure of A, finite-memory restriction, or extra state-liveness premise. `ExecutableReadback.strategy` enumerates only finitely many nodes/scenarios at the supplied view clock. |
| `thm:tree-bounded-representation` | `uncompressed_to_compressed`, `bounded_representation`, `block_bounded_representation`, `ExecutableReverse.tree_accepting` | Both directions and effective reverse construction are checked. The concrete product endpoint requires no added liveness, coverage, rank, subset, or simulation certificate. `CompressedTree.position_bound` proves the distinct full-node bound b = Ba at every supported node, including the root. |
| `lem:tree-mso`: logical formulas | `FiniteRunMSO.runFormula_correct`, `setRun_iff`, `infinitelyOftenFormula_branch`, `parityFormula_branch`, `acceptanceFormula_correct`, `satisfiable_correct` | Executable Local, Run, strict-ancestor recurrence, Parity, and universal Acc formulas for supplied finite letter/edge tables. Edge sets partition exactly the branch. Input tree labels already encode the X partition. The recursive correspondence below connects these formulas to concrete trees. |
| `lem:tree-symbolic-equivalence`: finite local data | `GeneratingAlphabet.Letter`, `StarLegal`, `starTest`, `Step` | A letter stores the current move and its incoming generating table. The finite local check verifies incidence, successor states, coverage and uniqueness across the actual child labels. No child order or correspondence is fixed by the parent letter. |
| `lem:tree-symbolic-equivalence`: correspondence | `GeneratingAlphabet.encode_local`, `complete_encode`, `model_tree_iff`, `run_forget`, `run_lift`, `decode_accepting` | For completeness, the existing canonical encoder supplies one choice of incoming maps. For soundness, arbitrary locally valid incoming maps reconstruct the successor records used by the executable decoder. Runs correspond in both directions with identical priorities. |
| `lem:tree-mso`: symbolic acceptance | `FiniteRunMSO.Star.starFormula_correct`, `GeneratingAlphabet.sentence_correct`, `mso_compressed_iff`, `satisfiable_correct` | A finite test of each node and its entire child-label family is conjoined with the existing universal run formula. All runs use the generating maps stored in the input labels. |
| Rabin and effective finite model generation | `MSO.Tree.NumericModel.extract`, `model_correct`, `extract_complete`, `FiniteRunMSO.Star.finiteGenerator_complete`, `model_sound` | Reuses the existing numeric full-MSO compiler and `FiniteController.extract`. The returned finite policy and monitor transitions generate the model; label decoding is executable arithmetic. No infinite model or winning policy is input data. |
| `thm:nowhere-dense-decision-procedure`, final proof | `CompiledObjective.compressed_equivalence`, `Effective.solve_correct`, `Effective.synthesize_complete`, `Effective.synthesize_sound` | Entire displayed chain, including the empty-adversary case. Reuses `Consensus.encodedConsensusBound` and the guarded-LTL compiler, computes exactly B and b, decides the finite MSO language, extracts a model, decodes a compressed tree, unfolds it, and performs executable local-view lookup. Soundness concerns the returned strategy itself, on every admitted execution of the original LTL formula. |

## Hypotheses and reused definitions

- `D > 0` is the standing positive consensus block length from main.tex.
  `V` is a fresh nontrivial consensus proposal type, independent of `I₁,I₂`.
  The application input alphabets need not be nontrivial.
- The forward theorem uses nonempty input alphabets, as stated in main.tex
  for all processes. Singleton inputs are permitted. No nontriviality of
  application inputs, closure of A as an omega-language, or finite-memory
  restriction is assumed.
- Histories, owner-indexed views, finite sets, policies, automata, parity,
  representative selection, and component equivalences reuse the library.
  `ViewVertex` is only the subtype of existing views occurring in a family.
  `historyBlocks` is a proved inverse of the existing `blockHistory` on
  histories of length nD, with D positive; ranks use this block indexing.
- To extend a selected source graph literally, the reused `Move` container
  has replacement `id`. `CompressedNode.extensionMove` uses it on `r(K)`;
  the source reduction has already been applied when this source is built.
- `edgeRank` keeps zero even coordinates to reuse finite lexicographic
  order lemmas; these constant coordinates do not change comparisons.
- Noncomputable choices used for ordinal ranks and semantic witnesses are
  not advertised as an effective construction of an accepting finite model.
  The reverse transformation has a separate executable implementation,
  outside any `noncomputable section`, proved equal to the semantic tree.

## Representation details

Finite descriptions use bounded numbered edge sets and Boolean owner-view
relations from the existing `Representation.Data`. `CanonicalPositions`
chooses one description per isomorphism class, retaining the initial singleton
as its class representative. `GeneratingAlphabet` stores this description,
the reduction, the rule, and the incoming generating table. A table records
its predecessor description once, then one block scenario per child edge.
Each scenario is equivalent to a predecessor edge and a signal block.
The local check requires that predecessor to be the actual parent and that
all generated extensions start in its reduced image.

The implementation enumerates arbitrary relation tables, including
unrealizable ones. They cannot occur at a supported node of a locally valid
tree: the root is concrete and the decoder preserves realizability at every
successor. Thus they do not add accepted trees. The internal `FiniteAlphabet`
and `CanonicalAlphabet` carry successor records; the decision procedure
uses `GeneratingAlphabet`. `GeneratingDecode.complete` reassembles those
internal successor records from the actual child labels, without changing
the input alphabet. The fixed-table `SymbolicAlphabet` is used only
to supply one valid encoding in the completeness proof.

The generic run checker reads successor data through finite edge identifiers.
Here an identifier also carries its node's incoming table. The allowed-edge
test forces that table to equal the input label's table, so this introduces
no run-dependent correspondence choices. `run_forget` and `run_lift` prove
the exact run correspondence. The extracted finite generator outputs the
whole letter, retaining all data needed for executable reconstruction.

For compatibility with the existing move container, a finite letter stores
a rule on the full source, restricted to the reduction image during decoding.
`FullExtensions.successor_iff` proves equality of the full successor positions,
including their labels; the encoder obtains this rule by pullback from the
image. The all-runs acceptance tests use this same node rule.

No additional mathematical hypothesis or English-proof obstruction was needed
for these proofs. Rank choices remain noncomputable only in the existence
argument. The decision procedure, finite generator extraction, reverse tree
constructions, and local output functions are executable. No efficiency bound,
new numeric primitive-recursive theorem for the entire synthesis procedure,
or finite-state distributed implementation is claimed.

## Verification

```sh
lake --wfail build DistributedSynthesis.Tests.ComponentTrees.Audit
python3 scripts/check_library.py --axioms DistributedSynthesis/Tests/ComponentTrees/Audit.lean
python3 verification/verify.py fast
```

`python3 verification/verify.py fast` runs both the general library axiom audit
and the component-tree audit after the warning-free build.

The component-tree audit includes the new completion, encoding, run
correspondence, MSO, decision, and synthesis endpoints. It permits only
`propext`, `Classical.choice`, and `Quot.sound`.
Tests also exercise maps between different rounds, collapsing distinct
edges while preserving both vertex owners, and fresh proposals with
singleton application inputs. The reverse endpoint is checked with singleton
inputs, and vertex transport is evaluated on a collapsing map. The complete
equivalence is also checked at singleton inputs with independent Bool
consensus proposals; live-path acceptance requires no membership in A.

The final API regressions check that no model or consensus-bound argument is
required, and test executable numeric-label decoding at singleton alphabets.
