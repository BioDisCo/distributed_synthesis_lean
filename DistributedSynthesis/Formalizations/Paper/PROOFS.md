# Proof locations

[Return to the paper guide](README.md).

Each row pairs a declaration in a paper entry file with the exact source
location of the proof it invokes. For a direct calculation in the entry file,
the second link stays in that file. Some source theorems compose further
lemmas; the links expose that composition rather than duplicating its proof.

The full types in the entry files are the place to check hypotheses and
conclusions. The source locations are the place to read the underlying proofs.

## The model and view complexes

| Statement or definition | Proof or construction |
| --- | --- |
| [`processes`](Model.lean#L41) | [In the entry file](Model.lean#L41) |
| [`graphs`](Model.lean#L45) | [In the entry file](Model.lean#L45) |
| [`inputSignals`](Model.lean#L49) | [In the entry file](Model.lean#L49) |
| [`view_update`](Model.lean#L53) | [In the entry file](Model.lean#L53) |
| [`round_outputs`](Model.lean#L64) | [In the entry file](Model.lean#L64) |
| [`execution_round`](Model.lean#L70) | [In the entry file](Model.lean#L70) |
| [`ViewComplexOutput`](Model.lean#L95) | [In the entry file](Model.lean#L95) |
| [`labelViewComplex`](Model.lean#L99) | [In the entry file](Model.lean#L99) |
| [`labelViewComplex_endpoints`](Model.lean#L104) | [In the entry file](Model.lean#L104) |

## The synthesis problem

| Statement or definition | Proof or construction |
| --- | --- |
| [`realizes_iff`](ProblemStatement.lean#L36) | [In the entry file](ProblemStatement.lean#L36) |
| [`synthesis_iff`](ProblemStatement.lean#L41) | [In the entry file](ProblemStatement.lean#L41) |
| [`adversary_synthesis_iff`](ProblemStatement.lean#L47) | [In the entry file](ProblemStatement.lean#L47) |
| [`full_synthesis_iff`](ProblemStatement.lean#L57) | [In the entry file](ProblemStatement.lean#L57) |

## Undecidability of lossy-link synthesis

| Statement or definition | Proof or construction |
| --- | --- |
| [`encoded_ltl_synthesis_undecidable`](Undecidability.lean#L30) | [`encoded_ltl_synthesis_undecidable`](../../Results/UnconditionalUndecidability.lean#L18) |

## Nowhere denseness characterizes decidability

| Statement or definition | Proof or construction |
| --- | --- |
| [`realizable_computable_iff_nowhere_dense`](Characterization.lean#L31) | [`realizable_computable_iff_nowhere_dense`](../../Results/HolesCharacterization.lean#L38) |

## Deciding realizability and constructing an algorithm

The proof first checks whether the adversary has any infinite word. If it has
none, every specification is realizable vacuously. Otherwise it computes a
consensus bound, constructs the block automaton, and decides the MSO sentence
for compressed component trees. `solve_correct` composes these equivalences;
`synthesize_complete` and `synthesize_sound` justify the returned strategies.

| Statement or definition | Proof or construction |
| --- | --- |
| [`solve_correct`](Decidability.lean#L40) | [`solve_correct`](../ComponentTrees/Decision.lean#L87) |
| [`synthesize_complete`](Decidability.lean#L51) | [`synthesize_complete`](../ComponentTrees/Synthesis.lean#L92) |
| [`synthesize_sound`](Decidability.lean#L63) | [`synthesize_sound`](../ComponentTrees/Synthesis.lean#L105) |

## Indistinguishability and preceding views

| Statement or definition | Proof or construction |
| --- | --- |
| [`indistinguishable_append`](Indistinguishability.lean#L28) | [`indistinguishable_append`](../../Library/Distributed/ViewIndistinguishability.lean#L9) |

## One round subdivides an edge into three

| Statement or definition | Proof or construction |
| --- | --- |
| [`induced_child_edge_iff`](SingleSubdivision.lean#L42) | [`induced_child_edge_iff`](../../Library/Distributed/GraphAdversaries/ViewPathIsomorphism.lean#L213) |

## The inputless view complex is a path

| Statement or definition | Proof or construction |
| --- | --- |
| [`view_edge_iff_consecutive`](ViewPath.lean#L35) | [`view_edge_iff_consecutive`](../../Library/Distributed/GraphAdversaries/ViewPathIsomorphism.lean#L37) |
| [`view_adjacent_iff_consecutive`](ViewPath.lean#L44) | [`view_adjacent_iff_consecutive`](../../Library/Distributed/GraphAdversaries/ViewPathIsomorphism.lean#L62) |

## The extreme vertices

| Statement or definition | Proof or construction |
| --- | --- |
| [`extreme_views_unique_neighbors`](ExtremeVertices.lean#L25) | [`extreme_views_unique_neighbors`](../../Library/Distributed/GraphAdversaries/ViewPathIsomorphism.lean#L112) |
| [`extreme_view_coordinates`](ExtremeVertices.lean#L40) | [`extreme_view_coordinates`](../../Library/Distributed/GraphAdversaries/ViewPathIsomorphism.lean#L71) |

## The index of an edge

| Statement or definition | Proof or construction |
| --- | --- |
| [`pathIndex_append`](PathIndex.lean#L33) | [`pathIndex_append`](../../Library/Distributed/GraphAdversaries/GeometryCoding.lean#L26) |
| [`orientation_agrees`](PathIndex.lean#L38) | [`orientation_agrees`](../../Library/Distributed/GraphAdversaries/GeometryCoding.lean#L119) |
| [`actual_endpoint_indices`](PathIndex.lean#L43) | [`actual_endpoint_indices`](../../Library/Distributed/GraphAdversaries/ComponentBounds.lean#L14) |

## Computing the position of a view

| Statement or definition | Proof or construction |
| --- | --- |
| [`initial_positions`](FindIndex.lean#L30) | [In the entry file](FindIndex.lean#L30) |
| [`nonreceiving_position`](FindIndex.lean#L35) | [In the entry file](FindIndex.lean#L35) |
| [`receiving_position`](FindIndex.lean#L39) | [In the entry file](FindIndex.lean#L39) |
| [`actual_endpoint_indices`](FindIndex.lean#L45) | [`actual_endpoint_indices`](../../Library/Distributed/GraphAdversaries/ComponentBounds.lean#L14) |

## Prefixes and inclusion of intervals

| Statement or definition | Proof or construction |
| --- | --- |
| [`cell_subset_iff_prefix`](CellInclusion.lean#L26) | [`cell_subset_iff_prefix`](../../Library/Distributed/GraphAdversaries/GeometryTopology.lean#L122) |

## Continuity and surjectivity of the geometric map

| Statement or definition | Proof or construction |
| --- | --- |
| [`continuous_geometricMap`](GeometricMap.lean#L25) | [`continuous_geometricMap`](../../Library/Distributed/GraphAdversaries/GeometryTopology.lean#L59) |
| [`geometricMap_surjective`](GeometricMap.lean#L30) | [`geometricMap_surjective`](../../Library/Distributed/GraphAdversaries/GeometryTopology.lean#L90) |
| [`coordinate_unique`](GeometricMap.lean#L35) | [`coordinate_unique`](../../Library/Distributed/GraphAdversaries/GeometryTopology.lean#L25) |

## The geometric map preserves closure

| Statement or definition | Proof or construction |
| --- | --- |
| [`geometricMap_image_closure`](Closure.lean#L25) | [`geometricMap_image_closure`](../../Library/Distributed/GraphAdversaries/GeometryTopology.lean#L116) |

## Removing a prefix from an edge index

| Statement or definition | Proof or construction |
| --- | --- |
| [`pathIndex_concat`](ConcatenationIndex.lean#L30) | [`pathIndex_concat`](../../Library/Distributed/GraphAdversaries/GeometryConcatenation.lean#L9) |
| [`pathIndex_suffix`](ConcatenationIndex.lean#L37) | [`pathIndex_suffix`](../../Library/Distributed/GraphAdversaries/GeometryConcatenation.lean#L43) |

## Removing a prefix from an interval

| Statement or definition | Proof or construction |
| --- | --- |
| [`endpoints_concat`](ConcatenationCell.lean#L30) | [`endpoints_concat`](../../Library/Distributed/GraphAdversaries/GeometryConcatenation.lean#L53) |
| [`prefixRescale_cell`](ConcatenationCell.lean#L41) | [`prefixRescale_cell`](../../Library/Distributed/GraphAdversaries/GeometryConcatenation.lean#L79) |

## Removing a prefix from the geometric image

| Statement or definition | Proof or construction |
| --- | --- |
| [`coordinate_prepend`](ConcatenationMap.lean#L30) | [`coordinate_prepend`](../../Library/Distributed/GraphAdversaries/GeometryConcatenation.lean#L116) |
| [`coordinate_residual_image`](ConcatenationMap.lean#L36) | [`coordinate_residual_image`](../../Library/Distributed/GraphAdversaries/GeometryConcatenation.lean#L128) |

## The preimage of an interval interior

| Statement or definition | Proof or construction |
| --- | --- |
| [`relative_interior_cell_forces_prefix`](CellInterior.lean#L25) | [`relative_interior_cell_forces_prefix`](../../Library/Distributed/GraphAdversaries/GeometryTopology.lean#L197) |

## Prefix cylinders are clopen

| Statement or definition | Proof or construction |
| --- | --- |
| [`isClopen_graphPrefix`](ClopenCones.lean#L25) | [`isClopen_graphPrefix`](../../Library/Distributed/GraphAdversaries/GeometryTopology.lean#L184) |

## Consensus and the geometric image

| Statement or definition | Proof or construction |
| --- | --- |
| [`consensus_iff_image_ne_univ`](Consensus.lean#L25) | [`consensus_iff_image_ne_univ`](../ComponentGames/ConsensusConnected.lean#L203) |

## Consensus in bounded time

| Statement or definition | Proof or construction |
| --- | --- |
| [`bounded_consensus_iff_not_dense`](BoundedConsensus.lean#L25) | [`bounded_consensus_iff_not_dense`](../ComponentGames/ConsensusGap.lean#L153) |

## Repeated consensus and nowhere denseness

| Statement or definition | Proof or construction |
| --- | --- |
| [`repeated_bounded_iff_nowhere_dense`](RepeatedConsensus.lean#L27) | [`repeated_bounded_iff_nowhere_dense`](../ComponentGames/ConsensusGap.lean#L179) |
| [`computable_consensus_bound`](RepeatedConsensus.lean#L36) | [`computable_consensus_bound`](../ComponentGames/ConsensusBound.lean#L46) |

## Empty interior implies repeated consensus

| Statement or definition | Proof or construction |
| --- | --- |
| [`repeated_consensus_of_empty_interior`](EmptyInterior.lean#L25) | [`repeated_consensus_of_empty_interior`](../ComponentGames/ConsensusConnected.lean#L210) |

## Agreeing on a broadcaster

| Statement or definition | Proof or construction |
| --- | --- |
| [`consensus_broadcaster`](Broadcaster.lean#L26) | [`consensus_broadcaster`](../ComponentTrees/ConsensusBroadcaster.lean#L63) |

## Computing a uniform consensus bound

| Statement or definition | Proof or construction |
| --- | --- |
| [`computable_consensus_bound`](ConsensusBound.lean#L27) | [`computable_consensus_bound`](../ComponentGames/ConsensusBound.lean#L46) |
| [`computedConsensusBound_correct`](ConsensusBound.lean#L42) | [`computedConsensusBound_correct`](../ComponentGames/ConsensusBound.lean#L22) |

## Nowhere denseness and missing extensions

| Statement or definition | Proof or construction |
| --- | --- |
| [`nowhere_dense_iff_missing_extension`](MissingExtension.lean#L26) | [`nowhere_dense_iff_missing_extension`](../Undecidability/Adversaries.lean#L26) |

## A dense residual adversary

| Statement or definition | Proof or construction |
| --- | --- |
| [`non_nowhere_dense_has_dense_residual`](DenseResidual.lean#L28) | [`non_nowhere_dense_has_dense_residual`](../Undecidability/Adversaries.lean#L41) |
| [`prefixDense_iff_dense`](DenseResidual.lean#L34) | [`prefixDense_iff_dense`](../../Library/Distributed/GraphAdversaries/SafetyClosure.lean#L33) |

## Agreement along a view path

| Statement or definition | Proof or construction |
| --- | --- |
| [`execution_agreement_implies_uniform`](PathAgreement.lean#L28) | [`execution_agreement_implies_uniform`](../../Library/Distributed/ViewAgreement.lean#L37) |

## Position residues and orientation

| Statement or definition | Proof or construction |
| --- | --- |
| [`position_rows`](PositionOrder.lean#L36) | [`position_rows`](../Undecidability/OneCounterRows.lean#L139) |
| [`oriented_decode`](PositionOrder.lean#L49) | [`oriented_decode`](../Lemma/LemScalingLTL.lean#L51) |
| [`monitor_orientation`](PositionOrder.lean#L55) | [`monitor_orientation`](../Lemma/LemScalingLTL.lean#L101) |
| [`position_decodes_view_orientation`](PositionOrder.lean#L66) | [In the entry file](PositionOrder.lean#L66) |

## Agreement on the control state

| Statement or definition | Proof or construction |
| --- | --- |
| [`agreement_row_uniform`](ControlAgreement.lean#L29) | [`agreement_row_uniform`](../Undecidability/OneCounterRows.lean#L149) |

## The local weight identity

| Statement or definition | Proof or construction |
| --- | --- |
| [`local_sum_on_view_edge`](LocalSum.lean#L35) | [`local_sum_on_view_edge`](../Undecidability/OneCounterRows.lean#L162) |

## Checking whether the counter is zero

| Statement or definition | Proof or construction |
| --- | --- |
| [`zero_claim_on_row`](ZeroCheck.lean#L29) | [`zero_claim_on_row`](../Undecidability/OneCounterRows.lean#L177) |

## Checking the initial configuration

| Statement or definition | Proof or construction |
| --- | --- |
| [`initial_check_on_row`](InitialCheck.lean#L29) | [`initial_check_on_row`](../Undecidability/OneCounterRows.lean#L208) |

## Checking a machine transition

| Statement or definition | Proof or construction |
| --- | --- |
| [`transition_child_weight`](ProperTransition.lean#L29) | [`transition_child_weight`](../Undecidability/OneCounterRows.lean#L240) |
| [`transition_leftmost_control`](ProperTransition.lean#L45) | [`transition_leftmost_control`](../Undecidability/OneCounterRows.lean#L256) |

## The formula and the row conditions

| Statement or definition | Proof or construction |
| --- | --- |
| [`global_rows_iff_formula`](RowConditions.lean#L35) | [`global_rows_iff_formula`](../Undecidability/OneCounterRows.lean#L132) |

## Soundness of the counter encoding

`formula_logarithmic_run` identifies the control state and the counter value
represented by the row mass at every step. The scalar construction is
transported to the existing counter implementation; `run_embed` proves that
this preserves the run. `soundness` instantiates the equivalence for every
scalar program, discharging `OnlyFirst` internally.

| Statement or definition | Proof or construction |
| --- | --- |
| [`formula_logarithmic_run`](CounterSoundness.lean#L41) | [`formula_logarithmic_run`](../Undecidability/OneCounterSoundness.lean#L18) |
| [`formula_zero_exact`](CounterSoundness.lean#L56) | [`formula_zero_exact`](../Undecidability/OneCounterSoundness.lean#L32) |
| [`soundness`](CounterSoundness.lean#L68) | [`ofCode_realizable_iff`](../Undecidability/OneCounterTransport.lean#L432) |

## Completeness of the counter encoding

`source_realizes` checks the right-plan strategy after projecting its outputs
to the scalar tuple. `completeness` instantiates this construction for an
arbitrary scalar program, using `ofCode_onlyFirst` to discharge the encoding
condition. It does not assume an invariant about the machine's run.

| Statement or definition | Proof or construction |
| --- | --- |
| [`source_realizes`](CounterCompleteness.lean#L38) | [`source_realizes`](../Undecidability/OneCounterSoundness.lean#L49) |
| [`completeness`](CounterCompleteness.lean#L50) | [`source_realizes`](../Undecidability/OneCounterSoundness.lean#L49) |

## Nonhalting is equivalent to realizability

| Statement or definition | Proof or construction |
| --- | --- |
| [`ofCode_realizable_iff`](CounterEquivalence.lean#L34) | [`ofCode_realizable_iff`](../Undecidability/OneCounterTransport.lean#L432) |

## Safety and closure of the adversary

| Statement or definition | Proof or construction |
| --- | --- |
| [`safety_closure_transfer`](SafetyClosure.lean#L29) | [`safety_closure_transfer`](../../Library/Distributed/GraphAdversaries/SafetyClosure.lean#L49) |
| [`actual_execution_causal`](SafetyClosure.lean#L36) | [`actual_execution_causal`](../../Library/Distributed/GraphAdversaries/ExecutionSafety.lean#L15) |
| [`same_strategy_closure`](SafetyClosure.lean#L44) | [In the entry file](SafetyClosure.lean#L44) |

## Reduction to an adversary with a dense residual

| Statement or definition | Proof or construction |
| --- | --- |
| [`guarded_safety_reduction_of_dense`](GuardedReduction.lean#L28) | [`guarded_safety_reduction_of_dense`](../Undecidability/Adversaries.lean#L101) |
| [`guardFormula_realizable_iff`](GuardedReduction.lean#L41) | [`guardFormula_realizable_iff`](../Undecidability/GuardedFormulaCorrespondence.lean#L30) |
| [`guardFormula_safety`](GuardedReduction.lean#L59) | [`guardFormula_safety`](../Undecidability/GuardedFormulaCorrespondence.lean#L13) |

## The specification automaton

| Statement or definition | Proof or construction |
| --- | --- |
| [`A_phi_language`](SpecificationAutomaton.lean#L28) | [`A_phi_language`](../ComponentGames/Objective.lean#L56) |
| [`A_phi_uniform_compiler`](SpecificationAutomaton.lean#L38) | [`A_phi_uniform_compiler`](../ComponentGames/Objective.lean#L68) |

## The block automaton and live states

| Statement or definition | Proof or construction |
| --- | --- |
| [`synthesisBlockAutomaton_language`](BlockAutomaton.lean#L33) | [`synthesisBlockAutomaton_language`](../ComponentTrees/SynthesisAutomaton.lean#L15) |
| [`synthesisBlockAutomaton_live`](BlockAutomaton.lean#L46) | [`synthesisBlockAutomaton_live`](../ComponentTrees/SynthesisAutomaton.lean#L28) |

## Algorithms and uncompressed component trees

| Statement or definition | Proof or construction |
| --- | --- |
| [`uncompressed_equivalence`](UncompressedTrees.lean#L33) | [`uncompressed_equivalence`](../ComponentTrees/CompiledObjective.lean#L57) |
| [`executable_readback_realizes`](UncompressedTrees.lean#L54) | [`executable_readback_realizes`](../ComponentTrees/CompiledObjective.lean#L83) |

## Extending maps of view complexes

| Statement or definition | Proof or construction |
| --- | --- |
| [`extend_history`](ViewExtension.lean#L31) | [`extend_history`](../ComponentTrees/ViewMaps.lean#L112) |
| [`extend_zero`](ViewExtension.lean#L39) | [`extend_zero`](../ComponentTrees/ViewMaps.lean#L132) |
| [`extend_identity`](ViewExtension.lean#L45) | [`extend_identity`](../ComponentTrees/ViewMaps.lean#L120) |
| [`extend_comp`](ViewExtension.lean#L52) | [`extend_comp`](../ComponentTrees/ViewMaps.lean#L126) |
| [`extend_inverse`](ViewExtension.lean#L59) | [`extend_inverse`](../ComponentTrees/ViewMaps.lean#L137) |

## A common preceding view in a component

| Statement or definition | Proof or construction |
| --- | --- |
| [`bounded_common_view`](CommonView.lean#L33) | [`bounded_common_view`](../ComponentTrees/CommonView.lean#L217) |

## Compressing a component

| Statement or definition | Proof or construction |
| --- | --- |
| [`compression_reduction`](Compression.lean#L32) | [`compression_reduction`](../ComponentTrees/ComponentSteps.lean#L97) |
| [`endpointTable_card`](Compression.lean#L60) | [`endpointTable_card`](../ComponentTrees/Compression.lean#L98) |
| [`endpointFold_image_bound`](Compression.lean#L68) | [`endpointFold_image_bound`](../ComponentTrees/Compression.lean#L105) |
| [`live_endpoints_bound`](Compression.lean#L85) | [`live_endpoints_bound`](../ComponentTrees/Compression.lean#L222) |

## Uncompressed and compressed trees

| Statement or definition | Proof or construction |
| --- | --- |
| [`block_bounded_representation`](BoundedRepresentation.lean#L34) | [`block_bounded_representation`](../ComponentTrees/BoundedRepresentation.lean#L46) |

## Compressed and symbolic trees

| Statement or definition | Proof or construction |
| --- | --- |
| [`model_tree_iff`](SymbolicTrees.lean#L35) | [`model_tree_iff`](../ComponentTrees/GeneratingEncode.lean#L201) |
| [`decode_accepting`](SymbolicTrees.lean#L53) | [`decode_accepting`](../ComponentTrees/GeneratingDecode.lean#L298) |

## MSO defines the accepting symbolic trees

`sentence_correct` connects MSO satisfaction to the local table conditions and
acceptance of all compatible runs. `mso_compressed_iff` then uses the encoding
and decoding of compressed trees. `satisfiable_correct` adds the executable
MSO satisfiability procedure to this equivalence.

| Statement or definition | Proof or construction |
| --- | --- |
| [`sentence_correct`](MSO.lean#L40) | [`sentence_correct`](../ComponentTrees/GeneratingAlphabet.lean#L131) |
| [`mso_compressed_iff`](MSO.lean#L53) | [`mso_compressed_iff`](../ComponentTrees/GeneratingEncode.lean#L214) |
| [`satisfiable_correct`](MSO.lean#L71) | [`satisfiable_correct`](../ComponentTrees/GeneratingEncode.lean#L221) |
