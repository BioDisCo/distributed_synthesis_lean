# Undecidability: constructions and proof correspondence

For the paper statements and their proofs, start with the
[paper correspondence guide](../Paper/README.md). It includes the scalar
soundness and completeness statements, the row conditions, and the extension
to general adversaries, with direct links to the underlying proofs.

The scalar output tuple and its exact transport to the shared counter-machine
implementation are in [OneCounterTransport.lean](OneCounterTransport.lean).
[OneCounterRows.lean](OneCounterRows.lean) proves the individual row conditions;
[OneCounterSoundness.lean](OneCounterSoundness.lean) identifies the logarithmic
counter value and checks the explicit realizing strategy. The position
alphabet is `Fin 3` throughout these constructions.

The table below describes the two-counter implementation reused by that
transport. It is an implementation map, rather than a second statement of
the paper's scalar results. The entry files give the corresponding statements
and proofs.

The output tuple is `(q, zero, rightPlan, carry, pos)`. The initial check
specifies the initial control state and zero indicators; the initial weights
follow from the zero-claim condition.

The formal reduction handles both counters directly, using `Fin 2`, a shared
control state, and two zero indicators, plans, and carries. It reuses the
existing `Machine`, `Plan`, views, strategies, LTL syntax, finite-letter tests,
numeric encodings, and computable reductions. The halting source remains the
existing checked reduction from Mathlib computability. No new machine model,
finite-set implementation, or assumed undecidability theorem is introduced.

## Shared counter-machine implementation

| Manuscript statement or step | Lean evidence | Scope |
| --- | --- | --- |
| Two-counter nonhalting source | `SourcePort.source`, `SourcePort.reduce_primrec`, `Unconditional.encoded_ltl_synthesis_undecidable` | Existing unconditional source chain and effective reduction reused. |
| Output tuple and initial check | `CounterMachine.Label`, `ResidueLTL.Output`, `Valid.initial`, `Paper.initialCheck_iff` | Current tuple only; no left plan. Checks the zero indicators, not an unmentioned stronger input certificate. |
| `lem:agreement_on_path`, `lem:pathagr` | Existing `Rows.row_path`, `Rows.row_uniform`; `Paper.agreement_iff` | Existing connected-path propagation and actual strategy rows reused. |
| `lem:posord` | `Paper.position_coordinates`, existing `oriented_update`, `oriented_decode`, `monitor_orientation` | Arbitrary strategies satisfying the position recurrence have the actual view coordinates modulo three. This is not restricted to the constructed winner. |
| `lem:local-sum` | `Paper.localCheck_iff`, `Valid.balance`, `Rows.row_recurrence` | Balance on each edge; carry cancellation across the entire row. No plan-agreement premise. |
| `lem:zero-claim` | `Rows.boundary_carries`, `Rows.row_guard`, `Rows.row_zero_exact` | Includes the false-zero leftmost-weight check required by C3. |
| `lem:init-check` | `Valid.initial`, `Rows.row_initial_weight`, `Rows.row_initial_mass`, `Rows.row_initial_control` | Initial weights are derived from the initial zero indicators and zero-weight rule. |
| `lem:prop-trans` | `Paper.pairCheck_iff`, `Rows.children_weight_sum`, `Rows.row_control_next` | Process-1 control transition is equivalent to the oriented check under path agreement. All three child weights use the same right plan. |
| Formula decomposition | `Paper.conditions_iff_checks` | Exact semantic clauses for position, path agreement, local sum, zero claim, initialization, transition, and the separate nonhalting conjunct. The corrected equivalence lemma includes the nonhalting conjunct. |
| `lem:soundness` | `Rows.forced_counters`, `Rows.extracted_eq_run`, `Rows.winning_implies_nonhalting`; `TernaryCounter.encoded_log_counter`, `forced_log_counters` | The existing integer induction establishes positivity and integrality; Mathlib logarithms identify it with the intended real-valued expression. |
| Logarithmic soundness for actual realizing strategies | `Paper.checks_row_masses`, `checks_logarithmic_transition`, `checks_logarithmic_run`, `checks_zero_iff_logarithm_zero`, `formula_logarithmic_run` | Derives positivity, the mass recurrence, the logarithmic transition, exact natural counter values, and zero detection from the formula. No row certificate or integrality assumption. Reuses the existing strategy rows. |
| Logarithmic case analysis | `TernaryCounter.logarithmic_mass_step`, `operation_logarithmic_change` | Follows the English normalized-mass calculation using Mathlib logarithm identities; factors 1, 3, and 9 give changes 1, 0, and -1. |
| Arithmetic soundness independent of monitor representation | `CounterMachine.nonhalting_of_row_masses` | General helper with explicit aggregate row hypotheses. The end-to-end theorem discharges these using actual rows; this helper alone is not advertised as full soundness. |
| `lem:find_index` | Existing `ScalingSafety.coordinate`, `child_coordinates`, `child_coordinates_reverse`, `Source.advance_geometry` | Reuses the structural view recursion and child geometry. |
| `lem:completeness` | `CounterMachine.Source.strategy`, `Source.wins`, `Paper.source_checks` | The explicit algorithm, including coordinate residues, is checked for every nonhalting two-counter machine. |
| Completeness arithmetic | Existing `TernaryCounter.weight_bound`, `carry_bound`, `conservation`, `carry_at_multiple`; `CounterMachine.Source.counter_bound` | Binary weights; carries below 9; exact local identity; vanishing boundary carries; counter at machine step n at most n. |
| `thm:nonhalt<=>realizability` | `Paper.checks_realizable_iff_nonhalting`, `ResidueLTL.ltl_realizable_iff_nonhalting` | Arbitrary perfect-recall strategies, singleton inputs, finite outputs, all three graphs. No extra left-plan, row, or finite-memory assumption. |
| Safety of the constructed formula | `Paper.checks_safety`, existing `counter_conditions_safety` | Proves that the constructed specification is a safety property. |
| `lem:safety:is:safe` | `safety_closure_transfer`, `actual_execution_causal` | Same fixed strategy; arbitrary adversary; standard product topology; no regularity assumption. |
| `lem:nowhere-dense-live` | `nowhere_dense_iff_missing_extension` | All finite prefixes, including already nonlive ones; reuses the geometric-prefix equivalence. |
| `lem:not:nowhere:dense:is:dense:somewhere` | `non_nowhere_dense_has_dense_residual`, `prefixDense_iff_dense` | Ordinary topological density, not only a separately named prefix condition. No omega-regularity premise needed. |
| `lem:guarded-safety-reduction` | `guarded_safety_reduction_of_dense`, `guarded_objective_safety`, `prefixed_mem_closure_of_dense_residual`, existing `seedStrategy_execution`, `resetStrategy_execution` | Both actual strategy transformations and exact suffix executions. The proof now follows the English closure argument: the same strategy satisfies the guarded safety objective on the closure, which contains the entire chosen prefix cylinder. |
| Literal guarded LTL formula | `guardFormula_safety`, `guardFormula_realizable_iff`, `guardedCompile_safety` | Connects the semantic argument to the existing guard syntax and decoded compiler output. Safety holds on all words in the actual finite alphabet, not only on executions of the constructed strategy. |
| Final effective adversary reduction | `guardedCompile_primrec`, existing `guardedCompile_computable`, `no_geometric_holes_encoded_undecidable`, `no_geometric_holes_undecidable` | The full compiler is primitive recursive for each fixed prefix. The endpoints hold for every non-nowhere-dense adversary, without requiring omega-regularity. |

## Verification

```sh
lake --wfail build DistributedSynthesis.Tests.Undecidability.Audit
python3 scripts/check_library.py --axioms DistributedSynthesis/Tests/Undecidability/Audit.lean
python3 verification/verify.py fast
```

The dedicated audit includes the new correspondence results and the reused
unconditional endpoints. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. The standard verification command also checks the existing
game and component-tree developments.

The dedicated audit now covers 53 endpoints, including the direct
logarithmic soundness bridge and guarded-formula correspondence. Run the commands above after changes to check
the current build and axiom dependencies.
