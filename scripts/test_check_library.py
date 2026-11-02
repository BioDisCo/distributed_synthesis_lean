"""Regression tests for the import-boundary checker (no source files modified)."""

import unittest
from pathlib import Path
import subprocess
import tempfile
from unittest.mock import patch

from check_library import architecture_checks, audit_axioms, check_graph, module_graph


class AxiomAuditTest(unittest.TestCase):
    def check_report(self, output, target="Example.result"):
        with tempfile.TemporaryDirectory() as directory:
            audit = Path(directory) / "Audit.lean"
            audit.write_text(f"#print axioms {target}\n")
            result = subprocess.CompletedProcess([], 0, stdout=output)
            with patch("check_library.subprocess.run", return_value=result) as run:
                errors = audit_axioms(audit)
                self.assertEqual(run.call_args.args[0][-1], str(audit))
            return errors

    def test_custom_audit_rejects_unapproved_axiom(self):
        errors = self.check_report("'Example.result' depends on axioms: [sorryAx]\n")
        self.assertTrue(any("unapproved axioms" in error for error in errors))

    def test_custom_audit_rejects_missing_report(self):
        errors = self.check_report("")
        self.assertTrue(any("missing axiom report" in error for error in errors))


    def test_primed_name_with_allowed_axioms(self):
        self.assertEqual(self.check_report(
            "'Example.result'' depends on axioms: [propext, Quot.sound]\n",
            "Example.result'"), [])

    def test_primed_name_without_axioms(self):
        self.assertEqual(self.check_report(
            "'Example.result'' does not depend on any axioms\n",
            "Example.result'"), [])

    def test_primed_name_rejects_unapproved_axiom(self):
        errors = self.check_report(
            "'Example.result'' depends on axioms: [sorryAx]\n", "Example.result'")
        self.assertTrue(any("unapproved axioms" in error for error in errors))


class LibraryBoundariesTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.graph = module_graph()

    def test_current_supported_graph(self):
        self.assertEqual(architecture_checks(self.graph), [])

    def test_unimported_public_module_is_rejected(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.UnimportedPublicModule"] = set()
        errors = architecture_checks(graph)
        self.assertTrue(any("public module omitted from root build" in error
                            for error in errors))

    def test_mso_semantics_does_not_import_automata(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Logic.MSO.Semantics"].add(
            "DistributedSynthesis.Library.Automata.Tree")
        self.assertTrue(any("MSO.Semantics: lightweight boundary" in error
                            for error in architecture_checks(graph)))

    def test_generic_threads_do_not_import_sender_narrowing(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Automata.UniversalThreads"].add(
            "DistributedSynthesis.Formalizations.Theorem.ThmUniversalThreadDeterminization")
        self.assertTrue(any("TreeComplement: MSO automata isolation" in error
                            for error in architecture_checks(graph)))

    def test_numeric_mso_does_not_import_synthesis_backend(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Automata.EncodedParityFamilies"].add(
            "DistributedSynthesis.Formalizations.Theorem.ThmBlindGameAPA")
        self.assertTrue(any("MSO.PrimitiveRecursive: MSO automata isolation" in error
                            for error in architecture_checks(graph)))

    def test_positive_holes_does_not_import_negative_reduction(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Distributed.LeaderPhases.ComponentLeader"].add(
            "DistributedSynthesis.Library.Distributed.GraphAdversaries.Undecidability.InstanceEncoding")
        self.assertTrue(any("Decidability: graph-adversary boundary violated" in error
                            for error in architecture_checks(graph)))

    def test_graph_model_does_not_import_leader_game(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Distributed.GraphAdversaries.Model"].add(
            "DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeaderGame")
        self.assertTrue(any("Model: graph-adversary boundary violated" in error
                            for error in architecture_checks(graph)))

    def test_numeric_parity_does_not_import_geometric_application(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Automata.EncodedMuller"].add(
            "DistributedSynthesis.Library.Topology.OpenHoles")
        self.assertTrue(any("generic holes prerequisite coupled to application" in error
                            for error in architecture_checks(graph)))

    def test_library_cannot_import_removed_addon(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Distributed.GraphAdversaries.Model"].add(
            "Characterisation.Conjecture")
        self.assertTrue(any("missing import Characterisation.Conjecture" in error
                            for error in architecture_checks(graph)))

    def test_missing_import_is_rejected(self):
        self.assertTrue(check_graph({"DistributedSynthesis.A": {"DistributedSynthesis.Absent"}}))

    def test_import_cycle_is_rejected(self):
        graph = {"DistributedSynthesis.A": {"DistributedSynthesis.B"}, "DistributedSynthesis.B": {"DistributedSynthesis.A"}}
        self.assertTrue(any("cycle" in error for error in check_graph(graph)))

    def test_synthesis_coupling_is_rejected_transitively(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Automata.Compilers"].add(
            "DistributedSynthesis.Formalizations.Definition.DefSynthesisProblem"
        )
        errors = architecture_checks(graph)
        self.assertTrue(any("automata isolation violated" in error for error in errors))
        self.assertTrue(any("Automata.Piterman: automata isolation" in error for error in errors))

    def test_sender_narrowing_cannot_return_to_ltl_pipeline(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Formalizations.Theorem.ThmAPAMembershipGame"].add(
            "DistributedSynthesis.Formalizations.Theorem.ThmUniversalThreadDeterminization"
        )
        errors = architecture_checks(graph)
        self.assertTrue(any("Automata.LTLTranslation: automata isolation" in error for error in errors))

    def test_computable_piterman_stays_independent_of_journal_synthesis(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Automata.PitermanComputable"].add(
            "DistributedSynthesis.Library.Distributed.NoDirectJournal"
        )
        errors = architecture_checks(graph)
        self.assertTrue(any("PitermanComputable: automata isolation" in error for error in errors))

    def test_finite_orbits_remains_independent_of_automata(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Combinatorics.FiniteOrbits"].add(
            "DistributedSynthesis.Library.Automata.Compilers"
        )
        errors = architecture_checks(graph)
        self.assertTrue(any("FiniteOrbits: lightweight boundary" in error for error in errors))

    def test_allocation_layer_cannot_import_language_correctness(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Automata.PitermanAllocation"].add(
            "DistributedSynthesis.Formalizations.Theorem.ThmPitermanDeterminization"
        )
        errors = architecture_checks(graph)
        self.assertTrue(any("PitermanAllocation: lightweight boundary" in error for error in errors))

    def test_execution_stays_out_of_padding_projection(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Distributed.PaddingProjection"].add(
            "DistributedSynthesis.Library.Distributed.Execution"
        )
        errors = architecture_checks(graph)
        self.assertTrue(any("PaddingProjection: lightweight boundary" in error for error in errors))

    def test_execution_cannot_import_game_certificates(self):
        for dependency in ("DistributedSynthesis.Library.Distributed.ParitySpecification",
                           "DistributedSynthesis.Formalizations.Definition.DefSynthesisProblem",
                           "DistributedSynthesis.Formalizations.Theorem.ThmDynhiersynth"):
            with self.subTest(dependency=dependency):
                graph = {module: imports.copy() for module, imports in self.graph.items()}
                graph["DistributedSynthesis.Library.Distributed.Execution"].add(dependency)
                errors = architecture_checks(graph)
                self.assertTrue(any("Distributed.Execution: lightweight boundary" in error
                                    for error in errors))

    def test_controller_core_cannot_import_physical_adapter(self):
        for name in ("PhysicalControllers", "MealyControllers"):
            with self.subTest(module=name):
                graph = {module: imports.copy() for module, imports in self.graph.items()}
                graph["DistributedSynthesis.Library.Distributed." + name].add(
                    "DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedPhysicalRoundAdapter"
                )
                errors = architecture_checks(graph)
                self.assertTrue(any(name + ": lightweight boundary" in error for error in errors))

    def test_source_port_stays_independent_of_distributed_consumers(self):
        for name in ("Halting", "ZeroInitialization", "ZeroInitializationComputable", "MMA2ToMM2"):
            with self.subTest(module=name):
                graph = {module: imports.copy() for module, imports in self.graph.items()}
                graph["DistributedSynthesis.Library.Computability.CounterMachines." + name].add(
                    "DistributedSynthesis.Library.Distributed.Execution"
                )
                errors = architecture_checks(graph)
                self.assertTrue(any("CounterMachines." + name + ": lightweight boundary" in error
                                    for error in errors))

    def test_generic_register_model_stays_independent_of_mm2(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Computability.CounterMachines.MMA"].add(
            "DistributedSynthesis.Library.Computability.CounterMachines.MM2"
        )
        errors = architecture_checks(graph)
        self.assertTrue(any("CounterMachines.MMA: lightweight boundary" in error for error in errors))

    def test_mathlib_bridge_stays_independent_of_rocq_and_targets(self):
        for name in ("FiniteControl", "InputEncoding", "UniversalStackMachine",
                     "BinaryStacks", "BinaryUniversalStackMachine"):
            for dependency in ("DistributedSynthesis.Library.Computability.CounterMachines.MMA",
                               "DistributedSynthesis.Library.Computability.TwoCounterMachines",
                               "DistributedSynthesis.Library.Distributed.Execution"):
                with self.subTest(module=name, dependency=dependency):
                    graph = {module: imports.copy() for module, imports in self.graph.items()}
                    module = "DistributedSynthesis.Library.Computability.CounterMachines.MathlibBridge." + name
                    graph[module].add(dependency)
                    errors = architecture_checks(graph)
                    self.assertTrue(any(module + ": lightweight boundary" in error for error in errors))

    def test_bsm_model_and_macros_stay_independent_of_the_bridge(self):
        for name in ("BSM", "BSMMacros", "BSMGraph", "TM2ToBSM"):
            for dependency in ("DistributedSynthesis.Library.Computability.CounterMachines.MMA",
                               "DistributedSynthesis.Library.Computability.CounterMachines.MathlibBridge.BinaryStacks",
                               "DistributedSynthesis.Library.Computability.TwoCounterMachines"):
                with self.subTest(module=name, dependency=dependency):
                    graph = {module: imports.copy() for module, imports in self.graph.items()}
                    module = "DistributedSynthesis.Library.Computability.CounterMachines." + name
                    graph[module].add(dependency)
                    errors = architecture_checks(graph)
                    self.assertTrue(any(module + ": lightweight boundary" in error for error in errors))

    def test_unconditional_bsm_source_cannot_import_open_mm2_interface(self):
        for dependency in ("DistributedSynthesis.Library.Computability.TwoCounterMachines",
                           "DistributedSynthesis.Library.Computability.CounterMachines.MMA2ToMM2",
                           "DistributedSynthesis.Library.Distributed.Execution"):
            with self.subTest(dependency=dependency):
                graph = {module: imports.copy() for module, imports in self.graph.items()}
                module = "DistributedSynthesis.Library.Computability.CounterMachines.BSMSource"
                graph[module].add(dependency)
                errors = architecture_checks(graph)
                self.assertTrue(any(module + ": lightweight boundary" in error for error in errors))

    def test_mm_port_has_no_mma_or_mm2_source_dependency(self):
        for name in ("MM", "MM.Frame", "MM.Arithmetic", "MM.StackEncoding", "MM.StackMacros",
                     "BSMToMM.Encoding", "BSMToMM.Compiler", "MMSource"):
            for dependency in ("DistributedSynthesis.Library.Computability.CounterMachines.MMA",
                               "DistributedSynthesis.Library.Computability.TwoCounterMachines",
                               "DistributedSynthesis.Library.Distributed.Execution"):
                with self.subTest(module=name, dependency=dependency):
                    graph = {module: imports.copy() for module, imports in self.graph.items()}
                    module = "DistributedSynthesis.Library.Computability.CounterMachines." + name
                    graph[module].add(dependency)
                    errors = architecture_checks(graph)
                    self.assertTrue(any(module + ": lightweight boundary" in error for error in errors))

    def test_mm_simulation_cannot_import_its_universal_source(self):
        for name in ("BSMToMM.Encoding", "BSMToMM.Compiler"):
            graph = {module: imports.copy() for module, imports in self.graph.items()}
            module = "DistributedSynthesis.Library.Computability.CounterMachines." + name
            graph[module].add("DistributedSynthesis.Library.Computability.CounterMachines.BSMSource")
            errors = architecture_checks(graph)
            self.assertTrue(any(module + ": lightweight boundary" in error for error in errors))

    def test_fractran_port_cannot_import_mma_or_open_mm2_interface(self):
        for name in ("FRACTRAN", "MMToFRACTRAN.Encoding", "MMToFRACTRAN.Blocks",
                     "MMToFRACTRAN.Compiler", "MMToFRACTRAN.Computable", "FRACTRANSource"):
            for dependency in ("DistributedSynthesis.Library.Computability.CounterMachines.MMA",
                               "DistributedSynthesis.Library.Computability.TwoCounterMachines",
                               "DistributedSynthesis.Library.Distributed.Execution"):
                with self.subTest(module=name, dependency=dependency):
                    graph = {module: imports.copy() for module, imports in self.graph.items()}
                    module = "DistributedSynthesis.Library.Computability.CounterMachines." + name
                    graph[module].add(dependency)
                    errors = architecture_checks(graph)
                    self.assertTrue(any(module + ": lightweight boundary" in error for error in errors))

    def test_fractran_simulation_cannot_import_universal_sources(self):
        for name in ("FRACTRAN", "MMToFRACTRAN.Encoding", "MMToFRACTRAN.Blocks",
                     "MMToFRACTRAN.Compiler", "MMToFRACTRAN.Computable"):
            for source in ("MMSource", "FRACTRANSource"):
                with self.subTest(module=name, source=source):
                    graph = {module: imports.copy() for module, imports in self.graph.items()}
                    module = "DistributedSynthesis.Library.Computability.CounterMachines." + name
                    graph[module].add("DistributedSynthesis.Library.Computability.CounterMachines." + source)
                    errors = architecture_checks(graph)
                    self.assertTrue(any(module + ": lightweight boundary" in error for error in errors))

    def test_mma_simulation_does_not_import_universality(self):
        for name in ("MMA.Execution", "MMA.Frame", "MMA.Arithmetic", "MMA.Subtract", "MMA.Division",
                     "FRACTRANToMMA.Fraction", "FRACTRANToMMA.Compiler"):
            for source in ("MMSource", "FRACTRANSource", "MMA2Source", "Source"):
                with self.subTest(module=name, source=source):
                    graph = {module: imports.copy() for module, imports in self.graph.items()}
                    module = "DistributedSynthesis.Library.Computability.CounterMachines." + name
                    graph[module].add("DistributedSynthesis.Library.Computability.CounterMachines." + source)
                    errors = architecture_checks(graph)
                    self.assertTrue(any(module + ": lightweight boundary" in error for error in errors))

    def test_mma2_source_cannot_import_the_interface_it_will_discharge(self):
        for dependency in ("DistributedSynthesis.Library.Computability.TwoCounterMachines",
                           "DistributedSynthesis.Library.Computability.CounterMachines.Source",
                           "DistributedSynthesis.Library.Computability.CounterMachines.MMA2ToMM2"):
            graph = {module: imports.copy() for module, imports in self.graph.items()}
            module = "DistributedSynthesis.Library.Computability.CounterMachines.MMA2Source"
            graph[module].add(dependency)
            errors = architecture_checks(graph)
            self.assertTrue(any(module + ": lightweight boundary" in error for error in errors))

    def test_completed_source_cannot_import_distributed_consumers(self):
        for dependency in ("DistributedSynthesis.Results.UnconditionalUndecidability",
                           "DistributedSynthesis.Library.Distributed.Execution"):
            graph = {module: imports.copy() for module, imports in self.graph.items()}
            module = "DistributedSynthesis.Library.Computability.CounterMachines.Source"
            graph[module].add(dependency)
            errors = architecture_checks(graph)
            self.assertTrue(any(module + ": lightweight boundary" in error for error in errors))

    def test_stable_source_interface_does_not_import_the_port(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Computability.TwoCounterMachines"].add(
            "DistributedSynthesis.Library.Computability.CounterMachines.ZeroInitializationComputable"
        )
        errors = architecture_checks(graph)
        self.assertTrue(any("TwoCounterMachines: lightweight boundary" in error for error in errors))

    def test_execution_coupling_is_rejected_by_binary_adapter(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Distributed.Execution"].add(
            "DistributedSynthesis.Formalizations.Theorem.ThmDynhiersynth"
        )
        errors = architecture_checks(graph)
        self.assertTrue(any("BinaryReduction: execution-adapter boundary" in error
                            for error in errors))

    def test_binary_agreement_stays_independent_of_source_machine(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Distributed.BinaryAgreement"].add(
            "DistributedSynthesis.Library.Computability.TwoCounterMachines"
        )
        errors = architecture_checks(graph)
        self.assertTrue(any("BinaryAgreement: execution-adapter boundary" in error for error in errors))

    def test_binary_word_tests_remain_independent_of_views(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Logic.BinaryWords"].add("DistributedSynthesis.Library.Distributed.Views")
        errors = architecture_checks(graph)
        self.assertTrue(any("BinaryWords: lightweight boundary" in error for error in errors))

    def test_binary_reduction_stays_independent_of_source_machine(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Distributed.BinaryReduction"].add(
            "DistributedSynthesis.Library.Computability.TwoCounterMachines"
        )
        errors = architecture_checks(graph)
        self.assertTrue(any("BinaryReduction: execution-adapter boundary" in error for error in errors))

    def test_encoded_compiler_remains_logic_only(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Logic.EncodedBinarySyntax"].add(
            "DistributedSynthesis.Library.Distributed.Views"
        )
        errors = architecture_checks(graph)
        self.assertTrue(any("EncodedBinarySyntax: lightweight boundary" in error for error in errors))

    def test_encoded_binary_adapter_stays_independent_of_source_machine(self):
        graph = {module: imports.copy() for module, imports in self.graph.items()}
        graph["DistributedSynthesis.Library.Distributed.EncodedBinaryReduction"].add(
            "DistributedSynthesis.Library.Computability.TwoCounterMachines"
        )
        errors = architecture_checks(graph)
        self.assertTrue(any("EncodedBinaryReduction: execution-adapter boundary" in error for error in errors))


    def test_executable_automata_stay_synthesis_independent(self):
        for name in ("MiyanoHayashiComputable", "WeakComputable", "LTLComputable",
                     "FiniteOrbitParity", "EncodedOrbitParity", "EncodedLTLStates", "EncodedLTLTransitions",
                     "AlternatingRetraction", "EncodedLTLAutomaton", "EncodedSupports", "EncodedSupportTables",
                     "EncodedBreakpoints", "EncodedLTLBreakpoints",
                     "EncodedPitermanStates", "EncodedPitermanTransition", "EncodedPitermanAllocation",
                     "EncodedPitermanCreation", "EncodedPitermanPruning", "EncodedPitermanMinima",
                     "EncodedPitermanDeletion", "EncodedPitermanGreen", "EncodedPitermanStep",
                     "EncodedParityTables", "EncodedPitermanAutomaton", "EncodedPitermanCompiler",
                     "EncodedLTLNumbering", "EncodedLTLParity"):
            with self.subTest(module=name):
                graph = {module: imports.copy() for module, imports in self.graph.items()}
                graph["DistributedSynthesis.Library.Automata." + name].add(
                    "DistributedSynthesis.Library.Distributed.Views"
                )
                errors = architecture_checks(graph)
                self.assertTrue(any(name + ": automata isolation" in error for error in errors))


    def test_tree_nonemptiness_stays_synthesis_independent(self):
        for name in ("TreeNonemptiness", "EncodedTreeNonemptiness"):
            with self.subTest(module=name):
                graph = {module: imports.copy() for module, imports in self.graph.items()}
                graph["DistributedSynthesis.Library.Automata." + name].add(
                    "DistributedSynthesis.Library.Distributed.Views"
                )
                errors = architecture_checks(graph)
                self.assertTrue(any(name + ": tree automata isolation" in error for error in errors))


    def test_encoded_normalization_stays_logic_only(self):
        for name in ("PostfixFold", "EncodedPositiveLTL", "EncodedPositiveBoolean"):
            with self.subTest(module=name):
                graph = {module: imports.copy() for module, imports in self.graph.items()}
                graph["DistributedSynthesis.Library.Logic." + name].add("DistributedSynthesis.Library.Automata.Piterman")
                errors = architecture_checks(graph)
                self.assertTrue(any(name + ": lightweight boundary" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
