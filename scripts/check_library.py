#!/usr/bin/env python3
"""Check public import boundaries; optionally audit selected Lean axioms.

Read-only. Run from any directory after `lake build` for --axioms.
Checks transitive dependencies through public and implementation
files. The extracted automata and execution/controller-core APIs must not import
the synthesis backend.
"""

import argparse
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^import\s+((?:DistributedSynthesis|Characterisation)(?:\.[A-Za-z0-9_]+)*)\s*$", re.MULTILINE)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def module_graph():
    paths = [ROOT / "DistributedSynthesis.lean", *sorted((ROOT / "DistributedSynthesis").rglob("*.lean"))]
    return {
        ".".join(path.relative_to(ROOT).with_suffix("").parts):
        set(IMPORT.findall(path.read_text()))
        for path in paths
    }


def check_graph(graph):
    errors = []
    for module, imports in graph.items():
        for dependency in imports:
            if dependency not in graph:
                errors.append(f"{module}: missing import {dependency}")
    active, finished = set(), set()

    def visit(module):
        if module in active:
            errors.append(f"import cycle through {module}")
            return
        if module in finished:
            return
        active.add(module)
        for dependency in graph.get(module, ()):
            visit(dependency)
        active.remove(module)
        finished.add(module)

    for module in graph:
        visit(module)
    return errors


def closure(graph, root):
    seen, pending = set(), [root]
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module)
            pending.extend(graph.get(module, ()))
    return seen


def family(module, prefix):
    return module == prefix or module.startswith(prefix + ".")


def architecture_checks(graph, report=False):
    library = sorted(m for m in graph if family(m, "DistributedSynthesis.Library"))
    results = sorted(m for m in graph if family(m, "DistributedSynthesis.Results"))
    # Check the supported public and test import closures.
    supported = set()
    roots = ["DistributedSynthesis", "DistributedSynthesis.Tests", "DistributedSynthesis.Tests.Axioms", *library, *results]
    for root in roots:
        supported.update(closure(graph, root))
    errors = check_graph({m: deps for m, deps in graph.items() if m in supported})
    if report:
        for module, imports in graph.items():
            if module not in supported:
                for dependency in imports - graph.keys():
                    print(f"Outside supported build: {module} imports missing {dependency}")
    if not library or not results:
        errors.append("missing Library or Results entry points")
    for module in library + results:
        dependencies = closure(graph, module)
        forbidden = {m for m in dependencies if m == "DistributedSynthesis" or family(m, "DistributedSynthesis.Legacy")}
        if module in library:
            forbidden |= {m for m in dependencies if family(m, "DistributedSynthesis.Results")}
        if forbidden:
            errors.append(f"{module}: forbidden dependency {sorted(forbidden)}")
        if report:
            print(f"{module}: {len(dependencies) - 1} transitive project imports")

    # Explicit small closures: additions require reviewing the new dependency.
    definitions = "DistributedSynthesis.Formalizations.Definition."
    lemmas = "DistributedSynthesis.Formalizations.Lemma."
    lightweight = {
        "DistributedSynthesis.Library.Distributed.Execution": {
            "DistributedSynthesis.Library.Distributed.Execution", "DistributedSynthesis.Basic",
            definitions + "DefHistory", definitions + "DefViews",
        },
        "DistributedSynthesis.Library.Distributed.DelayedHierarchy": {
            "DistributedSynthesis.Library.Distributed.DelayedHierarchy",
            "DistributedSynthesis.Library.Distributed.Views", "DistributedSynthesis.Basic",
            *(definitions + name for name in ("DefHistory", "DefViews", "DefObservations")),
            lemmas + "LemDelayonehierarchy",
        },
        "DistributedSynthesis.Library.Logic.LTL": {
            "DistributedSynthesis.Library.Logic.LTL", "DistributedSynthesis.Basic",
            definitions + "DefLTL", definitions + "DefLTLPositive",
        },
        "DistributedSynthesis.Library.Logic.FiniteEncoding": {
            "DistributedSynthesis.Library.Logic.FiniteEncoding", "DistributedSynthesis.Basic",
            definitions + "DefLTL", lemmas + "LemFiniteLetterLTL",
            lemmas + "LemEncodedFiniteLTL",
        },
        "DistributedSynthesis.Library.Computability.TwoCounterMachines": {
            "DistributedSynthesis.Library.Computability.TwoCounterMachines",
            lemmas + "LemMM2SourceSemantics", lemmas + "LemMM2SourceInterface",
        },
    }
    # Generic MSO syntax and semantics must remain independent of automata.
    mso_core = set()
    for name in ("Syntax", "Semantics", "Reachability", "Tree"):
        module = "DistributedSynthesis.Library.Logic.MSO." + name
        mso_core.add(module)
        if name == "Tree":
            mso_core.add(definitions + "DefTreeAutomata")
        lightweight[module] = mso_core.copy()

    physical_api = lightweight["DistributedSynthesis.Library.Distributed.Execution"] | {
        "DistributedSynthesis.Library.Distributed.PhysicalControllers",
    }
    lightweight["DistributedSynthesis.Library.Distributed.PhysicalControllers"] = physical_api
    lightweight["DistributedSynthesis.Library.Distributed.MealyControllers"] = physical_api | {
        "DistributedSynthesis.Library.Distributed.MealyControllers",
    }
    # The credited source port must not depend on its distributed consumers.
    # Keep the generic register model independent of the two-counter adapter.
    counter_port = "DistributedSynthesis.Library.Computability.CounterMachines"
    bridge_modules = tuple("MathlibBridge." + name for name in
                           ("FiniteControl", "InputEncoding", "UniversalStackMachine",
                            "BinaryStacks", "BinaryUniversalStackMachine"))
    mm_modules = ("MM", "MM.Frame", "MM.StackEncoding", "MM.Arithmetic", "MM.StackMacros",
                  "BSMToMM.Encoding", "BSMToMM.Compiler", "MMSource")
    fractran_modules = ("FRACTRAN", "MMToFRACTRAN.Encoding", "MMToFRACTRAN.Blocks",
                        "MMToFRACTRAN.Compiler", "MMToFRACTRAN.Computable", "FRACTRANSource")
    mma_arithmetic = ("MMA.Execution", "MMA.Frame", "MMA.Arithmetic", "MMA.Subtract", "MMA.Division")
    mma_compiler = ("FRACTRANToMMA.Fraction", "FRACTRANToMMA.Compiler")
    counter_modules = ("MM2", "Halting", "ZeroInitialization",
                       "ZeroInitializationComputable", "MMA", "MMA2ToMM2",
                       "BSM", "BSMMacros", "BSMGraph", "TM2ToBSM", "BSMSource",
                       *bridge_modules, *mm_modules, *fractran_modules,
                       *mma_arithmetic, *mma_compiler, "MMA2Source", "Source")
    counter_allowed = lightweight["DistributedSynthesis.Library.Computability.TwoCounterMachines"] | {
        counter_port, *(counter_port + "." + name for name in counter_modules),
    }
    for module in (counter_port, *(counter_port + "." + name for name in counter_modules)):
        lightweight[module] = counter_allowed
    lightweight[counter_port + ".MMA"] = {counter_port + ".MMA"}
    lightweight[counter_port + ".BSM"] = {counter_port + ".BSM"}
    lightweight[counter_port + ".BSMMacros"] = {
        counter_port + ".BSM", counter_port + ".BSMMacros",
    }
    for name, ancestors in (
            ("BSMGraph", ("BSM", "BSMMacros", "BSMGraph")),
            ("TM2ToBSM", ("BSM", "BSMMacros", "BSMGraph", "TM2ToBSM")),
            ("BSMSource", ("BSM", "BSMMacros", "BSMGraph", "TM2ToBSM", "BSMSource",
                           *bridge_modules))):
        lightweight[counter_port + "." + name] = {
            counter_port + "." + ancestor for ancestor in ancestors
        }
    for name, ancestors in (
            ("MM", ("MM",)),
            ("MM.Frame", ("MM", "MM.Frame")),
            ("MM.StackEncoding", ("MM.StackEncoding",)),
            ("MM.Arithmetic", ("MM", "MM.Frame", "MM.Arithmetic")),
            ("MM.StackMacros", ("MM", "MM.Frame", "MM.Arithmetic", "MM.StackEncoding", "MM.StackMacros")),
            ("BSMToMM.Encoding", ("BSM", "MM", "MM.Frame", "MM.StackEncoding", "BSMToMM.Encoding")),
            ("BSMToMM.Compiler", ("BSM", *mm_modules[:-1]))):
        lightweight[counter_port + "." + name] = {
            counter_port + "." + ancestor for ancestor in ancestors
        }
    lightweight[counter_port + ".MMSource"] = lightweight[counter_port + ".BSMSource"] | {
        counter_port + "." + name for name in mm_modules
    }
    for name, ancestors in (
            ("FRACTRAN", ("FRACTRAN",)),
            ("MMToFRACTRAN.Encoding", ("MM", "MMToFRACTRAN.Encoding")),
            ("MMToFRACTRAN.Blocks", ("MM", "FRACTRAN", "MMToFRACTRAN.Encoding", "MMToFRACTRAN.Blocks")),
            ("MMToFRACTRAN.Compiler", ("MM", "FRACTRAN", "MMToFRACTRAN.Encoding", "MMToFRACTRAN.Blocks",
                                      "MMToFRACTRAN.Compiler")),
            ("MMToFRACTRAN.Computable", ("MM", "MMToFRACTRAN.Encoding", "MMToFRACTRAN.Computable"))):
        lightweight[counter_port + "." + name] = {
            counter_port + "." + ancestor for ancestor in ancestors
        }
    lightweight[counter_port + ".FRACTRANSource"] = lightweight[counter_port + ".MMSource"] | {
        counter_port + "." + name for name in fractran_modules
    }
    for index, name in enumerate(mma_arithmetic):
        lightweight[counter_port + "." + name] = {
            counter_port + ".MMA", *(counter_port + "." + ancestor for ancestor in mma_arithmetic[:index + 1]),
        }
    lightweight[counter_port + ".FRACTRANToMMA.Fraction"] = {
        counter_port + ".MMA", *(counter_port + "." + name for name in mma_arithmetic),
        counter_port + ".FRACTRANToMMA.Fraction",
    }
    lightweight[counter_port + ".FRACTRANToMMA.Compiler"] = lightweight[counter_port + ".FRACTRANToMMA.Fraction"] | {
        counter_port + ".FRACTRAN", counter_port + ".FRACTRANToMMA.Compiler",
    }
    lightweight[counter_port + ".MMA2Source"] = lightweight[counter_port + ".FRACTRANSource"] | {
        counter_port + ".MMA", *(counter_port + "." + name for name in mma_arithmetic),
        *(counter_port + "." + name for name in mma_compiler), counter_port + ".MMA2Source",
    }
    # Source alone joins this unconditional chain to the existing MM2 interface.
    lightweight[counter_port + ".Source"] = counter_allowed
    # The unconditional Mathlib starting point cannot import the open MM2
    # source interface, a Rocq model, or a distributed target theorem.
    bridge_allowed = {counter_port + "." + name for name in bridge_modules}
    for module in bridge_allowed:
        lightweight[module] = bridge_allowed
    postfix_api = lightweight["DistributedSynthesis.Library.Logic.FiniteEncoding"] | {
        "DistributedSynthesis.Library.Logic.PostfixFold",
    }
    positive_code_api = postfix_api | lightweight["DistributedSynthesis.Library.Logic.LTL"] | {
        "DistributedSynthesis.Library.Logic.EncodedPositiveLTL",
    }
    lightweight["DistributedSynthesis.Library.Logic.PostfixFold"] = postfix_api
    lightweight["DistributedSynthesis.Library.Logic.EncodedPositiveLTL"] = positive_code_api
    boolean_code_api = postfix_api | {
        "DistributedSynthesis.Library.Logic.EncodedPositiveBoolean", definitions + "DefPositiveBoolean",
    }
    lightweight["DistributedSynthesis.Library.Logic.EncodedPositiveBoolean"] = boolean_code_api
    path_api = {"DistributedSynthesis.Library.Combinatorics.Paths"}
    view_path_api = {
        *path_api, "DistributedSynthesis.Library.Distributed.ViewPaths",
        "DistributedSynthesis.Library.Distributed.Views", "DistributedSynthesis.Basic",
        *(definitions + name for name in ("DefHistory", "DefViews", "DefObservations")),
    }
    lightweight["DistributedSynthesis.Library.Combinatorics.Paths"] = path_api
    lightweight["DistributedSynthesis.Library.Combinatorics.FiniteOrbits"] = {
        "DistributedSynthesis.Library.Combinatorics.FiniteOrbits",
    }
    lightweight["DistributedSynthesis.Library.Distributed.ViewPaths"] = view_path_api
    lightweight["DistributedSynthesis.Library.Distributed.PaddingProjection"] = {
        *view_path_api, "DistributedSynthesis.Library.Distributed.PaddingProjection",
    }
    lightweight["DistributedSynthesis.Library.Distributed.BlockEmbedding"] = {
        *lightweight["DistributedSynthesis.Library.Distributed.PaddingProjection"],
        "DistributedSynthesis.Library.Distributed.BlockEmbedding",
    }
    block_logic_api = {
        *lightweight["DistributedSynthesis.Library.Logic.LTL"],
        "DistributedSynthesis.Library.Logic.BlockTranslation",
    }
    lightweight["DistributedSynthesis.Library.Logic.BlockTranslation"] = block_logic_api
    lightweight["DistributedSynthesis.Library.Logic.BinaryClock"] = {
        *block_logic_api, "DistributedSynthesis.Library.Logic.BinaryClock",
    }
    lightweight["DistributedSynthesis.Library.Logic.BinaryWords"] = {
        *block_logic_api, "DistributedSynthesis.Library.Logic.BinaryWords",
    }
    lightweight["DistributedSynthesis.Library.Logic.EncodedBlockTranslation"] = {
        *block_logic_api, *lightweight["DistributedSynthesis.Library.Logic.FiniteEncoding"],
        "DistributedSynthesis.Library.Logic.EncodedBlockTranslation",
    }
    lightweight["DistributedSynthesis.Library.Logic.EncodedBinarySyntax"] = {
        *lightweight["DistributedSynthesis.Library.Logic.EncodedBlockTranslation"],
        *lightweight["DistributedSynthesis.Library.Logic.BinaryClock"],
        *lightweight["DistributedSynthesis.Library.Logic.BinaryWords"],
        "DistributedSynthesis.Library.Logic.EncodedBinarySyntax",
    }
    lightweight["DistributedSynthesis.Library.Automata.PitermanTransition"] = {
        *closure(graph, "DistributedSynthesis.Library.Automata.Compilers"),
        "DistributedSynthesis.Library.Automata.PitermanTransition",
    }
    lightweight["DistributedSynthesis.Library.Automata.PitermanAllocation"] = {
        *lightweight["DistributedSynthesis.Library.Automata.PitermanTransition"],
        "DistributedSynthesis.Library.Automata.PitermanAllocation",
    }
    for module, allowed in lightweight.items():
        if module not in graph:
            errors.append(f"missing lightweight entry point {module}")
        unexpected = closure(graph, module) - allowed
        if unexpected:
            errors.append(f"{module}: lightweight boundary exceeded: {sorted(unexpected)}")

    # Execution adapters may depend on the explicitly bounded execution core,
    # but not on the finite-game certificate or physical adapters.
    graph_execution_api = {
        *lightweight["DistributedSynthesis.Library.Distributed.Execution"],
        *lightweight["DistributedSynthesis.Library.Distributed.BlockEmbedding"],
        "DistributedSynthesis.Library.Distributed.GraphExecutions",
    }
    adapters = {
        "DistributedSynthesis.Library.Distributed.GraphExecutions": graph_execution_api,
        "DistributedSynthesis.Library.Distributed.BinaryAgreement": {
            *graph_execution_api, *lightweight["DistributedSynthesis.Library.Logic.BinaryClock"],
            "DistributedSynthesis.Library.Distributed.BinaryAgreement",
        },
    }
    adapters["DistributedSynthesis.Library.Distributed.BinaryStrategy"] = {
        *adapters["DistributedSynthesis.Library.Distributed.BinaryAgreement"],
        *lightweight["DistributedSynthesis.Library.Logic.BinaryWords"],
        "DistributedSynthesis.Library.Distributed.BinaryStrategy",
    }
    adapters["DistributedSynthesis.Library.Distributed.BinaryReduction"] = {
        *adapters["DistributedSynthesis.Library.Distributed.BinaryStrategy"],
        "DistributedSynthesis.Library.Distributed.BinaryReduction",
    }
    adapters["DistributedSynthesis.Library.Distributed.EncodedBinaryReduction"] = {
        *adapters["DistributedSynthesis.Library.Distributed.BinaryReduction"],
        *lightweight["DistributedSynthesis.Library.Logic.EncodedBinarySyntax"],
        "DistributedSynthesis.Library.Distributed.EncodedBinaryReduction",
    }
    for module, allowed in adapters.items():
        if module not in graph:
            errors.append(f"missing execution adapter {module}")
        unexpected = closure(graph, module) - allowed
        if unexpected:
            errors.append(f"{module}: execution-adapter boundary exceeded: {sorted(unexpected)}")

    # Actual automata isolation, not just a prohibition on umbrella imports.
    # New dependencies require review even if hidden behind transitive import paths.
    automata_allowed = {
        *positive_code_api,
        *boolean_code_api,
        "DistributedSynthesis.Library.Computability.FiniteSearch",
        "DistributedSynthesis.Library.Computability.FiniteSubsets",
        "DistributedSynthesis.Library.Combinatorics.FiniteOrbits",
        "DistributedSynthesis.Basic",
        *(definitions + name for name in (
            "DefAlternatingAutomata", "DefLTL", "DefLTLPositive",
            "DefMullerAutomata", "DefNondeterministicOmegaAutomata",
            "DefOmegaAutomata", "DefPathSummary", "DefPositiveBoolean",
            "DefTreeAutomata",
        )),
        *("DistributedSynthesis.Formalizations.Theorem." + name for name in (
            "ThmAPAAlternationRemoval", "ThmAPAMembershipGame", "ThmDPACombinators",
            "ThmFiniteWidthStreettRanking", "ThmLTLAPASemanticBridge",
            "ThmLTLAlternatingAutomaton", "ThmLTLAlternatingStep", "ThmLTLTableau",
            "ThmLTLtoDPA", "ThmMiyanoHayashiAlternationRemoval",
            "ThmMiyanoHayashiEquivalence", "ThmMullerCombinators", "ThmMullerToDPA",
            "ThmParityTreeEmptinessGame", "ThmPitermanDeterminization",
            "ThmWeakAlternationRemoval", "ThmZielonkaCountableParity",
        )),
        *("DistributedSynthesis.Library.Automata." + name for name in (
            "Compilers", "AlternatingSupport", "Piterman", "PitermanTransition",
            "PitermanAllocation", "PitermanComputable", "LTLTranslation",
            "MiyanoHayashiComputable", "WeakComputable", "LTLComputable",
            "FiniteOrbitParity", "EncodedOrbitParity",
            "EncodedLTLStates", "EncodedLTLTransitions",
            "AlternatingRetraction", "EncodedLTLAutomaton", "EncodedSupports", "EncodedSupportTables",
            "EncodedBreakpoints", "EncodedLTLBreakpoints",
            "EncodedPitermanStates", "EncodedPitermanTransition", "EncodedPitermanAllocation",
            "EncodedPitermanCreation", "EncodedPitermanPruning", "EncodedPitermanMinima",
            "EncodedPitermanDeletion", "EncodedPitermanGreen", "EncodedPitermanStep",
            "EncodedParityTables", "EncodedPitermanAutomaton", "EncodedPitermanCompiler",
            "EncodedLTLNumbering", "EncodedLTLParity",
        )),
    }
    for name in ("Compilers", "AlternatingSupport", "Piterman", "PitermanTransition",
                 "PitermanAllocation", "PitermanComputable", "LTLTranslation",
                 "MiyanoHayashiComputable", "WeakComputable", "LTLComputable",
                 "FiniteOrbitParity", "EncodedOrbitParity", "EncodedLTLStates", "EncodedLTLTransitions",
                 "AlternatingRetraction", "EncodedLTLAutomaton", "EncodedSupports", "EncodedSupportTables",
                 "EncodedBreakpoints", "EncodedLTLBreakpoints",
                 "EncodedPitermanStates", "EncodedPitermanTransition", "EncodedPitermanAllocation",
                 "EncodedPitermanCreation", "EncodedPitermanPruning", "EncodedPitermanMinima",
                 "EncodedPitermanDeletion", "EncodedPitermanGreen", "EncodedPitermanStep",
                 "EncodedParityTables", "EncodedPitermanAutomaton", "EncodedPitermanCompiler",
                 "EncodedLTLNumbering", "EncodedLTLParity"):
        module = "DistributedSynthesis.Library.Automata." + name
        if module not in graph:
            errors.append(f"missing extracted automata API {module}")
        unexpected = closure(graph, module) - automata_allowed
        if unexpected:
            errors.append(f"{module}: automata isolation violated: {sorted(unexpected)}")

    # Tree monitors retain a small finite-memory/rationality adapter.
    # Keep this allowance separate from the word-compiler boundary above.
    tree_allowed = automata_allowed | {
        "DistributedSynthesis.Library.Automata.TreeNonemptiness",
        "DistributedSynthesis.Library.Automata.EncodedTreeNonemptiness",
        lemmas + "LemParityTreePositionalization",
        lemmas + "LemRationalrun",
        "DistributedSynthesis.Formalizations.Theorem.ThmBerardfinitememory",
        "DistributedSynthesis.Formalizations.Theorem.ThmDeterministicBlockAutomaton",
        "DistributedSynthesis.Formalizations.Theorem.ThmTransitionrationality",
    }
    for name in ("TreeNonemptiness", "EncodedTreeNonemptiness", "FiniteController"):
        module = "DistributedSynthesis.Library.Automata." + name
        allowed = tree_allowed
        if name == "FiniteController":
            allowed = tree_allowed | {
                "DistributedSynthesis.Library.Automata.FiniteController",
                "DistributedSynthesis.Library.Computability.FiniteOrders",
            }
        unexpected = closure(graph, module) - allowed
        if unexpected:
            errors.append(f"{module}: tree automata isolation violated: {sorted(unexpected)}")

    # MSO tree-language closure reuses generic word determinization. It must
    # not regain the sender-narrowing dependency of the wrapper.
    mso_tree_modules = {
        "DistributedSynthesis.Library.Automata." + name for name in (
            "Tree", "TreeLocal", "TreeProjection", "TreeAcceptanceGame", "TreeComplement",
            "TreeBoolean", "TreeSingleton", "SequenceParity", "UniversalThreads", "WordTreeMonitor", "UniversalThreadsComputable",
            "ParityPairComputable", "TreeComputable", "RunTreeNonemptiness")
    }
    mso_tree_modules |= {
        "DistributedSynthesis.Library.Automata." + name for name in (
            "EncodedThreadBuchi", "EncodedThreadNumbering", "EncodedThreadCompiler", "EncodedUniversalThreads",
            "EncodedProjectedTree", "EncodedWordTree", "EncodedTreeWord", "EncodedTreeShape",
            "EncodedTreeProjection", "EncodedTreeComplement", "EncodedTreeComplementCorrect",
            "EncodedTreeIntersection", "EncodedTreeIntersectionCorrect", "TreeStateEncoding",
            "EncodedRunTree", "EncodedRunTreeCorrect", "EncodedRunTreeEnumeration", "EncodedTreeComap")
    }
    mso_tree_allowed = tree_allowed | mso_tree_modules | {
        *("DistributedSynthesis.Library.Automata." + name for name in (
            "EncodedParityOperations", "EncodedMuller", "EncodedMullerCorrect", "EncodedParityFamilies",
            "EncodedParityFamiliesCorrect", "EncodedParityProduct", "EncodedParityProductCorrect")),
        *("DistributedSynthesis.Library.Computability." + name for name in (
            "FiniteCodeNumbering", "FiniteFunctionCoding", "PrimrecFunProp")),
        "DistributedSynthesis.Library.Computability.FiniteOrders",
        "DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting",
    }
    mso_modules = {"DistributedSynthesis.Library.Logic.MSO"} | {
        "DistributedSynthesis.Library.Logic.MSO." + name for name in (
            "Syntax", "Semantics", "Reachability", "Tree", "Encoding", "Compilation", "NodeQuantification", "TreeAtoms",
            "Recognizability", "Terms", "FirstOrder", "ToTreeAutomaton", "FiniteQuantification",
            "Branches", "AutomatonRuns", "AutomatonParity", "FromTreeAutomaton", "Rabin",
            "ExecutableRecognition", "ExecutableTerms", "ExecutableFirstOrder", "Executable",
            "ExecutableFromAutomaton", "EffectiveRabin",
            "NumericValuations", "NumericAtoms", "NumericAtomsCorrect", "NumericAtomLanguages",
            "NumericRenaming", "NumericOperations", "NumericProgram", "NumericRecognition",
            "NumericTerms", "NumericFirstOrder", "PrimitiveRecursive", "NumericModel")
    }
    for module in mso_tree_modules | mso_modules:
        allowed = mso_tree_allowed | mso_modules if module in mso_modules else mso_tree_allowed
        # Model extraction reuses the existing finite winning-policy search.
        # Keep this dependency out of the MSO compiler and tree-closure modules.
        if module in {"DistributedSynthesis.Library.Logic.MSO",
                      "DistributedSynthesis.Library.Logic.MSO.NumericModel"}:
            allowed = allowed | {"DistributedSynthesis.Library.Automata.FiniteController"}
        unexpected = closure(graph, module) - allowed
        if unexpected:
            errors.append(f"{module}: MSO automata isolation violated: {sorted(unexpected)}")

    # Graph-adversary integration: model and positive proof must stay independent
    # of the counter-machine reduction. Check closures, including transitive import paths.
    graph_api = "DistributedSynthesis.Library.Distributed.GraphAdversaries"
    model = graph_api + ".Model"
    positive = graph_api + ".Decidability"
    for module in (model, positive):
        if module not in graph:
            errors.append(f"missing graph-adversary API {module}")
        unexpected = {m for m in closure(graph, module)
                      if family(m, graph_api + ".Undecidability") or "CounterMachine" in m}
        if module == model:
            unexpected |= {m for m in closure(graph, module)
                           if family(m, "DistributedSynthesis.Library.Distributed.LeaderPhases")
                           or family(m, "DistributedSynthesis.Library.Distributed.LeaderGame")}
        if unexpected:
            errors.append(f"{module}: graph-adversary boundary violated: {sorted(unexpected)}")

    # Generic numeric automata remain independent of the graph-specific geometry
    # and leader construction. Existing automata adapters are retained.
    for name in ("EncodedMuller", "EncodedMullerCorrect", "EncodedParityFamilies",
                 "EncodedParityFamiliesCorrect", "EncodedParityProduct",
                 "EncodedParityProductCorrect", "EncodedParityConjunction",
                 "EncodedParityConjunctionCorrect", "PrefixHoles"):
        module = "DistributedSynthesis.Library.Automata." + name
        if module not in graph:
            errors.append(f"missing generic holes prerequisite {module}")
        unexpected = {m for m in closure(graph, module) if any(family(m, p) for p in (
            graph_api, "DistributedSynthesis.Library.Distributed.LeaderPhases",
            "DistributedSynthesis.Library.Distributed.LeaderGame",
            "DistributedSynthesis.Library.Topology", "DistributedSynthesis.Results",
            "DistributedSynthesis.Tests", "Characterisation"))}
        if unexpected:
            errors.append(f"{module}: generic holes prerequisite coupled to application: {sorted(unexpected)}")

    # Every public library and result module must remain in the root build.
    root_closure = closure(graph, "DistributedSynthesis")
    for module in library + results:
        if module not in root_closure:
            errors.append(f"public module omitted from root build: {module}")
    return errors


def audit_axioms(audit=Path("DistributedSynthesis/Tests/Axioms.lean")):
    audit = ROOT / audit
    targets = re.findall(r"^#print axioms (\S+)$", audit.read_text(), re.MULTILINE)
    result = subprocess.run(
        ["lake", "env", "lean", str(audit)], cwd=ROOT,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if result.returncode:
        return ["Lean axiom audit failed:\n" + result.stdout]
    reports = dict(re.findall(
        r"^'(.+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout, re.MULTILINE
    ))
    for target in re.findall(r"^'(.+)' does not depend on any axioms", result.stdout, re.MULTILINE):
        reports[target] = ""
    errors = []
    if not targets:
        errors.append("axiom audit has no targets")
    for target in targets:
        if target not in reports:
            errors.append(f"missing axiom report for {target}:\n{result.stdout}")
            continue
        axioms = {a.strip() for a in reports[target].split(",") if a.strip()}
        unexpected = axioms - ALLOWED_AXIOMS
        if unexpected:
            errors.append(f"{target}: unapproved axioms {sorted(unexpected)}")
    if not errors:
        print(f"Axiom audit passed for {len(targets)} endpoints.")
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", action="store_true", help="show transitive project import counts")
    parser.add_argument("--axioms", nargs="?", type=Path,
                        const=Path("DistributedSynthesis/Tests/Axioms.lean"), metavar="FILE",
                        help="audit endpoints in FILE (default: DistributedSynthesis/Tests/Axioms.lean)")
    args = parser.parse_args()
    graph = module_graph()
    errors = architecture_checks(graph, args.report)
    if args.axioms and not errors:
        errors.extend(audit_axioms(args.axioms))
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Library boundaries passed ({len(graph)} project modules scanned; supported closures checked).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
