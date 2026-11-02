/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Syntax
import DistributedSynthesis.Library.Logic.MSO.Semantics
import DistributedSynthesis.Library.Logic.MSO.Reachability
import DistributedSynthesis.Library.Logic.MSO.Tree
import DistributedSynthesis.Library.Logic.MSO.Encoding
import DistributedSynthesis.Library.Logic.MSO.Compilation
import DistributedSynthesis.Library.Logic.MSO.NodeQuantification
import DistributedSynthesis.Library.Logic.MSO.TreeAtoms

import DistributedSynthesis.Library.Logic.MSO.Recognizability
import DistributedSynthesis.Library.Logic.MSO.Terms
import DistributedSynthesis.Library.Logic.MSO.FirstOrder
import DistributedSynthesis.Library.Logic.MSO.ToTreeAutomaton
import DistributedSynthesis.Library.Logic.MSO.FiniteQuantification
import DistributedSynthesis.Library.Logic.MSO.Branches
import DistributedSynthesis.Library.Logic.MSO.AutomatonRuns
import DistributedSynthesis.Library.Logic.MSO.AutomatonParity
import DistributedSynthesis.Library.Logic.MSO.FromTreeAutomaton
import DistributedSynthesis.Library.Logic.MSO.Rabin
import DistributedSynthesis.Library.Logic.MSO.EffectiveRabin
import DistributedSynthesis.Library.Logic.MSO.PrimitiveRecursive
import DistributedSynthesis.Library.Logic.MSO.NumericModel
/-! # Monadic second-order logic

Full powerset semantics extending Mathlib first-order syntax, interpretation on
the existing full labelled trees, reachability, and Rabin's semantic equivalence
with parity tree automata. Both translations have unconditional correctness
theorems. `EffectiveRabin` additionally provides executable translations and
satisfiability/validity procedures on explicit finite data. `NumericModel`
extracts a finite generating table for a model, with soundness and completeness.
Import `MSO.Semantics` alone for the generic logic without automata dependencies.
-/
