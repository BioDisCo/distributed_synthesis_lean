/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryCoding
import DistributedSynthesis.Library.Distributed.GraphAdversaries.ExecutionSafety
import DistributedSynthesis.Library.Logic.FiniteEncoding
import DistributedSynthesis.Formalizations.Definition.DefOmegaAutomata
import Mathlib.Computability.RE

/-! Exact singleton-input target, proved in `HolesIff.lean`.
Finite output alphabets, finite atomic truth tables, and finite LTL syntax are
part of the input. The observation and strategy semantics are the repository's.
The topology is the relative topology on [0,1]. -/

namespace Characterisation

open DistributedSynthesis

/-- Positive output cardinalities (minus one), a finite atomic truth table,
and the repository's total postfix encoding of LTL. -/
abbrev SynthesisInstance :=
  Nat × Nat × List (Nat × (Fin 3 × Nat × Nat)) × EncodedFiniteLTL.Code Nat

abbrev OutputOne (d : SynthesisInstance) := Fin (d.1 + 1)
abbrev OutputTwo (d : SynthesisInstance) := Fin (d.2.1 + 1)
abbrev Letter (d : SynthesisInstance) :=
  RoundRecord Unit Unit Graph (OutputOne d) (OutputTwo d)

def graphCode : Graph → Fin 3
  | .right => 0
  | .both => 1
  | .left => 2

def atomInterpretation (d : SynthesisInstance) (a : Nat) (r : Letter d) : Prop :=
  (a, (graphCode r.graph, r.outputOne.val, r.outputTwo.val)) ∈ d.2.2.1

def Realizable (A : Set (Nat → Graph)) (d : SynthesisInstance) : Prop :=
  ∃ σ : StrategyPair Unit Unit (OutputOne d) (OutputTwo d),
    ∀ x ∈ A, LTL.Satisfies (atomInterpretation d)
      (execution σ (GraphExecutions.ofGraphs x)) (EncodedFiniteLTL.decode d.2.2.2)

def OmegaRegular (A : Set (Nat → Graph)) : Prop :=
  ∃ M : DetParityAutomaton.{0, 0} Graph, ∀ x, x ∈ A ↔ M.Accepts x

/-- The characterization proved by `holesCharacterization` in `HolesIff.lean`.
`ComputablePred`, rather than classical `Decidable`, expresses
the required algorithmic assertion. -/
def HolesCharacterization : Prop :=
  ∀ A : Set (Nat → Graph), OmegaRegular A →
    (ComputablePred (Realizable A) ↔ GeometricHoles A)

end Characterisation
