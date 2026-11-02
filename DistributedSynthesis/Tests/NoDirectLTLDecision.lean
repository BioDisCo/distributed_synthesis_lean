/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedNoDirect

namespace DistributedSynthesis.Tests.NoDirectLTLDecision

variable {AP In₁ In₂ Out₁ Out₂ : Type}
variable [DecidableEq AP]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable (interp : AP → RoundRecord In₁ In₂ Graph Out₁ Out₂ → Prop)
variable (dec : ∀ ap letter, Decidable (interp ap letter))

def solve (φ : LTL AP) : Bool := DistributedSynthesis.NoDirectLTLDecision.solve interp dec φ

example (φ : LTL AP) : solve interp dec φ = true ↔
    ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        NoDirectReversalSequence env → LTL.Satisfies interp (execution σ env) φ :=
  DistributedSynthesis.NoDirectLTLDecision.solve_correct interp dec φ

def data : EncodedNoDirect.Instance where
  inputOneSizeMinusOne := 0
  inputTwoSizeMinusOne := 0
  outputOneSizeMinusOne := 1
  outputTwoSizeMinusOne := 0
  truthTable := [(7, 0, 0, 2, 1, 0), (7, 99, 0, 2, 0, 0)]
  formula := EncodedFiniteLTL.atom 7

def letter (graph : Graph) (out : Fin 2) : EncodedNoDirect.Letter data :=
  ⟨0, 0, graph, out, 0⟩

def atomTest (atom : Nat) (graph : Graph) (out : Fin 2) : Bool :=
  @decide _ (EncodedNoDirect.interpDecidable data atom (letter graph out))

#guard atomTest 7 .both 1
#guard !(atomTest 7 .both 0)
#guard !(atomTest 7 .left 1)
#guard !(atomTest 8 .both 1)
#guard EncodedNoDirect.graphCode .left = 0
#guard EncodedNoDirect.graphCode .right = 1
#guard EncodedFiniteLTL.decode data.formula = .atom 7
#guard EncodedFiniteLTL.decode ([] : EncodedFiniteLTL.Code Nat) = .falsum
#guard EncodedFiniteLTL.decode ([.inr 5] : EncodedFiniteLTL.Code Nat) = .falsum
-- Underflow resets to false; later negation can turn that into a true formula.
#guard EncodedFiniteLTL.decode ([.inr 5, .inr 2] : EncodedFiniteLTL.Code Nat) = .neg .falsum

/-- This client takes only a finite record; no function-valued solver or decider input. -/
def encodedSolve (input : EncodedNoDirect.Instance) : Bool := EncodedNoDirect.solve input

example : Primrec EncodedNoDirect.stateTables := EncodedNoDirect.stateTables_primrec
#guard (EncodedNoDirect.stateTables data).2 = [0]
example : Primrec₂ EncodedNoDirect.transitionTable := EncodedNoDirect.transitionTable_primrec
#guard (EncodedNoDirect.transitionRow data (0, 0, 2, 1, 0)).map
  EncodedPositiveBoolean.decode = [.verum]
#guard (EncodedNoDirect.transitionRow data (0, 0, 2, 0, 0)).map
  EncodedPositiveBoolean.decode = [.falsum]
#guard (EncodedNoDirect.transitionRow data (0, 0, 0, 1, 0)).map
  EncodedPositiveBoolean.decode = [.falsum]
#guard EncodedNoDirect.supportTables data (0, 0, 2, 1, 0) [0] = [[(0, [])]]
#guard EncodedNoDirect.supportTables data (0, 0, 2, 0, 0) [0] = []
example : Primrec (fun x : EncodedNoDirect.Instance × EncodedNoDirect.LetterCode × List Nat =>
    EncodedNoDirect.supportTables x.1 x.2.1 x.2.2) := EncodedNoDirect.supportTables_primrec
example : Primrec EncodedNoDirect.alternatingTables := EncodedNoDirect.alternatingTables_primrec
example : Primrec EncodedNoDirect.buchiTables := EncodedNoDirect.buchiTables_primrec
#guard (([0], []), ([], [])) ∈ EncodedNoDirect.buchiEdges data (0, 0, 2, 1, 0)
#guard (([0], []), ([], [])) ∉ EncodedNoDirect.buchiEdges data (0, 0, 2, 0, 0)
#guard (EncodedNoDirect.buchiTables data).1.length = 4
#guard (EncodedNoDirect.buchiTables data).2.2.2.length = 6
#guard (EncodedNoDirect.letters data).length = 6
#guard (99, 0, 2, 0, 0) ∉ EncodedNoDirect.letters data
#guard (EncodedNoDirect.alternatingTables data).2.2.length = 6
#guard ((EncodedNoDirect.alternatingTables data).2.2.map
  (List.map EncodedPositiveBoolean.decode)) =
    [[.falsum], [.falsum], [.falsum], [.falsum], [.falsum], [.verum]]

example (input : EncodedNoDirect.Instance) :
    Encodable.decode (Encodable.encode input) = some input := Encodable.encodek input

example (input : EncodedNoDirect.Instance) :
    encodedSolve input = true ↔ EncodedNoDirect.Realizable input :=
  EncodedNoDirect.solve_correct input

end DistributedSynthesis.Tests.NoDirectLTLDecision
