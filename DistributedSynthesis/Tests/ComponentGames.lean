/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Results.ComponentGames
import DistributedSynthesis.Formalizations.ComponentGames.ConsensusTopology
import DistributedSynthesis.Tests.ComponentGames.EdgeCases

open DistributedSynthesis Characterisation

-- Merely importing the result must preserve the standard componentwise order.
example : ¬ ((1, 3) : Nat × Nat) ≤ (2, 2) := by decide

example : ¬ (fun b : Bool => if b then (3 : Nat) else 1) ≤ (fun _ => 2) := by
  intro bound
  have := bound true
  norm_num at this

namespace DistributedSynthesis.Tests.ComponentGames

example (d : EncodedGuardedObjective.Data)
    (alphabet : (EncodedParityTables.rows d.1).length = 3)
    (promise : IsNowhereDense (geometricMap '' {w | (Characterisation.ComponentGames.graphInput d.1).Accepts w})) :
    Characterisation.ComponentGames.solve d promise = true ↔
      WithInputs.Realizable {w | (Characterisation.ComponentGames.graphInput d.1).Accepts w} d.2 :=
  Characterisation.ComponentGames.solve_correct d alphabet promise

example (d : EncodedGuardedObjective.Data)
    (alphabet : (EncodedParityTables.rows d.1).length = 3)
    (promise : IsNowhereDense (geometricMap '' {w | (Characterisation.ComponentGames.graphInput d.1).Accepts w})) :
    (∃ σ, Characterisation.ComponentGames.synthesize d promise = some σ) ↔
      WithInputs.Realizable {w | (Characterisation.ComponentGames.graphInput d.1).Accepts w} d.2 :=
  Characterisation.ComponentGames.synthesize_complete d alphabet promise

section Extraction
open scoped DistributedSynthesis.FiniteOrders

def controlled : DeterministicBlockMonitor Unit Bool where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := Bool
  stateFinite := inferInstance
  initial := false
  step := fun _ move _ => move
  priority := fun state => if state then 2 else 1

def extractedWins : Bool :=
  match @FiniteController.extract Unit Bool inferInstance inferInstance inferInstance controlled
      (inferInstanceAs (LinearOrder Bool)) with
  | none => false
  | some policy => policy false && policy true

#guard extractedWins

end Extraction
end DistributedSynthesis.Tests.ComponentGames
