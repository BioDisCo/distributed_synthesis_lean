/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.FiniteOrders
import DistributedSynthesis.Library.Automata.FiniteController
import DistributedSynthesis.Formalizations.ComponentGames.FiniteEquivalence

namespace Characterisation.ComponentGames.Representation.FiniteArena
open scoped Characterisation.ComponentGames.Representation.FiniteArena
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks FiniteEnumeration
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D B L : Nat}
variable [Fintype I₁] [Fintype I₂] [LinearOrder I₁] [LinearOrder I₂]
variable [Fintype O₁] [Fintype O₂] [LinearOrder O₁] [LinearOrder O₂]
variable [Fintype G] [Fintype Q] [LinearOrder G] [LinearOrder Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (χ : Q → Nat) (priorityBound : ∀ q, χ q ≤ L)
variable (W : Nat) (q₀ : Q) (positive : 0 < B)

scoped instance progressStateOrder : LinearOrder (MonitorCompiler.automaton (B:=B) (K:=L) 0).State := by
  rw [MonitorCompiler.automaton_eq_numeric]
  change LinearOrder (Fin _)
  infer_instance

scoped instance productStateOrder : LinearOrder (product (D:=D) M step χ priorityBound W q₀ positive).State := by
  letI := progressStateOrder (B:=B) (L:=L)
  letI : ∀ m : Move I₁ I₂ O₁ O₂ G Q D B, LinearOrder (Finset m.End) := fun _ => inferInstance
  change LinearOrder (Observation I₁ I₂ O₁ O₂ G Q D B × (MonitorCompiler.automaton (B:=B) (K:=L) 0).State × Bool × Bool)
  infer_instance

/-- An actual returned finite controller, rather than an existential
winning-policy witness or a Boolean answer. -/
def extractController : Option ((product (D:=D) M step χ priorityBound W q₀ positive).State → Move I₁ I₂ O₁ O₂ G Q D B) :=
  FiniteController.extract (product M step χ priorityBound W q₀ positive)

theorem extractController_correct : (∃ policy, extractController (D:=D) M step χ priorityBound W q₀ positive = some policy) ↔
    ∃ tree, Winning (D:=D) M step χ priorityBound W q₀ positive tree := by
  rw [extractController,FiniteController.extract_complete]
  exact exists_congr (product_winning_iff M step χ priorityBound W q₀ positive)

theorem extractedController_wins
    (policy : (product (D:=D) M step χ priorityBound W q₀ positive).State → Move I₁ I₂ O₁ O₂ G Q D B)
    (found : extractController M step χ priorityBound W q₀ positive = some policy) :
    Winning M step χ priorityBound W q₀ positive
      (FiniteController.tree (product M step χ priorityBound W q₀ positive) policy) :=
  (product_winning_iff M step χ priorityBound W q₀ positive _).mp
    (FiniteController.extracted_tree_wins _ policy found)

end Characterisation.ComponentGames.Representation.FiniteArena
