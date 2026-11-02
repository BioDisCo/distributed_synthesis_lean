/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.FiniteTransport

/-! Executable reconstruction of a node by transporting its finite
reduction and output rule through the current position isomorphism.
-/
namespace Characterisation.ComponentTrees.FiniteTransport
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D capacity bound : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable [DecidableEq B.State]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (P : Position I₁ I₂ B.State D) (valid : PositionValid B M P)
variable (m : FiniteAlphabet.Move (capacity:=capacity) B)
variable (e : Representation.Iso (FinitePositions.historyData P) m.source.2)
variable (checks : FinitePositions.ReductionChecks m.source.2 bound m.replacement)
variable (coherent : ClosingPolicyCoherent m.source.2.shape m.rule)

include checks in
theorem pullChecks : FinitePositions.ReductionChecks (FinitePositions.historyData P) bound
    (Representation.replacement e.toEquiv.symm m.replacement) :=
  (FinitePositions.reductionChecks_transport m.source.2 (FinitePositions.historyData P)
    e.symm bound m.replacement).mpr checks

def pullReduction : Reduction P.past P.state where
  map := ExecutableReverse.finiteViewMap P.past P.past
    (Representation.replacement e.toEquiv.symm m.replacement) (by
      intro p h k same
      have views := (pullChecks B P m e checks).1 p h k
      simp only [FinitePositions.historyData,ExecutableHistories.shape_eq] at views
      exact (extractInputShape_exact P.past p _ _).mp
        (views ((extractInputShape_exact P.past p h k).mpr same)))
  idempotent := (pullChecks B P m e checks).2.1
  states := (pullChecks B P m e checks).2.2.1

def pullRule : ClosingPolicy P.Root I₁ I₂ O₁ O₂ D := Representation.policy e.toEquiv.symm m.rule

include coherent in
theorem pullRule_coherent : ClosingPolicyCoherent P.shape (pullRule B P m e) := by
  have pulled := (Representation.coherent_iff e.toEquiv.symm m.source.2.shape
    (FinitePositions.historyData P).shape e.symm.shape_same m.rule).mpr coherent
  simpa only [FinitePositions.historyData,ExecutableHistories.shape_eq] using pulled

def pullNode : CompressedNode B M bound :=
  FullExtensions.node B M P (pullReduction B P m e checks) (pullRule B P m e) valid
    (pullChecks B P m e checks).2.2.2 (pullRule_coherent B P m e coherent)

theorem push_pull :
    pushMove B P (pullReduction B P m e checks) (pullRule B P m e) m.source e = m := by
  change ⟨m.source,Representation.policy e.toEquiv (Representation.policy e.toEquiv.symm m.rule),
    Representation.replacement e.toEquiv (Representation.replacement e.toEquiv.symm m.replacement)⟩ = m
  have rule : Representation.policy e.toEquiv (Representation.policy e.toEquiv.symm m.rule) = m.rule := by
    funext n s
    change m.rule n (mapClosingLayer e.toEquiv _ (mapClosingLayer e.toEquiv.symm _ s)) = _
    rw [Representation.mapLayer_inverse']
  have replacement : Representation.replacement e.toEquiv
      (Representation.replacement e.toEquiv.symm m.replacement) = m.replacement := by
    funext h
    simp only [Representation.replacement, Equiv.symm_symm, e.toEquiv.apply_symm_apply]
  rw [rule,replacement]

end Characterisation.ComponentTrees.FiniteTransport
