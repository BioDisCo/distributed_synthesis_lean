/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphCollectorCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderAnnotationsCorrect

/-! Instantiate the generated collector with the numbered game's actual
graph/objective/minimum labels. The replay transition table is generated
from the objective data and the fixed chosen graph transitions. -/
namespace Characterisation
open DistributedSynthesis

variable {H G GQ I₁ I₂ O₁ O₂ : Type} {R E V N₁ N₂ P₁ P₂ S N B C d K : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype GQ]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq GQ]
variable (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
variable (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (output : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂)) [DecidableEq objective.State]
variable (graphNumber : GraphRootState GQ d K ≃ Fin S) (objectiveNumber : objective.State ≃ Fin N)
variable (objectiveData : EncodedParityTables.Data) (rank : objective.State → Fin (C+1))
variable (transition : ∀ q r o, EncodedParityTables.next objectiveData (objectiveNumber q).val
  ((env r).val*V+(output o).val) = (objectiveNumber (objective.step q (r,o))).val)
variable (priority : ∀ q, EncodedParityTables.priority objectiveData (objectiveNumber q).val = (rank q).val)
variable (shape : InputShape H) (slot : H → Fin (B+1))
variable (state : GraphLeaderMemory H GQ
  (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) I₁ I₂ O₁ O₂ d K)

noncomputable def numberedCollectorData : EncodedGraphCollector.Data :=
  EncodedGraphCollector.dataEncode root env one two output outOne outTwo
    (leaderAnnotationNumber objective graphNumber objectiveNumber)
    (jointLeaderShape shape state.2.2) state.2.1 state.1.2.2
    (EncodedLeaderAnnotations.compile
      (EncodedLeaderAnnotations.dataEncode (C:=C) (N:=N) (V:=V) recognizer graphNumber env objectiveData) (E*V))
    recognizer graphNumber state.1.1 state.2.2 slot (fun q => q.2 ()) state.1.2.1

include transition priority in
/-- The numeric collector in the numbered leader game computes the exact
existing joint graph collector, with its actual phase-minimum update. -/
theorem numberedCollectorData_correct
    (letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁))
    (outcome : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) :
    EncodedLeaderAlphabet.outcomeEncode (leaderAnnotationNumber objective graphNumber objectiveNumber) outcome ∈
      EncodedGraphCollector.collect
        (numberedCollectorData root env one two output outOne outTwo recognizer objective graphNumber objectiveNumber
          objectiveData shape slot state) ↔
      outcome ∈ jointGraphLeaderCollect recognizer (leaderAnnotationStep recognizer objective rank) shape
        slot (fun q => q.2 ()) state letter := by
  exact EncodedGraphCollector.collect_encode root env one two output outOne outTwo
    (leaderAnnotationNumber objective graphNumber objectiveNumber) _ _ _ _ recognizer graphNumber _ _ slot _ _
    (leaderAnnotationStep recognizer objective rank)
    (EncodedLeaderAnnotations.compile_encode recognizer objective graphNumber objectiveNumber env output objectiveData rank transition priority)
    outcome

end Characterisation
