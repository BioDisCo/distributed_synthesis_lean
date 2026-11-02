/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderAlphabetCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeaderGame

/-! Use the numeric alphabet for the existing concrete numbered leader game.
Graph numbering is fixed with the adversary; only objective state count,
priority bound, and input-dependent family width enter the numeric context. -/
namespace Characterisation
open DistributedSynthesis

section
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C graphCount objectiveCount : Nat}
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable (graphNumber : GraphRootState GQ d K ≃ Fin graphCount)
variable (objectiveNumber : objective.State ≃ Fin objectiveCount)

/-- Flatten graph state, objective state, and the minimum since the boundary
using exactly the library's product and singleton-domain function encodings. -/
def leaderAnnotationNumber :
    LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective ≃
      Fin ((graphCount*objectiveCount)*(C+1)) :=
  FiniteFunctionCodes.prod (FiniteFunctionCodes.prod graphNumber objectiveNumber)
    (Equiv.funUnique Unit (Fin (C+1)))

def numberedAlphabetContext : EncodedLeaderAlphabet.Context :=
  (B,(graphCount*objectiveCount)*(C+1),C)

noncomputable def numberedOutcomeNumber :
    NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective ≃
      Fin (EncodedLeaderAlphabet.outcomes (numberedAlphabetContext (B:=B) (C:=C)
        (graphCount:=graphCount) (objectiveCount:=objectiveCount))).length :=
  EncodedLeaderAlphabet.outcomeNumber (leaderAnnotationNumber objective graphNumber objectiveNumber)

noncomputable def numberedMoveNumber :
    NumberedLeaderMove (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective ≃
      Fin (EncodedLeaderAlphabet.moves (numberedAlphabetContext (B:=B) (C:=C)
        (graphCount:=graphCount) (objectiveCount:=objectiveCount))).length :=
  EncodedLeaderAlphabet.moveNumber (leaderAnnotationNumber objective graphNumber objectiveNumber)

attribute [local instance] Classical.propDecidable

/-- Numeric offeredness is exactly membership in the original whole-outcome
set. It does not choose separate successor families for different slots. -/
theorem numbered_offered_code
    (move : NumberedLeaderMove (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (outcome : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) :
    EncodedLeaderAlphabet.offered
      (EncodedLeaderAlphabet.moveEncode (leaderAnnotationNumber objective graphNumber objectiveNumber) move)
      (numberedOutcomeNumber objective graphNumber objectiveNumber outcome).val =
        numberedLeaderOffers objective move outcome := by
  apply Bool.eq_iff_iff.mpr
  exact (EncodedLeaderAlphabet.offered_encode (leaderAnnotationNumber objective graphNumber objectiveNumber) move outcome).trans
    (by simp only [numberedLeaderOffers,decide_eq_true_eq])

/-- The encoded edge retains exactly the existing hidden-history compatibility
relation, including the target slot's own completed-phase minimum. -/
theorem numbered_handover_code
    (outcome : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (old next : HandoverCode B C) :
    EncodedLeaderAlphabet.edge
      (EncodedLeaderAlphabet.outcomeEncode (leaderAnnotationNumber objective graphNumber objectiveNumber) outcome)
      (old.1.val,old.2.val) (next.1.val,next.2.val) = true ↔
        HandoverEdge old outcome () next :=
  EncodedLeaderAlphabet.edge_encode (leaderAnnotationNumber objective graphNumber objectiveNumber) outcome old next

end

/-- All numeric alphabet parameters are obtained by primitive-recursive
arithmetic from the graph, objective, and boundary bounds. -/
theorem numberedAlphabetContext_primrec : Primrec (fun x : Nat × Nat × Nat × Nat =>
    numberedAlphabetContext (B:=x.1) (graphCount:=x.2.1) (objectiveCount:=x.2.2.1) (C:=x.2.2.2)) :=
  Primrec.fst.pair ((Primrec.nat_mul.comp
    (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

theorem numberedOutcomes_primrec : Primrec (fun x : Nat × Nat × Nat × Nat =>
    EncodedLeaderAlphabet.outcomes
      (numberedAlphabetContext (B:=x.1) (graphCount:=x.2.1) (objectiveCount:=x.2.2.1) (C:=x.2.2.2))) :=
  EncodedLeaderAlphabet.outcomes_primrec.comp numberedAlphabetContext_primrec

theorem numberedMoves_primrec : Primrec (fun x : Nat × Nat × Nat × Nat =>
    EncodedLeaderAlphabet.moves
      (numberedAlphabetContext (B:=x.1) (graphCount:=x.2.1) (objectiveCount:=x.2.2.1) (C:=x.2.2.2))) :=
  EncodedLeaderAlphabet.moves_primrec.comp numberedAlphabetContext_primrec

end Characterisation
