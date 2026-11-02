/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedPublicLeaderLegality
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderProgressCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedAllowedExtensionality
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedHeaderSolverCorrect

/-! Exact numbering and table lookup for the assembled public game. -/
noncomputable section
namespace Characterisation.EncodedPublicLeaderGame
open DistributedSynthesis
variable {GQ : Type} {S B D K : Nat} [Fintype GQ] [DecidableEq GQ]
variable (o : EncodedRoundObjectives.Data)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (graphs : GraphRootState GQ D K ≃ Fin S)
local notation "M" => EncodedLeaderObjective.automaton o
local notation "rankBound" => EncodedLeaderObjective.priorityBound o
local notation "annNumber" => leaderAnnotationNumber (C:=rankBound) M graphs (Equiv.refl _)
local instance publicTablesObjectiveEq : DecidableEq (M).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount o)))
variable (first : NumberedLeaderOutcome (GQ:=GQ) (d:=D) (K:=K) (B:=B) (C:=EncodedLeaderObjective.priorityBound o) (EncodedLeaderObjective.automaton o))
variable (code : HandoverCode B (EncodedLeaderObjective.priorityBound o))

local notation "input" => dataEncode o recognizer graphs first code
local notation "ctx" => (B,S*EncodedRoundObjectives.stateCount o*(rankBound+1),rankBound)
local notation "Outcome" => NumberedLeaderOutcome (GQ:=GQ) (d:=D) (K:=K) (B:=B) (C:=rankBound) M
local notation "Move" => NumberedLeaderMove (GQ:=GQ) (d:=D) (K:=K) (B:=B) (C:=rankBound) M

theorem observations_eq : EncodedSupportedGame.observations (compile input) = (outcomes input).length :=
  Nat.sub_add_cancel (EncodedLeaderAlphabet.outcomes_pos B _ rankBound)

def observationNumber : Outcome ≃ Fin (EncodedSupportedGame.observations (compile input)) :=
  (EncodedLeaderAlphabet.outcomeNumber annNumber).trans (finCongr (observations_eq o recognizer graphs first code).symm)
def moveNumber : Move ≃ Fin (EncodedSupportedGame.moves (compile input)) :=
  EncodedLeaderAlphabet.moveNumber annNumber

theorem observationNumber_val (b : Outcome) :
    (observationNumber o recognizer graphs first code b).val = (EncodedLeaderAlphabet.outcomeNumber annNumber b).val := rfl

theorem outcome_get (b : Outcome) :
    (outcomes input)[(EncodedLeaderAlphabet.outcomeNumber annNumber b).val] = EncodedLeaderAlphabet.outcomeEncode annNumber b := by
  apply Option.some.inj
  apply (List.getElem?_eq_getElem (EncodedLeaderAlphabet.outcomeNumber annNumber b).isLt).symm.trans
  simpa only [EncodedLeaderAlphabet.outcomes,EncodedLeaderAlphabet.outcomeNumber_val,EncodedLeaderAlphabet.outcomeName] using
    (FiniteCodeNumbering.get_name (EncodedLeaderAlphabet.rawOutcomes ctx) (EncodedLeaderAlphabet.outcomeEncode annNumber)
      (EncodedLeaderAlphabet.outcomeEncode_mem annNumber) b)

theorem move_get (m : Move) :
    (moves input)[(EncodedLeaderAlphabet.moveNumber annNumber m).val] = EncodedLeaderAlphabet.moveEncode annNumber m := by
  apply Option.some.inj
  apply (List.getElem?_eq_getElem (EncodedLeaderAlphabet.moveNumber annNumber m).isLt).symm.trans
  simpa only [EncodedLeaderAlphabet.moves,EncodedLeaderAlphabet.moveNumber_val,EncodedLeaderAlphabet.moveName] using
    (FiniteCodeNumbering.get_name (EncodedLeaderAlphabet.rawMoves ctx) (EncodedLeaderAlphabet.moveEncode annNumber)
      (EncodedLeaderAlphabet.moveEncode_mem annNumber) m)

/-- Two-dimensional specialization of the shared flattened-table lookup. -/
theorem lookup2 {X Y Z : Type} (xs : List X) (ys : List Y) (f : X → Y → Z)
    (i : Fin xs.length) (j : Fin ys.length) (fallback : Z) :
    (xs.flatMap (fun x => ys.map (f x))).getD (i.val*ys.length+j.val) fallback = f xs[i.val] ys[j.val] := by
  rw [List.getD_eq_getElem?_getD,
    FiniteTableLookup.flat_lookup xs (fun x => ys.map (f x)) ys.length (fun _ _ => List.length_map _)
      i.val j.val i.isLt j.isLt,List.getElem?_map,List.getElem?_eq_getElem j.isLt]
  rfl

theorem offered_encode (m : Move) (b : Outcome) :
    EncodedSupportedGame.offered (compile input) (moveNumber o recognizer graphs first code m).val
      (observationNumber o recognizer graphs first code b).val = numberedLeaderOffers M m b := by
  unfold EncodedSupportedGame.offered
  rw [observationNumber_val,observations_eq]
  have row := lookup2 (moves input) (outcomes input)
    (fun m b => EncodedLeaderAlphabet.offered m (EncodedLeaderAlphabet.outcomeName (context input) b))
    (EncodedLeaderAlphabet.moveNumber annNumber m) (EncodedLeaderAlphabet.outcomeNumber annNumber b) false
  have evaluated := row.trans (congrArg₂
    (fun m b => EncodedLeaderAlphabet.offered m (EncodedLeaderAlphabet.outcomeName (context input) b))
    (move_get o recognizer graphs first code m) (outcome_get o recognizer graphs first code b))
  change (offerTable input).getD _ false = _
  apply evaluated.trans
  apply Bool.eq_iff_iff.mpr
  simpa only [numberedLeaderOffers,decide_eq_true_eq] using
    (EncodedLeaderAlphabet.offered_encode annNumber m b)

theorem allowed_encode (b : Outcome) (m : Move) :
    EncodedSupportedGame.allowed (compile input) (observationNumber o recognizer graphs first code b).val
      (moveNumber o recognizer graphs first code m).val =
      numberedLeaderLegal recognizer M (EncodedLeaderObjective.rank o) b.1 m := by
  have row := lookup2 (outcomes input) (moves input) (fun b m => legal input b.1 m)
    (EncodedLeaderAlphabet.outcomeNumber annNumber b) (EncodedLeaderAlphabet.moveNumber annNumber m) false
  have evaluated := row.trans (congrArg₂ (fun b m => legal input b.1 m)
    (outcome_get o recognizer graphs first code b) (move_get o recognizer graphs first code m))
  change (legalTable input).getD _ false = _
  exact evaluated.trans (legal_encode o recognizer graphs first code b.1 m)

theorem initial_number : (EncodedSupportedGame.semantic (compile input)).initial.1 =
    observationNumber o recognizer graphs first code first := by
  apply Fin.ext
  change EncodedLeaderAlphabet.outcomeName (context input) (EncodedLeaderAlphabet.outcomeEncode annNumber first) %
    EncodedSupportedGame.observations (compile input) = _
  rw [observationNumber_val,observations_eq]
  exact Nat.mod_eq_of_lt (EncodedLeaderAlphabet.outcomeNumber annNumber first).isLt

end Characterisation.EncodedPublicLeaderGame
