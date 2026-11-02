/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedPublicLeaderTables
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderProgressCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedAllowedExtensionality
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedHeaderSolverCorrect

/-! Reindexing preserves every transition and the global parity language. -/
set_option maxHeartbeats 1000000
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
local instance publicProgressObjectiveEq : DecidableEq (M).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount o)))
variable (first : NumberedLeaderOutcome (GQ:=GQ) (d:=D) (K:=K) (B:=B) (C:=EncodedLeaderObjective.priorityBound o) (EncodedLeaderObjective.automaton o))
variable (code : HandoverCode B (EncodedLeaderObjective.priorityBound o))

local notation "input" => dataEncode o recognizer graphs first code
local notation "ctx" => (B,S*EncodedRoundObjectives.stateCount o*(rankBound+1),rankBound)
local notation "Outcome" => NumberedLeaderOutcome (GQ:=GQ) (d:=D) (K:=K) (B:=B) (C:=rankBound) M
local notation "Move" => NumberedLeaderMove (GQ:=GQ) (d:=D) (K:=K) (B:=B) (C:=rankBound) M

def publicProgress : DetParityAutomaton (Move × Outcome) :=
  (EncodedSupportedGame.wordAutomaton (compile input)).comap
    (fun a => (moveNumber o recognizer graphs first code a.1,observationNumber o recognizer graphs first code a.2))

theorem progress_next (q : Nat) (a : Move × Outcome) :
    EncodedParityTables.next (progress input) q
      ((moveNumber o recognizer graphs first code a.1).val * EncodedSupportedGame.observations (compile input) +
        (observationNumber o recognizer graphs first code a.2).val) =
      EncodedParityTables.next (EncodedLeaderProgress.compile (ctx,(code.1.val,code.2.val))) q
        (EncodedLeaderProgress.rowIndex annNumber a).val := by
  rw [observationNumber_val,observations_eq]
  have row := lookup2 (moves input) (outcomes input)
    (fun m b => (EncodedParityTables.rows (progressBase input)).getD
      ((EncodedLeaderProgress.letters (context input)).idxOf (m,b)) [])
    (EncodedLeaderAlphabet.moveNumber annNumber a.1) (EncodedLeaderAlphabet.outcomeNumber annNumber a.2) []
  have evaluated := row.trans (congrArg₂
    (fun m b => (EncodedParityTables.rows (progressBase input)).getD
      ((EncodedLeaderProgress.letters (context input)).idxOf (m,b)) [])
    (move_get o recognizer graphs first code a.1) (outcome_get o recognizer graphs first code a.2))
  unfold EncodedParityTables.next
  change ((progressRows input).getD _ []).getD q 0 % _ = _
  have result := congrArg (fun row : List Nat => row.getD q 0 % EncodedParityTables.size (progress input)) evaluated
  convert result using 1
  simp only [progressRows]
  congr 6
  funext m
  congr 1
  funext b
  apply congrArg (fun eqInst : BEq EncodedLeaderProgress.Letter =>
    (EncodedParityTables.rows (progressBase input)).getD
      (@List.idxOf EncodedLeaderProgress.Letter eqInst (m,b) (EncodedLeaderProgress.letters (context input))) [])
  exact lawful_beq_subsingleton _ _

theorem publicProgress_eq : publicProgress o recognizer graphs first code =
    EncodedLeaderProgress.automaton annNumber code := by
  rw [EncodedLeaderProgress.automaton,EncodedThreadCompiler.automaton_eq]
  unfold publicProgress EncodedSupportedGame.wordAutomaton DetParityAutomaton.comap EncodedParityTables.automaton
  congr 1
  funext q a
  apply Fin.ext
  exact progress_next o recognizer graphs first code q.val a

theorem publicProgress_accepts (word : OmegaWord (Move × Outcome)) :
    (publicProgress o recognizer graphs first code).Accepts word ↔
      (EncodedLeaderProgress.source (Q:=LeaderAnnotation (GQ:=GQ) (d:=D) (K:=K) (C:=rankBound) M) code).universalRunDPA.Accepts word := by
  rw [publicProgress_eq]
  exact EncodedLeaderProgress.accepts_iff annNumber code word

end Characterisation.EncodedPublicLeaderGame
