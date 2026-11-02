/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedPublicLeaderGame
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedAllowedExtensionality
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedHeaderSolverCorrect

/-! Exact public move legality: the elected process must be the original
leader at every source, and its local test uses the advertised whole outcomes. -/
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
local instance publicLegalObjectiveEq : DecidableEq (M).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount o)))
variable (first : NumberedLeaderOutcome (GQ:=GQ) (d:=D) (K:=K) (B:=B) (C:=EncodedLeaderObjective.priorityBound o) (EncodedLeaderObjective.automaton o))
variable (code : HandoverCode B (EncodedLeaderObjective.priorityBound o))

def leaderTable := List.ofFn (fun i => EncodedLeaderAlphabet.procCode (graphRootLeader (graphs.symm i)))
def dataEncode : Data :=
  (EncodedHeaderCompiler.graphDataEncode (B:=B) recognizer graphs,leaderTable graphs,o,
    EncodedLeaderAlphabet.outcomeEncode annNumber first,(code.1.val,code.2.val))
local notation "input" => dataEncode o recognizer graphs first code

theorem context_encode : context input = (B,S*EncodedRoundObjectives.stateCount o*(rankBound+1),rankBound) := rfl

theorem leader_lookup (q : LeaderAnnotation (GQ:=GQ) (d:=D) (K:=K) (C:=EncodedLeaderObjective.priorityBound o) (EncodedLeaderObjective.automaton o)) :
    (leaders input).getD (graphOf input (annNumber q).val) false =
      EncodedLeaderAlphabet.procCode (graphRootLeader q.1.1) := by
  have split : graphOf input (annNumber q).val = (graphs q.1.1).val :=
    EncodedLeaderAnnotations.graphState_encode (C:=rankBound)
    (V:=EncodedPhysicalObjective.outputs o) recognizer M graphs (Equiv.refl _)
    (EncodedPhysicalObjective.environmentNumber o) (EncodedPhysicalObjective.compile o) q
  change (leaderTable graphs).getD (graphOf input (annNumber q).val) false = _
  rw [split]
  exact EncodedClosingBanks.table_eval graphs (fun q => EncodedLeaderAlphabet.procCode (graphRootLeader q)) false q.1.1

variable (h : NumberedLeaderHeader (GQ:=GQ) (d:=D) (K:=K) (B:=B) (C:=EncodedLeaderObjective.priorityBound o) (EncodedLeaderObjective.automaton o))
variable (move : NumberedLeaderMove (GQ:=GQ) (d:=D) (K:=K) (B:=B) (C:=EncodedLeaderObjective.priorityBound o) (EncodedLeaderObjective.automaton o))

theorem agrees_encode : agrees input (EncodedLeaderAlphabet.headerEncode annNumber h) (EncodedLeaderAlphabet.moveEncode annNumber move) =
    decide (∀ i, graphRootLeader (h.2.2 i).1.1 = move.1) := by
  apply Bool.eq_iff_iff.mpr
  rw [agrees,decide_eq_true_eq,decide_eq_true_eq]
  change (∀ q ∈ List.ofFn (fun i => (annNumber (h.2.2 i)).val),
    (leaders input).getD (graphOf input q) false = EncodedLeaderAlphabet.procCode move.1) ↔ _
  constructor
  · intro checked i
    have eq := checked _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    rw [leader_lookup] at eq
    exact EncodedLeaderAlphabet.procCode_injective eq
  · intro agree q member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    rw [leader_lookup,agree]

theorem selected_encode (b : EncodedLeaderAlphabet.Outcome) :
    b ∈ selected input (EncodedLeaderAlphabet.moveEncode annNumber move) ↔
      b ∈ EncodedGraphMemory.allowedEncode annNumber move.2 := by
  rw [selected,List.mem_filter]
  constructor
  · rintro ⟨member,offered⟩
    have raw : b ∈ EncodedLeaderAlphabet.rawOutcomes (B,S*EncodedRoundObjectives.stateCount o*(rankBound+1),rankBound) := by
      change b ∈ EncodedLeaderAlphabet.outcomes _ at member
      rw [EncodedLeaderAlphabet.outcomes] at member
      exact (FiniteCodeNumbering.mem_unique _ _).mp member
    obtain ⟨outcome,rfl⟩ := EncodedLeaderAlphabet.outcomeEncode_sound annNumber b raw
    apply (EncodedGraphMemory.mem_allowedEncode annNumber move.2 outcome).mpr
    exact (EncodedLeaderAlphabet.offered_encode annNumber move outcome).mp offered
  · intro member
    obtain ⟨outcome,ho,rfl⟩ := List.mem_map.mp member
    refine ⟨?_,?_⟩
    · change _ ∈ EncodedLeaderAlphabet.outcomes _
      rw [EncodedLeaderAlphabet.outcomes]
      exact (FiniteCodeNumbering.mem_unique _ _).mpr (EncodedLeaderAlphabet.outcomeEncode_mem annNumber outcome)
    · exact (EncodedLeaderAlphabet.offered_encode annNumber move outcome).mpr (Finset.mem_toList.mp ho)

theorem legal_encode : legal input (EncodedLeaderAlphabet.headerEncode annNumber h) (EncodedLeaderAlphabet.moveEncode annNumber move) =
    numberedLeaderLegal recognizer M (EncodedLeaderObjective.rank o) h move := by
  unfold legal
  rw [agrees_encode]
  rw [EncodedHeaderCompiler.test_membership_congr _ _ _ _ _
    (selected_encode o recognizer graphs first code move)]
  cases move with
  | mk proc allowed =>
    cases proc with
    | one =>
      change (decide (∀ i, graphRootLeader (h.2.2 i).1.1 = Proc.one) && EncodedHeaderCompiler.test (EncodedHeaderCompiler.questionEncode o recognizer graphs h allowed) true) = _
      rw [EncodedHeaderCompiler.test_right_eq_legal]
      rfl
    | two =>
      change (decide (∀ i, graphRootLeader (h.2.2 i).1.1 = Proc.two) && EncodedHeaderCompiler.test (EncodedHeaderCompiler.questionEncode o recognizer graphs h allowed) false) = _
      rw [EncodedHeaderCompiler.test_left_eq_legal]
      rfl

end Characterisation.EncodedPublicLeaderGame
