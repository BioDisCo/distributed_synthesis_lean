/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedHolesSolver
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedPublicLeaderInitialCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedGameEquivalence
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGuardedFrontend

/-! Exact correspondence between the uniform numeric solver and finite-input
LTL realizability. The original graph recognizer is retained, and language
equivalence suffices for the computed guarded physical objective. -/
noncomputable section
namespace Characterisation.EncodedHolesSolver
open DistributedSynthesis
set_option maxHeartbeats 1200000

section GraphData
variable {GQ : Type} {S delay K : Nat} [Fintype GQ] [DecidableEq GQ]
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (graphs : GraphRootState GQ delay K ≃ Fin S)

theorem withWidth_encode (oldWidth newWidth : Nat) :
    withWidth (EncodedHeaderCompiler.graphDataEncode (B:=oldWidth) recognizer graphs) newWidth =
      EncodedHeaderCompiler.graphDataEncode (B:=newWidth) recognizer graphs := rfl

end GraphData

variable (A : Set (Nat → Graph)) (adversary : DetParityAutomaton Graph)
variable (recognizes : ∀ word, word ∈ A ↔ adversary.Accepts word)
variable {S delay K : Nat}
local instance holesSolverGraphEq : DecidableEq adversary.State := Classical.typeDecidableEq _
local instance holesSolverAcceptDec : DecidablePred (· ∈ (prefixRecognizer adversary).accept) := fun _ => Classical.propDecidable _
variable (graphs : GraphRootState adversary.State delay K ≃ Fin S)
variable (initialGraph : GraphRootState adversary.State delay K)
variable (initialRep : GraphRootRep (LivePrefix A) (prefixRecognizer adversary) [] initialGraph)
variable (tables : EncodedNoDirect.Instance → EncodedParityTables.Data)
local instance holesSolverObjectiveEq (i : EncodedNoDirect.Instance) :
    DecidableEq (EncodedLeaderObjective.automaton (i,tables i)).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount (i,tables i))))
variable (language : ∀ i (word : OmegaWord (WithInputs.TupleLetter i)),
  (EncodedLeaderObjective.automaton (i,tables i)).Accepts word ↔
    (WithInputs.guardedInstanceObjective adversary i).Accepts word)

include recognizes language in
/-- Leaving the live-prefix language makes the original infinite-adversary
implication true, including when the adversary is not closed. -/
theorem objective_escape (i : WithInputs.Instance) (σ : WithInputs.Strategies i)
    (env : EnvironmentSequence (Fin (i.inputOneSizeMinusOne+1)) (Fin (i.inputTwoSizeMinusOne+1)))
    (bad : ∃ n, ¬ LivePrefix A (branchNode (fun t => (env t).graph) n)) :
    (EncodedLeaderObjective.automaton (i,tables i)).Accepts
      (fun n => recordContinuationLetter (execution σ env n)) := by
  apply (language i _).mpr
  apply (WithInputs.guardedInstanceObjective_execution_iff adversary i σ env).mpr
  intro admitted
  obtain ⟨n,missing⟩ := bad
  apply False.elim
  apply missing
  refine ⟨(fun t => (env t).graph),(recognizes _).mpr admitted,?_⟩
  simp [graphPrefix,branchNode_eq_ofFn]

include recognizes language in
/-- The computed physical objective has the original realizability semantics. -/
theorem objective_realizability (i : WithInputs.Instance) :
    (∃ σ : WithInputs.Strategies i, ∀ env,
      (EncodedLeaderObjective.automaton (i,tables i)).Accepts
        (fun n => recordContinuationLetter (execution σ env n))) ↔ WithInputs.Realizable A i := by
  rw [WithInputs.realizable_iff_guarded_objective A adversary recognizes i]
  apply exists_congr
  intro σ
  apply forall_congr'
  intro env
  exact language i _

variable (recent : ∀ h, LivePrefix A h → ∃ p, RecentOther (LivePrefix A) delay h p)
variable (bounded : ∀ h, LivePrefix A h → Finite (HistoryComponent (LivePrefix A) h) ∧
  Nat.card (HistoryComponent (LivePrefix A) h) ≤ K)
variable (live : LivePrefix A [])

include recognizes initialRep language recent bounded live in
/-- No semantic initial family, rank bound, or input-dependent width is supplied
as an oracle: the numeric solver generates all three. -/
theorem solve_correct (i : WithInputs.Instance) :
    solve (EncodedHeaderCompiler.graphDataEncode (B:=0) (prefixRecognizer adversary) graphs)
      (EncodedPublicLeaderGame.leaderTable graphs) K (graphs initialGraph).val tables i = true ↔
      WithInputs.Realizable A i := by
  let objective := EncodedLeaderObjective.automaton (i,tables i)
  let initial := numberedInitialChoice (C:=EncodedLeaderObjective.priorityBound (i,tables i))
    objective (width_pos K delay i) initialGraph
  have represented := numberedInitialChoice_rep (C:=EncodedLeaderObjective.priorityBound (i,tables i)) (prefixRecognizer adversary) objective (LivePrefix A)
    (width_pos K delay i) initialGraph initialRep
  have small : ∀ h : EnvHistory (Fin (i.inputOneSizeMinusOne+1)) (Fin (i.inputTwoSizeMinusOne+1)),
      LivePrefix A (History.graphSequence h) → leaderBoundary (LivePrefix A) delay h = true →
      Nat.card (InputHistoryComponent (LivePrefix A) h) ≤ width K delay i := by
    intro h alive boundary
    simpa only [width,Nat.card_fin] using
      (EncodedBoundaryWidth.boundary_bound (LivePrefix A) (livePrefix_closed A) K bounded delay recent h alive boundary).2
  have numeric := EncodedPublicLeaderGame.solveInitial_encode (i,tables i) (prefixRecognizer adversary)
    graphs (width_pos K delay i) initialGraph
  unfold solve
  rw [withWidth_encode]
  apply (Iff.of_eq (congrArg (fun answer : Bool => answer = true) numeric)).trans
  exact (numberedGameTest_realizability_iff (prefixRecognizer adversary) objective
    (EncodedLeaderObjective.rank (i,tables i)) (EncodedLeaderObjective.rank_exact (i,tables i))
    (LivePrefix A) (livePrefix_closed A) (prefixRecognizer_correct adversary A recognizes)
    recent bounded small live (objective_escape A adversary recognizes tables language i) initial represented).trans
      (objective_realizability A adversary recognizes tables language i)

end Characterisation.EncodedHolesSolver
