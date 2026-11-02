/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedPublicLeaderParity
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderProgressCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedAllowedExtensionality
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedHeaderSolverCorrect

/-! The primitive-recursive public-game solver agrees with the existing
numbered leader game, including common-leader legality and global parity. -/
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
local instance publicCorrectObjectiveEq : DecidableEq (M).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount o)))
variable (first : NumberedLeaderOutcome (GQ:=GQ) (d:=D) (K:=K) (B:=B) (C:=EncodedLeaderObjective.priorityBound o) (EncodedLeaderObjective.automaton o))
variable (code : HandoverCode B (EncodedLeaderObjective.priorityBound o))

local notation "input" => dataEncode o recognizer graphs first code
local notation "ctx" => (B,S*EncodedRoundObjectives.stateCount o*(rankBound+1),rankBound)
local notation "Outcome" => NumberedLeaderOutcome (GQ:=GQ) (d:=D) (K:=K) (B:=B) (C:=rankBound) M
local notation "Move" => NumberedLeaderMove (GQ:=GQ) (d:=D) (K:=K) (B:=B) (C:=rankBound) M


local notation "obsNumber" => observationNumber o recognizer graphs first code
local notation "movNumber" => moveNumber o recognizer graphs first code
local notation "numeric" => EncodedSupportedGame.semantic (compile input)

def typedPublicGame := supportedPublicTreeMonitor (publicProgress o recognizer graphs first code)
  (numberedLeaderOffers M) first
  (fun b m => numberedLeaderLegal recognizer M (EncodedLeaderObjective.rank o) b.1 m = true)

local notation "typed" => typedPublicGame o recognizer graphs first code

def publicStateDecode (q : (numeric).State) : (typed).State := ((obsNumber).symm q.1,q.2)

theorem publicStateDecode_initial : publicStateDecode o recognizer graphs first code (numeric).initial = (typed).initial := by
  apply Prod.ext
  · exact (congrArg (obsNumber).symm (initial_number o recognizer graphs first code)).trans ((obsNumber).symm_apply_apply first)
  · rfl

theorem publicStateDecode_step (q : (numeric).State)
    (m : Fin (EncodedSupportedGame.moves (compile input)))
    (b : Fin (EncodedSupportedGame.observations (compile input))) :
    publicStateDecode o recognizer graphs first code ((numeric).step q m b) =
      (typed).step (publicStateDecode o recognizer graphs first code q) ((movNumber).symm m) ((obsNumber).symm b) := by
  have offers := offered_encode o recognizer graphs first code ((movNumber).symm m) ((obsNumber).symm b)
  have legal := allowed_encode o recognizer graphs first code ((obsNumber).symm q.1) ((movNumber).symm m)
  simp only [Equiv.apply_symm_apply] at offers legal
  simp only [publicStateDecode,EncodedSupportedGame.semantic,supportedPublicTreeMonitor,
    typedPublicGame,publicProgress,DetParityAutomaton.comap,Equiv.apply_symm_apply,offers,legal]
  rfl

theorem public_nonempty_iff :
    (∃ tree, (numeric).toRunAutomaton.acceptsTree tree) ↔ ∃ tree, (typed).toRunAutomaton.acceptsTree tree := by
  apply TreeMonitorRetraction.nonempty_iff numeric typed
    (publicStateDecode o recognizer graphs first code) (obsNumber).symm (movNumber).symm
  · exact publicStateDecode_initial o recognizer graphs first code
  · exact publicStateDecode_step o recognizer graphs first code
  · intro q; rfl
  · exact (obsNumber).symm.surjective
  · exact (movNumber).symm.surjective

attribute [local irreducible] FiniteThreadSystem.universalRunDPA

theorem typedPublicGame_winning_iff (tree : LabeledTree Outcome Move) :
    (typed).WinningTree tree ↔
      (numberedLeaderGame recognizer M (EncodedLeaderObjective.rank o) first code).WinningTree tree := by
  letI : Inhabited Outcome := ⟨first⟩
  unfold typedPublicGame numberedLeaderGame supportedLeaderProgressMonitor
  conv_lhs => rw [supportedPublicTreeMonitor_winning_iff]
  conv_rhs => rw [supportedPublicTreeMonitor_winning_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro branch
  apply imp_congr_right
  intro _
  have offersEqual : (EncodedLeaderProgress.offers : Move → Outcome → Bool) = numberedLeaderOffers M := by
    funext m b
    apply Bool.eq_iff_iff.mpr
    simp only [EncodedLeaderProgress.offers,numberedLeaderOffers,decide_eq_true_eq]
  simpa only [EncodedLeaderProgress.source,offersEqual] using
    (publicProgress_accepts o recognizer graphs first code (observableThreadWord tree branch))

/-- The generated numeric decision is exactly the established finite public-game test. -/
theorem solve_encode : solve input =
    numberedLeaderGameTest recognizer M (EncodedLeaderObjective.rank o) first code := by
  apply Bool.eq_iff_iff.mpr
  unfold solve EncodedSupportedGame.solve
  rw [EncodedTreeNonemptiness.solve_correct,EncodedSupportedGame.nonempty_iff,public_nonempty_iff,
    numberedLeaderGameTest,TreeNonemptiness.nonempty_correct]
  apply exists_congr
  intro tree
  exact ((typed).acceptsTree_iff_winningTree tree).trans
    ((typedPublicGame_winning_iff o recognizer graphs first code tree).trans
      ((numberedLeaderGame recognizer M (EncodedLeaderObjective.rank o) first code).acceptsTree_iff_winningTree tree).symm)

end Characterisation.EncodedPublicLeaderGame
