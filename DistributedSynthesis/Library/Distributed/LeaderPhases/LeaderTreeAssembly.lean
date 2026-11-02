/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.SupportedLeaderProgress

/-! Assemble one global public tree from current-family successor witnesses.
The input is one-step data, not a pre-existing winning tree or a parity
assumption on independently selected successors. -/
namespace Characterisation
open DistributedSynthesis

section Assembly
variable {α Q Move Source : Type} {B C : Nat}
variable (score : List α → Nat)
variable (offers : Move → LeaderHandover Q B C → Bool)
variable (family : Source → LeaderHandover Q B C)
variable (past : Source → Fin (B+1) → List α) (cut : Source → Nat)
variable (move : Source → Move)

/-- One whole successor family extends the current family. All its slots
use the same successor source, and its advertised minima refer to that
source's literal histories at the new physical cut. -/
def LeaderSuccessor (source : Source) (outcome : LeaderHandover Q B C) (target : Source) : Prop :=
  family target = outcome ∧ cut source < cut target ∧
  (∀ i : Fin outcome.1.1.val,
    (past source (outcome.2.1 i)).IsPrefix (past target (handoverSlot outcome i))) ∧
  ∀ i : Fin outcome.1.1.val,
    (outcome.2.2 i).val = historyPhaseMinimum score (cut source)
      (cut target) (past target (handoverSlot outcome i))

variable (successor : ∀ source outcome, offers (move source) outcome = true →
  ∃ target, LeaderSuccessor score family past cut source outcome target)

/-- Choose one witness per whole offer, retaining the current source as the
fallback after an unsupported observation. No chosen successor may depend
on the hidden slot being followed. -/
noncomputable def leaderWitnessStep (source : Source) (outcome : LeaderHandover Q B C) : Source :=
  if offered : offers (move source) outcome = true then
    Classical.choose (successor source outcome offered)
  else source

theorem leaderWitnessStep_correct (source : Source) (outcome : LeaderHandover Q B C)
    (offered : offers (move source) outcome = true) :
    LeaderSuccessor score family past cut source outcome
      (leaderWitnessStep score offers family past cut move successor source outcome) := by
  rw [leaderWitnessStep, dif_pos offered]
  exact Classical.choose_spec (successor source outcome offered)

variable (initial : Source)

noncomputable def leaderWitnessSource (node : List (LeaderHandover Q B C)) : Source :=
  node.foldl (leaderWitnessStep score offers family past cut move successor) initial

noncomputable def leaderWitnessTree : LabeledTree (LeaderHandover Q B C) Move :=
  fun node => move (leaderWitnessSource score offers family past cut move successor initial node)

theorem leaderWitnessSource_append (node : List (LeaderHandover Q B C))
    (outcome : LeaderHandover Q B C) :
    leaderWitnessSource score offers family past cut move successor initial (node ++ [outcome]) =
      leaderWitnessStep score offers family past cut move successor
        (leaderWitnessSource score offers family past cut move successor initial node) outcome := by
  simp only [leaderWitnessSource, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- On supported public histories the chosen family's incoming header is
exactly the public observation. Unsupported histories impose no such claim. -/
theorem leaderWitnessSource_family (node : List (LeaderHandover Q B C))
    (supported : publicSupport offers (leaderWitnessTree score offers family past cut move successor initial) node = true) :
    family (leaderWitnessSource score offers family past cut move successor initial node) =
      observableAt (family initial) node := by
  cases node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node outcome =>
    rw [publicSupport_append, Bool.and_eq_true] at supported
    rw [leaderWitnessSource_append]
    have correct := leaderWitnessStep_correct score offers family past cut move successor
      (leaderWitnessSource score offers family past cut move successor initial node) outcome supported.2
    simpa only [observableAt, List.getLast?_concat, Option.getD_some] using correct.1

variable (depth : ∀ source i, (past source i).length = cut source)
variable (zero : cut initial = 0)

/-- The recursive choice constructs the literal histories and all equations
required by the existing global parity-lifting theorem. It does not assume
the existence of a compatible global family tree. -/
noncomputable def leaderWitnessRealization :
    LeaderProgressRealization score offers
      (leaderWitnessTree score offers family past cut move successor initial) where
  past node := past (leaderWitnessSource score offers family past cut move successor initial node)
  cut node := cut (leaderWitnessSource score offers family past cut move successor initial node)
  depth node i := depth _ i
  initial := zero
  advances node outcome offered := by
    rw [leaderWitnessSource_append]
    exact (leaderWitnessStep_correct score offers family past cut move successor _ outcome offered).2.1
  parents node outcome offered i := by
    rw [leaderWitnessSource_append]
    exact (leaderWitnessStep_correct score offers family past cut move successor _ outcome offered).2.2.1 i
  minima node outcome offered i := by
    rw [leaderWitnessSource_append]
    exact (leaderWitnessStep_correct score offers family past cut move successor _ outcome offered).2.2.2 i

variable (Legal : SwitchInterface Q B → Move → Prop)
variable (localLegal : ∀ source, Legal (family source).1 (move source))

include localLegal in
theorem leaderWitnessTree_legal :
    SupportedMovesValid offers (family initial) (fun f m => Legal f.1 m)
      (leaderWitnessTree score offers family past cut move successor initial) := by
  intro node supported
  rw [← leaderWitnessSource_family score offers family past cut move successor initial node supported]
  exact localLegal _

variable [Fintype Q] [Fintype Move] [Inhabited (LeaderHandover Q B C)] [DecidableRel Legal]

include successor depth zero localLegal in
/-- Close the forward global assembly from one-step current-family witnesses.
The finite controller is extracted once from the resulting complete public
tree. Physical winning is used only after lifting a coherent hidden thread
to one infinite word with its original increasing physical cuts. -/
theorem finite_leader_tree_from_successors
    (winning : ∀ physical : Nat → α,
      NatSeqMinEvenParity (fun t => score (branchNode physical (t+1))))
    (initialCode : HandoverCode B C) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (supportedLeaderProgressMonitor offers initialCode (family initial) Legal).toRunAutomaton,
      (supportedLeaderProgressMonitor offers initialCode (family initial) Legal).WinningTree
        table.toTransitionRationalTree.labeledTree := by
  let tree := leaderWitnessTree score offers family past cut move successor initial
  have legal := leaderWitnessTree_legal score offers family past cut move successor initial Legal localLegal
  have progress := leaderProgress_of_realization score offers tree
    (leaderWitnessRealization score offers family past cut move successor initial depth zero)
    winning initialCode
  exact finite_supported_leader_progress offers initialCode (family initial) Legal tree legal progress

end Assembly
end Characterisation
