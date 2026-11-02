/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedOrdinaryCheckerAssembly
import DistributedSynthesis.Library.Distributed.EncodedChainCheckerAssembly
import DistributedSynthesis.Library.Distributed.EncodedReversalForgivingCorrect

/-! # Assembled journals using the verified numeric thread machines

This construction supplies all three checker interfaces. Its semantic theorem
also transfers the reversal-forgiving construction to its numeric state space.
It does not yet number the outer journal states or produce numeric tree tables.
-/
namespace DistributedSynthesis.EncodedJournalAssembly
open EncodedRoundObjectives DetParityAutomaton
variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d
local instance : DecidableEq (A).State := inferInstanceAs (DecidableEq (Fin (stateCount d)))
local instance : Inhabited (Fin (inputOne d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (inputTwo d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (outputOne d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (outputTwo d)) := ⟨⟨0,Nat.succ_pos _⟩⟩

def compile :=
  letI := JournalCheckers.labelFintype A
  JournalCompilation.compile A (EncodedOrdinaryCheckerAssembly.left d)
    (EncodedOrdinaryCheckerAssembly.right d) (EncodedChainCheckerAssembly.checker d)

theorem compile_toRunAutomaton : (compile d).toRunAutomaton =
    globalJournalAutomaton A (EncodedOrdinaryCheckerAssembly.left d)
      (EncodedOrdinaryCheckerAssembly.right d) (EncodedChainCheckerAssembly.checker d) := rfl

/-- A change of the companion's state representation preserves the journal
reduction when it preserves its word language. -/
theorem realizable_iff_nonempty : NoDirectJournal.Realizable A ↔
    ∃ tree, (compile (EncodedReversalForgiving.compile d)).toRunAutomaton.acceptsTree tree := by
  classical
  let B := EncodedRoundObjectives.automaton (EncodedReversalForgiving.compile d)
  let CL := EncodedOrdinaryCheckerAssembly.left (EncodedReversalForgiving.compile d)
  let CR := EncodedOrdinaryCheckerAssembly.right (EncodedReversalForgiving.compile d)
  let CC := EncodedChainCheckerAssembly.checker (EncodedReversalForgiving.compile d)
  rw [compile_toRunAutomaton]
  constructor
  · intro h
    obtain ⟨σ,hσ⟩ := (reversalForgiving_realizable_iff A).mpr h
    have hB : ∀ env, B.Accepts (execution σ env) := fun env =>
      (EncodedReversalForgiving.accepts_iff d _).mpr (hσ env)
    obtain ⟨τ,hτ⟩ := exists_positional_uniformization_winner σ hB
    exact ⟨tauTree σ τ,tauTree_acceptsTree σ τ CL CR CC hτ⟩
  · intro h
    letI := B.globalJournalLabelFintype
    obtain ⟨t,ht⟩ := (globalJournalAutomaton B CL CR CC).exists_transitionRational_accepted h
    letI : DecidableEq t.Control := Classical.decEq _
    letI : Inhabited t.Control := ⟨t.initial⟩
    obtain ⟨plans,hplans⟩ := journal_readback_accepts_of_accepts t CL CR CC ht
    refine ⟨journalStrategy plans,?_⟩
    intro env hnd
    have hno : ¬ HasDirectReversalWord (execution (journalStrategy plans) env) := by
      rw [hasDirectReversalWord_execution_iff]
      exact fun h => h hnd
    exact (reversalForgiving_accepts_iff_of_noReversal A _ hno).mp
      ((EncodedReversalForgiving.accepts_iff d _).mp (hplans env hnd))
end DistributedSynthesis.EncodedJournalAssembly
