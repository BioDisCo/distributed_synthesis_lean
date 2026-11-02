/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ConsensusExistence
import DistributedSynthesis.Formalizations.ComponentGames.AdversaryEncoding

namespace Characterisation.ComponentGames.Consensus
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2000000
variable (M : DetParityAutomaton.{0,0} Graph) [DecidableEq M.State]

/-- The manuscript's increasing search. Only the finite automaton is
algorithmic data. The nowhere-dense promise proves termination. -/
def computedConsensusBound
    (promise : IsNowhereDense (geometricMap '' {word | M.Accepts word})) : Nat :=
  boundFromRepeated M {word | M.Accepts word} (fun _ => Iff.rfl)
    (repeated_bounded_of_nowhere_dense M _ (fun _ => Iff.rfl) promise)

/-- Full consensus-bound conclusion: one computed positive bound works
under every live residual, with fresh proposals and arbitrary later inputs.
It works for every nonempty proposal alphabet, hence in particular for
every finite proposal alphabet with at least two values. -/
theorem computedConsensusBound_correct {V : Type} [Nonempty V]
    (promise : IsNowhereDense (geometricMap '' {word | M.Accepts word})) :
    0 < computedConsensusBound M promise ∧
      ∀ h, LivePrefix {word | M.Accepts word} h →
        ∃ σ : StrategyPair V V (Option V) (Option V),
          SolvesBy σ (Residual {word | M.Accepts word} h) (computedConsensusBound M promise) := by
  have positive : 0 < computedConsensusBound M promise := searchBound_positive M _
  refine ⟨positive,fun h live => ?_⟩
  let q := (prefixRecognizer M).eval h
  have reachable : reachableState M q = true := (reachableState_exact M q).mpr ⟨h,rfl⟩
  have stateLive : liveState M q = true := (liveState_correct M q).mpr
    ((prefixRecognizer_correct M {word | M.Accepts word} (fun _ => Iff.rfl) h).mp live)
  have all : checkAll M (computedConsensusBound M promise) = true := by
    unfold computedConsensusBound boundFromRepeated searchBound
    exact Nat.find_spec (p := fun n => checkAll M (n+1) = true) _
  rw [checkAll,decide_eq_true_eq] at all
  obtain ⟨σ,solves⟩ := solves_general_of_checkState (V:=V) M q _ positive (all q reachable stateLive)
  refine ⟨σ,?_⟩
  rw [residual_state_language M {word | M.Accepts word} (fun _ => Iff.rfl) h]
  exact solves

/-- Same theorem with the paper's named adversary A and an explicit
recognition hypothesis, rather than identifying A definitionally with the
automaton language. -/
theorem computable_consensus_bound {V : Type} [Nonempty V]
    (A : Set (Nat → Graph)) (recognizes : ∀ word, word ∈ A ↔ M.Accepts word)
    (nowhereDense : IsNowhereDense (geometricMap '' A)) :
    ∃ promise : IsNowhereDense (geometricMap '' {word | M.Accepts word}),
      0 < computedConsensusBound M promise ∧
      ∀ h, LivePrefix A h → ∃ σ : StrategyPair V V (Option V) (Option V),
        SolvesBy σ (Residual A h) (computedConsensusBound M promise) := by
  have language : A = {word | M.Accepts word} := Set.ext recognizes
  subst A
  exact ⟨nowhereDense,computedConsensusBound_correct M nowhereDense⟩

/-- A single executable function on the repository's numeric automaton
encoding; there are no semantic sets or chosen consensus bounds as inputs.
The promise argument is a proof and is erased by compilation. -/
def encodedConsensusBound (d : EncodedParityTables.Data)
    (promise : IsNowhereDense (geometricMap '' {word | (graphInput d).Accepts word})) : Nat :=
  computedConsensusBound (graphInput d) promise

theorem encodedConsensusBound_correct {V : Type} [Nonempty V] (d : EncodedParityTables.Data)
    (promise : IsNowhereDense (geometricMap '' {word | (graphInput d).Accepts word})) :
    0 < encodedConsensusBound d promise ∧
      ∀ h, LivePrefix {word | (graphInput d).Accepts word} h →
        ∃ σ : StrategyPair V V (Option V) (Option V),
          SolvesBy σ (Residual {word | (graphInput d).Accepts word} h) (encodedConsensusBound d promise) :=
  computedConsensusBound_correct (graphInput d) promise

end Characterisation.ComponentGames.Consensus
