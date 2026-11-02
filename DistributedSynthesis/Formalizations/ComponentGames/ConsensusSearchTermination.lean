/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ConsensusFiniteTest

namespace Characterisation.ComponentGames.Consensus
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable (M : DetParityAutomaton Graph) [DecidableEq M.State]

def stateLanguage (q : M.State) : Set (Nat → Graph) := {word | M.AcceptsFrom q word}

theorem state_prefix_extension (q : M.State) (gs : List Graph)
    (live : liveState M ((prefixRecognizer M).evalFrom q gs) = true) :
    ∃ word ∈ stateLanguage M q, graphPrefix word gs.length = gs := by
  obtain ⟨tail,accepted⟩ := (liveState_correct M _).mp live
  let word := prependGraphs gs tail
  refine ⟨word,?_,prependGraphs_prefix gs tail⟩
  apply (M.acceptsFrom_runFrom_drop_iff q word gs.length).mp
  have state : M.runFrom q word gs.length = (prefixRecognizer M).evalFrom q gs := by
    rw [← prefixRecognizer_eval,prependGraphs_prefix]
  rw [state,prependGraphs_drop]
  exact accepted

theorem residual_state_language (A : Set (Nat → Graph))
    (recognizes : ∀ word, word ∈ A ↔ M.Accepts word) (u : List Graph) :
    Residual A u = stateLanguage M ((prefixRecognizer M).eval u) := by
  ext word
  change prependGraphs u word ∈ A ↔ M.AcceptsFrom ((prefixRecognizer M).eval u) word
  rw [recognizes]
  have eq := M.acceptsFrom_runFrom_drop_iff M.initial (prependGraphs u word) u.length
  rw [← prefixRecognizer_eval,prependGraphs_prefix,prependGraphs_drop] at eq
  exact eq.symm

theorem SolvesBy.mono {V : Type} {σ : StrategyPair V V (Option V) (Option V)}
    {A : Set (Nat → Graph)} {R S : Nat} (solves : SolvesBy σ A R) (le : R ≤ S) : SolvesBy σ A S := by
  refine ⟨solves.irrevocable,solves.valid,?_⟩
  intro env admitted p
  obtain ⟨n,before,v,eq⟩ := solves.bound env admitted p
  exact ⟨n,lt_of_lt_of_le before le,v,eq⟩

/-- Every actual bounded consensus algorithm occurs in the finite test
when later inputs are fixed to the initial proposals, as in the paper. -/
theorem checkState_of_solves (q : M.State) (R : Nat) (positive : 0 < R)
    (σ : StrategyPair Bool Bool (Option Bool) (Option Bool))
    (solves : SolvesBy σ (stateLanguage M q) R) : checkState M q R = true := by
  apply (checkState_exact M q R).mpr
  let total : StrategyPair Bool Bool Bool Bool := ⟨fun v => (σ.one v).getD false,fun v => (σ.two v).getD false⟩
  refine ⟨total,fun c live => ?_⟩
  obtain ⟨word,admitted,pref⟩ := state_prefix_extension M q c.2.val live
  rw [c.2.property] at pref
  obtain ⟨o,valid,outputs⟩ := solves.decidesAt (proposalEnvironment c.1 word) admitted
  have correct (p : Proc) : strategyOutput σ p (currentView p (caseHistory c)) = some (o p) := by
    have out := outputs p
    rw [outputAt_view,show R-1+1 = R by omega,proposalEnvironment_prefix,pref] at out
    exact out
  have one := correct .one
  change σ.one (currentView .one (caseHistory c)) = some (o .one) at one
  have two := correct .two
  change σ.two (currentView .two (caseHistory c)) = some (o .two) at two
  simp only [caseValid,total,one,two,Option.getD_some]
  exact valid

/-- Termination follows from repeated bounded consensus. The bounds and
algorithms may depend on the prefix. Finite-state residual equality reduces
this to finitely many cases; no computable bound is assumed in advance. -/
theorem exists_successful_round (A : Set (Nat → Graph))
    (recognizes : ∀ word, word ∈ A ↔ M.Accepts word)
    (repeated : ∀ u, LivePrefix A u → ∃ R, 0 < R ∧
      ∃ σ : StrategyPair Bool Bool (Option Bool) (Option Bool), SolvesBy σ (Residual A u) R) :
    ∃ n, checkAll M (n+1) = true := by
  classical
  have perState (q : M.State) : ∃ R : Nat,
      reachableState M q = true → liveState M q = true →
      ∃ σ : StrategyPair Bool Bool (Option Bool) (Option Bool), SolvesBy σ (stateLanguage M q) R := by
    by_cases good : reachableState M q = true ∧ liveState M q = true
    · obtain ⟨u,state⟩ := (reachableState_exact M q).mp good.1
      have live : LivePrefix A u := (prefixRecognizer_correct M A recognizes u).mpr
        (by rw [state]; exact (liveState_correct M q).mp good.2)
      obtain ⟨R,_,σ,solves⟩ := repeated u live
      rw [residual_state_language M A recognizes u,state] at solves
      exact ⟨R,fun _ _ => ⟨σ,solves⟩⟩
    · exact ⟨0,fun reachable live => False.elim (good ⟨reachable,live⟩)⟩
  choose rounds correct using perState
  let maximum := Finset.univ.sup rounds
  refine ⟨maximum,?_⟩
  rw [checkAll,decide_eq_true_eq]
  intro q reachable live
  obtain ⟨σ,solves⟩ := correct q reachable live
  apply checkState_of_solves M q (maximum+1) (by omega) σ
  apply solves.mono
  exact (Finset.le_sup (Finset.mem_univ q)).trans (Nat.le_succ maximum)

/-- The compiled increasing search receives only the automaton as data.
The semantic proof of repeated bounded solvability guarantees termination. -/
def boundFromRepeated (A : Set (Nat → Graph))
    (recognizes : ∀ word, word ∈ A ↔ M.Accepts word)
    (repeated : ∀ u, LivePrefix A u → ∃ R, 0 < R ∧
      ∃ σ : StrategyPair Bool Bool (Option Bool) (Option Bool), SolvesBy σ (Residual A u) R) : Nat :=
  searchBound M (exists_successful_round M A recognizes repeated)

end Characterisation.ComponentGames.Consensus
