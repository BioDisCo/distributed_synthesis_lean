/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.ObjectiveBridge
import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderCheckpoints
import DistributedSynthesis.Formalizations.ComponentGames.ConsensusFinite
import DistributedSynthesis.Library.Distributed.GraphAdversaries.Undecidability.ResidualUndecidability

/- The paper's missing-extension argument, on actual StrategyPair executions.
The task relation, histories, views, residuals and live prefixes are reused.
SolvesBy spells out the paper's bounded reactive decision-task interface. -/
namespace Characterisation.ComponentGames.Consensus
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 1800000
variable {V : Type}

def proposals (env : EnvironmentSequence V V) : Proc → V
  | .one => (env 0).inputOne
  | .two => (env 0).inputTwo

def outputAt (σ : StrategyPair V V (Option V) (Option V))
    (env : EnvironmentSequence V V) (n : Nat) : Proc → Option V
  | .one => (execution σ env n).outputOne
  | .two => (execution σ env n).outputTwo

/-- Exact bounded consensus requirements: all input sequences, irreversible
outputs, task validity for the initial proposals, and decisions by round D.
Execution index n denotes round n+1 in the manuscript. -/
structure SolvesBy (σ : StrategyPair V V (Option V) (Option V))
    (A : Set (Nat → Graph)) (D : Nat) : Prop where
  irrevocable : ∀ env, (fun n => (env n).graph) ∈ A → ∀ p n m, n ≤ m → ∀ v,
    outputAt σ env n p = some v → outputAt σ env m p = some v
  valid : ∀ env, (fun n => (env n).graph) ∈ A → ∀ o : Proc → V,
    (∀ p, ∃ n, outputAt σ env n p = some (o p)) → (task V).allows (proposals env) o
  bound : ∀ env, (fun n => (env n).graph) ∈ A → ∀ p,
    ∃ n, n < D ∧ ∃ v, outputAt σ env n p = some v

/-- Only this necessary consequence is used in the impossibility argument.
Its weaker premise makes that argument stronger, not weaker, than needed. -/
def DecidesAt (σ : StrategyPair V V (Option V) (Option V))
    (A : Set (Nat → Graph)) (D : Nat) : Prop :=
  ∀ env, (fun n => (env n).graph) ∈ A → ∃ o : Proc → V,
    (task V).allows (proposals env) o ∧ ∀ p, outputAt σ env (D-1) p = some (o p)

theorem SolvesBy.decidesAt {σ : StrategyPair V V (Option V) (Option V)}
    {A : Set (Nat → Graph)} {D : Nat} (solves : SolvesBy σ A D) : DecidesAt σ A D := by
  intro env admitted
  choose n before value decided using solves.bound env admitted
  refine ⟨value,solves.valid env admitted value (fun p => ⟨n p,decided p⟩),fun p => ?_⟩
  exact solves.irrevocable env admitted p (n p) (D-1) (by have := before p; omega) _ (decided p)

def proposalEnvironment (x : Proc → V) (word : Nat → Graph) : EnvironmentSequence V V :=
  fun n => ⟨x .one,x .two,word n⟩

def strategyOutput (σ : StrategyPair V V (Option V) (Option V)) : (p : Proc) → View V V p → Option V
  | .one => σ.one
  | .two => σ.two

theorem outputAt_view (σ : StrategyPair V V (Option V) (Option V))
    (env : EnvironmentSequence V V) (n : Nat) (p : Proc) :
    outputAt σ env n p = strategyOutput σ p (currentView p (branchNode (environmentWord env) (n+1))) := by
  have outputs := environmentWord_outputs σ env n
  cases p
  · exact congrArg (fun z => z.2.1) outputs
  · exact congrArg (fun z => z.2.2) outputs

theorem proposalEnvironment_prefix (x : Proc → V) (word : Nat → Graph) (n : Nat) :
    branchNode (environmentWord (proposalEnvironment x word)) n = proposalHistory x (graphPrefix word n) := by
  simp only [branchNode_eq_ofFn,proposalHistory,graphPrefix,List.map_ofFn]
  rfl

/-- Every live uz supplies an admissible residual word beginning with z.
The same witness is used for all proposal pairs: the adversary restricts graphs. -/
theorem live_extension_residual (A : Set (Nat → Graph)) (u z : List Graph)
    (live : LivePrefix A (u++z)) :
    ∃ word ∈ Residual A u, graphPrefix word z.length = z := by
  obtain ⟨word,admitted,pref⟩ := live
  have full : graphPrefix word (u.length+z.length) = u++z := by simpa only [List.length_append] using pref
  have first : graphPrefix word u.length = u := by
    have eq := congrArg (List.take u.length) full
    rw [graphPrefix_take _ _ _ (by omega)] at eq
    simpa using eq
  have last : graphPrefix (OmegaWord.drop word u.length) z.length = z := by
    rw [graphPrefix_split,first] at full
    exact List.append_cancel_left full
  refine ⟨OmegaWord.drop word u.length,?_,last⟩
  change prependGraphs u (OmegaWord.drop word u.length) ∈ A
  rw [prepend_drop_of_prefix word u first]
  exact admitted

/-- The English proof's contradiction: a D-round consensus algorithm on a
residual cannot coexist with all its length-D graph extensions being live. -/
theorem decidesAt_missing_extension [Nontrivial V] (A : Set (Nat → Graph)) (u : List Graph)
    (D : Nat) (positive : 0 < D) (σ : StrategyPair V V (Option V) (Option V))
    (decides : DecidesAt σ (Residual A u) D) :
    ∃ z : List Graph, z.length = D ∧ ¬ LivePrefix A (u++z) := by
  classical
  by_contra missing
  have allLive : ∀ z : List Graph, z.length = D → LivePrefix A (u++z) := by
    intro z len
    by_contra dead
    exact missing ⟨z,len,dead⟩
  let default : V := Classical.choice inferInstance
  let one (_ : V) (v : View V V .one) := (σ.one v).getD default
  let two (_ : V) (v : View V V .two) := (σ.two v).getD default
  apply no_full_table (V:=V) D
  refine ⟨one,two,fun x gs len => ?_⟩
  obtain ⟨word,admitted,pref⟩ := live_extension_residual A u gs (allLive gs len)
  obtain ⟨o,valid,outputs⟩ := decides (proposalEnvironment x word) admitted
  have correct (p : Proc) : strategyOutput σ p (currentView p (proposalHistory x gs)) = some (o p) := by
    have out := outputs p
    rw [outputAt_view,show D-1+1 = D by omega,proposalEnvironment_prefix,← len,pref] at out
    exact out
  have eq : (fun p => match p with
      | .one => one (x .one) (currentView .one (proposalHistory x gs))
      | .two => two (x .two) (currentView .two (proposalHistory x gs))) = o := by
    funext p
    cases p
    · change (strategyOutput σ .one (currentView .one (proposalHistory x gs))).getD default = _
      rw [correct]; rfl
    · change (strategyOutput σ .two (currentView .two (proposalHistory x gs))).getD default = _
      rw [correct]; rfl
  have inputs : proposals (proposalEnvironment x word) = x := by
    funext p; cases p <;> rfl
  rw [inputs] at valid
  exact Eq.mpr (congrArg ((task V).allows x) eq) valid

/-- The exact-depth missing-extension property needed by the common-view
lemma. No regularity, closedness or effective representation of A is needed. -/
theorem repeated_consensus_exact_holes [Nontrivial V]
    (A : Set (Nat → Graph)) (D : Nat) (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
      SolvesBy σ (Residual A u) D) :
    ∀ u, ∃ z : List Graph, z.length = D ∧ ¬ LivePrefix A (u++z) := by
  intro u
  by_cases live : LivePrefix A u
  · obtain ⟨σ,solves⟩ := consensus u live
    exact decidesAt_missing_extension A u D positive σ solves.decidesAt
  · refine ⟨List.replicate D .both,List.length_replicate,?_⟩
    intro extension
    exact live (livePrefix_closed A u _ extension)

/-- Lemma 4.5 with its original consensus hypothesis, arbitrary private
inputs, arbitrary connected live families, and exactly the given D. -/
theorem repeated_consensus_common_view [Nontrivial V] {I₁ I₂ : Type}
    (A : Set (Nat → Graph)) (D : Nat) (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
      SolvesBy σ (Residual A u) D)
    (h : EnvHistory I₁ I₂) (deep : D ≤ List.length h) (live : LivePrefix A (History.graphSequence h)) :
    ∃ p, ∀ k, InputConnected (LivePrefix A) h k →
      lagView D (currentView p h) = lagView D (currentView p k) :=
  exact_holes_common_view (LivePrefix A) D
    (repeated_consensus_exact_holes A D positive consensus) h deep live

/-- The literal set-of-histories conclusion, written with the earlier
prefix h[...r-D] rather than the library's equivalent lagView operation. -/
theorem repeated_consensus_common_view_set [Nontrivial V] {I₁ I₂ : Type}
    (A : Set (Nat → Graph)) (D : Nat) (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
      SolvesBy σ (Residual A u) D)
    (r : Nat) (deep : D ≤ r) (C : Set (EnvHistory I₁ I₂)) (nonempty : C.Nonempty)
    (lengths : ∀ h ∈ C, List.length h = r)
    (live : ∀ h ∈ C, LivePrefix A (History.graphSequence h))
    (connected : ∀ h ∈ C, ∀ k ∈ C, InputConnected (LivePrefix A) h k) :
    ∃ p, ∀ h ∈ C, ∀ k ∈ C,
      currentView p (h.take (r-D)) = currentView p (k.take (r-D)) := by
  obtain ⟨a,inside⟩ := nonempty
  obtain ⟨p,shared⟩ := repeated_consensus_common_view A D positive consensus a
    (by rw [lengths a inside]; exact deep) (live a inside)
  refine ⟨p,fun h hh k hk => ?_⟩
  have eq := (shared h (connected a inside h hh)).symm.trans (shared k (connected a inside k hk))
  rw [lagView_take p h D (by rw [lengths h hh]; exact deep),
    lagView_take p k D (by rw [lengths k hk]; exact deep),lengths h hh,lengths k hk] at eq
  exact eq

end Characterisation.ComponentGames.Consensus

