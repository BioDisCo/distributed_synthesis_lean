/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.ComponentGames.ConsensusHoles
import DistributedSynthesis.Library.Distributed.GraphAdversaries.Model
import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryTopology

/-! Necessary topological conditions for bounded consensus on arbitrary
adversaries. The decision bound may depend on the residual prefix. -/
namespace Characterisation.ComponentGames.Consensus
open DistributedSynthesis Characterisation Set
variable {V : Type}

/-- Increasing a decision bound does not change the strategy or its safety
requirements. This also covers an empty adversary and a bound of zero. -/
theorem SolvesBy.mono_bound {σ : StrategyPair V V (Option V) (Option V)}
    {A : Set (Nat → Graph)} {D E : Nat} (solves : SolvesBy σ A D) (bound : D ≤ E) :
    SolvesBy σ A E where
  irrevocable := solves.irrevocable
  valid := solves.valid
  bound := by
    intro env admitted p
    obtain ⟨n, before, v, decided⟩ := solves.bound env admitted p
    exact ⟨n, before.trans_le bound, v, decided⟩

/-- The necessary direction of repeated bounded-time consensus does not
require regularity, or a common bound for the different residuals. -/
theorem repeated_bounded_implies_nowhere_dense [Nontrivial V]
    (A : Set (Nat → Graph))
    (consensus : ∀ h, LivePrefix A h → ∃ D,
      ∃ σ : StrategyPair V V (Option V) (Option V), SolvesBy σ (Residual A h) D) :
    IsNowhereDense (geometricMap '' A) := by
  apply (DistributedSynthesis.GraphAdversaries.geometricHoles_iff_isNowhereDense A).mp
  apply (geometric_holes_iff_prefix_holes A).mpr
  intro h live
  obtain ⟨D, σ, solves⟩ := consensus h live
  obtain ⟨z, _, missing⟩ := decidesAt_missing_extension A h (D+1) (by omega) σ
    (solves.mono_bound (Nat.le_succ D)).decidesAt
  exact ⟨z, missing⟩

/-- The necessary direction of `bounded:cons:char`, without regularity or
closedness. A finite decision bound supplies a missing finite prefix. -/
theorem bounded_implies_not_dense [Nontrivial V] (A : Set (Nat → Graph))
    (D : Nat) (σ : StrategyPair V V (Option V) (Option V))
    (solves : SolvesBy σ A D) : ¬ Dense (geometricMap '' A) := by
  have residual : Residual A [] = A := by
    ext word
    have empty : Characterisation.prependGraphs [] word = word := by
      funext n
      simp [Characterisation.prependGraphs]
    change Characterisation.prependGraphs [] word ∈ A ↔ word ∈ A
    rw [empty]
  obtain ⟨z, _, missing⟩ := decidesAt_missing_extension A [] (D+1) (by omega) σ
    (by rw [residual]; exact (solves.mono_bound (Nat.le_succ D)).decidesAt)
  have hole := missing_prefix_gives_hole A z (by simpa using missing)
  intro dense
  obtain ⟨x, image, inside⟩ := dense.exists_mem_open (cellInterior_open z) (cellInterior_nonempty z)
  exact Set.disjoint_left.mp hole inside image

/-- The compactness step in `bounded:cons:char`, on the actual reactive
execution model. The input streams are arbitrary, the input alphabet is
finite, and the graph adversary is closed. No finite-state strategy is assumed. -/
theorem uniform_decision_bound_of_closed [Finite V]
    [TopologicalSpace Graph] [DiscreteTopology Graph]
    (A : Set (Nat → Graph)) (closed : IsClosed A)
    (σ : StrategyPair V V (Option V) (Option V))
    (terminates : ∀ env, (fun n => (env n).graph) ∈ A → ∀ p,
      ∃ n v, outputAt σ env n p = some v) :
    ∃ D, ∀ env, (fun n => (env n).graph) ∈ A → ∀ p,
      ∃ n, n < D ∧ ∃ v, outputAt σ env n p = some v := by
  classical
  letI := Fintype.ofFinite V
  letI : TopologicalSpace (EnvironmentRound V V) := ⊥
  letI : DiscreteTopology (EnvironmentRound V V) := ⟨rfl⟩
  let K : Set (EnvironmentSequence V V) := {env | (fun n => (env n).graph) ∈ A}
  have compact : IsCompact K := by
    apply IsClosed.isCompact
    apply closed.preimage
    apply continuous_pi
    intro n
    exact continuous_of_discreteTopology.comp (continuous_apply n)
  let U : Nat → Set (EnvironmentSequence V V) := fun D =>
    {env | ∀ p, ∃ n, n < D ∧ ∃ v, outputAt σ env n p = some v}
  have openU (D : Nat) : IsOpen (U D) := by
    apply isOpen_iff_mem_nhds.mpr
    intro env decided
    apply Filter.mem_of_superset ((isOpen_agreeBefore env D).mem_nhds (fun _ _ => rfl))
    intro other agree p
    obtain ⟨n, before, v, value⟩ := decided p
    have same : execution σ env n = execution σ other n := by
      have prefixes := executionPrefix_congr_of_env_eq_lt σ
        (n := n) (fun k hk => agree k (hk.trans before))
      simp only [execution_apply, prefixes, agree n before]
    refine ⟨n, before, v, ?_⟩
    cases p <;> simpa only [outputAt, ← same] using value
  have monotoneU : Monotone U := by
    intro D E bound env decided p
    obtain ⟨n, before, v, value⟩ := decided p
    exact ⟨n, before.trans_le bound, v, value⟩
  have cover : K ⊆ ⋃ D, U D := by
    intro env admitted
    choose n v value using terminates env admitted
    refine Set.mem_iUnion.mpr ⟨(Finset.univ.sup n)+1, fun p => ?_⟩
    exact ⟨n p, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ p)), v p, value p⟩
  obtain ⟨D, bound⟩ := compact.elim_directed_cover U openU cover
    (fun i j => ⟨max i j, monotoneU (le_max_left _ _), monotoneU (le_max_right _ _)⟩)
  exact ⟨D, fun env admitted => bound admitted⟩

end Characterisation.ComponentGames.Consensus
