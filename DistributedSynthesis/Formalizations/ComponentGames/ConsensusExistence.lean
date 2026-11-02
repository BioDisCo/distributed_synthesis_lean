/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ConsensusProposals

namespace Characterisation.ComponentGames.Consensus
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2000000

/-- The existing library's common local selection, combined with its
input-knowledge theorem, supplies bounded consensus. This discharges the
search's existence premise; it does not replace the increasing search. -/
theorem bounded_consensus_of_regular_holes (A : Set (Nat → Graph))
    (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ R, 0 < R ∧ ∃ σ : StrategyPair Bool Bool (Option Bool) (Option Bool), SolvesBy σ A R := by
  obtain ⟨d,select,selection⟩ := holes_local_recent_receiver_selection
    (I₁:=Bool) (I₂:=Bool) (O₁:=Unit) (O₂:=Unit) A regular holes
  let table : StrategyPair Bool Bool Bool Bool :=
    ⟨fun v => readProposal false (select.one v) v,fun v => readProposal false (select.two v) v⟩
  have correct : ProposalTableCorrect table A (d+1) := by
    intro x gs len live
    have graph : History.graphSequence (proposalHistory x gs) = gs := by
      simp [History.graphSequence,proposalHistory,List.map_map,Function.comp_def]
    obtain ⟨p,one,two,recent⟩ := selection (proposalHistory x gs) (by rwa [graph])
    have outputs (q : Proc) : plainOutput table q (currentView q (proposalHistory x gs)) = x p := by
      have selected : plainOutput table q (currentView q (proposalHistory x gs)) =
          readProposal false p (currentView q (proposalHistory x gs)) := by
        cases q
        · change readProposal false (select.one _) _ = _
          rw [one]
        · change readProposal false (select.two _) _ = _
          rw [two]
      rw [selected]
      by_cases same : p = q
      · rw [same]
        exact readProposal_own false x gs (by omega) q
      · have other : p = q.other := by cases p <;> cases q <;> simp_all [Proc.other]
        have young : silentAge (currentView q (proposalHistory x gs)) < d := by
          by_contra old
          exact same (old_view_owner (LivePrefix A) d (proposalHistory x gs) p q recent (by omega)).symm
        rw [other]
        exact readProposal_other false x gs q (by omega)
    change _ = _ ∧ (_ = x .one ∨ _ = x .two)
    simp only [outputs]
    refine ⟨True.intro,?_⟩
    cases p
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact ⟨d+1,by omega,retainTable (d+1) table,correct.solves table A (d+1) (by omega)⟩

theorem livePrefix_residual (A : Set (Nat → Graph)) (h u : List Graph) :
    LivePrefix (Residual A h) u ↔ LivePrefix A (h++u) := by
  constructor
  · rintro ⟨word,admitted,pref⟩
    refine ⟨prependGraphs h word,admitted,?_⟩
    rw [List.length_append,graphPrefix_split,prependGraphs_prefix,prependGraphs_drop,pref]
  · intro live
    exact live_extension_residual A h u live

theorem residual_geometric_holes (A : Set (Nat → Graph)) (holes : GeometricHoles A) (h : List Graph) :
    GeometricHoles (Residual A h) := by
  apply (geometric_holes_iff_prefix_holes _).mpr
  intro u live
  obtain ⟨z,missing⟩ := (geometric_holes_iff_prefix_holes A).mp holes (h++u)
    ((livePrefix_residual A h u).mp live)
  refine ⟨z,fun extension => missing ?_⟩
  simpa only [List.append_assoc] using (livePrefix_residual A h (u++z)).mp extension

variable (M : DetParityAutomaton.{0,0} Graph) [DecidableEq M.State]

theorem residual_regular (A : Set (Nat → Graph))
    (recognizes : ∀ word, word ∈ A ↔ M.Accepts word) (h : List Graph) : OmegaRegular (Residual A h) := by
  rw [residual_state_language M A recognizes h]
  exact ⟨M.withInitial ((prefixRecognizer M).eval h),fun word =>
    (M.withInitial_accepts_iff ((prefixRecognizer M).eval h) word).symm⟩

/-- The original nowhere-dense-image hypothesis suffices for the actual
repeated consensus premise used by the search termination proof. -/
theorem repeated_bounded_of_nowhere_dense (A : Set (Nat → Graph))
    (recognizes : ∀ word, word ∈ A ↔ M.Accepts word)
    (nowhereDense : IsNowhereDense (geometricMap '' A)) :
    ∀ h, LivePrefix A h → ∃ R, 0 < R ∧
      ∃ σ : StrategyPair Bool Bool (Option Bool) (Option Bool), SolvesBy σ (Residual A h) R := by
  intro h _
  exact bounded_consensus_of_regular_holes (Residual A h) (residual_regular M A recognizes h)
    (residual_geometric_holes A ((geometricHoles_iff A).mpr nowhereDense) h)

end Characterisation.ComponentGames.Consensus
