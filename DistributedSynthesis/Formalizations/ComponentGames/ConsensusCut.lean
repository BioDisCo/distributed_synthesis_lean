/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.ComponentGames.ConsensusTermination

namespace Characterisation.ComponentGames.Consensus
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks Set
variable {V : Type}

noncomputable def lowerStar (h : List Graph) (p : Proc) : ℝ :=
  ((PaddingProjection.project (fun _ => true) (graphView p h) : ℝ) - 1) / 3^h.length

noncomputable def upperStar (h : List Graph) (p : Proc) : ℝ :=
  ((PaddingProjection.project (fun _ => true) (graphView p h) : ℝ) + 1) / 3^h.length

/-- The local uncertainty interval contains the actual edge cell, with at
most one additional cell width on either side. -/
theorem star_bounds (h : List Graph) (p : Proc) :
    lowerStar h p ≤ leftEndpoint h ∧ rightEndpoint h ≤ upperStar h p ∧
      leftEndpoint h - (1/3 : ℝ)^h.length ≤ lowerStar h p ∧
      upperStar h p ≤ rightEndpoint h + (1/3 : ℝ)^h.length := by
  have bounds : pathIndex h ≤ PaddingProjection.project (fun _ => true) (graphView p h) ∧
      PaddingProjection.project (fun _ => true) (graphView p h) ≤ pathIndex h + 1 := by
    cases p
    · exact (actual_process_index_bounds h).1
    · exact (actual_process_index_bounds h).2
  have lo : (pathIndex h : ℝ) ≤ PaddingProjection.project (fun _ => true) (graphView p h) := by exact_mod_cast bounds.1
  have hi : (PaddingProjection.project (fun _ => true) (graphView p h) : ℝ) ≤ (pathIndex h : ℝ)+1 := by exact_mod_cast bounds.2
  have positive : (0 : ℝ) < 3^h.length := by positivity
  simp only [lowerStar, upperStar, leftEndpoint, rightEndpoint, one_div_pow]
  constructor
  · apply (div_le_div_iff_of_pos_right positive).mpr; linarith
  constructor
  · apply (div_le_div_iff_of_pos_right positive).mpr; linarith
  constructor
  · rw [← sub_div]
    exact (div_le_div_iff_of_pos_right positive).mpr (by linarith)
  · rw [← add_div]
    exact (div_le_div_iff_of_pos_right positive).mpr (by linarith)

noncomputable def cutSuggestion (fallback : V) (c : UnitInterval) (p : Proc) (v : View V V p) : Option V := by
  classical
  let coordinate : ℝ := PaddingProjection.project (fun _ => true) (eraseView v)
  let scale : ℝ := 3^viewDepth v
  exact if (coordinate+1)/scale < c.val then some (readProposal fallback .one v)
    else if c.val < (coordinate-1)/scale then some (readProposal fallback .two v) else none

/-- Tentative decisions reveal a known proposal; the extreme process never
needs an input it has not received. -/
theorem cutSuggestion_history (fallback : V) (c : UnitInterval)
    (x : Proc → V) (h : List Graph) (positive : 0 < h.length) (p : Proc) :
    cutSuggestion fallback c p (currentView p (proposalHistory x h)) =
      if upperStar h p < c.val then some (x .one)
      else if c.val < lowerStar h p then some (x .two) else none := by
  classical
  have age : silentAge (currentView p (proposalHistory x h)) = silentAge (graphView p h) := by
    rw [← silentAge_erase, eraseView_current]
    simp [History.graphSequence,proposalHistory,List.map_map,Function.comp_def]
  have scale : (0 : ℝ) < 3^h.length := by positivity
  have readOne (left : upperStar h p < c.val) :
      readProposal fallback .one (currentView p (proposalHistory x h)) = x .one := by
    cases p
    · exact readProposal_own fallback x h positive .one
    · apply readProposal_other fallback x h .two
      by_contra old
      have extreme := silent_graph_coordinate h .two (by rw [← age]; omega)
      simp only [upperStar, extreme, Nat.cast_pow, Nat.cast_ofNat] at left
      have := (div_lt_iff₀ scale).mp left
      have := c.property.2
      nlinarith
  have readTwo (right : c.val < lowerStar h p) :
      readProposal fallback .two (currentView p (proposalHistory x h)) = x .two := by
    cases p
    · apply readProposal_other fallback x h .one
      by_contra old
      have extreme := silent_graph_coordinate h .one (by rw [← age]; omega)
      simp only [lowerStar, extreme, Nat.cast_zero, zero_sub] at right
      have := (lt_div_iff₀ scale).mp right
      have := c.property.1
      nlinarith
    · exact readProposal_own fallback x h positive .two
  unfold cutSuggestion
  rw [proposal_coordinate, viewDepth_history]
  have len : List.length (proposalHistory x h) = h.length := by simp [proposalHistory]
  rw [len]
  change (if upperStar h p < c.val then _ else if c.val < lowerStar h p then _ else _) = _
  split_ifs with left right
  · rw [readOne left]
  · rw [readTwo right]
  · rfl

/-- Every finite suggestion lies on the same side of the missing point as
the execution's limit coordinate. -/
theorem cutSuggestion_consistent (fallback : V) (c : UnitInterval) (x : Proc → V)
    (word : Nat → Graph) (n : Nat) (p : Proc) (v : V)
    (suggested : cutSuggestion fallback c p
      (currentView p (proposalHistory x (graphPrefix word (n+1)))) = some v) :
    v = if coordinate word < c.val then x .one else x .two := by
  classical
  rw [cutSuggestion_history fallback c x _ (by simp) p] at suggested
  have cell := coordinate_in_prefix_cell word (n+1)
  have bounds := star_bounds (graphPrefix word (n+1)) p
  split_ifs at suggested with left right
  · have side : coordinate word < c.val := cell.2.trans (bounds.2.1) |>.trans_lt left
    rw [if_pos side]
    exact (Option.some.inj suggested).symm
  · have side : ¬ coordinate word < c.val := by linarith [cell.1, bounds.1]
    rw [if_neg side]
    exact (Option.some.inj suggested).symm

/-- Shrinking cells eventually put each local uncertainty interval wholly
on one side of a point different from the execution's coordinate. -/
theorem cutSuggestion_terminates (fallback : V) (c : UnitInterval) (x : Proc → V)
    (word : Nat → Graph) (different : coordinate word ≠ c.val) (p : Proc) :
    ∃ n v, cutSuggestion fallback c p
      (currentView p (proposalHistory x (graphPrefix word (n+1)))) = some v := by
  classical
  have positive : 0 < |coordinate word - c.val| / 2 := by
    exact div_pos (abs_pos.mpr (sub_ne_zero.mpr different)) (by norm_num)
  obtain ⟨m,small⟩ := exists_pow_lt_of_lt_one positive (by norm_num : (1/3 : ℝ) < 1)
  have smallNext : 2 * (1/3 : ℝ)^(m+1) < |coordinate word - c.val| := by
    rw [pow_succ]
    have nonnegative : 0 ≤ (1/3 : ℝ)^m := by positivity
    nlinarith
  have cell := coordinate_in_prefix_cell word (m+1)
  have bounds := star_bounds (graphPrefix word (m+1)) p
  have width := cell_width (graphPrefix word (m+1))
  simp only [graphPrefix_length] at bounds width
  by_cases left : coordinate word < c.val
  · refine ⟨m,x .one,?_⟩
    rw [cutSuggestion_history fallback c x _ (by simp) p]
    apply if_pos
    rw [abs_of_neg (sub_neg.mpr left)] at smallNext
    linarith [cell.1, bounds.2.2.2]
  · have right : c.val < coordinate word := lt_of_le_of_ne (le_of_not_gt left) (Ne.symm different)
    refine ⟨m,x .two,?_⟩
    rw [cutSuggestion_history fallback c x _ (by simp) p]
    have notLeft : ¬ upperStar (graphPrefix word (m+1)) p < c.val := by
      linarith [cell.2,bounds.2.1]
    rw [if_neg notLeft]
    apply if_pos
    rw [abs_of_pos (sub_pos.mpr right)] at smallNext
    linarith [cell.2,bounds.2.2.1]

/-- Ignore later private inputs when computing a tentative consensus decision. -/
noncomputable def cutCandidate (fallback : V) (c : UnitInterval)
    (p : Proc) (v : View V V p) : Option V :=
  cutSuggestion fallback c p (proposalView v)

/-- A point outside the geometric image gives an eventually terminating
consensus protocol, with no uniform decision-time assumption. -/
theorem consensus_of_missing_point [Nonempty V] (A : Set (Nat → Graph))
    (c : UnitInterval) (missing : c ∉ geometricMap '' A) :
    ∃ σ : StrategyPair V V (Option V) (Option V), Solves σ A := by
  classical
  let fallback : V := Classical.choice inferInstance
  refine ⟨retainedStrategy (cutCandidate fallback c), retained_solves _ A ?_ ?_⟩
  · intro env _
    refine ⟨if coordinate (fun n => (env n).graph) < c.val then proposals env .one
      else proposals env .two, ?_, ?_⟩
    · split_ifs <;> simp
    · intro n p w value
      unfold cutCandidate at value
      rw [proposalView_environment] at value
      exact cutSuggestion_consistent fallback c (proposals env) _ n p w value
  · intro env admitted p
    have different : coordinate (fun n => (env n).graph) ≠ c.val := by
      intro eq
      apply missing
      exact ⟨_,admitted,Subtype.ext eq⟩
    obtain ⟨n,v,value⟩ := cutSuggestion_terminates fallback c (proposals env) _ different p
    exact ⟨n,v,by simpa only [cutCandidate,proposalView_environment] using value⟩

theorem consensus_of_image_ne_univ [Nonempty V] (A : Set (Nat → Graph))
    (proper : geometricMap '' A ≠ Set.univ) :
    ∃ σ : StrategyPair V V (Option V) (Option V), Solves σ A := by
  have existsMissing : ∃ c, c ∉ geometricMap '' A := by
    by_contra h
    apply proper
    exact Set.eq_univ_of_forall (by simpa only [not_exists, not_not] using h)
  obtain ⟨c,missing⟩ := existsMissing
  exact consensus_of_missing_point A c missing

/-- On a closed adversary with finite proposal alphabet, eventual
termination has a common finite bound, as in the manuscript's compactness step. -/
theorem Solves.bounded_of_closed [Finite V]
    [TopologicalSpace Graph] [DiscreteTopology Graph]
    {A : Set (Nat → Graph)} {σ : StrategyPair V V (Option V) (Option V)}
    (solves : Solves σ A) (closed : IsClosed A) : ∃ R, SolvesBy σ A R := by
  obtain ⟨R,bound⟩ := uniform_decision_bound_of_closed A closed σ solves.terminates
  exact ⟨R,⟨solves.irrevocable,solves.valid,bound⟩⟩

end Characterisation.ComponentGames.Consensus
