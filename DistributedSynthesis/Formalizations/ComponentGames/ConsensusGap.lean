/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.ComponentGames.ConsensusExistence
import DistributedSynthesis.Formalizations.ComponentGames.ConsensusTopology
import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryTopology

namespace Characterisation.ComponentGames.Consensus
open DistributedSynthesis Characterisation FullViewPath Set
variable {V : Type}

/-- A process that has never received is at its extreme coordinate. -/
theorem silent_graph_coordinate (h : List Graph) (p : Proc)
    (blind : h.length ≤ silentAge (graphView p h)) :
    PaddingProjection.project (fun _ => true) (graphView p h) =
      match p with | .one => 0 | .two => 3^h.length := by
  induction h using List.reverseRecOn with
  | nil => cases p <;> rfl
  | append_singleton h g ih =>
    cases p <;> cases g <;>
      simp only [graphView, at_append, advance, advanceViews, silentAge, List.length_append,
        List.length_singleton] at blind ⊢
    all_goals first
      | omega
      | have prev := ih (by simpa only [graphView] using Nat.le_of_succ_le_succ blind)
        simp only [graphView] at prev
        simp [PaddingProjection.project, prev, pow_succ, Nat.mul_comm]

theorem proposal_coordinate (x : Proc → V) (h : List Graph) (p : Proc) :
    PaddingProjection.project (fun _ => true) (eraseView (currentView p (proposalHistory x h))) =
      PaddingProjection.project (fun _ => true) (graphView p h) := by
  rw [eraseView_current]
  simp [History.graphSequence, proposalHistory, List.map_map, Function.comp_def]

noncomputable def gapSelection {p : Proc} (cut : Nat) (v : View V V p) : Proc :=
  if PaddingProjection.project (fun _ => true) (eraseView v) ≤ cut then .one else .two

noncomputable def gapTable (fallback : V) (cut : Nat) : StrategyPair V V V V :=
  ⟨fun v => readProposal fallback (gapSelection cut v) v,
   fun v => readProposal fallback (gapSelection cut v) v⟩

/-- A selected proposal is locally known: an uninformed process is at an
extreme, where the selection always chooses its own proposal. -/
theorem gapTable_reads_selected (fallback : V) (cut : Nat) (x : Proc → V)
    (h : List Graph) (positive : 0 < h.length) (inside : cut < 3^h.length) (p : Proc) :
    plainOutput (gapTable fallback cut) p (currentView p (proposalHistory x h)) =
      x (gapSelection cut (currentView p (proposalHistory x h))) := by
  have graphAge : silentAge (currentView p (proposalHistory x h)) = silentAge (graphView p h) := by
    rw [← silentAge_erase, eraseView_current]
    simp [History.graphSequence, proposalHistory, List.map_map, Function.comp_def]
  have known : gapSelection cut (currentView p (proposalHistory x h)) ≠ p →
      silentAge (currentView p (proposalHistory x h)) < h.length := by
    intro other
    by_contra old
    have extreme := silent_graph_coordinate h p (by rw [← graphAge]; omega)
    unfold gapSelection at other
    rw [proposal_coordinate, extreme] at other
    cases p <;> simp_all
  have selected : plainOutput (gapTable fallback cut) p (currentView p (proposalHistory x h)) =
      readProposal fallback (gapSelection cut (currentView p (proposalHistory x h)))
        (currentView p (proposalHistory x h)) := by cases p <;> rfl
  rw [selected]
  by_cases own : gapSelection cut (currentView p (proposalHistory x h)) = p
  · rw [own]
    exact readProposal_own fallback x h positive p
  · have other : gapSelection cut (currentView p (proposalHistory x h)) = p.other := by
      generalize eq : gapSelection cut (currentView p (proposalHistory x h)) = q at *
      cases p <;> cases q <;> simp_all [Proc.other]
    rw [other]
    exact readProposal_other fallback x h p (known own)

theorem gapSelection_agrees (cut : Nat) (x : Proc → V) (h : List Graph)
    (different : pathIndex h ≠ cut) :
    ∃ selected : Proc, ∀ p, gapSelection cut (currentView p (proposalHistory x h)) = selected := by
  have bounds := actual_process_index_bounds h
  by_cases before : pathIndex h < cut
  · refine ⟨.one, fun p => ?_⟩
    unfold gapSelection
    rw [proposal_coordinate]
    apply if_pos
    cases p <;> simp only [graphView] <;> omega
  · refine ⟨.two, fun p => ?_⟩
    unfold gapSelection
    rw [proposal_coordinate]
    apply if_neg
    cases p <;> simp only [graphView] <;> omega

/-- Deleting one edge splits the finite row. Each side chooses the proposal
of its extreme process, which every process on that side knows. -/
theorem gapTable_correct (fallback : V) (A : Set (Nat → Graph)) (hole : List Graph)
    (positive : 0 < hole.length) (missing : ¬ LivePrefix A hole) :
    ProposalTableCorrect (gapTable fallback (pathIndex hole)) A hole.length := by
  intro x h len live
  have different : pathIndex h ≠ pathIndex hole := by
    intro eq
    exact missing ((pathIndex_injective h hole len eq) ▸ live)
  obtain ⟨selected, same⟩ := gapSelection_agrees (pathIndex hole) x h different
  have outputs (p : Proc) : plainOutput (gapTable fallback (pathIndex hole)) p
      (currentView p (proposalHistory x h)) = x selected := by
    rw [gapTable_reads_selected fallback _ x h (by omega)
      (by rw [len]; exact pathIndex_lt hole), same]
  change (plainOutput _ .one _ = plainOutput _ .two _) ∧
    (plainOutput _ .one _ = x .one ∨ plainOutput _ .one _ = x .two)
  rw [outputs .one, outputs .two]
  refine ⟨rfl, ?_⟩
  cases selected
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Bounded consensus follows from a single missing finite prefix, with
no regularity or effectiveness premise on the adversary. -/
theorem bounded_consensus_of_missing_prefix [Nonempty V]
    (A : Set (Nat → Graph)) (hole : List Graph) (missing : ¬ LivePrefix A hole) :
    ∃ R, 0 < R ∧ ∃ σ : StrategyPair V V (Option V) (Option V), SolvesBy σ A R := by
  classical
  let fallback : V := Classical.choice inferInstance
  let longer := hole ++ [.both]
  have dead : ¬ LivePrefix A longer := fun live => missing (livePrefix_closed A hole [.both] live)
  have positive : 0 < longer.length := by simp [longer]
  let table := gapTable fallback (pathIndex longer)
  have correct := gapTable_correct fallback A longer positive dead
  exact ⟨longer.length, positive, retainTable longer.length table,
    correct.solves table A longer.length positive⟩

/-- Non-density of the geometric image is equivalent to a missing finite
prefix. The reverse implication uses a cell interior, not an endpoint gap. -/
theorem not_dense_iff_missing_prefix (A : Set (Nat → Graph)) :
    ¬ Dense (geometricMap '' A) ↔ ∃ h : List Graph, ¬ LivePrefix A h := by
  classical
  constructor
  · intro notDense
    by_contra none
    have live : ∀ h : List Graph, LivePrefix A h := by
      intro h
      by_contra dead
      exact none ⟨h,dead⟩
    letI : TopologicalSpace Graph := ⊥
    letI : DiscreteTopology Graph := ⟨rfl⟩
    have prefixDense : PrefixDense A := by
      intro x n
      obtain ⟨y, admitted, pref⟩ := live (graphPrefix x n)
      simp only [graphPrefix_length] at pref
      exact ⟨y, admitted, (graphPrefix_eq_iff_agreeBefore x y n).mp pref.symm⟩
    have denseA := (prefixDense_iff_dense A).mp prefixDense
    apply notDense
    apply dense_iff_closure_eq.mpr
    rw [← geometricMap_image_closure, denseA.closure_eq, Set.image_univ]
    exact Set.range_eq_univ.mpr geometricMap_surjective
  · rintro ⟨h, missing⟩ dense
    obtain ⟨x, image, inside⟩ := dense.exists_mem_open (cellInterior_open h) (cellInterior_nonempty h)
    exact Set.disjoint_left.mp (missing_prefix_gives_hole A h missing) inside image

/-- The full arbitrary-adversary bounded-consensus characterization. The
sufficiency proof constructs a decision table from an interval gap. -/
theorem bounded_consensus_iff_not_dense [Nontrivial V] (A : Set (Nat → Graph)) :
    (∃ R, ∃ σ : StrategyPair V V (Option V) (Option V), SolvesBy σ A R) ↔
      ¬ Dense (geometricMap '' A) := by
  constructor
  · rintro ⟨R,σ,solves⟩
    exact bounded_implies_not_dense A R σ solves
  · intro notDense
    obtain ⟨h,missing⟩ := (not_dense_iff_missing_prefix A).mp notDense
    obtain ⟨R,_,σ,solves⟩ := bounded_consensus_of_missing_prefix (V:=V) A h missing
    exact ⟨R,σ,solves⟩

/-- Nowhere density supplies one finite gap in each residual, independently
of any recognizer. The bound and algorithm may depend on the prefix. -/
theorem repeated_bounded_of_nowhere_dense_general [Nonempty V]
    (A : Set (Nat → Graph)) (nowhereDense : IsNowhereDense (geometricMap '' A)) :
    ∀ h, LivePrefix A h → ∃ R, 0 < R ∧
      ∃ σ : StrategyPair V V (Option V) (Option V), SolvesBy σ (Residual A h) R := by
  intro h live
  have holes := (geometric_holes_iff_prefix_holes A).mp
    ((DistributedSynthesis.GraphAdversaries.geometricHoles_iff_isNowhereDense A).mpr nowhereDense)
  obtain ⟨z,missing⟩ := holes h live
  apply bounded_consensus_of_missing_prefix (Residual A h) z
  exact fun extension => missing ((livePrefix_residual A h z).mp extension)

/-- The arbitrary-adversary iff in `lem:repeated_bounded_time_consensus`.
No regularity, common bound, or supplied strategy is assumed. -/
theorem repeated_bounded_iff_nowhere_dense [Nontrivial V] (A : Set (Nat → Graph)) :
    (∀ h, LivePrefix A h → ∃ R,
      ∃ σ : StrategyPair V V (Option V) (Option V), SolvesBy σ (Residual A h) R) ↔
      IsNowhereDense (geometricMap '' A) := by
  constructor
  · exact repeated_bounded_implies_nowhere_dense A
  · intro nowhereDense h live
    obtain ⟨R,_,σ,solves⟩ := repeated_bounded_of_nowhere_dense_general (V:=V) A nowhereDense h live
    exact ⟨R,σ,solves⟩

end Characterisation.ComponentGames.Consensus
