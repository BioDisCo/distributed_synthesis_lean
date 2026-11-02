/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.ComponentGames.ConsensusCut
import DistributedSynthesis.Library.Distributed.GraphAdversaries.ViewPathIsomorphism
import Mathlib.Topology.LocallyConstant.Basic
import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryConcatenation

namespace Characterisation.ComponentGames.Consensus
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks Set
variable {V : Type}

/-- Eventual irrevocable consensus supplies a common decision, and every
local decision made at any time has that value. -/
theorem Solves.commonDecision {A : Set (Nat → Graph)}
    {σ : StrategyPair V V (Option V) (Option V)} (solves : Solves σ A)
    (env : EnvironmentSequence V V) (admitted : (fun n => (env n).graph) ∈ A) :
    ∃ v n, (∀ p, outputAt σ env n p = some v) ∧
      (v = proposals env .one ∨ v = proposals env .two) ∧
      ∀ k p w, outputAt σ env k p = some w → w = v := by
  classical
  choose n value decided using solves.terminates env admitted
  have valid := solves.valid env admitted value (fun p => ⟨n p,decided p⟩)
  have same (p : Proc) : value p = value .one := by cases p; rfl; exact valid.1.symm
  let N := max (n .one) (n .two)
  have bound (p : Proc) : n p ≤ N := by cases p; exact le_max_left ..; exact le_max_right ..
  refine ⟨value .one,N,?_,valid.2,?_⟩
  · intro p
    rw [← same p]
    exact solves.irrevocable env admitted p (n p) N (bound p) _ (decided p)
  · intro k p w out
    have a := solves.irrevocable env admitted p k (max k (n p)) (le_max_left ..) w out
    have b := solves.irrevocable env admitted p (n p) (max k (n p)) (le_max_right ..) _ (decided p)
    exact (Option.some.inj (a.symm.trans b)).trans (same p)

/-- Adjacent cells have an identical local view, also after restoring the
same constant proposal pair. -/
theorem adjacent_proposal_views (x : Proc → V) {h k : List Graph}
    (adjacent : Adjacent h k) :
    ∃ p, currentView p (proposalHistory x h) = currentView p (proposalHistory x k) := by
  have relabel (gs : List Graph) (p : Proc) :
      InputAlphabetRelabeling.view (fun _ : Unit => x .one) (fun _ : Unit => x .two)
        (graphView p gs) = currentView p (proposalHistory x gs) := by
    have unitView : graphView p gs = currentView p (proposalHistory (fun _ => ()) gs) := by
      have eq := FullViewPath.at_views gs
      cases p
      · exact congrArg Prod.fst eq
      · exact congrArg Prod.snd eq
    rw [unitView,relabel_proposalView]
    congr 2
    funext q; cases q <;> rfl
  rcases adjacent with one | two
  · refine ⟨.one,?_⟩
    rw [← relabel h .one,← relabel k .one]
    exact congrArg (InputAlphabetRelabeling.view (fun _ : Unit => x .one) (fun _ : Unit => x .two)) one
  · refine ⟨.two,?_⟩
    rw [← relabel h .two,← relabel k .two]
    exact congrArg (InputAlphabetRelabeling.view (fun _ : Unit => x .one) (fun _ : Unit => x .two)) two

/-- Points less than one round-r cell width apart have equal or adjacent
round-r histories. Boundary points are included. -/
theorem near_coordinates_adjacent (u w : Nat → Graph) (r : Nat)
    (near : |coordinate u - coordinate w| < (1/3 : ℝ)^r) :
    Adjacent (graphPrefix u r) (graphPrefix w r) := by
  have cu := coordinate_in_prefix_cell u r
  have cw := coordinate_in_prefix_cell w r
  have positive : (0 : ℝ) < 3^r := by positivity
  simp only [leftEndpoint,rightEndpoint,graphPrefix_length] at cu cw
  rw [one_div_pow] at near
  have diff := abs_lt.mp near
  have lo : (pathIndex (graphPrefix u r) : ℝ) < pathIndex (graphPrefix w r) + 2 := by
    have := (div_lt_div_iff_of_pos_right positive).mp
      (show (pathIndex (graphPrefix u r) : ℝ) / 3^r <
        ((pathIndex (graphPrefix w r) : ℝ)+2)/3^r by
          have add : ((pathIndex (graphPrefix w r) : ℝ)+2)/3^r =
              ((pathIndex (graphPrefix w r) : ℝ)+1)/3^r + 1/3^r := by rw [← add_div]; congr 1; ring
          rw [add]; linarith [cu.1,cw.2])
    exact this
  have hi : (pathIndex (graphPrefix w r) : ℝ) < pathIndex (graphPrefix u r) + 2 := by
    apply (div_lt_div_iff_of_pos_right positive).mp
    have add : ((pathIndex (graphPrefix u r) : ℝ)+2)/3^r =
        ((pathIndex (graphPrefix u r) : ℝ)+1)/3^r + 1/3^r := by rw [← add_div]; congr 1; ring
    rw [add]; linarith [cw.1,cu.2]
  have loNat : pathIndex (graphPrefix u r) < pathIndex (graphPrefix w r)+2 := by exact_mod_cast lo
  have hiNat : pathIndex (graphPrefix w r) < pathIndex (graphPrefix u r)+2 := by exact_mod_cast hi
  rcases lt_trichotomy (pathIndex (graphPrefix u r)) (pathIndex (graphPrefix w r)) with lt | eq | gt
  · exact adjacent_of_consecutive_indices _ _ (by simp) (by omega)
  · have same := pathIndex_injective (graphPrefix u r) (graphPrefix w r) (by simp) eq
    exact Or.inl (congrArg (fun h => (FullViewPath.evaluate h).one) same)
  · have reverse := adjacent_of_consecutive_indices (graphPrefix w r) (graphPrefix u r) (by simp) (by omega)
    exact reverse.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)

theorem coordinate_zero_prefix (word : Nat → Graph) (zero : coordinate word = 0) (r : Nat) :
    graphPrefix word r = List.replicate r .right := by
  have lower := (coordinate_in_prefix_cell word r).1
  rw [zero,leftEndpoint] at lower
  have index : pathIndex (graphPrefix word r) = 0 := by
    have realIndex : (pathIndex (graphPrefix word r) : ℝ) ≤ 0 :=
      by
        have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 3^(graphPrefix word r).length)).mp lower
        simpa using h
    exact_mod_cast (le_antisymm realIndex (by positivity))
  have extreme := (extreme_view_coordinates r).1
  have bounds := (actual_process_index_bounds (List.replicate r .right)).1.1
  change PaddingProjection.project (fun _ => true) (FullViewPath.evaluate (List.replicate r .right)).one = 0 at extreme
  rw [extreme] at bounds
  exact pathIndex_injective _ _ (by simp) (by omega)

theorem coordinate_one_prefix (word : Nat → Graph) (one : coordinate word = 1) (r : Nat) :
    graphPrefix word r = List.replicate r .left := by
  have upper := (coordinate_in_prefix_cell word r).2
  rw [one,rightEndpoint,graphPrefix_length] at upper
  have index : 3^r ≤ pathIndex (graphPrefix word r)+1 := by
    have realIndex := (le_div_iff₀ (by positivity : (0 : ℝ) < 3^r)).mp upper
    norm_num only [one_mul] at realIndex
    exact_mod_cast realIndex
  have extreme := (extreme_view_coordinates r).2
  have bounds := (actual_process_index_bounds (List.replicate r .left)).2.2
  change PaddingProjection.project (fun _ => true) (FullViewPath.evaluate (List.replicate r .left)).two = 3^r at extreme
  rw [extreme] at bounds
  have a := pathIndex_lt (graphPrefix word r)
  have b := pathIndex_lt (List.replicate r .left)
  simp only [graphPrefix_length,List.length_replicate] at a b
  exact pathIndex_injective _ _ (by simp) (by omega)

/-- At either geometric extreme, the nonreceiving process sees only its
own proposal, independently of the other process's input. -/
theorem extreme_proposal_view (x y : Proc → V) (p : Proc) (r : Nat)
    (own : x p = y p) :
    currentView p (proposalHistory x (List.replicate r (match p with | .one => .right | .two => .left))) =
      currentView p (proposalHistory y (List.replicate r (match p with | .one => .right | .two => .left))) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ',proposalHistory_append,proposalHistory_append]
    cases p
    all_goals change currentView _ (History.append _ _) = currentView _ (History.append _ _)
    all_goals simp only [currentView_one_append,currentView_two_append,own,ih]

/-- The eventual decision at the left/right extreme is forced to be the
proposal of the corresponding nonreceiving process. -/
theorem Solves.extreme_value {A : Set (Nat → Graph)}
    {σ : StrategyPair V V (Option V) (Option V)} (solves : Solves σ A)
    (x : Proc → V) (word : Nat → Graph) (admitted : word ∈ A) (p : Proc)
    (extreme : coordinate word = match p with | .one => 0 | .two => 1)
    (v : V) (consistent : ∀ k q w, outputAt σ (proposalEnvironment x word) k q = some w → w = v) :
    v = x p := by
  obtain ⟨u,n,decided,valid,_⟩ := solves.commonDecision (proposalEnvironment (fun _ => x p) word) admitted
  have value : u = x p := valid.elim id id
  subst u
  have same : currentView p (proposalHistory x (graphPrefix word (n+1))) =
      currentView p (proposalHistory (fun _ => x p) (graphPrefix word (n+1))) := by
    cases p
    · rw [coordinate_zero_prefix word extreme]
      exact extreme_proposal_view x (fun _ => x .one) .one (n+1) rfl
    · rw [coordinate_one_prefix word extreme]
      exact extreme_proposal_view x (fun _ => x .two) .two (n+1) rfl
  apply Eq.symm
  apply consistent n p (x p)
  have out := decided p
  rw [outputAt_view,proposalEnvironment_prefix] at out ⊢
  rw [same]
  exact out

/-- Surjectivity of the geometric image would make the eventual consensus
decision a locally constant function on the entire interval. -/
theorem Solves.image_ne_univ [Nontrivial V] {A : Set (Nat → Graph)}
    {σ : StrategyPair V V (Option V) (Option V)} (solves : Solves σ A) :
    geometricMap '' A ≠ Set.univ := by
  classical
  intro full
  obtain ⟨a,b,distinct⟩ := exists_pair_ne V
  let x : Proc → V := fun p => match p with | .one => a | .two => b
  have preimages (c : UnitInterval) : ∃ word ∈ A, geometricMap word = c := by
    have : c ∈ geometricMap '' A := by rw [full]; trivial
    exact this
  choose word admitted image using preimages
  have decisions (c : UnitInterval) := solves.commonDecision (proposalEnvironment x (word c)) (admitted c)
  choose value round decided valid consistent using decisions
  have locally : IsLocallyConstant value := by
    apply (IsLocallyConstant.iff_exists_open value).mpr
    intro c
    let ε : ℝ := (1/3 : ℝ)^(round c+1)
    refine ⟨Metric.ball c ε,Metric.isOpen_ball,Metric.mem_ball_self (by dsimp [ε]; positivity),?_⟩
    intro d near
    have distance : |coordinate (word c) - coordinate (word d)| < ε := by
      have ic : coordinate (word c) = c.val := congrArg Subtype.val (image c)
      have id : coordinate (word d) = d.val := congrArg Subtype.val (image d)
      rw [ic,id,abs_sub_comm]
      exact near
    obtain ⟨p,same⟩ := adjacent_proposal_views x (near_coordinates_adjacent _ _ (round c+1) distance)
    have out := decided c p
    rw [outputAt_view,proposalEnvironment_prefix] at out
    rw [same] at out
    exact (consistent d (round c) p (value c) (by rw [outputAt_view,proposalEnvironment_prefix]; exact out)).symm
  let zero : UnitInterval := ⟨0,by norm_num⟩
  let one : UnitInterval := ⟨1,by norm_num⟩
  have left : value zero = a := solves.extreme_value x (word zero) (admitted zero) .one
    (congrArg Subtype.val (image zero)) _ (consistent zero)
  have right : value one = b := solves.extreme_value x (word one) (admitted one) .two
    (congrArg Subtype.val (image one)) _ (consistent one)
  exact distinct (left.symm.trans ((locally.apply_eq_of_isPreconnected isPreconnected_univ
    (Set.mem_univ zero) (Set.mem_univ one)).trans right))

theorem consensus_iff_image_ne_univ [Nontrivial V] (A : Set (Nat → Graph)) :
    (∃ σ : StrategyPair V V (Option V) (Option V), Solves σ A) ↔
      geometricMap '' A ≠ Set.univ :=
  ⟨fun ⟨_,solves⟩ => solves.image_ne_univ,consensus_of_image_ne_univ A⟩

/-- Empty interior suffices for repeated eventual consensus. This uses
literal residuals and makes no regularity or bounded-time assumption. -/
theorem repeated_consensus_of_empty_interior [Nonempty V] (A : Set (Nat → Graph))
    (empty : interior (geometricMap '' A) = ∅) (h : List Graph) :
    ∃ σ : StrategyPair V V (Option V) (Option V), Solves σ (Residual A h) := by
  apply consensus_of_image_ne_univ
  intro full
  have inside : cellInterior h ⊆ geometricMap '' A := by
    intro c hc
    have cell : c.val ∈ Set.Icc (leftEndpoint h) (rightEndpoint h) := ⟨hc.1.le,hc.2.le⟩
    obtain ⟨u,pref,eq⟩ := (coordinate_image_graphPrefix h).symm ▸ cell
    let d : UnitInterval := geometricMap (OmegaWord.drop u h.length)
    have mem : d ∈ geometricMap '' Residual A h := by rw [full]; trivial
    obtain ⟨w,admitted,same⟩ := mem
    refine ⟨Characterisation.prependGraphs h w,admitted,Subtype.ext ?_⟩
    change coordinate (Characterisation.prependGraphs h w) = c.val
    apply prefixRescale_injective h
    rw [coordinate_prepend]
    have suffix := coordinate_prepend h (OmegaWord.drop u h.length)
    rw [prepend_drop_of_prefix u h pref] at suffix
    exact (congrArg Subtype.val same).trans (suffix.symm.trans (congrArg (prefixRescale h) eq))
  have sub := (cellInterior_open h).subset_interior_iff.mpr inside
  rw [empty] at sub
  exact Set.not_nonempty_empty ((cellInterior_nonempty h).mono sub)

end Characterisation.ComponentGames.Consensus
