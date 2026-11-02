/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryCoding
import DistributedSynthesis.Library.Automata.PrefixHoles

/-! Closed subdivision cells, their nesting, and the location of infinite
coordinates. Interior points determine the finite prefix; endpoints need not. -/

namespace Characterisation

open DistributedSynthesis Set

noncomputable def rightEndpoint (h : List Graph) : ℝ :=
  ((pathIndex h : ℝ) + 1) / (3 : ℝ) ^ h.length

@[simp] theorem graphPrefix_length (x : Nat → Graph) (n : Nat) :
    (graphPrefix x n).length = n := by simp [graphPrefix]

@[simp] theorem graphPrefix_succ (x : Nat → Graph) (n : Nat) :
    graphPrefix x (n + 1) = graphPrefix x n ++ [x n] := by
  simpa [graphPrefix] using List.ofFn_succ' (fun i : Fin (n + 1) => x i)

theorem endpoints_strict (h : List Graph) : leftEndpoint h < rightEndpoint h := by
  unfold leftEndpoint rightEndpoint
  apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
  linarith

theorem rightEndpoint_le_one (h : List Graph) : rightEndpoint h ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℝ) < 3 ^ h.length)).mpr
  exact_mod_cast (pathIndex_lt h)

theorem rightEndpoint_append_antitone (h : List Graph) (g : Graph) :
    rightEndpoint (h ++ [g]) ≤ rightEndpoint h := by
  have positive : (0 : ℝ) < 3 ^ h.length := by positivity
  have hb : (indexStep (pathIndex h) g : ℝ) + 1 ≤ 3 * pathIndex h + 3 := by
    exact_mod_cast (indexStep_bounds (pathIndex h) g).2
  simp only [rightEndpoint, pathIndex_append, List.length_append,
    List.length_singleton, pow_succ]
  apply (div_le_div_iff₀ (by positivity) positive).mpr
  nlinarith

theorem endpoints_append (h u : List Graph) :
    leftEndpoint h ≤ leftEndpoint (h ++ u) ∧
      rightEndpoint (h ++ u) ≤ rightEndpoint h := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u g ih =>
    rw [← List.append_assoc]
    exact ⟨ih.1.trans (leftEndpoint_append_mono _ _),
      (rightEndpoint_append_antitone _ _).trans ih.2⟩

theorem prefix_left_monotone (x : Nat → Graph) :
    Monotone (fun n => leftEndpoint (graphPrefix x n)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [graphPrefix_succ]
  exact leftEndpoint_append_mono _ _

theorem prefix_right_antitone (x : Nat → Graph) :
    Antitone (fun n => rightEndpoint (graphPrefix x n)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [graphPrefix_succ]
  exact rightEndpoint_append_antitone _ _

theorem coordinate_in_prefix_cell (x : Nat → Graph) (n : Nat) :
    leftEndpoint (graphPrefix x n) ≤ coordinate x ∧
      coordinate x ≤ rightEndpoint (graphPrefix x n) := by
  have bounded : BddAbove (Set.range (fun k => leftEndpoint (graphPrefix x k))) :=
    ⟨1, by rintro y ⟨k, rfl⟩; exact (leftEndpoint_bounds _).2⟩
  refine ⟨le_csSup bounded (Set.mem_range_self n), ?_⟩
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨k, rfl⟩
  rcases le_total k n with before | after
  · exact (prefix_left_monotone x before).trans (endpoints_strict _).le
  · exact (endpoints_strict _).le.trans (prefix_right_antitone x after)

/-- An infinite coordinate in the open interior of a finite cell has that
prefix. No injectivity of the infinite coordinate map is asserted. -/
theorem interior_cell_forces_prefix (x : Nat → Graph) (h : List Graph)
    (inside : coordinate x ∈ Ioo (leftEndpoint h) (rightEndpoint h)) :
    graphPrefix x h.length = h := by
  let k := graphPrefix x h.length
  have sameLength : k.length = h.length := graphPrefix_length _ _
  have ownCell := coordinate_in_prefix_cell x h.length
  have positive : (0 : ℝ) < 3 ^ h.length := by positivity
  have hleft : (pathIndex h : ℝ) < coordinate x * 3 ^ h.length :=
    (div_lt_iff₀ positive).mp inside.1
  have hright : coordinate x * 3 ^ h.length < (pathIndex h : ℝ) + 1 :=
    (lt_div_iff₀ positive).mp inside.2
  have kleft : (pathIndex k : ℝ) ≤ coordinate x * 3 ^ h.length := by
    apply (div_le_iff₀ positive).mp
    simpa only [leftEndpoint, graphPrefix_length] using ownCell.1
  have kright : coordinate x * 3 ^ h.length ≤ (pathIndex k : ℝ) + 1 := by
    apply (le_div_iff₀ positive).mp
    simpa only [rightEndpoint, graphPrefix_length] using ownCell.2
  have hk : pathIndex h < pathIndex k + 1 := by exact_mod_cast hleft.trans_le kright
  have kh : pathIndex k < pathIndex h + 1 := by exact_mod_cast kleft.trans_lt hright
  exact pathIndex_injective k h sameLength (by omega)

def LivePrefix (A : Set (Nat → Graph)) (h : List Graph) : Prop :=
  ∃ x ∈ A, graphPrefix x h.length = h

def cellInterior (h : List Graph) : Set UnitInterval :=
  {z | leftEndpoint h < z.val ∧ z.val < rightEndpoint h}

theorem cellInterior_open (h : List Graph) : IsOpen (cellInterior h) :=
  isOpen_Ioo.preimage continuous_subtype_val

theorem cellInterior_nonempty (h : List Graph) : (cellInterior h).Nonempty := by
  let m := (leftEndpoint h + rightEndpoint h) / 2
  have strict := endpoints_strict h
  have lo := (leftEndpoint_bounds h).1
  have hi := rightEndpoint_le_one h
  exact ⟨⟨m, by dsimp [m]; constructor <;> linarith⟩,
    by change leftEndpoint h < m ∧ m < rightEndpoint h; dsimp [m]; constructor <;> linarith⟩

theorem missing_prefix_gives_hole (A : Set (Nat → Graph)) (h : List Graph)
    (missing : ¬ LivePrefix A h) : Disjoint (cellInterior h) (geometricMap '' A) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨x, hx, rfl⟩
  exact missing ⟨x, hx, interior_cell_forces_prefix x h hz⟩

end Characterisation
