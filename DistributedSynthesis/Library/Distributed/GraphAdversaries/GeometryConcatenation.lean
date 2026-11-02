/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryTopology
import DistributedSynthesis.Library.Distributed.GraphAdversaries.Undecidability.ResidualUndecidability

namespace Characterisation
open DistributedSynthesis Set

/-- The two affine identities, without truncated natural subtraction. -/
theorem pathIndex_concat (h u : List Graph) :
    (pathIndex h % 2 = 0 →
      pathIndex (h ++ u) = 3 ^ u.length * pathIndex h + pathIndex u) ∧
    (pathIndex h % 2 = 1 →
      pathIndex (h ++ u) + pathIndex u + 1 = 3 ^ u.length * (pathIndex h + 1)) := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u g ih =>
    have casesU : pathIndex u % 2 = 0 ∨ pathIndex u % 2 = 1 := by omega
    constructor
    · intro even
      have old := ih.1 even
      have parity : pathIndex (h ++ u) % 2 = pathIndex u % 2 := by
        rw [old]
        simp [Nat.add_mod, Nat.mul_mod, even]
      rw [← List.append_assoc, pathIndex_append, pathIndex_append]
      simp only [List.length_append, List.length_singleton, pow_succ]
      rcases casesU with hu | hu <;> cases g <;>
        simp [indexStep,graphDigit,parity,hu] <;> nlinarith [old]
    · intro odd
      have old := ih.2 odd
      have parity : pathIndex (h ++ u) % 2 + pathIndex u % 2 = 1 := by
        have modProduct : (3 ^ u.length * (pathIndex h + 1)) % 2 = 0 := by
          simp [Nat.mul_mod, Nat.add_mod, odd]
        omega
      rw [← List.append_assoc, pathIndex_append, pathIndex_append]
      simp only [List.length_append, List.length_singleton, pow_succ]
      rcases casesU with hu | hu
      · have hc : pathIndex (h ++ u) % 2 = 1 := by omega
        cases g <;> simp [indexStep,graphDigit,hu,hc] <;> nlinarith [old]
      · have hc : pathIndex (h ++ u) % 2 = 0 := by omega
        cases g <;> simp [indexStep,graphDigit,hu,hc] <;> nlinarith [old]

/-- `concat:pos`, in the displayed form of the manuscript. -/
theorem pathIndex_suffix (h u : List Graph) :
    pathIndex u = if pathIndex h % 2 = 0 then
      pathIndex (h ++ u) - 3 ^ u.length * pathIndex h else
      3 ^ u.length * (pathIndex h + 1) - pathIndex (h ++ u) - 1 := by
  split
  · have := (pathIndex_concat h u).1 ‹_›; omega
  · have odd : pathIndex h % 2 = 1 := by omega
    have := (pathIndex_concat h u).2 odd; omega

/-- Scaled endpoints, with reflection exchanging left and right. -/
theorem endpoints_concat (h u : List Graph) :
    (pathIndex h % 2 = 0 →
      (3 : ℝ) ^ h.length * leftEndpoint (h ++ u) - pathIndex h = leftEndpoint u ∧
      (3 : ℝ) ^ h.length * rightEndpoint (h ++ u) - pathIndex h = rightEndpoint u) ∧
    (pathIndex h % 2 = 1 →
      (pathIndex h : ℝ) + 1 - 3 ^ h.length * rightEndpoint (h ++ u) = leftEndpoint u ∧
      (pathIndex h : ℝ) + 1 - 3 ^ h.length * leftEndpoint (h ++ u) = rightEndpoint u) := by
  constructor
  · intro even
    have index : (pathIndex (h ++ u) : ℝ) = 3 ^ u.length * pathIndex h + pathIndex u := by
      exact_mod_cast (pathIndex_concat h u).1 even
    constructor <;> simp only [leftEndpoint, rightEndpoint, List.length_append, pow_add]
    all_goals field_simp; nlinarith [index]
  · intro odd
    have index : (pathIndex (h ++ u) : ℝ) + pathIndex u + 1 =
        3 ^ u.length * ((pathIndex h : ℝ) + 1) := by
      exact_mod_cast (pathIndex_concat h u).2 odd
    constructor <;> simp only [leftEndpoint, rightEndpoint, List.length_append, pow_add]
    all_goals field_simp; nlinarith [index]

/-- The affine rescaling displayed in the three concatenation lemmas. -/
def prefixRescale (h : List Graph) (x : ℝ) : ℝ :=
  if pathIndex h % 2 = 0 then (3 : ℝ) ^ h.length * x - pathIndex h
  else (pathIndex h : ℝ) + 1 - 3 ^ h.length * x

/-- `concat:interval`: exact affine equality, not just inclusion. -/
theorem prefixRescale_cell (h u : List Graph) :
    prefixRescale h '' Icc (leftEndpoint (h ++ u)) (rightEndpoint (h ++ u)) =
      Icc (leftEndpoint u) (rightEndpoint u) := by
  have pos : (0 : ℝ) < 3 ^ h.length := by positivity
  ext y
  by_cases even : pathIndex h % 2 = 0
  · obtain ⟨lo, hi⟩ := (endpoints_concat h u).1 even
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [prefixRescale, if_pos even, mem_Icc]
      constructor <;> nlinarith [hx.1,hx.2]
    · intro hy
      refine ⟨(y + pathIndex h) / 3 ^ h.length, ?_, ?_⟩
      · constructor
        · apply (le_div_iff₀ pos).mpr
          nlinarith [hy.1]
        · apply (div_le_iff₀ pos).mpr
          nlinarith [hy.2]
      · simp only [prefixRescale, if_pos even]
        field_simp; ring
  · have odd : pathIndex h % 2 = 1 := by omega
    obtain ⟨lo, hi⟩ := (endpoints_concat h u).2 odd
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [prefixRescale, if_neg even, mem_Icc]
      constructor <;> nlinarith [hx.1,hx.2]
    · intro hy
      refine ⟨((pathIndex h : ℝ) + 1 - y) / 3 ^ h.length, ?_, ?_⟩
      · constructor
        · apply (le_div_iff₀ pos).mpr
          nlinarith [hy.2]
        · apply (div_le_iff₀ pos).mpr
          nlinarith [hy.1]
      · simp only [prefixRescale, if_neg even]
        field_simp; ring

/-- Prefixing an infinite word performs the same reflected affine change. -/
theorem coordinate_prepend (h : List Graph) (word : Nat → Graph) :
    prefixRescale h (coordinate (prependGraphs h word)) = coordinate word := by
  symm
  apply coordinate_unique
  intro n
  rw [← prefixRescale_cell h (graphPrefix word n)]
  refine ⟨coordinate (prependGraphs h word), ?_, rfl⟩
  have inside := coordinate_in_prefix_cell (prependGraphs h word) (h.length + n)
  rw [graphPrefix_split, prependGraphs_prefix, prependGraphs_drop] at inside
  exact inside

/-- `concat:pi`, with the interval points coerced to real coordinates. -/
theorem coordinate_residual_image (A : Set (Nat → Graph)) (h : List Graph) :
    coordinate '' Residual A h = prefixRescale h ''
      (coordinate '' (A ∩ {word | graphPrefix word h.length = h})) := by
  ext z
  constructor
  · rintro ⟨word, admitted, rfl⟩
    exact ⟨coordinate (prependGraphs h word),
      ⟨prependGraphs h word, ⟨admitted, prependGraphs_prefix h word⟩, rfl⟩,
      coordinate_prepend h word⟩
  · rintro ⟨_, ⟨word, ⟨admitted, pref⟩, rfl⟩, rfl⟩
    refine ⟨OmegaWord.drop word h.length, ?_, ?_⟩
    · change prependGraphs h (OmegaWord.drop word h.length) ∈ A
      rw [prepend_drop_of_prefix word h pref]
      exact admitted
    · have eq := coordinate_prepend h (OmegaWord.drop word h.length)
      rw [prepend_drop_of_prefix word h pref] at eq
      exact eq.symm

/-- Reflected rescaling is injective in both orientations. -/
theorem prefixRescale_injective (h : List Graph) : Function.Injective (prefixRescale h) := by
  have positive : (0 : ℝ) < 3 ^ h.length := by positivity
  intro x y same
  unfold prefixRescale at same
  split_ifs at same <;> nlinarith

/-- The entire closed cell, including both endpoints, is the image of its
prefix cylinder. -/
theorem coordinate_image_graphPrefix (h : List Graph) :
    coordinate '' {word | graphPrefix word h.length = h} =
      Icc (leftEndpoint h) (rightEndpoint h) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨word, pref, rfl⟩
    exact coordinate_in_cell_of_prefix word h pref
  · intro x hx
    have scaled : prefixRescale h x ∈ Icc (0 : ℝ) 1 := by
      have member : prefixRescale h x ∈ prefixRescale h ''
          Icc (leftEndpoint (h ++ [])) (rightEndpoint (h ++ [])) :=
        ⟨x, by simpa using hx, rfl⟩
      rw [prefixRescale_cell] at member
      simpa [leftEndpoint, rightEndpoint, pathIndex] using member
    obtain ⟨word, eq⟩ := geometricMap_surjective ⟨prefixRescale h x, scaled⟩
    refine ⟨prependGraphs h word, prependGraphs_prefix h word, ?_⟩
    apply prefixRescale_injective h
    rw [coordinate_prepend]
    exact congrArg Subtype.val eq

end Characterisation
