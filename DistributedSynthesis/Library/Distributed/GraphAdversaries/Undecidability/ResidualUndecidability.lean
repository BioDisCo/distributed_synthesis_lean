/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.RegularPrefixes
import DistributedSynthesis.Library.Distributed.GraphAdversaries.Undecidability.FullPrefixUndecidability

/-! If geometric holes fail, a residual adversary below a fixed finite prefix
is prefix-dense and has undecidable encoded LTL synthesis. Transporting this
back to the original adversary still requires a guarded-restart reduction. -/

namespace Characterisation

open DistributedSynthesis

def Residual (A : Set (Nat → Graph)) (h : List Graph) : Set (Nat → Graph) :=
  {x | prependGraphs h x ∈ A}

theorem graphPrefix_split (x : Nat → Graph) (m n : Nat) :
    graphPrefix x (m + n) = graphPrefix x m ++ graphPrefix (OmegaWord.drop x m) n := by
  simp [graphPrefix, List.ofFn_add, OmegaWord.drop]

theorem prepend_drop_of_prefix (x : Nat → Graph) (h : List Graph)
    (hp : graphPrefix x h.length = h) : prependGraphs h (OmegaWord.drop x h.length) = x := by
  funext k
  by_cases before : k < h.length
  · have eq := congrArg (fun l => l.getD k Graph.both) hp
    have eq' : x k = h.getD k Graph.both := by simpa [graphPrefix, before] using eq
    simpa [prependGraphs, before] using eq'.symm
  · simp [prependGraphs, before, OmegaWord.drop, Nat.add_sub_of_le (by omega : h.length ≤ k)]

theorem full_cone_residual_prefixDense (A : Set (Nat → Graph)) (h : List Graph)
    (cone : FullCone (LivePrefix A) h) : PrefixDense (Residual A h) := by
  intro x n
  obtain ⟨z, hz, hp⟩ := cone (graphPrefix x n)
  have prefixEq : graphPrefix z (h.length + n) = h ++ graphPrefix x n := by
    simpa only [List.length_append, graphPrefix_length] using hp
  have smallEq : graphPrefix z h.length = h := by
    have eq := congrArg (List.take h.length) prefixEq
    rw [graphPrefix_take _ _ _ (by omega)] at eq
    simpa using eq
  have tailEq : graphPrefix (OmegaWord.drop z h.length) n = graphPrefix x n := by
    rw [graphPrefix_split, smallEq] at prefixEq
    exact List.append_cancel_left prefixEq
  refine ⟨OmegaWord.drop z h.length, ?_, ?_⟩
  · change prependGraphs h (OmegaWord.drop z h.length) ∈ A
    rw [prepend_drop_of_prefix z h smallEq]
    exact hz
  · intro t ht
    have eq := congrArg (fun l => l.getD t Graph.both) tailEq
    simpa [graphPrefix, ht] using eq.symm

theorem no_geometric_holes_has_prefixDense_residual (A : Set (Nat → Graph))
    (noHoles : ¬ GeometricHoles A) :
    ∃ h, PrefixDense (Residual A h) := by
  classical
  have cone : ∃ h, FullCone (LivePrefix A) h := by
    by_contra none
    exact noHoles ((geometric_holes_iff_no_full_cone A).mpr none)
  obtain ⟨h, hh⟩ := cone
  exact ⟨h, full_cone_residual_prefixDense A h hh⟩

/-- An unconditional negative endpoint for a residual environment. This
theorem does not silently identify residual synthesis with synthesis over A. -/
theorem no_geometric_holes_has_undecidable_residual (A : Set (Nat → Graph))
    (noHoles : ¬ GeometricHoles A) :
    ∃ h, ¬ ComputablePred (RestrictedEncodedRealizable (Residual A h)) := by
  obtain ⟨h, dense⟩ := no_geometric_holes_has_prefixDense_residual A noHoles
  exact ⟨h, prefixDense_encoded_undecidable _ dense⟩

end Characterisation
