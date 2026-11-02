/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Tactic
import DistributedSynthesis.Formalizations.Definition.DefPathSummary
import DistributedSynthesis.Formalizations.Lemma.LemBoundedendpointpullback

/-!
# Endpoint windows under three-edge path expansion
-/

namespace DistributedSynthesis

universe u v

/-- Expand each old path edge into its finite successor block. -/
def expandPath
    {OldEdge : Type u} {NewEdge : Type v}
    (block : OldEdge -> List NewEdge)
    (path : List OldEdge) :
    List NewEdge :=
  path.flatMap block

/-- If every old edge expands to three successor edges, the expanded length triples. -/
theorem length_expandPath
    {OldEdge : Type u} {NewEdge : Type v}
    (block : OldEdge -> List NewEdge)
    (hlen : ∀ edge, (block edge).length = 3)
    (path : List OldEdge) :
    (expandPath block path).length = 3 * path.length := by
  unfold expandPath
  induction path with
  | nil =>
      simp
  | cons edge rest ih =>
      simp [hlen, ih]
      omega

/--
Taking the first `c` successor edges after a three-edge expansion only needs
the first `k` old edges, provided `c ≤ 3*k`.
-/
theorem expanded_take_eq_take_old_window
    {OldEdge : Type u} {NewEdge : Type v}
    (block : OldEdge -> List NewEdge)
    (hlen : ∀ edge, (block edge).length = 3)
    (path : List OldEdge)
    {c k : Nat}
    (hc : c ≤ 3 * k) :
    (expandPath block path).take c =
      (expandPath block (path.take k)).take c := by
  conv_lhs => rw [← List.take_append_drop k path]
  rw [expandPath, List.flatMap_append]
  change
    List.take c
        (List.flatMap block (List.take k path) ++
          List.flatMap block (List.drop k path)) =
      List.take c (List.flatMap block (List.take k path))
  rw [List.take_eq_left_iff]
  by_cases hk : k ≤ path.length
  · right
    have hlen_take := length_expandPath block hlen (path.take k)
    unfold expandPath at hlen_take
    rw [hlen_take]
    have ht : (path.take k).length = k := by
      simp [hk]
    omega
  · left
    have hle : path.length ≤ k := by
      omega
    simp [List.drop_eq_nil_of_le hle]

/-- The bound `β(c)` covers at least the old edges needed for `c` expanded edges. -/
theorem endpointPullbackBound_triple_ge (c : Nat) :
    c ≤ 3 * endpointPullbackBound c := by
  unfold endpointPullbackBound
  omega

/--
The prefix endpoint window of a three-edge expansion is determined by the
prefix endpoint window of radius `β(c)` in the old path.
-/
theorem expanded_prefix_depends_on_endpoint_window
    {OldEdge : Type u} {NewEdge : Type v}
    (block : OldEdge -> List NewEdge)
    (hlen : ∀ edge, (block edge).length = 3)
    (path : List OldEdge)
    (c : Nat) :
    prefixAtMost c (expandPath block path) =
      prefixAtMost c
        (expandPath block (prefixAtMost (endpointPullbackBound c) path)) := by
  unfold prefixAtMost
  exact expanded_take_eq_take_old_window block hlen path (endpointPullbackBound_triple_ge c)

/-- A suffix window is the reverse of the corresponding prefix window of the reversed path. -/
theorem suffix_eq_reverse_prefix_reverse
    {Edge : Type u}
    (c : Nat)
    (path : List Edge) :
    suffixAtMost c path = (prefixAtMost c path.reverse).reverse := by
  unfold suffixAtMost prefixAtMost
  rw [List.take_reverse, List.reverse_reverse]

/-- Reversing an expanded path reverses the old path and each successor block. -/
theorem reverse_expandPath
    {OldEdge : Type u} {NewEdge : Type v}
    (block : OldEdge -> List NewEdge)
    (path : List OldEdge) :
    (expandPath block path).reverse =
      expandPath (fun edge => (block edge).reverse) path.reverse := by
  unfold expandPath
  induction path with
  | nil =>
      simp
  | cons edge rest ih =>
      simp [ih]

/--
The suffix endpoint window of a three-edge expansion is determined by the
suffix endpoint window of radius `β(c)` in the old path.
-/
theorem expanded_suffix_depends_on_endpoint_window
    {OldEdge : Type u} {NewEdge : Type v}
    (block : OldEdge -> List NewEdge)
    (hlen : ∀ edge, (block edge).length = 3)
    (path : List OldEdge)
    (c : Nat) :
    suffixAtMost c (expandPath block path) =
      suffixAtMost c
        (expandPath block (suffixAtMost (endpointPullbackBound c) path)) := by
  rw [suffix_eq_reverse_prefix_reverse, suffix_eq_reverse_prefix_reverse]
  rw [reverse_expandPath block path]
  rw [reverse_expandPath block (suffixAtMost (endpointPullbackBound c) path)]
  rw [expanded_prefix_depends_on_endpoint_window (fun edge => (block edge).reverse)]
  · congr 2
    rw [suffix_eq_reverse_prefix_reverse, List.reverse_reverse]
  · intro edge
    simp [hlen edge]

/--
Lemma `lem:endpointwindowpreimage`: if two old paths have the same
`β(c)`-prefix and `β(c)`-suffix, then every three-edge expansion gives the
same length-`c` endpoint windows.
-/
theorem endpoint_windows_pull_back_to_endpoint_windows
    {OldEdge : Type u} {NewEdge : Type v}
    (block : OldEdge -> List NewEdge)
    (hlen : ∀ edge, (block edge).length = 3)
    (old₁ old₂ : List OldEdge)
    (c : Nat)
    (hpref :
      prefixAtMost (endpointPullbackBound c) old₁ =
        prefixAtMost (endpointPullbackBound c) old₂)
    (hsuff :
      suffixAtMost (endpointPullbackBound c) old₁ =
        suffixAtMost (endpointPullbackBound c) old₂) :
    prefixAtMost c (expandPath block old₁) =
        prefixAtMost c (expandPath block old₂) ∧
      suffixAtMost c (expandPath block old₁) =
        suffixAtMost c (expandPath block old₂) := by
  constructor
  · rw [expanded_prefix_depends_on_endpoint_window block hlen old₁ c]
    rw [expanded_prefix_depends_on_endpoint_window block hlen old₂ c]
    rw [hpref]
  · rw [expanded_suffix_depends_on_endpoint_window block hlen old₁ c]
    rw [expanded_suffix_depends_on_endpoint_window block hlen old₂ c]
    rw [hsuff]

end DistributedSynthesis
