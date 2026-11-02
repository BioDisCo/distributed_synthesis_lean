/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RollingLeaderReadback

/-! Align concrete histories with the input-tree nodes of the carried
closing banks. Roots are compared by their histories, never by assuming
that a process can observe the root index. -/
namespace Characterisation
open DistributedSynthesis

@[simp] theorem rollingSourceHistory_length {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (node : List (I₂ × I₁)) (h : H) :
    List.length (rollingSourceHistory past node h) = List.length (past h) + node.length := by
  simp [rollingSourceHistory,rightInputHistory]

theorem rightInputHistory_injective {I₁ I₂ : Type} :
    Function.Injective (@rightInputHistory I₁ I₂) := by
  apply Function.Injective.list_map
  intro r s same
  exact Prod.ext (congrArg RoundRecord.inputTwo same) (congrArg RoundRecord.inputOne same)

/-- Taking an absolute-depth prefix of a one-way source takes the
corresponding prefix of its pair-input word. -/
theorem rollingSourceHistory_take {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (word : List (I₂ × I₁)) (h : H) (n : Nat) :
    (rollingSourceHistory past word h).take (L+n) =
      rollingSourceHistory past (word.take n) h := by
  unfold rollingSourceHistory
  rw [List.take_append,List.take_of_length_le (by rw [depth]; omega),depth,
    Nat.add_sub_cancel_left]
  simp only [rightInputHistory,List.map_take]

/-- Recovering an earlier source determines its input-tree prefix and
its initial history, even if several root indices represent that history. -/
theorem rollingSourceHistory_prefix_coordinates {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (node word : List (I₂ × I₁)) (h k : H)
    (same : rollingSourceHistory past node h =
      (rollingSourceHistory past word k).take (List.length (rollingSourceHistory past node h))) :
    past h = past k ∧ node = word.take node.length := by
  rw [rollingSourceHistory_length,depth,rollingSourceHistory_take past L depth] at same
  have parts := List.append_inj same ((depth h).trans (depth k).symm)
  exact ⟨parts.1,rightInputHistory_injective parts.2⟩

/-- Equal receiver views at a common final round align the earlier source
with a prefix of the later input-tree node. Perfect recall first projects
both views to the earlier absolute cut. -/
theorem receiver_windows_source_alignment {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (leaders : ∀ h k, currentView .one (past h) = currentView .one (past k))
    (node word : List (I₂ × I₁)) (h k : H)
    (u v : EnvHistory I₁ I₂) (ordered : node.length ≤ word.length)
    (same : currentView .two (rollingSourceHistory past node h ++ u) =
      currentView .two (rollingSourceHistory past word k ++ v)) :
    past h = past k ∧ node = word.take node.length := by
  have old := equal_currentView_take .two _ _ same (L+node.length)
    (by simp only [List.length_append,rollingSourceHistory_length,depth]; omega)
  have firstCut : (rollingSourceHistory past node h ++ u).take (L+node.length) =
      rollingSourceHistory past node h := by
    rw [← depth h,← rollingSourceHistory_length,List.take_left]
  have secondCut : (rollingSourceHistory past word k ++ v).take (L+node.length) =
      rollingSourceHistory past (word.take node.length) k := by
    rw [List.take_append_of_le_length (by rw [rollingSourceHistory_length,depth]; omega),
      rollingSourceHistory_take past L depth]
  rw [firstCut,secondCut] at old
  have histories := rollingSourceHistory_two_identifies past L depth leaders _ _ h k old
  have parts := List.append_inj histories ((depth h).trans (depth k).symm)
  exact ⟨parts.1,rightInputHistory_injective parts.2⟩

end Characterisation
