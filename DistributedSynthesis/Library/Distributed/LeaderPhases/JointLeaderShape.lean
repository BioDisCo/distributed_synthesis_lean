/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.FiniteLeaderGroups

/-! The full boundary family need not share a leader view. Its observation
matrix changes after the first common rightward round: the receiver learns
the initial leader view. Later common rightward rounds preserve that matrix. -/
namespace Characterisation
open DistributedSynthesis

def rightRefinedShape {H : Type} (shape : InputShape H) : InputShape H
  | .one => shape .one
  | .two => fun h k => shape .two h k && shape .one h k

theorem rightRefinedShape_idempotent {H : Type} (shape : InputShape H) :
    rightRefinedShape (rightRefinedShape shape) = rightRefinedShape shape := by
  funext p h k
  cases p <;> simp [rightRefinedShape]

def jointLeaderShape {H : Type} (shape : InputShape H) (initial : Bool) : InputShape H :=
  if initial then shape else rightRefinedShape shape

theorem rightRefinedShape_exact {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape) (r : I₂ × I₁) :
    RepresentsInputShape (fun h => past h ++ [⟨r.2,r.1,.right,(),()⟩]) (rightRefinedShape shape) := by
  intro p h k
  cases p
  · change shape .one h k = true ↔ currentView .one (History.append _ _) = currentView .one (History.append _ _)
    rw [currentView_one_append,currentView_one_append]
    simpa using rep .one h k
  · change (shape .two h k && shape .one h k) = true ↔
      currentView .two (History.append _ _) = currentView .two (History.append _ _)
    rw [currentView_two_append,currentView_two_append]
    simp [Proc.other, ← rep .one h k, ← rep .two h k]

/-- No common initial leader view is assumed. The bit is true exactly at
the original boundary, and is switched off after one physical round. -/
theorem jointLeaderShape_exact {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape) (node : List (I₂ × I₁)) :
    RepresentsInputShape (rollingSourceHistory past node) (jointLeaderShape shape (decide (node = []))) := by
  induction node using List.reverseRecOn with
  | nil =>
    intro p h k
    simpa [rollingSourceHistory,rightInputHistory,jointLeaderShape] using rep p h k
  | append_singleton node r ih =>
    have next := rightRefinedShape_exact (rollingSourceHistory past node) _ ih r
    have shapes : rightRefinedShape (jointLeaderShape shape (decide (node = []))) = rightRefinedShape shape := by
      by_cases empty : node = [] <;> simp [jointLeaderShape,empty,rightRefinedShape_idempotent]
    rw [shapes] at next
    intro p h k
    simpa [rollingSourceHistory_snoc,jointLeaderShape] using next p h k

end Characterisation
