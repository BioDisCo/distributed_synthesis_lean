/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.HistoryGames

/- The easy directions of the actual manuscript game equivalences. The
opposite directions require strategy constructions; they are not asserted. -/
namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section

variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

theorem mapClosingLayer_identity {H I₁ I₂ : Type} (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    mapClosingLayer id n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (ih s.1) rfl

omit [Fintype I₁] [Fintype I₂] [DecidablePred (· ∈ M.accept)] in
theorem component_legal_replacement (P : Position I₁ I₂ Q D) (m : Move I₁ I₂ O₁ O₂ Q D)
    (legal : Legal M step .component P m) : Legal M step .replacement P m := by
  obtain ⟨source,distributed,identity⟩ := legal
  refine ⟨source,distributed,?_⟩
  change ReplacementChecks _ _ _ _ _ _ _
  rw [identity]
  constructor
  · intro p s t same
    simpa only [mapClosingLayer_identity] using same
  · intro n s
    simp only [mapClosingLayer_identity,and_self]

omit [Fintype I₁] [Fintype I₂] [DecidablePred (· ∈ M.accept)] in
theorem bounded_legal_replacement (W : Nat) (P : Position I₁ I₂ Q D)
    (m : Move I₁ I₂ O₁ O₂ Q D) (legal : Legal M step (.bounded W) P m) :
    Legal M step .replacement P m := ⟨legal.1,legal.2.1,legal.2.2.1⟩

theorem component_winning_replacement (q₀ : Q) (χ : Q → Nat)
    (tree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D))
    (winning : Winning M step .component q₀ χ tree) :
    Winning M step .replacement q₀ χ tree :=
  ⟨fun node supported => component_legal_replacement M step _ _ (winning.1 node supported),winning.2⟩

theorem bounded_winning_replacement (W : Nat) (q₀ : Q) (χ : Q → Nat)
    (tree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D))
    (winning : Winning M step (.bounded W) q₀ χ tree) :
    Winning M step .replacement q₀ χ tree :=
  ⟨fun node supported => bounded_legal_replacement M step W _ _ (winning.1 node supported),winning.2⟩

end
end Characterisation.ComponentGames.HistoryGame
