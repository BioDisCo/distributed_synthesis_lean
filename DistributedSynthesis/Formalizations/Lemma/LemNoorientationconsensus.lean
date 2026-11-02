/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefViews

/-!
# No local consensus on a hidden orientation bit
-/

namespace DistributedSynthesis

universe u v x y

/-- A round record with explicitly chosen inputs, graph, and irrelevant outputs. -/
def mkGraphRound
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (inputOne : In₁) (inputTwo : In₂) (graph : Graph)
    (outputOne : Out₁) (outputTwo : Out₂) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ where
  inputOne := inputOne
  inputTwo := inputTwo
  graph := graph
  outputOne := outputOne
  outputTwo := outputTwo

/-- The two-round history used by `lem:noorientationconsensus`. -/
def twoRoundOrientationHistory
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (firstGraph : Graph)
    (x₁₀ : In₁) (x₂₀ : In₂) (x₁₁ : In₁) (x₂₁ : In₂)
    (y₁₀ : Out₁) (y₂₀ : Out₂) (y₁₁ : Out₁) (y₂₁ : Out₂) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  History.append
    (History.append History.empty (mkGraphRound x₁₀ x₂₀ firstGraph y₁₀ y₂₀))
    (mkGraphRound x₁₁ x₂₁ .right y₁₁ y₂₁)

/--
Process `1` cannot distinguish the histories `left,right` and `both,right`
with the same inputs and arbitrary outputs.
-/
theorem no_orientation_consensus_procOne_same_view
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (x₁₀ : In₁) (x₂₀ : In₂) (x₁₁ : In₁) (x₂₁ : In₂)
    (y₁₀ : Out₁) (y₂₀ : Out₂) (y₁₁ : Out₁) (y₂₁ : Out₂) :
    currentView Proc.one
        (twoRoundOrientationHistory .left x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁) =
      currentView Proc.one
        (twoRoundOrientationHistory .both x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁) := by
  simp [twoRoundOrientationHistory, mkGraphRound]

/--
Process `2` distinguishes the same two histories: its first-round self-view is
`noRecv` in the `left` history and `recv` in the `both` history, and that
previous self-view is retained after the final `right` round.
-/
theorem no_orientation_consensus_procTwo_distinguishes
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (x₁₀ : In₁) (x₂₀ : In₂) (x₁₁ : In₁) (x₂₁ : In₂)
    (y₁₀ : Out₁) (y₂₀ : Out₂) (y₁₁ : Out₁) (y₂₁ : Out₂) :
    currentView Proc.two
        (twoRoundOrientationHistory .left x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁) ≠
      currentView Proc.two
        (twoRoundOrientationHistory .both x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁) := by
  simp [twoRoundOrientationHistory, mkGraphRound]

/--
Paper-facing Lemma `lem:noorientationconsensus`: any Boolean orientation bit
that separates the two histories cannot be computed from process `1`'s local
view, hence cannot be computed by both processes.
-/
theorem no_local_consensus_on_hidden_orientation_bit
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (x₁₀ : In₁) (x₂₀ : In₂) (x₁₁ : In₁) (x₂₁ : In₂)
    (y₁₀ : Out₁) (y₂₀ : Out₂) (y₁₁ : Out₁) (y₂₁ : Out₂)
    (bit : History In₁ In₂ Graph Out₁ Out₂ -> Bool)
    (hbit :
      bit (twoRoundOrientationHistory .left x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁) ≠
        bit (twoRoundOrientationHistory .both x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)) :
    ¬ ∃ localOne : View In₁ In₂ Proc.one -> Bool,
      (localOne
          (currentView Proc.one
            (twoRoundOrientationHistory .left x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)) =
        bit (twoRoundOrientationHistory .left x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)) ∧
      (localOne
          (currentView Proc.one
            (twoRoundOrientationHistory .both x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)) =
        bit (twoRoundOrientationHistory .both x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)) := by
  intro hlocal
  rcases hlocal with ⟨localOne, hleft, hboth⟩
  have hview :=
    no_orientation_consensus_procOne_same_view
      x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁
  apply hbit
  calc
    bit (twoRoundOrientationHistory .left x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)
        = localOne
            (currentView Proc.one
              (twoRoundOrientationHistory .left x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)) := hleft.symm
    _ = localOne
            (currentView Proc.one
              (twoRoundOrientationHistory .both x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)) := by
          rw [hview]
    _ = bit (twoRoundOrientationHistory .both x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁) := hboth

end DistributedSynthesis
