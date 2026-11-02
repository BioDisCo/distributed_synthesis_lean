/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemExactViewRectangleClosure

/-!
# Rectangle freeness does not supply a common continuation

The exact delay-one transition is rectangle-free, but that incidence fact
alone does not justify regrouping two finite roots under one blind sender.
This file gives the smallest connected counterexample.

The three-edge Boolean path is rectangle-free.  A locally uniform raw
strategy wins at every edge by playing its left view.  Nevertheless the two
endpoint histories can be collapsed to the same finite root code while
requiring different sender choices, so they have no common continuation.
Thus a positive end-to-end regrouping theorem must retain an exact
equal-view/history witness (or prove an equivalent quotient congruence); it
cannot follow from rectangle freeness alone.
-/

namespace DistributedSynthesis

/-- The connected Boolean path with edges `(false,false)`, `(false,true)`,
and `(true,true)`. -/
def BoolPathRelation (left right : Bool) : Prop :=
  left = false ∨ right = true

/-- The three-edge path has no non-degenerate `2 × 2` rectangle. -/
theorem boolPathRelation_rectangleFree :
    RectangleFree BoolPathRelation := by
  intro left₀ left₁ right₀ right₁ h₀₀ h₀₁ h₁₀ h₁₁
  cases left₀ <;> cases left₁ <;> cases right₀ <;> cases right₁ <;>
    simp_all [BoolPathRelation]

/-- A locally uniform raw sender: its choice depends only on its own view. -/
def boolPathRawSender (leftView : Bool) : Bool :=
  leftView

/-- The toy continuation condition at an edge.  The sender must play the
choice prescribed by its left local view. -/
def BoolPathContinuationWins
    (leftView rightView choice : Bool) : Prop :=
  BoolPathRelation leftView rightView ∧ choice = leftView

/-- The raw sender wins separately at every history in the relation. -/
theorem boolPathRawSender_wins
    {leftView rightView : Bool}
    (hedge : BoolPathRelation leftView rightView) :
    BoolPathContinuationWins leftView rightView
      (boolPathRawSender leftView) := by
  exact ⟨hedge, rfl⟩

/-- A deliberately coarse finite root code, modelling the information lost
when a rationalized controller state is retained without its exact history. -/
def boolPathRootCode (_leftView _rightView : Bool) : Unit :=
  ()

/-- The endpoint histories collide at the finite root code. -/
theorem boolPath_endpoints_sameRootCode :
    boolPathRootCode false false = boolPathRootCode true true :=
  rfl

/-- Both endpoint histories are genuine edges of the connected relation. -/
theorem boolPath_endpoint_edges :
    BoolPathRelation false false ∧ BoolPathRelation true true := by
  simp [BoolPathRelation]

/-- Despite rectangle freeness, edgewise raw realizability, connectedness,
and equality of the retained finite code, the two endpoints have no common
sender continuation. -/
theorem boolPath_no_commonContinuation :
    ¬ ∃ choice,
      BoolPathContinuationWins false false choice ∧
        BoolPathContinuationWins true true choice := by
  simp [BoolPathContinuationWins]

/-- Packaged logical counterexample to the proposed implication. -/
theorem rectangleFree_rawWinning_sameCode_not_commonContinuation :
    ∃ (relation : Bool → Bool → Prop)
        (rawSender : Bool → Bool)
        (rootCode : Bool → Bool → Unit),
      RectangleFree relation ∧
      (∀ {leftView rightView}, relation leftView rightView →
        relation leftView rightView ∧
          rawSender leftView = leftView) ∧
      relation false false ∧
      relation true true ∧
      rootCode false false = rootCode true true ∧
      ¬ ∃ choice,
        (relation false false ∧ choice = false) ∧
          (relation true true ∧ choice = true) := by
  refine ⟨BoolPathRelation, boolPathRawSender, boolPathRootCode,
    boolPathRelation_rectangleFree, ?_, boolPath_endpoint_edges.1,
    boolPath_endpoint_edges.2, boolPath_endpoints_sameRootCode, ?_⟩
  · intro leftView rightView hedge
    exact ⟨hedge, rfl⟩
  · simpa [BoolPathContinuationWins] using boolPath_no_commonContinuation

end DistributedSynthesis
