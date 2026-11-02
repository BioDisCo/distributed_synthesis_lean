/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenActiveLineagePersistence

/-!
# Active pivots from provenance-valid indexed codes

The persistent-lineage argument needs an active, row-functional, reflexive
pivot at every proof-side query.  For a provenance-valid code, the last two
properties are automatic once the pivot lineage is active:

* finite validity supplies row-functionality; and
* the semantic representative carried by provenance validity identifies the
  stored pattern with literal equality of the pivot's old opposite view.

Thus the concrete recut construction only has to select an active lineage.
The selector is proof data and is never exposed to either process.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

/-! ## Reflexivity of the semantic patterns on active slots -/

omit [Fintype I] [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- An active right semantic slot is related to itself by the exact old-view
equality pattern. -/
theorem ProfiledOpenIndexedRightSemanticShadow.pattern_self_eq_true_of_active
    (shadow : ProfiledOpenIndexedRightSemanticShadow A strategy hwin basis
      (I := I))
    (pivot : IndexedLineageCandidate I)
    (hactive : shadow.slots A strategy hwin basis pivot.1 ≠ none) :
    shadow.pattern A strategy hwin basis pivot pivot = true := by
  classical
  cases shadow with
  | none =>
      simp [ProfiledOpenIndexedRightSemanticShadow.slots] at hactive
  | some lane =>
      cases hmember : lane.memberAt pivot.1 with
      | none =>
          simp [ProfiledOpenIndexedRightSemanticShadow.slots, hmember] at hactive
      | some member =>
          simp [ProfiledOpenIndexedRightSemanticShadow.pattern, hmember,
            procOneEntryOppositeViewPattern]

omit [Fintype I] [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left semantic mirror. -/
theorem ProfiledOpenIndexedLeftSemanticShadow.pattern_self_eq_true_of_active
    (shadow : ProfiledOpenIndexedLeftSemanticShadow A strategy hwin basis
      (I := I))
    (pivot : IndexedLineageCandidate I)
    (hactive : shadow.slots A strategy hwin basis pivot.1 ≠ none) :
    shadow.pattern A strategy hwin basis pivot pivot = true := by
  classical
  cases shadow with
  | none =>
      simp [ProfiledOpenIndexedLeftSemanticShadow.slots] at hactive
  | some lane =>
      cases hmember : lane.memberAt pivot.1 with
      | none =>
          simp [ProfiledOpenIndexedLeftSemanticShadow.slots, hmember] at hactive
      | some member =>
          simp [ProfiledOpenIndexedLeftSemanticShadow.pattern, hmember,
            procTwoEntryOppositeViewPattern]

/-! ## Provenance-valid public codes -/

section
omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂]

/-- On a provenance-valid public node, activity of the selected right pivot
is the only additional premise needed by the persistence theorem. -/
theorem profiledOpenIndexedProvenanceValid_activeReflexiveRightPivot
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hvalid : ProfiledOpenIndexedProvenanceValid A strategy hwin basis
      code move)
    (hactive : code.rightSlots direction.rightPivot.1 ≠ none) :
    ProfiledOpenIndexedActiveReflexivePivot A code .right direction := by
  rcases hvalid with ⟨hfinite, point, hcode, hmove⟩
  refine ⟨hactive, hfinite.2.2.1 direction.rightPivot, ?_⟩
  have hactive' :
      point.state.right.slots A strategy hwin basis
          direction.rightPivot.1 ≠ none := by
    change
      (point.state.code A strategy hwin basis).rightSlots
          direction.rightPivot.1 ≠ none
    rw [hcode]
    exact hactive
  have hreflexive :=
    ProfiledOpenIndexedRightSemanticShadow.pattern_self_eq_true_of_active
      A strategy hwin basis point.state.right direction.rightPivot hactive'
  change
    (point.state.code A strategy hwin basis).rightPattern
        direction.rightPivot direction.rightPivot = true at hreflexive
  rw [hcode] at hreflexive
  exact hreflexive

/-- Left provenance-valid mirror. -/
theorem profiledOpenIndexedProvenanceValid_activeReflexiveLeftPivot
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hvalid : ProfiledOpenIndexedProvenanceValid A strategy hwin basis
      code move)
    (hactive : code.leftSlots direction.leftPivot.1 ≠ none) :
    ProfiledOpenIndexedActiveReflexivePivot A code .left direction := by
  rcases hvalid with ⟨hfinite, point, hcode, hmove⟩
  refine ⟨hactive, hfinite.2.2.2 direction.leftPivot, ?_⟩
  have hactive' :
      point.state.left.slots A strategy hwin basis
          direction.leftPivot.1 ≠ none := by
    change
      (point.state.code A strategy hwin basis).leftSlots
          direction.leftPivot.1 ≠ none
    rw [hcode]
    exact hactive
  have hreflexive :=
    ProfiledOpenIndexedLeftSemanticShadow.pattern_self_eq_true_of_active
      A strategy hwin basis point.state.left direction.leftPivot hactive'
  change
    (point.state.code A strategy hwin basis).leftPattern
        direction.leftPivot direction.leftPivot = true at hreflexive
  rw [hcode] at hreflexive
  exact hreflexive

/-- Side-generic provenance bridge. -/
theorem profiledOpenIndexedProvenanceValid_activeReflexivePivot
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (side : IndexedLineageSide)
    (hvalid : ProfiledOpenIndexedProvenanceValid A strategy hwin basis
      code move)
    (hactive : match side with
      | .right => code.rightSlots direction.rightPivot.1 ≠ none
      | .left => code.leftSlots direction.leftPivot.1 ≠ none) :
    ProfiledOpenIndexedActiveReflexivePivot A code side direction := by
  cases side with
  | right =>
      exact profiledOpenIndexedProvenanceValid_activeReflexiveRightPivot A
        strategy hwin basis code move direction hvalid hactive
  | left =>
      exact profiledOpenIndexedProvenanceValid_activeReflexiveLeftPivot A
        strategy hwin basis code move direction hvalid hactive

/-- The form consumed by the installed rational policy: realizability already
contains provenance validity of the current `(code, move)`. -/
theorem
    profiledOpenIndexedProvenanceCodePolicyMoveRealizesAt_activeReflexivePivot
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (state : ProfiledOpenIndexedProvenanceCodePolicyState A strategy hwin basis
      initialCode)
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (side : IndexedLineageSide)
    (hmove : ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy
      hwin basis initialCode policy state move)
    (hactive : match side with
      | .right => state.1.rightSlots direction.rightPivot.1 ≠ none
      | .left => state.1.leftSlots direction.leftPivot.1 ≠ none) :
    ProfiledOpenIndexedActiveReflexivePivot A state.1 side direction :=
  profiledOpenIndexedProvenanceValid_activeReflexivePivot A strategy hwin basis
    state.1 move direction side hmove.1 hactive

end

end

end DetParityAutomaton

end DistributedSynthesis
