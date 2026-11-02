/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedSurvivorHandoff

/-!
# Total correlated semantic successor

The two literal handoffs are combined into one total semantic successor.
Each nonempty normalized survivor family is reified by its correlated
handoff; an empty family becomes an inactive semantic lane.  The resulting
semantic state's finite code is exactly the source-free public `Next`.
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

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

/-- Chosen literal left-to-right handoff for a nonempty survivor family. -/
noncomputable def profiledOpenIndexedChosenLeftToRightHandoff
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hleft : state.left = some lane)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hsurvivor : Nonempty
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    ProfiledOpenIndexedLeftToRightSemanticHandoff A strategy hwin basis
      state lane hleft direction :=
  Classical.choice (exists_profiledOpenIndexedLeftToRightSemanticHandoff A
    strategy hwin basis state lane hleft direction hsurvivor)

/-- Chosen literal right-to-left handoff for a nonempty survivor family. -/
noncomputable def profiledOpenIndexedChosenRightToLeftHandoff
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (hright : state.right = some lane)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hsurvivor : Nonempty
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    ProfiledOpenIndexedRightToLeftSemanticHandoff A strategy hwin basis
      state lane hright direction :=
  Classical.choice (exists_profiledOpenIndexedRightToLeftSemanticHandoff A
    strategy hwin basis state lane hright direction hsurvivor)

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- A normalized left-to-right survivor forces the old left semantic lane to
be active. -/
theorem exists_profiledOpenIndexedLeftLane_of_survivor
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (survivor :
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    ∃ lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
        (I := I), state.left = some lane := by
  classical
  cases hleft : state.left with
  | some lane => exact ⟨lane, rfl⟩
  | none =>
      exfalso
      have hold : (state.code A strategy hwin basis).leftSlots
          survivor.lineage = none := by
        simp [ProfiledOpenIndexedCorrelatedSemanticState.code, hleft,
          ProfiledOpenIndexedLeftSemanticShadow.slots]
      have hnone := profiledOpenIndexedBiBeliefNext_right_none_of_left_none A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction survivor.lineage hold
      have hsome :
          (profiledOpenIndexedBiBeliefNext A
            (state.code A strategy hwin basis)
            (state.move A strategy hwin basis) direction).rightSlots
              survivor.lineage = some survivor.root := by
        change (profiledOpenIndexedLeftRawChildCode A
            (state.code A strategy hwin basis)
            (state.move A strategy hwin basis)
            direction).deduplicateRoots.rootSlots survivor.lineage =
          some survivor.root
        simp [IndexedLineageChildCode.rootSlots, survivor.slot]
      cases hsome.symm.trans hnone

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Right-to-left active-lane mirror. -/
theorem exists_profiledOpenIndexedRightLane_of_survivor
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (survivor :
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    ∃ lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
        (I := I), state.right = some lane := by
  classical
  cases hright : state.right with
  | some lane => exact ⟨lane, rfl⟩
  | none =>
      exfalso
      have hold : (state.code A strategy hwin basis).rightSlots
          survivor.lineage = none := by
        simp [ProfiledOpenIndexedCorrelatedSemanticState.code, hright,
          ProfiledOpenIndexedRightSemanticShadow.slots]
      have hnone := profiledOpenIndexedBiBeliefNext_left_none_of_right_none A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction survivor.lineage hold
      have hsome :
          (profiledOpenIndexedBiBeliefNext A
            (state.code A strategy hwin basis)
            (state.move A strategy hwin basis) direction).leftSlots
              survivor.lineage = some survivor.root := by
        change (profiledOpenIndexedRightRawChildCode A
            (state.code A strategy hwin basis)
            (state.move A strategy hwin basis)
            direction).deduplicateRoots.rootSlots survivor.lineage =
          some survivor.root
        simp [IndexedLineageChildCode.rootSlots, survivor.slot]
      cases hsome.symm.trans hnone

/-- The active old left lane selected from a nonempty normalized family. -/
noncomputable def profiledOpenIndexedLeftLaneOfSurvivor
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hsurvivor : Nonempty
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis (I := I) :=
  Classical.choose (exists_profiledOpenIndexedLeftLane_of_survivor A strategy
    hwin basis state direction (Classical.choice hsurvivor))

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenIndexedLeftLaneOfSurvivor_spec
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hsurvivor : Nonempty
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    state.left = some (profiledOpenIndexedLeftLaneOfSurvivor A strategy hwin
      basis state direction hsurvivor) :=
  Classical.choose_spec (exists_profiledOpenIndexedLeftLane_of_survivor A
    strategy hwin basis state direction (Classical.choice hsurvivor))

/-- The old right-lane mirror. -/
noncomputable def profiledOpenIndexedRightLaneOfSurvivor
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hsurvivor : Nonempty
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    ProfiledOpenIndexedRightSemanticLane A strategy hwin basis (I := I) :=
  Classical.choose (exists_profiledOpenIndexedRightLane_of_survivor A strategy
    hwin basis state direction (Classical.choice hsurvivor))

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenIndexedRightLaneOfSurvivor_spec
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hsurvivor : Nonempty
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    state.right = some (profiledOpenIndexedRightLaneOfSurvivor A strategy hwin
      basis state direction hsurvivor) :=
  Classical.choose_spec (exists_profiledOpenIndexedRightLane_of_survivor A
    strategy hwin basis state direction (Classical.choice hsurvivor))

/-- New right semantic shadow, generated by the old left lane. -/
noncomputable def profiledOpenIndexedCorrelatedNextRight
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledOpenIndexedRightSemanticShadow A strategy hwin basis (I := I) := by
  classical
  exact if hsurvivor : Nonempty
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor then
    let lane := profiledOpenIndexedLeftLaneOfSurvivor A strategy hwin basis
      state direction hsurvivor
    let hleft := profiledOpenIndexedLeftLaneOfSurvivor_spec A strategy hwin
      basis state direction hsurvivor
    some ((profiledOpenIndexedChosenLeftToRightHandoff A strategy hwin
      basis state lane hleft direction hsurvivor).child)
  else none

/-- New left semantic shadow, generated by the old right lane. -/
noncomputable def profiledOpenIndexedCorrelatedNextLeft
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledOpenIndexedLeftSemanticShadow A strategy hwin basis (I := I) := by
  classical
  exact if hsurvivor : Nonempty
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor then
    let lane := profiledOpenIndexedRightLaneOfSurvivor A strategy hwin basis
      state direction hsurvivor
    let hright := profiledOpenIndexedRightLaneOfSurvivor_spec A strategy hwin
      basis state direction hsurvivor
    some ((profiledOpenIndexedChosenRightToLeftHandoff A strategy hwin
      basis state lane hright direction hsurvivor).child)
  else none

/-- The total correlated semantic successor. -/
noncomputable def profiledOpenIndexedCorrelatedSemanticNext
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I) :=
  { right := profiledOpenIndexedCorrelatedNextRight A strategy hwin basis
      state direction
    left := profiledOpenIndexedCorrelatedNextLeft A strategy hwin basis
      state direction }

/-! ## Exact public-code equations -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The total next-right shadow has exactly the normalized public slots
computed from the old left lane. -/
theorem profiledOpenIndexedCorrelatedNextRight_slots
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledOpenIndexedRightSemanticShadow.slots A strategy hwin basis
        (profiledOpenIndexedCorrelatedNextRight A strategy hwin basis state
          direction) =
      (profiledOpenIndexedLeftChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).rootSlots := by
  classical
  by_cases hsurvivor : Nonempty
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor
  · let lane := profiledOpenIndexedLeftLaneOfSurvivor A strategy hwin basis
      state direction hsurvivor
    let hleft := profiledOpenIndexedLeftLaneOfSurvivor_spec A strategy hwin
      basis state direction hsurvivor
    let handoff := profiledOpenIndexedChosenLeftToRightHandoff A strategy hwin
      basis state lane hleft direction hsurvivor
    have hslots := handoff.child_slots
    simpa [profiledOpenIndexedCorrelatedNextRight, hsurvivor, lane, hleft,
      handoff] using hslots
  · have hdead :=
      IndexedLineageChildCode.RootSurvivor.rootSlots_eq_none_of_not_nonempty
        (code := profiledOpenIndexedLeftRawChildCode A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) direction) hsurvivor
    calc
      ProfiledOpenIndexedRightSemanticShadow.slots A strategy hwin basis
          (profiledOpenIndexedCorrelatedNextRight A strategy hwin basis
            state direction) = fun _ => none := by
        simp [profiledOpenIndexedCorrelatedNextRight, hsurvivor,
          ProfiledOpenIndexedRightSemanticShadow.slots]
      _ = (profiledOpenIndexedLeftChildCode A
            (state.code A strategy hwin basis)
            (state.move A strategy hwin basis) direction).rootSlots := by
        simpa [profiledOpenIndexedLeftChildCode] using hdead.symm

/-- Left-shadow slot mirror. -/
theorem profiledOpenIndexedCorrelatedNextLeft_slots
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledOpenIndexedLeftSemanticShadow.slots A strategy hwin basis
        (profiledOpenIndexedCorrelatedNextLeft A strategy hwin basis state
          direction) =
      (profiledOpenIndexedRightChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).rootSlots := by
  classical
  by_cases hsurvivor : Nonempty
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor
  · let lane := profiledOpenIndexedRightLaneOfSurvivor A strategy hwin basis
      state direction hsurvivor
    let hright := profiledOpenIndexedRightLaneOfSurvivor_spec A strategy hwin
      basis state direction hsurvivor
    let handoff := profiledOpenIndexedChosenRightToLeftHandoff A strategy hwin
      basis state lane hright direction hsurvivor
    have hslots := handoff.child_slots
    simpa [profiledOpenIndexedCorrelatedNextLeft, hsurvivor, lane, hright,
      handoff] using hslots
  · have hdead :=
      IndexedLineageChildCode.RootSurvivor.rootSlots_eq_none_of_not_nonempty
        (code := profiledOpenIndexedRightRawChildCode A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) direction) hsurvivor
    calc
      ProfiledOpenIndexedLeftSemanticShadow.slots A strategy hwin basis
          (profiledOpenIndexedCorrelatedNextLeft A strategy hwin basis
            state direction) = fun _ => none := by
        simp [profiledOpenIndexedCorrelatedNextLeft, hsurvivor,
          ProfiledOpenIndexedLeftSemanticShadow.slots]
      _ = (profiledOpenIndexedRightChildCode A
            (state.code A strategy hwin basis)
            (state.move A strategy hwin basis) direction).rootSlots := by
        simpa [profiledOpenIndexedRightChildCode] using hdead.symm

/-- The next-right semantic pattern is exactly the public active-gated row
diagonal. -/
theorem profiledOpenIndexedCorrelatedNextRight_pattern
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledOpenIndexedRightSemanticShadow.pattern A strategy hwin basis
        (profiledOpenIndexedCorrelatedNextRight A strategy hwin basis state
          direction) =
      profiledOpenIndexedActiveCanonicalRowPattern A
        (profiledOpenIndexedLeftChildCode A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) direction).rootSlots := by
  classical
  by_cases hsurvivor : Nonempty
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor
  · let lane := profiledOpenIndexedLeftLaneOfSurvivor A strategy hwin basis
      state direction hsurvivor
    let hleft := profiledOpenIndexedLeftLaneOfSurvivor_spec A strategy hwin
      basis state direction hsurvivor
    let handoff := profiledOpenIndexedChosenLeftToRightHandoff A strategy hwin
      basis state lane hleft direction hsurvivor
    have hpattern := handoff.child_pattern
    simpa [profiledOpenIndexedCorrelatedNextRight, hsurvivor, lane, hleft,
      handoff] using hpattern
  · rw [← profiledOpenIndexedCorrelatedNextRight_slots A strategy hwin
      basis state direction]
    funext left right
    simp [profiledOpenIndexedCorrelatedNextRight, hsurvivor,
      ProfiledOpenIndexedRightSemanticShadow.pattern,
      ProfiledOpenIndexedRightSemanticShadow.slots,
      profiledOpenIndexedActiveCanonicalRowPattern]

/-- Next-left pattern mirror. -/
theorem profiledOpenIndexedCorrelatedNextLeft_pattern
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledOpenIndexedLeftSemanticShadow.pattern A strategy hwin basis
        (profiledOpenIndexedCorrelatedNextLeft A strategy hwin basis state
          direction) =
      profiledOpenIndexedActiveCanonicalRowPattern A
        (profiledOpenIndexedRightChildCode A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) direction).rootSlots := by
  classical
  by_cases hsurvivor : Nonempty
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor
  · let lane := profiledOpenIndexedRightLaneOfSurvivor A strategy hwin basis
      state direction hsurvivor
    let hright := profiledOpenIndexedRightLaneOfSurvivor_spec A strategy hwin
      basis state direction hsurvivor
    let handoff := profiledOpenIndexedChosenRightToLeftHandoff A strategy hwin
      basis state lane hright direction hsurvivor
    have hpattern := handoff.child_pattern
    simpa [profiledOpenIndexedCorrelatedNextLeft, hsurvivor, lane, hright,
      handoff] using hpattern
  · rw [← profiledOpenIndexedCorrelatedNextLeft_slots A strategy hwin
      basis state direction]
    funext left right
    simp [profiledOpenIndexedCorrelatedNextLeft, hsurvivor,
      ProfiledOpenIndexedLeftSemanticShadow.pattern,
      ProfiledOpenIndexedLeftSemanticShadow.slots,
      profiledOpenIndexedActiveCanonicalRowPattern]

/-- Forgetting the total semantic successor yields definitionally the same
finite node as the public source-free transition. -/
theorem profiledOpenIndexedCorrelatedSemanticNext_code
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis state
        direction).code A strategy hwin basis =
      profiledOpenIndexedBiBeliefNext A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction := by
  unfold ProfiledOpenIndexedCorrelatedSemanticState.code
    profiledOpenIndexedCorrelatedSemanticNext
  rw [profiledOpenIndexedCorrelatedNextRight_slots A strategy hwin basis
      state direction,
    profiledOpenIndexedCorrelatedNextLeft_slots A strategy hwin basis
      state direction,
    profiledOpenIndexedCorrelatedNextRight_pattern A strategy hwin basis
      state direction,
    profiledOpenIndexedCorrelatedNextLeft_pattern A strategy hwin basis
      state direction]
  rfl

end

/-! ## Literal survivor memory bridges -/

/-- The canonical left-to-right handoff selected by one particular literal
survivor.  The survivor itself supplies nonemptiness; no root representative
is selected again. -/
noncomputable def profiledOpenIndexedLeftToRightHandoffOfSurvivor
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (survivor :
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :=
  let hsurvivor : Nonempty
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor :=
    ⟨survivor⟩
  let lane := profiledOpenIndexedLeftLaneOfSurvivor A strategy hwin basis
    state direction hsurvivor
  let hleft := profiledOpenIndexedLeftLaneOfSurvivor_spec A strategy hwin
    basis state direction hsurvivor
  profiledOpenIndexedChosenLeftToRightHandoff A strategy hwin basis state
    lane hleft direction hsurvivor

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The exact child of the survivor-indexed handoff is the right lane stored
by the total successor. -/
theorem profiledOpenIndexedCorrelatedSemanticNext_right_eq_child
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (survivor :
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis state
        direction).right =
      some ((profiledOpenIndexedLeftToRightHandoffOfSurvivor A strategy hwin
        basis state direction survivor).child) := by
  classical
  have hsurvivor : Nonempty
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor :=
    ⟨survivor⟩
  simp [profiledOpenIndexedCorrelatedSemanticNext,
    profiledOpenIndexedCorrelatedNextRight,
    profiledOpenIndexedLeftToRightHandoffOfSurvivor, hsurvivor]

/-- Right-to-left survivor-indexed handoff. -/
noncomputable def profiledOpenIndexedRightToLeftHandoffOfSurvivor
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (survivor :
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :=
  let hsurvivor : Nonempty
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor :=
    ⟨survivor⟩
  let lane := profiledOpenIndexedRightLaneOfSurvivor A strategy hwin basis
    state direction hsurvivor
  let hright := profiledOpenIndexedRightLaneOfSurvivor_spec A strategy hwin
    basis state direction hsurvivor
  profiledOpenIndexedChosenRightToLeftHandoff A strategy hwin basis state
    lane hright direction hsurvivor

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The total successor stores exactly the left child of the literal
right-to-left handoff. -/
theorem profiledOpenIndexedCorrelatedSemanticNext_left_eq_child
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (survivor :
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis state
        direction).left =
      some ((profiledOpenIndexedRightToLeftHandoffOfSurvivor A strategy hwin
        basis state direction survivor).child) := by
  classical
  have hsurvivor : Nonempty
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor :=
    ⟨survivor⟩
  simp [profiledOpenIndexedCorrelatedSemanticNext,
    profiledOpenIndexedCorrelatedNextLeft,
    profiledOpenIndexedRightToLeftHandoffOfSurvivor, hsurvivor]

/-- The pointed child member selected by a left-to-right survivor has exactly
that survivor's classified root. -/
theorem profiledOpenIndexedLeftToRightHandoffOfSurvivor_child_anchor
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (survivor :
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    let handoff := profiledOpenIndexedLeftToRightHandoffOfSurvivor A strategy
      hwin basis state direction survivor
    ProfiledOpenClassifiedAnchor.right
        (handoff.childMember survivor).1 = survivor.root := by
  classical
  dsimp only
  let handoff := profiledOpenIndexedLeftToRightHandoffOfSurvivor A strategy
    hwin basis state direction survivor
  have hsemantic :
      ProfiledOpenIndexedRightSemanticShadow.slots A strategy hwin basis
          (some handoff.child) survivor.lineage =
        some (.right (handoff.childMember survivor).1) := by
    simp [ProfiledOpenIndexedRightSemanticShadow.slots,
      handoff.childMember_at survivor]
  have hpublic := congrFun handoff.child_slots survivor.lineage
  have hroot :
      (profiledOpenIndexedLeftChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).rootSlots
          survivor.lineage = some survivor.root := by
    change (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis)
        direction).deduplicateRoots.rootSlots survivor.lineage =
      some survivor.root
    simp [IndexedLineageChildCode.rootSlots, survivor.slot]
  apply Option.some.inj
  exact hsemantic.symm.trans (hpublic.trans hroot)

/-- Right-to-left child-anchor mirror. -/
theorem profiledOpenIndexedRightToLeftHandoffOfSurvivor_child_anchor
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (survivor :
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    let handoff := profiledOpenIndexedRightToLeftHandoffOfSurvivor A strategy
      hwin basis state direction survivor
    ProfiledOpenClassifiedAnchor.left
        (handoff.childMember survivor).1 = survivor.root := by
  classical
  dsimp only
  let handoff := profiledOpenIndexedRightToLeftHandoffOfSurvivor A strategy
    hwin basis state direction survivor
  have hsemantic :
      ProfiledOpenIndexedLeftSemanticShadow.slots A strategy hwin basis
          (some handoff.child) survivor.lineage =
        some (.left (handoff.childMember survivor).1) := by
    simp [ProfiledOpenIndexedLeftSemanticShadow.slots,
      handoff.childMember_at survivor]
  have hpublic := congrFun handoff.child_slots survivor.lineage
  have hroot :
      (profiledOpenIndexedRightChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).rootSlots
          survivor.lineage = some survivor.root := by
    change (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis)
        direction).deduplicateRoots.rootSlots survivor.lineage =
      some survivor.root
    simp [IndexedLineageChildCode.rootSlots, survivor.slot]
  apply Option.some.inj
  exact hsemantic.symm.trans (hpublic.trans hroot)

/-- Full literal left-to-right bridge carried by the total successor.  The
same normalized survivor selects both semantic members, and the displayed
memory equation is the original strategy's operational step. -/
theorem profiledOpenIndexedLeftToRight_literal_memory_bridge
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (survivor :
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    let hsurvivor : Nonempty
        (profiledOpenIndexedLeftRawChildCode A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) direction).RootSurvivor :=
      ⟨survivor⟩
    let lane := profiledOpenIndexedLeftLaneOfSurvivor A strategy hwin basis
      state direction hsurvivor
    let handoff := profiledOpenIndexedLeftToRightHandoffOfSurvivor A strategy
      hwin basis state direction survivor
    (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis state
        direction).right = some handoff.child ∧
      lane.memberAt survivor.lineage =
        some (handoff.sourceMember survivor) ∧
      handoff.child.memberAt survivor.lineage =
        some (handoff.childMember survivor) ∧
      PairedStrategyMemory.step (A := A)
          (.processTwo
            (lane.realization.entry (handoff.sourceMember survivor))
            (lane.realization.minimum (handoff.sourceMember survivor)))
          (.fromTwo survivor.row handoff.semanticPast direction.leftInput) =
        .processOne
          (handoff.child.realization.entry (handoff.childMember survivor))
          (handoff.child.realization.minimum
            (handoff.childMember survivor)) := by
  dsimp only
  let handoff := profiledOpenIndexedLeftToRightHandoffOfSurvivor A strategy
    hwin basis state direction survivor
  exact ⟨profiledOpenIndexedCorrelatedSemanticNext_right_eq_child A strategy
      hwin basis state direction survivor,
    handoff.sourceMember_at survivor,
    handoff.childMember_at survivor,
    handoff.memory_step survivor⟩

/-- Full literal right-to-left bridge. -/
theorem profiledOpenIndexedRightToLeft_literal_memory_bridge
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (survivor :
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    let hsurvivor : Nonempty
        (profiledOpenIndexedRightRawChildCode A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) direction).RootSurvivor :=
      ⟨survivor⟩
    let lane := profiledOpenIndexedRightLaneOfSurvivor A strategy hwin basis
      state direction hsurvivor
    let handoff := profiledOpenIndexedRightToLeftHandoffOfSurvivor A strategy
      hwin basis state direction survivor
    (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis state
        direction).left = some handoff.child ∧
      lane.memberAt survivor.lineage =
        some (handoff.sourceMember survivor) ∧
      handoff.child.memberAt survivor.lineage =
        some (handoff.childMember survivor) ∧
      PairedStrategyMemory.step (A := A)
          (.processOne
            (lane.realization.entry (handoff.sourceMember survivor))
            (lane.realization.minimum (handoff.sourceMember survivor)))
          (.fromOne survivor.row handoff.semanticPast direction.rightInput) =
        .processTwo
          (handoff.child.realization.entry (handoff.childMember survivor))
          (handoff.child.realization.minimum
            (handoff.childMember survivor)) := by
  dsimp only
  let handoff := profiledOpenIndexedRightToLeftHandoffOfSurvivor A strategy
    hwin basis state direction survivor
  exact ⟨profiledOpenIndexedCorrelatedSemanticNext_left_eq_child A strategy
      hwin basis state direction survivor,
    handoff.sourceMember_at survivor,
    handoff.childMember_at survivor,
    handoff.memory_step survivor⟩

end

/-! ## The complete recursive semantic tree -/

/-- Recursively unfold the total correlated successor below every hidden
environment direction.  Only the finite code and the shared finite move are
exposed; semantic lanes and recovered pasts remain proof-side. -/
noncomputable def profiledOpenIndexedCorrelatedSemanticTree
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I)) :
    SourceFreeBeliefSemanticTree
      (ProfiledOpenIndexedBiBeliefDirection
        (I := I) (In₁ := In₁) (In₂ := In₂))
      (ProfiledOpenIndexedBiBeliefMove A)
      (ProfiledOpenIndexedBiBeliefCode A (I := I)) where
  Semantic := ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
    basis (I := I)
  initial := initial
  step := profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
  code := fun state => state.code A strategy hwin basis
  move := fun state => state.move A strategy hwin basis

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenIndexedCorrelatedSemanticTree_initial_code
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I)) :
    let raw := profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
      initial
    raw.code raw.initial = initial.code A strategy hwin basis :=
  rfl

/-- Every node of the recursive tree exposes a valid finite move. -/
theorem profiledOpenIndexedCorrelatedSemanticTree_valid
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I)) (node : TreeNode
        (ProfiledOpenIndexedBiBeliefDirection
          (I := I) (In₁ := In₁) (In₂ := In₂))) :
    ProfiledOpenIndexedBiBeliefValid A
      ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
        initial).code
        ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
          initial).stateAt node))
      ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
        initial).move
        ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
          initial).stateAt node)) := by
  exact ProfiledOpenIndexedCorrelatedSemanticState.valid A strategy hwin basis
    _

/-- The recursive semantic tree satisfies the unconditional source-free T1
equation at every node. -/
theorem profiledOpenIndexedCorrelatedSemanticTree_next_code
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I)) (node : TreeNode
        (ProfiledOpenIndexedBiBeliefDirection
          (I := I) (In₁ := In₁) (In₂ := In₂)))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    let raw := profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
      initial
    raw.code (raw.step (raw.stateAt node) direction) =
      profiledOpenIndexedBiBeliefNext A
        (raw.code (raw.stateAt node)) (raw.move (raw.stateAt node))
        direction := by
  exact profiledOpenIndexedCorrelatedSemanticNext_code A strategy hwin basis
    _ direction

end

end

end DetParityAutomaton

end DistributedSynthesis
