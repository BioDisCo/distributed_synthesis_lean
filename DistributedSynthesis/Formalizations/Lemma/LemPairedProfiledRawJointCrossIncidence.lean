/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSemanticChild
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenPhysicalQueryCoverage

/-!
# Cross-incidence after one raw joint step

Once the selected right and left source rows have been identified with one
literal generated history, a successor cross-incidence is independent of that
history and of the strategy.  It is exactly equality of two concrete finite
environment suffixes.

This is useful both positively and negatively.  It gives a source-free finite
cross-incidence matrix.  It also shows that the current simultaneous child
construction is not recursively an exact fibre after a nonempty strict scan:
the right suffix starts with a `right` round and the left suffix starts with a
`left` round.  A physical interleaving does not turn those two projections into
equal suffixes.
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
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-! ## Environment suffixes carried by a raw direction -/

/-- The closing right-side environment round for one selected row. -/
def ProfiledRawJointFamilyDirection.rightClosingEnvironment
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (row : PairedEntryRow) : EnvironmentRound In₁ In₂ :=
  match row with
  | .first => rightEnvironment direction.rightInput
  | .both =>
      { inputOne := direction.rightInput.2
        inputTwo := direction.rightInput.1
        graph := .both }

/-- The closing left-side environment round for one selected row. -/
def ProfiledRawJointFamilyDirection.leftClosingEnvironment
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (row : PairedEntryRow) : EnvironmentRound In₁ In₂ :=
  match row with
  | .first => leftEnvironment direction.leftInput
  | .both =>
      { inputOne := direction.leftInput.1
        inputTwo := direction.leftInput.2
        graph := .both }

/-- Concrete environment suffix generating a right-to-left fresh child row. -/
def ProfiledRawJointFamilyDirection.rightEnvironmentSuffix
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (row : PairedEntryRow) : List (EnvironmentRound In₁ In₂) :=
  direction.rightPhysicalPast.map rightEnvironment ++
    [direction.rightClosingEnvironment row]

/-- Concrete environment suffix generating a left-to-right fresh child row. -/
def ProfiledRawJointFamilyDirection.leftEnvironmentSuffix
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (row : PairedEntryRow) : List (EnvironmentRound In₁ In₂) :=
  direction.leftPhysicalPast.map leftEnvironment ++
    [direction.leftClosingEnvironment row]

/-! ## Extension is injective in its environment suffix -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Projecting a strategy extension back to environment rounds forgets only
the strategy outputs and returns the literal base followed by the suffix. -/
theorem map_environment_extendPrefix
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (suffix : List (EnvironmentRound In₁ In₂)) :
    (extendPrefix strategy base suffix).map RoundRecord.environment =
      base.map RoundRecord.environment ++ suffix := by
  induction suffix using List.reverseRecOn with
  | nil => simp
  | append_singleton suffix round ih =>
      rw [extendPrefix_snoc]
      simp [History.append, ih]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- At a fixed base, two generated extensions are literally equal exactly
when their concrete environment suffixes are equal. -/
theorem extendPrefix_eq_iff_suffix_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (left right : List (EnvironmentRound In₁ In₂)) :
    extendPrefix strategy base left = extendPrefix strategy base right ↔
      left = right := by
  constructor
  · intro heq
    have hmap := congrArg (List.map RoundRecord.environment) heq
    rw [map_environment_extendPrefix, map_environment_extendPrefix] at hmap
    exact List.append_right_injective _ hmap
  · exact congrArg (extendPrefix strategy base)

/-! ## Literal fresh rows are precisely the concrete suffixes -/

section
omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

theorem profiledRawProcTwoFreshRowHistory_eq_extendPrefix
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (hgen : StrategyGeneratedPrefix strategy base)
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (row : PairedEntryRow) :
    profiledRawProcTwoRowHistory
        (procTwoFreshPair strategy
          (extendPrefix strategy base
            (direction.rightPhysicalPast.map rightEnvironment))
          (strategyGenerated_extendPrefix_basic strategy hgen _)
          direction.rightInput.2 direction.rightInput.1) row =
      extendPrefix strategy base (direction.rightEnvironmentSuffix row) := by
  cases row <;>
    simp [profiledRawProcTwoRowHistory, procTwoFreshPair,
      ProfiledRawJointFamilyDirection.rightEnvironmentSuffix,
      ProfiledRawJointFamilyDirection.rightClosingEnvironment,
      extendPrefix_snoc, rightEnvironment, nextRound]

theorem profiledRawProcOneFreshRowHistory_eq_extendPrefix
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (hgen : StrategyGeneratedPrefix strategy base)
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (row : PairedEntryRow) :
    profiledRawProcOneRowHistory
        (procOneFreshPair strategy
          (extendPrefix strategy base
            (direction.leftPhysicalPast.map leftEnvironment))
          (strategyGenerated_extendPrefix_basic strategy hgen _)
          direction.leftInput.1 direction.leftInput.2) row =
      extendPrefix strategy base (direction.leftEnvironmentSuffix row) := by
  cases row <;>
    simp [profiledRawProcOneRowHistory, procOneFreshPair,
      ProfiledRawJointFamilyDirection.leftEnvironmentSuffix,
      ProfiledRawJointFamilyDirection.leftClosingEnvironment,
      extendPrefix_snoc, leftEnvironment, nextRound]

/-- **Source-free successor incidence.**  For two fresh children of one
common generated source, literal row-history equality is equivalent to
equality of their concrete environment suffixes. -/
theorem profiledRawFreshRows_eq_iff_environmentSuffix_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (hgen : StrategyGeneratedPrefix strategy base)
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (rightRow leftRow : PairedEntryRow) :
    profiledRawProcTwoRowHistory
        (procTwoFreshPair strategy
          (extendPrefix strategy base
            (direction.rightPhysicalPast.map rightEnvironment))
          (strategyGenerated_extendPrefix_basic strategy hgen _)
          direction.rightInput.2 direction.rightInput.1) rightRow =
      profiledRawProcOneRowHistory
        (procOneFreshPair strategy
          (extendPrefix strategy base
            (direction.leftPhysicalPast.map leftEnvironment))
          (strategyGenerated_extendPrefix_basic strategy hgen _)
          direction.leftInput.1 direction.leftInput.2) leftRow ↔
      direction.rightEnvironmentSuffix rightRow =
        direction.leftEnvironmentSuffix leftRow := by
  rw [profiledRawProcTwoFreshRowHistory_eq_extendPrefix (hgen := hgen),
    profiledRawProcOneFreshRowHistory_eq_extendPrefix (hgen := hgen),
    extendPrefix_eq_iff_suffix_eq]

end

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] in
/-- Homogeneous right and left suffixes can coincide only in the zero-open,
`both`/`both` case.  The remaining input equality is deliberately left in the
suffix equation itself. -/
theorem empty_pasts_and_both_rows_of_environmentSuffix_eq
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (rightRow leftRow : PairedEntryRow)
    (heq : direction.rightEnvironmentSuffix rightRow =
      direction.leftEnvironmentSuffix leftRow) :
    direction.rightPhysicalPast = [] ∧
      direction.leftPhysicalPast = [] ∧
      rightRow = .both ∧ leftRow = .both := by
  cases hright : direction.rightPhysicalPast with
  | nil =>
      cases hleft : direction.leftPhysicalPast with
      | nil =>
          cases rightRow <;> cases leftRow <;>
            simp [ProfiledRawJointFamilyDirection.rightEnvironmentSuffix,
              ProfiledRawJointFamilyDirection.leftEnvironmentSuffix,
              ProfiledRawJointFamilyDirection.rightClosingEnvironment,
              ProfiledRawJointFamilyDirection.leftClosingEnvironment,
              hright, hleft, rightEnvironment, leftEnvironment] at heq ⊢
      | cons left rest =>
          cases rightRow <;> cases leftRow <;>
            simp [ProfiledRawJointFamilyDirection.rightEnvironmentSuffix,
              ProfiledRawJointFamilyDirection.leftEnvironmentSuffix,
              ProfiledRawJointFamilyDirection.rightClosingEnvironment,
              ProfiledRawJointFamilyDirection.leftClosingEnvironment,
              hright, hleft, rightEnvironment, leftEnvironment] at heq
  | cons right rest =>
      cases hleft : direction.leftPhysicalPast with
      | nil =>
          cases rightRow <;> cases leftRow <;>
            simp [ProfiledRawJointFamilyDirection.rightEnvironmentSuffix,
              ProfiledRawJointFamilyDirection.leftEnvironmentSuffix,
              ProfiledRawJointFamilyDirection.rightClosingEnvironment,
              ProfiledRawJointFamilyDirection.leftClosingEnvironment,
              hright, hleft, rightEnvironment, leftEnvironment] at heq
      | cons left rest =>
          cases rightRow <;> cases leftRow <;>
            simp [ProfiledRawJointFamilyDirection.rightEnvironmentSuffix,
              ProfiledRawJointFamilyDirection.leftEnvironmentSuffix,
              ProfiledRawJointFamilyDirection.rightClosingEnvironment,
              ProfiledRawJointFamilyDirection.leftClosingEnvironment,
              hright, hleft, rightEnvironment, leftEnvironment] at heq

/-! ## Adapter from one physical strict scan -/

/-- Field-for-field adapter from the established physical strict-history
direction to the basis-free raw joint direction. -/
def profiledRawJointPhysicalStrictHistoryDirection
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (rightPivot leftPivot : ProfiledRawJointCandidate I)
    (closingInputOne : In₁) (closingInputTwo : In₂) :
    ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂) :=
  { rightPivot := rightPivot
    rightTaggedPast := profiledOpenPhysicalStrictRightPast history
    rightInput := (closingInputTwo, closingInputOne)
    leftPivot := leftPivot
    leftTaggedPast := profiledOpenPhysicalStrictLeftPast history
    leftInput := (closingInputOne, closingInputTwo) }

section
omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂]

/-- The adapter is literally the same six-field direction as the old physical
constructor; only its result type is the raw pre-rationalization interface. -/
theorem profiledRawJointPhysicalStrictHistoryDirection_fields
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (rightPivot leftPivot : ProfiledRawJointCandidate I)
    (closingInputOne : In₁) (closingInputTwo : In₂) :
    let raw := profiledRawJointPhysicalStrictHistoryDirection history
      rightPivot leftPivot closingInputOne closingInputTwo
    raw.rightTaggedPast = profiledOpenPhysicalStrictRightPast history ∧
      raw.leftTaggedPast = profiledOpenPhysicalStrictLeftPast history ∧
      raw.rightInput = (closingInputTwo, closingInputOne) ∧
      raw.leftInput = (closingInputOne, closingInputTwo) := by
  simp [profiledRawJointPhysicalStrictHistoryDirection]

/-- Every strict physical letter occurs in exactly one of the two projections,
so both projections are empty exactly for the empty physical history. -/
theorem physicalStrictPasts_both_empty_iff
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))) :
    profiledOpenPhysicalStrictRightPast history = [] ∧
        profiledOpenPhysicalStrictLeftPast history = [] ↔
      history = [] := by
  induction history with
  | nil => simp [profiledOpenPhysicalStrictRightPast,
      profiledOpenPhysicalStrictLeftPast]
  | cons letter history ih =>
      cases hside : letter.side <;>
        simp [profiledOpenPhysicalStrictRightPast,
          profiledOpenPhysicalStrictLeftPast, hside]

/-- Consequently a nonempty physical strict scan has no successor
cross-incidence in the present simultaneous semantic-child construction. -/
theorem profiledRawJointPhysicalStrictHistoryDirection_suffix_ne
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (rightPivot leftPivot : ProfiledRawJointCandidate I)
    (closingInputOne : In₁) (closingInputTwo : In₂)
    (hne : history ≠ []) (rightRow leftRow : PairedEntryRow) :
    let direction := profiledRawJointPhysicalStrictHistoryDirection history
      rightPivot leftPivot closingInputOne closingInputTwo
    direction.rightEnvironmentSuffix rightRow ≠
      direction.leftEnvironmentSuffix leftRow := by
  dsimp only
  intro heq
  have hempty := empty_pasts_and_both_rows_of_environmentSuffix_eq
    (profiledRawJointPhysicalStrictHistoryDirection history rightPivot
      leftPivot closingInputOne closingInputTwo) rightRow leftRow heq
  have hright : profiledOpenPhysicalStrictRightPast history = [] := by
    simpa [profiledRawJointPhysicalStrictHistoryDirection,
      ProfiledRawJointFamilyDirection.rightPhysicalPast] using hempty.1
  have hleft : profiledOpenPhysicalStrictLeftPast history = [] := by
    simpa [profiledRawJointPhysicalStrictHistoryDirection,
      ProfiledRawJointFamilyDirection.leftPhysicalPast] using hempty.2.1
  exact hne ((physicalStrictPasts_both_empty_iff history).1 ⟨hright, hleft⟩)

end

end

end DetParityAutomaton

end DistributedSynthesis
