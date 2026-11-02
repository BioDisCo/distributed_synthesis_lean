/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicySelectionOwnerFibreAtKey

/-!
# Fixed-key locality of owner-fibre safety

This file lifts the one-round fixed-key theorem to arbitrary finite prefixes
and to the universal parity safety property.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev RootKey :=
  ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy

private abbrev PolicySelection :=
  ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy hwin

namespace ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection

variable (selection other : PolicySelection A strategy hwin)

private theorem foldl_congr_of_invariant
    {State Move : Type*}
    (Invariant : State → Prop)
    (left right : State → Move → State)
    (right_preserves : ∀ state move, Invariant state →
      Invariant (right state move))
    (agree : ∀ state move, Invariant state →
      left state move = right state move)
    (initial : State) (moves : List Move)
    (hinitial : Invariant initial) :
    moves.foldl left initial = moves.foldl right initial := by
  induction moves generalizing initial with
  | nil => rfl
  | cons move moves ih =>
      simp only [List.foldl_cons]
      rw [agree initial move hinitial]
      exact ih
        (initial := right initial move)
        (right_preserves initial move hinitial)

/-- The key invariant on the control coordinate of a safety-product state. -/
def SafetyStateAtKey
    (key : RootKey A strategy)
    (state :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin) : Prop :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
      state.1.1 ∧
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
      state.1.2

theorem ownerFibreSafetyStep_atKey
    (key : RootKey A strategy)
    (state :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin)
    (direction :
      ProfiledRawJointRecurrentOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂))
    (hkey : SafetyStateAtKey A strategy hwin key state) :
    SafetyStateAtKey A strategy hwin key
      (selection.ownerFibreSafetyStep A strategy hwin state direction) := by
  exact selection.ownerFibreRound_atKey A strategy hwin key state.1
    direction.1 direction.2 hkey.1 hkey.2

theorem ownerFibreSafetyStep_congr_at
    (key : RootKey A strategy)
    (state :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin)
    (direction :
      ProfiledRawJointRecurrentOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂))
    (hkey : SafetyStateAtKey A strategy hwin key state)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.ownerFibreSafetyStep A strategy hwin state direction =
      other.ownerFibreSafetyStep A strategy hwin state direction := by
  unfold ownerFibreSafetyStep ownerFibreRoundRecord
  rw [selection.ownerFibreRound_congr_at A strategy hwin other key state.1
    direction.1 direction.2 hkey.1 hkey.2 hagrees]

/-- Every finite environment prefix stays inside the entry's root-key fibre. -/
theorem ownerFibreSafetyStateAt_atKey
    (key : RootKey A strategy)
    (initial :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin)
    (node : TreeNode
      (ProfiledRawJointRecurrentOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂)))
    (hinitial : SafetyStateAtKey A strategy hwin key initial) :
    SafetyStateAtKey A strategy hwin key
      (selection.ownerFibreSafetyStateAt A strategy hwin initial node) := by
  unfold ownerFibreSafetyStateAt
  induction node generalizing initial with
  | nil => exact hinitial
  | cons direction node ih =>
      simp only [List.foldl_cons]
      exact ih
        (initial := selection.ownerFibreSafetyStep A strategy hwin initial
          direction)
        (selection.ownerFibreSafetyStep_atKey A strategy hwin key initial
          direction hinitial)

/-- Selections agreeing at the entry key have identical finite closed-loop
states along every environment prefix. -/
theorem ownerFibreSafetyStateAt_congr_at
    (key : RootKey A strategy)
    (initial :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin)
    (node : TreeNode
      (ProfiledRawJointRecurrentOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂)))
    (hinitial : SafetyStateAtKey A strategy hwin key initial)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.ownerFibreSafetyStateAt A strategy hwin initial node =
      other.ownerFibreSafetyStateAt A strategy hwin initial node := by
  unfold ownerFibreSafetyStateAt
  exact foldl_congr_of_invariant
    (SafetyStateAtKey A strategy hwin key)
    (selection.ownerFibreSafetyStep A strategy hwin)
    (other.ownerFibreSafetyStep A strategy hwin)
    (fun state direction hkey ↦
      other.ownerFibreSafetyStep_atKey A strategy hwin key state direction
        hkey)
    (fun state direction hkey ↦
      selection.ownerFibreSafetyStep_congr_at A strategy hwin other key state
        direction hkey hagrees)
    initial node hinitial

/-- Safety of a fixed-key entry is invariant under changes to every other
root-key policy. -/
theorem ownerFibreSafe_congr_at
    (key : RootKey A strategy)
    (initial :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin)
    (hinitial : SafetyStateAtKey A strategy hwin key initial)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.OwnerFibreSafe A strategy hwin initial ↔
      other.OwnerFibreSafe A strategy hwin initial := by
  unfold OwnerFibreSafe
  constructor
  · intro h branch
    have hpriorities :
        (fun n ↦ A.priority
          (selection.ownerFibreSafetyStateAt A strategy hwin initial
            (branchNode branch n)).2) =
        fun n ↦ A.priority
          (other.ownerFibreSafetyStateAt A strategy hwin initial
            (branchNode branch n)).2 := by
      funext n
      rw [selection.ownerFibreSafetyStateAt_congr_at A strategy hwin other
        key initial (branchNode branch n) hinitial hagrees]
    exact hpriorities ▸ h branch
  · intro h branch
    have hpriorities :
        (fun n ↦ A.priority
          (selection.ownerFibreSafetyStateAt A strategy hwin initial
            (branchNode branch n)).2) =
        fun n ↦ A.priority
          (other.ownerFibreSafetyStateAt A strategy hwin initial
            (branchNode branch n)).2 := by
      funext n
      rw [selection.ownerFibreSafetyStateAt_congr_at A strategy hwin other
        key initial (branchNode branch n) hinitial hagrees]
    exact hpriorities.symm ▸ h branch

theorem ownerFibreSafeOn_congr_at
    (key : RootKey A strategy)
    (entries : Finset
      (ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin))
    (hentries : ∀ initial ∈ entries,
      SafetyStateAtKey A strategy hwin key initial)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.OwnerFibreSafeOn A strategy hwin entries ↔
      other.OwnerFibreSafeOn A strategy hwin entries := by
  unfold OwnerFibreSafeOn
  constructor
  · intro h initial hinitial
    exact (selection.ownerFibreSafe_congr_at A strategy hwin other key
      initial (hentries initial hinitial) hagrees).mp (h initial hinitial)
  · intro h initial hinitial
    exact (selection.ownerFibreSafe_congr_at A strategy hwin other key
      initial (hentries initial hinitial) hagrees).mpr (h initial hinitial)

/-- Independently safe root-key fibres assemble without a global product.
The diagonal selection chooses at `key` exactly the policy used by that key's
local witness; fixed-key extensionality transfers all its entry guarantees. -/
theorem exists_ownerFibreSafeSelection_of_pointwise
    (entries : RootKey A strategy → Finset
      (ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin))
    (hentries : ∀ key initial, initial ∈ entries key →
      SafetyStateAtKey A strategy hwin key initial)
    (hlocal : ∀ key, ∃ localSelection : PolicySelection A strategy hwin,
      localSelection.OwnerFibreSafeOn A strategy hwin (entries key)) :
    ∃ global : PolicySelection A strategy hwin,
      ∀ key, global.OwnerFibreSafeOn A strategy hwin (entries key) := by
  choose localSelection hsafe using hlocal
  let global : PolicySelection A strategy hwin :=
    fun key ↦ localSelection key key
  refine ⟨global, ?_⟩
  intro key
  have hagrees :
      global.AgreeAt A strategy hwin (localSelection key) key := rfl
  exact (global.ownerFibreSafeOn_congr_at A strategy hwin
    (localSelection key) key
    (entries key) (hentries key) hagrees).mpr (hsafe key)

end ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection

end

end DetParityAutomaton

end DistributedSynthesis
