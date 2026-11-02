/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelectionOwnerFibreAtKey

/-!
# Fixed-key locality of finite-memory owner-fibre safety

The one-round locality theorem is lifted through the rejecting-sink monitor.
Selections agreeing at one root key therefore have identical monitored states
after every finite environment prefix, and satisfy the same infinite parity
safety obligation from every state in that fibre.  The final theorem performs
the diagonal assembly of independently safe root fibres.
-/

namespace DistributedSynthesis

universe u v x y s m

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Memory : Type m}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype Memory]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev RootKey :=
  ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy

private abbrev Direction :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyDirection
    (In₁ := In₁) (In₂ := In₂)

private abbrev LiveState :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
    (Memory := Memory) A strategy

private abbrev SafetyState :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyState
    (Memory := Memory) A strategy

private abbrev PolicySelection
    (initialMemory : RootKey A strategy → Memory) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
    (Memory := Memory) A strategy hwin initialMemory

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

variable
  (initialMemory : RootKey A strategy → Memory)
  (selection other : PolicySelection (Memory := Memory) A strategy hwin
    initialMemory)

/-- The monitored failure state is harmless for key confinement; every live
state must keep all of its bank coordinates in the fixed fibre. -/
def SafetyStateAtKey
    (key : RootKey A strategy)
    (state : SafetyState (Memory := Memory) A strategy) : Prop :=
  match state with
  | none => True
  | some live =>
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
        (Memory := Memory) A strategy key live

theorem ownerFibreSafetyLiveStep_atKey
    (key : RootKey A strategy)
    (state : LiveState (Memory := Memory) A strategy)
    (direction : Direction (In₁ := In₁) (In₂ := In₂))
    (hkey :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
        (Memory := Memory) A strategy key state) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
      (Memory := Memory) A strategy key
      (selection.ownerFibreSafetyLiveStep A strategy hwin initialMemory state
        direction) := by
  unfold ownerFibreSafetyLiveStep
  exact selection.ownerFibreRound_atKey A strategy hwin initialMemory key
    state.1 direction.1 direction.2 hkey.1 hkey.2

theorem ownerFibreSafetyLiveStep_congr_at
    (key : RootKey A strategy)
    (state : LiveState (Memory := Memory) A strategy)
    (direction : Direction (In₁ := In₁) (In₂ := In₂))
    (hkey :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
        (Memory := Memory) A strategy key state)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.ownerFibreSafetyLiveStep A strategy hwin initialMemory state
        direction =
      other.ownerFibreSafetyLiveStep A strategy hwin initialMemory state
        direction := by
  unfold ownerFibreSafetyLiveStep
  rw [selection.ownerFibreRound_congr_at A strategy hwin initialMemory other
    key state.1 direction.1 direction.2 hkey.1 hkey.2 hagrees]
  rw [selection.ownerFibreRoundRecord_congr_at A strategy hwin initialMemory
    other key state.1 direction.1 direction.2 hkey.1 hkey.2 hagrees]

theorem ownerFibreSafetyStep_atKey
    (key : RootKey A strategy)
    (state : SafetyState (Memory := Memory) A strategy)
    (direction : Direction (In₁ := In₁) (In₂ := In₂))
    (hkey : SafetyStateAtKey (Memory := Memory) A strategy key state) :
    SafetyStateAtKey (Memory := Memory) A strategy key
      (selection.ownerFibreSafetyStep A strategy hwin initialMemory state
        direction) := by
  cases state with
  | none => trivial
  | some live =>
      by_cases hdecodes :
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
            (Memory := Memory) A strategy live.1.1 live.1.2
      · simp only [ownerFibreSafetyStep, hdecodes, if_pos,
          SafetyStateAtKey]
        exact selection.ownerFibreSafetyLiveStep_atKey A strategy hwin
          initialMemory key live direction hkey
      · simp [ownerFibreSafetyStep, hdecodes, SafetyStateAtKey]

theorem ownerFibreSafetyStep_congr_at
    (key : RootKey A strategy)
    (state : SafetyState (Memory := Memory) A strategy)
    (direction : Direction (In₁ := In₁) (In₂ := In₂))
    (hkey : SafetyStateAtKey (Memory := Memory) A strategy key state)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.ownerFibreSafetyStep A strategy hwin initialMemory state
        direction =
      other.ownerFibreSafetyStep A strategy hwin initialMemory state
        direction := by
  cases state with
  | none => rfl
  | some live =>
      by_cases hdecodes :
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
            (Memory := Memory) A strategy live.1.1 live.1.2
      · simp only [ownerFibreSafetyStep, hdecodes, if_pos,
          Option.some.injEq]
        exact selection.ownerFibreSafetyLiveStep_congr_at A strategy hwin
          initialMemory other key live direction hkey hagrees
      · simp [ownerFibreSafetyStep, hdecodes]

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

private theorem foldl_preserves_invariant
    {State Move : Type*}
    (Invariant : State → Prop)
    (step : State → Move → State)
    (preserves : ∀ state move, Invariant state →
      Invariant (step state move))
    (initial : State) (moves : List Move)
    (hinitial : Invariant initial) :
    Invariant (moves.foldl step initial) := by
  induction moves generalizing initial with
  | nil => exact hinitial
  | cons move moves ih =>
      simp only [List.foldl_cons]
      exact ih (step initial move) (preserves initial move hinitial)

/-- Every finite monitored prefix remains either failed or inside the initial
root-key fibre. -/
theorem ownerFibreSafetyStateAt_atKey
    (key : RootKey A strategy)
    (initial : LiveState (Memory := Memory) A strategy)
    (node : TreeNode (Direction (In₁ := In₁) (In₂ := In₂)))
    (hinitial :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
        (Memory := Memory) A strategy key initial) :
    SafetyStateAtKey (Memory := Memory) A strategy key
      (selection.ownerFibreSafetyStateAt A strategy hwin initialMemory initial
        node) := by
  unfold ownerFibreSafetyStateAt
  exact foldl_preserves_invariant
    (SafetyStateAtKey (Memory := Memory) A strategy key)
    (selection.ownerFibreSafetyStep A strategy hwin initialMemory)
    (fun state direction hstate ↦
      selection.ownerFibreSafetyStep_atKey A strategy hwin initialMemory key
        state direction hstate)
    (some initial) node hinitial

/-- Selections agreeing at the entry key have identical monitored states
after every finite environment prefix. -/
theorem ownerFibreSafetyStateAt_congr_at
    (key : RootKey A strategy)
    (initial : LiveState (Memory := Memory) A strategy)
    (node : TreeNode (Direction (In₁ := In₁) (In₂ := In₂)))
    (hinitial :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
        (Memory := Memory) A strategy key initial)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.ownerFibreSafetyStateAt A strategy hwin initialMemory initial
        node =
      other.ownerFibreSafetyStateAt A strategy hwin initialMemory initial
        node := by
  unfold ownerFibreSafetyStateAt
  exact foldl_congr_of_invariant
    (SafetyStateAtKey (Memory := Memory) A strategy key)
    (selection.ownerFibreSafetyStep A strategy hwin initialMemory)
    (other.ownerFibreSafetyStep A strategy hwin initialMemory)
    (fun state direction hstate ↦
      other.ownerFibreSafetyStep_atKey A strategy hwin initialMemory key state
        direction hstate)
    (fun state direction hstate ↦
      selection.ownerFibreSafetyStep_congr_at A strategy hwin initialMemory
        other key state direction hstate hagrees)
    (some initial) node hinitial

/-- Infinite owner-fibre safety is extensional in the policy chosen at the
entry's root key. -/
theorem ownerFibreSafe_congr_at
    (key : RootKey A strategy)
    (initial : LiveState (Memory := Memory) A strategy)
    (hinitial :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
        (Memory := Memory) A strategy key initial)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.OwnerFibreSafe A strategy hwin initialMemory initial ↔
      other.OwnerFibreSafe A strategy hwin initialMemory initial := by
  unfold OwnerFibreSafe
  constructor
  · intro h branch
    have hpriorities :
        (fun n ↦ ownerFibreSafetyPriority (Memory := Memory) A strategy
          (selection.ownerFibreSafetyStateAt A strategy hwin initialMemory
            initial (branchNode branch n))) =
        fun n ↦ ownerFibreSafetyPriority (Memory := Memory) A strategy
          (other.ownerFibreSafetyStateAt A strategy hwin initialMemory initial
            (branchNode branch n)) := by
      funext n
      rw [selection.ownerFibreSafetyStateAt_congr_at A strategy hwin
        initialMemory other key initial (branchNode branch n) hinitial hagrees]
    exact hpriorities ▸ h branch
  · intro h branch
    have hpriorities :
        (fun n ↦ ownerFibreSafetyPriority (Memory := Memory) A strategy
          (selection.ownerFibreSafetyStateAt A strategy hwin initialMemory
            initial (branchNode branch n))) =
        fun n ↦ ownerFibreSafetyPriority (Memory := Memory) A strategy
          (other.ownerFibreSafetyStateAt A strategy hwin initialMemory initial
            (branchNode branch n)) := by
      funext n
      rw [selection.ownerFibreSafetyStateAt_congr_at A strategy hwin
        initialMemory other key initial (branchNode branch n) hinitial hagrees]
    exact hpriorities.symm ▸ h branch

theorem ownerFibreSafeOn_congr_at
    (key : RootKey A strategy)
    (entries : Finset (LiveState (Memory := Memory) A strategy))
    (hentries : ∀ initial ∈ entries,
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
        (Memory := Memory) A strategy key initial)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.OwnerFibreSafeOn A strategy hwin initialMemory entries ↔
      other.OwnerFibreSafeOn A strategy hwin initialMemory entries := by
  unfold OwnerFibreSafeOn
  constructor
  · intro h initial hinitial
    exact (selection.ownerFibreSafe_congr_at A strategy hwin initialMemory
      other key initial (hentries initial hinitial) hagrees).mp
        (h initial hinitial)
  · intro h initial hinitial
    exact (selection.ownerFibreSafe_congr_at A strategy hwin initialMemory
      other key initial (hentries initial hinitial) hagrees).mpr
        (h initial hinitial)

/-- Independent safety witnesses over fixed, key-indexed entry sets assemble
into one global finite-memory policy selection. -/
theorem exists_ownerFibreSafeSelection_of_pointwise
    (entries : RootKey A strategy →
      Finset (LiveState (Memory := Memory) A strategy))
    (hentries : ∀ key initial, initial ∈ entries key →
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
        (Memory := Memory) A strategy key initial)
    (hlocal : ∀ key, ∃ localSelection :
        PolicySelection (Memory := Memory) A strategy hwin initialMemory,
      localSelection.OwnerFibreSafeOn A strategy hwin initialMemory
        (entries key)) :
    ∃ global : PolicySelection (Memory := Memory) A strategy hwin
        initialMemory,
      ∀ key, global.OwnerFibreSafeOn A strategy hwin initialMemory
        (entries key) := by
  choose localSelection hsafe using hlocal
  let global : PolicySelection (Memory := Memory) A strategy hwin
      initialMemory := fun key ↦ localSelection key key
  refine ⟨global, ?_⟩
  intro key
  have hagrees :
      global.AgreeAt A strategy hwin initialMemory (localSelection key) key :=
    rfl
  exact (global.ownerFibreSafeOn_congr_at A strategy hwin initialMemory
    (localSelection key) key (entries key) (hentries key) hagrees).mpr
      (hsafe key)

/-! ## Canonical honest entries and diagonal assembly -/

theorem root_congr_at
    (key : RootKey A strategy)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.root A strategy hwin initialMemory key =
      other.root A strategy hwin initialMemory key := by
  unfold root AgreeAt at *
  rw [hagrees]

/-- Agreement at `key` preserves not only later transitions but also the
unique live realization of every selection-independent honest-front context
at `key`. -/
theorem realizesOwnerFibreFrontContextAt_congr_at
    (key : RootKey A strategy)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key)
    (state : LiveState (Memory := Memory) A strategy)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.RealizesOwnerFibreFrontContextAt A strategy hwin initialMemory
        key context state ↔
      other.RealizesOwnerFibreFrontContextAt A strategy hwin initialMemory key
        context state := by
  have hroot := selection.root_congr_at A strategy hwin initialMemory other key
    hagrees
  rcases context with context | context
  · unfold RealizesOwnerFibreFrontContextAt
    dsimp only
    rw [hroot]
    rw [selection.resolvePacket_congr_at A strategy hwin initialMemory other
      key (other.root A strategy hwin initialMemory key) rfl _ hagrees]
  · unfold RealizesOwnerFibreFrontContextAt
    dsimp only
    rw [hroot]
    rw [selection.resolvePacket_congr_at A strategy hwin initialMemory other
      key (other.root A strategy hwin initialMemory key) rfl _ hagrees]

theorem ownerFibreHonestEntriesAt_congr_at
    (key : RootKey A strategy)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.ownerFibreHonestEntriesAt A strategy hwin initialMemory key =
      other.ownerFibreHonestEntriesAt A strategy hwin initialMemory key := by
  classical
  apply Finset.ext
  intro state
  rw [selection.mem_ownerFibreHonestEntriesAt_iff_exists_frontContext A
    strategy hwin initialMemory key state]
  rw [other.mem_ownerFibreHonestEntriesAt_iff_exists_frontContext A strategy
    hwin initialMemory key state]
  constructor
  · rintro ⟨context, hrealizes⟩
    exact ⟨context,
      (selection.realizesOwnerFibreFrontContextAt_congr_at A strategy hwin
        initialMemory other key context state hagrees).mp hrealizes⟩
  · rintro ⟨context, hrealizes⟩
    exact ⟨context,
      (selection.realizesOwnerFibreFrontContextAt_congr_at A strategy hwin
        initialMemory other key context state hagrees).mpr hrealizes⟩

/-- The exact safety obligation over canonical honest entries depends only on
the policy selected at the advertised root key. -/
theorem ownerFibreSafeOnHonestEntriesAt_congr_at
    (key : RootKey A strategy)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.OwnerFibreSafeOnHonestEntriesAt A strategy hwin initialMemory
        key ↔
      other.OwnerFibreSafeOnHonestEntriesAt A strategy hwin initialMemory key :=
    by
  unfold OwnerFibreSafeOnHonestEntriesAt
  have hsafe := selection.ownerFibreSafeOn_congr_at A strategy hwin
    initialMemory other key
      (selection.ownerFibreHonestEntriesAt A strategy hwin initialMemory key)
      (selection.ownerFibreHonestEntriesAt_liveStateAtKey A strategy hwin
        initialMemory key) hagrees
  have hentries := selection.ownerFibreHonestEntriesAt_congr_at A strategy
    hwin initialMemory other key hagrees
  rw [← hentries]
  exact hsafe

/-- If every root key has some locally safe finite-memory policy selection,
the pointwise diagonal is one global selection safe on its own canonical
honest entries at every key. -/
theorem exists_ownerFibreSafeOnHonestEntriesAtSelection_of_pointwise
    (hlocal : ∀ key, ∃ localSelection :
        PolicySelection (Memory := Memory) A strategy hwin initialMemory,
      localSelection.OwnerFibreSafeOnHonestEntriesAt A strategy hwin
        initialMemory key) :
    ∃ global : PolicySelection (Memory := Memory) A strategy hwin
        initialMemory,
      ∀ key, global.OwnerFibreSafeOnHonestEntriesAt A strategy hwin
        initialMemory key := by
  choose localSelection hsafe using hlocal
  let global : PolicySelection (Memory := Memory) A strategy hwin
      initialMemory := fun key ↦ localSelection key key
  refine ⟨global, ?_⟩
  intro key
  have hagrees :
      global.AgreeAt A strategy hwin initialMemory (localSelection key) key :=
    rfl
  exact (global.ownerFibreSafeOnHonestEntriesAt_congr_at A strategy hwin
    initialMemory (localSelection key) key hagrees).mpr (hsafe key)

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

end

end DetParityAutomaton

end DistributedSynthesis
