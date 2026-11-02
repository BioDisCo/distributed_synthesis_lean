/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableOwnerFibreAtKey
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEffectCoherence

/-!
# Transfer from fixed-key raw owner checks to an assembled certified policy

The enriched automaton checks owner safety using the raw singleton family of
one table.  Pointwise table choices, however, are certified as one global
table family.  Fixed-key extensionality identifies every singleton safety
trace with the corresponding trace of that global certified policy.  Thus
independently checked effect-coherent tables assemble directly into one
finite-memory policy selection which is safe on all of its canonical honest
entries.
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

private abbrev TableSelection :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
    (Memory := Memory) A strategy

private abbrev FixedTable (key : RootKey A strategy) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
    (Memory := Memory) A strategy key

private abbrev PolicySelection
    (initialMemory : RootKey A strategy → Memory) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
    (Memory := Memory) A strategy hwin initialMemory

private abbrev LiveState :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
    (Memory := Memory) A strategy

private abbrev SafetyState :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyState
    (Memory := Memory) A strategy

private abbrev Direction :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyDirection
    (In₁ := In₁) (In₂ := In₂)

private abbrev Context (key : RootKey A strategy) :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy key

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

variable
  (initialMemory : RootKey A strategy → Memory)
  (source tables : TableSelection (Memory := Memory) A strategy)

/-- A raw family agreeing with a globally certified family at the stored key
has exactly the certified family's guarded one-step behavior there. -/
theorem ownerFibreSafetyStep_eq_toPolicySelection_of_agreeAt
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (key : RootKey A strategy)
    (state : SafetyState (Memory := Memory) A strategy)
    (direction : Direction (In₁ := In₁) (In₂ := In₂))
    (hkey :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.SafetyStateAtKey
        (Memory := Memory) A strategy key state)
    (hagrees : source.AgreeAt A strategy tables key) :
    source.ownerFibreSafetyStep A strategy hwin state direction =
      (tables.toPolicySelection A strategy hwin initialMemory hvalid
          haccepts).ownerFibreSafetyStep A strategy hwin initialMemory state
        direction := by
  calc
    source.ownerFibreSafetyStep A strategy hwin state direction =
        tables.ownerFibreSafetyStep A strategy hwin state direction :=
      source.ownerFibreSafetyStep_congr_at A strategy hwin tables key state
        direction hkey hagrees
    _ =
        (tables.toPolicySelection A strategy hwin initialMemory hvalid
          haccepts).ownerFibreSafetyStep A strategy hwin initialMemory state
            direction :=
      tables.ownerFibreSafetyStep_toPolicySelection A strategy hwin
        initialMemory hvalid haccepts state direction

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

/-- Every finite raw singleton trace equals the trace of the assembled
certified policy when both use the same table at the entry key. -/
theorem ownerFibreSafetyStateAt_eq_toPolicySelection_of_agreeAt
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (key : RootKey A strategy)
    (initial : LiveState (Memory := Memory) A strategy)
    (node : TreeNode (Direction (In₁ := In₁) (In₂ := In₂)))
    (hinitial :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
        (Memory := Memory) A strategy key initial)
    (hagrees : source.AgreeAt A strategy tables key) :
    source.ownerFibreSafetyStateAt A strategy hwin (some initial) node =
      (tables.toPolicySelection A strategy hwin initialMemory hvalid
        haccepts).ownerFibreSafetyStateAt A strategy hwin initialMemory
          initial node := by
  unfold
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreSafetyStateAt
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreSafetyStateAt
  exact foldl_congr_of_invariant
    (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.SafetyStateAtKey
      (Memory := Memory) A strategy key)
    (source.ownerFibreSafetyStep A strategy hwin)
    ((tables.toPolicySelection A strategy hwin initialMemory hvalid
      haccepts).ownerFibreSafetyStep A strategy hwin initialMemory)
    (fun state direction hstate ↦
      (tables.toPolicySelection A strategy hwin initialMemory hvalid
        haccepts).ownerFibreSafetyStep_atKey A strategy hwin initialMemory key
          state direction hstate)
    (fun state direction hstate ↦
      source.ownerFibreSafetyStep_eq_toPolicySelection_of_agreeAt A strategy
        hwin initialMemory tables hvalid haccepts key state direction hstate
          hagrees)
    (some initial) node hinitial

/-- Raw singleton safety from a live state transfers exactly to the policy
obtained by certifying a global family which agrees at that state's key. -/
theorem ownerFibreSafe_toPolicySelection_of_agreeAt
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (key : RootKey A strategy)
    (initial : LiveState (Memory := Memory) A strategy)
    (hinitial :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
        (Memory := Memory) A strategy key initial)
    (hagrees : source.AgreeAt A strategy tables key)
    (hsafe : source.OwnerFibreSafe A strategy hwin (some initial)) :
    (tables.toPolicySelection A strategy hwin initialMemory hvalid
      haccepts).OwnerFibreSafe A strategy hwin initialMemory initial := by
  intro branch
  have hpriorities :
      (fun n ↦
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreSafetyPriority
          (Memory := Memory) A strategy
          (source.ownerFibreSafetyStateAt A strategy hwin (some initial)
            (branchNode branch n))) =
        fun n ↦
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreSafetyPriority
            (Memory := Memory) A strategy
            ((tables.toPolicySelection A strategy hwin initialMemory hvalid
              haccepts).ownerFibreSafetyStateAt A strategy hwin initialMemory
                initial (branchNode branch n)) := by
    funext n
    rw [source.ownerFibreSafetyStateAt_eq_toPolicySelection_of_agreeAt
      A strategy hwin initialMemory tables hvalid haccepts key initial
        (branchNode branch n) hinitial hagrees]
  exact hpriorities ▸ hsafe branch

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

variable
  (initialMemory : RootKey A strategy → Memory)
  (key : RootKey A strategy)
  (table : FixedTable (Memory := Memory) A strategy key)
  (tables : TableSelection (Memory := Memory) A strategy)

/-- A front context has the same realized live state in the raw fixed-key
checker and in a globally certified family agreeing with that fixed table. -/
theorem realizesOwnerFibreFrontContext_iff_toPolicySelection
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (hagrees :
      (table.family A strategy key).AgreeAt A strategy tables key)
    (context : Context A strategy key)
    (state : LiveState (Memory := Memory) A strategy) :
    table.RealizesOwnerFibreFrontContext A strategy hwin initialMemory key
        context state ↔
      (tables.toPolicySelection A strategy hwin initialMemory hvalid
        haccepts).RealizesOwnerFibreFrontContextAt A strategy hwin
          initialMemory key context state := by
  have hroot := tables.toPolicySelection_root A strategy hwin initialMemory
    hvalid haccepts key
  rcases context with context | context
  · unfold RealizesOwnerFibreFrontContext
    unfold
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.RealizesOwnerFibreFrontContextAt
    dsimp only
    rw [hroot]
    rw [(table.family A strategy key).resolvePacket_congr_at A strategy hwin
      tables key
        (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.root
          A strategy initialMemory key)
        rfl _ hagrees]
    rw [tables.resolvePacket_toPolicySelection A strategy hwin initialMemory
      hvalid haccepts]
  · unfold RealizesOwnerFibreFrontContext
    unfold
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.RealizesOwnerFibreFrontContextAt
    dsimp only
    rw [hroot]
    rw [(table.family A strategy key).resolvePacket_congr_at A strategy hwin
      tables key
        (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.root
          A strategy initialMemory key)
        rfl _ hagrees]
    rw [tables.resolvePacket_toPolicySelection A strategy hwin initialMemory
      hvalid haccepts]

/-- For a context realized by the assembled policy, the raw checker starts
from exactly that live state rather than its rejecting sink. -/
theorem ownerFibreInitialState_eq_some_of_toPolicySelection_realizes
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (hagrees :
      (table.family A strategy key).AgreeAt A strategy tables key)
    (context : Context A strategy key)
    (state : LiveState (Memory := Memory) A strategy)
    (hrealizes :
      (tables.toPolicySelection A strategy hwin initialMemory hvalid
        haccepts).RealizesOwnerFibreFrontContextAt A strategy hwin
          initialMemory key context state) :
    table.ownerFibreInitialState A strategy hwin initialMemory key context =
      some state := by
  classical
  have hraw :
      table.RealizesOwnerFibreFrontContext A strategy hwin initialMemory key
        context state :=
    (table.realizesOwnerFibreFrontContext_iff_toPolicySelection A strategy
      hwin initialMemory key tables hvalid haccepts hagrees context state).mpr
        hrealizes
  unfold ownerFibreInitialState
  rw [dif_pos ⟨state, hraw⟩]
  congr 1
  apply
    (tables.toPolicySelection A strategy hwin initialMemory hvalid
      haccepts).ownerFibreFrontContext_realization_unique A strategy hwin
        initialMemory key context
  · exact
      (table.realizesOwnerFibreFrontContext_iff_toPolicySelection A strategy
        hwin initialMemory key tables hvalid haccepts hagrees context _).mp
        (Classical.choose_spec ⟨state, hraw⟩)
  · exact hrealizes

/-- The raw owner branch of one checked fixed-key table proves safety of the
same key's canonical honest entries in the assembled certified policy. -/
theorem EnrichedOwnerSafe.toPolicySelection_safeOnHonestEntriesAt
    (howner : table.EnrichedOwnerSafe A strategy hwin initialMemory key)
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (hagrees :
      (table.family A strategy key).AgreeAt A strategy tables key) :
    (tables.toPolicySelection A strategy hwin initialMemory hvalid
      haccepts).OwnerFibreSafeOnHonestEntriesAt A strategy hwin initialMemory
        key := by
  rw [(tables.toPolicySelection A strategy hwin initialMemory hvalid
    haccepts).ownerFibreSafeOnHonestEntriesAt_iff A strategy hwin
      initialMemory key]
  intro context state hrealizes
  have hinitial := table.ownerFibreInitialState_eq_some_of_toPolicySelection_realizes
    A strategy hwin initialMemory key tables hvalid haccepts hagrees context
      state hrealizes
  have hraw := howner context
  rw [hinitial] at hraw
  have hmem : state ∈
      (tables.toPolicySelection A strategy hwin initialMemory hvalid
        haccepts).ownerFibreHonestEntriesAt A strategy hwin initialMemory
          key :=
    ((tables.toPolicySelection A strategy hwin initialMemory hvalid
      haccepts).mem_ownerFibreHonestEntriesAt_iff_exists_frontContext A
        strategy hwin initialMemory key state).mpr ⟨context, hrealizes⟩
  have hkey :=
    (tables.toPolicySelection A strategy hwin initialMemory hvalid
      haccepts).ownerFibreHonestEntriesAt_liveStateAtKey A strategy hwin
        initialMemory key state hmem
  exact
    (table.family A strategy key).ownerFibreSafe_toPolicySelection_of_agreeAt
      A strategy hwin initialMemory tables hvalid haccepts key state hkey
        hagrees hraw

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

/-- Pointwise effect-coherent enriched checks assemble into one certified
finite-memory selection which is owner-safe at every canonical honest entry.
No Cartesian product of unrelated root-key choices is used. -/
theorem
    exists_profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection_safe_of_effectEnrichedChecks
    (initialMemory : RootKey A strategy → Memory)
    (hlocal : ∀ key : RootKey A strategy,
      ∃ table : FixedTable (Memory := Memory) A strategy key,
        table.EffectEnrichedChecks A strategy hwin initialMemory key) :
    ∃ selection : PolicySelection (Memory := Memory) A strategy hwin
        initialMemory,
      ∀ key,
        selection.OwnerFibreSafeOnHonestEntriesAt A strategy hwin
          initialMemory key := by
  choose chosen hchecks using hlocal
  let tables : TableSelection (Memory := Memory) A strategy :=
    fun key ↦ chosen key
  have hvalid : tables.ValidAt A strategy hwin initialMemory := by
    intro key
    exact (hchecks key).1.toTransitionTableValidAt A strategy hwin
      initialMemory key (chosen key)
  have haccepts : tables.Accepts A strategy initialMemory := by
    intro key
    exact (hchecks key).2.1
  let selection : PolicySelection (Memory := Memory) A strategy hwin
      initialMemory :=
    tables.toPolicySelection A strategy hwin initialMemory hvalid haccepts
  refine ⟨selection, ?_⟩
  intro key
  have hagrees :
      ((chosen key).family A strategy key).AgreeAt A strategy tables key := by
    unfold
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable.family
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.AgreeAt
      tables
    simp
  exact (hchecks key).2.2.toPolicySelection_safeOnHonestEntriesAt A strategy
    hwin initialMemory key (chosen key) tables hvalid haccepts hagrees

end

end DetParityAutomaton

end DistributedSynthesis
