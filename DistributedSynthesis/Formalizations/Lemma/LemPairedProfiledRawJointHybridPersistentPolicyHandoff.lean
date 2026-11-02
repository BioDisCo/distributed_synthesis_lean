/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPersistentPhysicalClose
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitRightPolicyHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitLeftPolicyHandoff

/-!
# Persistent hybrid-policy macros and handoff

The recurrent macro stores a reachable `oneSided` key of one fixed hybrid
policy and its unique active lane.  A block certificate may propose any
finite policy state, but the physical-close projection recognizes only a
`oneSided` target with the required opposite lane.  Thus an allowed physical
close stages another macro in the same policy; common/dead targets cannot be
silently admitted.
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

/-! ## Live macros in one fixed hybrid policy -/

structure ProfiledRawJointHybridPersistentRightMacro
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode) where
  key : ProfiledRawJointHybridOneSidedPolicyKey A strategy initialCode policy
  slot : ProfiledRawRightSlot A
  active_slot : key.incidenceCode.family.right () = some slot

structure ProfiledRawJointHybridPersistentLeftMacro
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode) where
  key : ProfiledRawJointHybridOneSidedPolicyKey A strategy initialCode policy
  slot : ProfiledRawLeftSlot A
  active_slot : key.incidenceCode.family.left () = some slot

noncomputable instance profiledRawJointHybridPersistentRightMacroFintype
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode) :
    Fintype (ProfiledRawJointHybridPersistentRightMacro A strategy initialCode
      policy) := by
  classical
  let encode := fun entry : ProfiledRawJointHybridPersistentRightMacro A
      strategy initialCode policy ↦ (entry.key, entry.slot)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftKey, leftSlot, leftActive⟩
    rcases right with ⟨rightKey, rightSlot, rightActive⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rfl)

noncomputable instance profiledRawJointHybridPersistentLeftMacroFintype
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode) :
    Fintype (ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode
      policy) := by
  classical
  let encode := fun entry : ProfiledRawJointHybridPersistentLeftMacro A
      strategy initialCode policy ↦ (entry.key, entry.slot)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftKey, leftSlot, leftActive⟩
    rcases right with ⟨rightKey, rightSlot, rightActive⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rfl)

/-! ## Monitor-facing target projections -/

noncomputable instance profiledRawJointHybridProvenancePolicyStateInhabited
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A} :
    Inhabited (ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode) :=
  ⟨(initialCode, (profiledRawJointHybridCodeParityDPA A initialCode).initial)⟩

/-- A right close recognizes only a tagged one-sided target with a live left
slot.  Common and dead tags deliberately project to the impossible initial
profiled state. -/
def profiledRawJointHybridPersistentRightTargetProfiledState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    (target : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode) : PairedProfiledTreeState A :=
  match target.1 with
  | .oneSided code =>
      match code.family.left () with
      | some slot => .inr (.inr slot)
      | none => .inl PUnit.unit
  | _ => .inl PUnit.unit

/-- Left-close mirror. -/
def profiledRawJointHybridPersistentLeftTargetProfiledState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    (target : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode) : PairedProfiledTreeState A :=
  match target.1 with
  | .oneSided code =>
      match code.family.right () with
      | some slot => .inr (.inl slot)
      | none => .inl PUnit.unit
  | _ => .inl PUnit.unit

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointHybridPersistentRightTargetProfiledState_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    (target : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawLeftSlot A)
    (hcode : target.1 = .oneSided code)
    (hslot : code.family.left () = some slot) :
    profiledRawJointHybridPersistentRightTargetProfiledState A target =
      .inr (.inr slot) := by
  simp [profiledRawJointHybridPersistentRightTargetProfiledState, hcode, hslot]

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointHybridPersistentLeftTargetProfiledState_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    (target : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawRightSlot A)
    (hcode : target.1 = .oneSided code)
    (hslot : code.family.right () = some slot) :
    profiledRawJointHybridPersistentLeftTargetProfiledState A target =
      .inr (.inl slot) := by
  simp [profiledRawJointHybridPersistentLeftTargetProfiledState, hcode, hslot]

/-! ## Staging an allowed target -/

def profiledRawJointHybridPersistentStageLeftOfAllowed
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointHybridPersistentRightMacro A strategy
      initialCode policy)
    (target : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawLeftSlot A)
    (hallowed : ProfiledRawJointHybridProvenanceAllowedTarget A strategy
      initialCode policy source.key.state target)
    (hcode : target.1 = .oneSided code)
    (hslot : code.family.left () = some slot) :
    ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode policy :=
  { key :=
      { incidenceCode := code
        state := target
        reachable :=
          SourceFreeBeliefFiniteCodePolicyImage.reachable_of_allowedTarget
            (profiledRawJointHybridCodeParityDPA A initialCode)
            initialCode (ProfiledRawJointHybridProvenanceValid A strategy)
            (profiledRawJointHybridNext A) policy source.key.reachable hallowed
        state_code := hcode }
    slot := slot
    active_slot := hslot }

def profiledRawJointHybridPersistentStageRightOfAllowed
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode
      policy)
    (target : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawRightSlot A)
    (hallowed : ProfiledRawJointHybridProvenanceAllowedTarget A strategy
      initialCode policy source.key.state target)
    (hcode : target.1 = .oneSided code)
    (hslot : code.family.right () = some slot) :
    ProfiledRawJointHybridPersistentRightMacro A strategy initialCode policy :=
  { key :=
      { incidenceCode := code
        state := target
        reachable :=
          SourceFreeBeliefFiniteCodePolicyImage.reachable_of_allowedTarget
            (profiledRawJointHybridCodeParityDPA A initialCode)
            initialCode (ProfiledRawJointHybridProvenanceValid A strategy)
            (profiledRawJointHybridNext A) policy source.key.reachable hallowed
        state_code := hcode }
    slot := slot
    active_slot := hslot }

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridPersistentStageLeftOfAllowed_state
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointHybridPersistentRightMacro A strategy
      initialCode policy)
    (target : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawLeftSlot A)
    (hallowed hcode hslot) :
    (profiledRawJointHybridPersistentStageLeftOfAllowed A strategy initialCode
      policy source target code slot hallowed hcode hslot).key.state = target :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridPersistentStageRightOfAllowed_state
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode
      policy)
    (target : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawRightSlot A)
    (hallowed hcode hslot) :
    (profiledRawJointHybridPersistentStageRightOfAllowed A strategy initialCode
      policy source target code slot hallowed hcode hslot).key.state = target :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
