/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPersistentControllerBank
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointTargetBlockHandoff

/-!
# Local handoff below one root-pinned hybrid policy

For a fixed first input, every recurrent right or left block uses a finite
controller selected from the same root-pinned guarded policy.  This file adds
the executable shell: finite owner and receiver controls, local steps, and a
checked handoff to an opposite live macro.

The staged macro stores the target literally emitted by the narrowed
controller.  Its reachability and false root bit are derived from the checked
edge of the original guarded policy.  No local transition receives a graph,
an orientation, or a strict-leader signal.
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
  (first : In₁ × In₂)

/-! ## Inverting a checked target and staying in the guarded policy -/

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- A checked right close can only project from a one-sided guarded target
with a live left slot. -/
theorem
    exists_profiledRawJointHybridInitialRootPinnedLeftData_of_rightTarget_erasesClose
    (target :
      ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy first)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointHybridInitialRootPinnedRightTargetProfiledState A
          target) = pairedRightCloseTarget A scan row physical) :
    ∃ code : ProfiledRawJointIncidenceCode A (I := Unit),
      ∃ slot : ProfiledRawLeftSlot A,
        target.2.1 = .oneSided code ∧ code.family.left () = some slot := by
  cases hcode : target.2.1 with
  | common code =>
      cases row <;>
        simp [profiledRawJointHybridInitialRootPinnedRightTargetProfiledState,
          hcode, erasePairedProfiledState, pairedRightCloseTarget] at hclose
  | oneSided code =>
      cases hslot : code.family.left () with
      | none =>
          cases row <;>
            simp [
              profiledRawJointHybridInitialRootPinnedRightTargetProfiledState,
              hcode, hslot, erasePairedProfiledState, pairedRightCloseTarget]
              at hclose
      | some slot => exact ⟨code, slot, rfl, hslot⟩
  | dead =>
      cases row <;>
        simp [profiledRawJointHybridInitialRootPinnedRightTargetProfiledState,
          hcode, erasePairedProfiledState, pairedRightCloseTarget] at hclose

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left-to-right mirror of target-shape inversion. -/
theorem
    exists_profiledRawJointHybridInitialRootPinnedRightData_of_leftTarget_erasesClose
    (target :
      ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy first)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState A
          target) = pairedLeftCloseTarget A scan row physical) :
    ∃ code : ProfiledRawJointIncidenceCode A (I := Unit),
      ∃ slot : ProfiledRawRightSlot A,
        target.2.1 = .oneSided code ∧ code.family.right () = some slot := by
  cases hcode : target.2.1 with
  | common code =>
      cases row <;>
        simp [profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState,
          hcode, erasePairedProfiledState, pairedLeftCloseTarget] at hclose
  | oneSided code =>
      cases hslot : code.family.right () with
      | none =>
          cases row <;>
            simp [
              profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState,
              hcode, hslot, erasePairedProfiledState, pairedLeftCloseTarget]
              at hclose
      | some slot => exact ⟨code, slot, rfl, hslot⟩
  | dead =>
      cases row <;>
        simp [profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState,
          hcode, erasePairedProfiledState, pairedLeftCloseTarget] at hclose

/-- Package an allowed right-block target as the exact opposite live macro
of the same fixed-first guarded policy. -/
def profiledRawJointHybridInitialRootPinnedStageLeftOfAllowed
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (target :
      ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy first)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawLeftSlot A)
    (hallowed : ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy
      hwin first source.key.state target)
    (hcode : target.2.1 = .oneSided code)
    (hslot : code.family.left () = some slot) :
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy hwin
      first := by
  let childCode := Classical.choose hallowed
  have hchild := Classical.choose_spec hallowed
  refine {
    key := {
      incidenceCode := code
      state := target
      reachable := ?_
      fresh_false := ?_
      state_code := hcode }
    slot := slot
    active_slot := hslot }
  · rcases source.key.reachable with ⟨node, hnode⟩
    refine ⟨node ++ [childCode], ?_⟩
    rw [← (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin
      first).policy.successor_at node childCode, hnode, hchild]
  · rw [← hchild]
    exact profiledRawJointHybridInitialRootPinned_successor_fresh_false A
      strategy hwin first source.key.state source.key.reachable
        source.key.fresh_false childCode

/-- Package an allowed left-block target as the exact opposite live macro. -/
def profiledRawJointHybridInitialRootPinnedStageRightOfAllowed
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (target :
      ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy first)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawRightSlot A)
    (hallowed : ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy
      hwin first source.key.state target)
    (hcode : target.2.1 = .oneSided code)
    (hslot : code.family.right () = some slot) :
    ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy hwin
      first := by
  let childCode := Classical.choose hallowed
  have hchild := Classical.choose_spec hallowed
  refine {
    key := {
      incidenceCode := code
      state := target
      reachable := ?_
      fresh_false := ?_
      state_code := hcode }
    slot := slot
    active_slot := hslot }
  · rcases source.key.reachable with ⟨node, hnode⟩
    refine ⟨node ++ [childCode], ?_⟩
    rw [← (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin
      first).policy.successor_at node childCode, hnode, hchild]
  · rw [← hchild]
    exact profiledRawJointHybridInitialRootPinned_successor_fresh_false A
      strategy hwin first source.key.state source.key.reachable
        source.key.fresh_false childCode

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledRawJointHybridInitialRootPinnedStageLeftOfAllowed_state
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (target :
      ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy first)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawLeftSlot A) (hallowed hcode hslot) :
    (profiledRawJointHybridInitialRootPinnedStageLeftOfAllowed A strategy hwin
      first source target code slot hallowed hcode hslot).key.state = target :=
  by
    simp [profiledRawJointHybridInitialRootPinnedStageLeftOfAllowed]

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledRawJointHybridInitialRootPinnedStageRightOfAllowed_state
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (target :
      ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy first)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawRightSlot A) (hallowed hcode hslot) :
    (profiledRawJointHybridInitialRootPinnedStageRightOfAllowed A strategy hwin
      first source target code slot hallowed hcode hslot).key.state = target :=
  by
    simp [profiledRawJointHybridInitialRootPinnedStageRightOfAllowed]

/-! ## Stable certificate-to-macro maps -/

/-- Turn one checked target certificate into the exact emitted left macro.
The choices only unpack the finite one-sided payload forced by `hclose`. -/
noncomputable def
    profiledRawJointHybridInitialRootPinnedLeftMacroOfRightCertificate
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (target :
      ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy first)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointHybridInitialRootPinnedRightTargetProfiledState A
          target) = pairedRightCloseTarget A scan row physical)
    (hallowed : ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy
      hwin first source.key.state target) :
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy hwin
      first :=
  let data :=
    exists_profiledRawJointHybridInitialRootPinnedLeftData_of_rightTarget_erasesClose
      A strategy first target scan row physical hclose
  profiledRawJointHybridInitialRootPinnedStageLeftOfAllowed A strategy hwin
    first source target (Classical.choose data)
      (Classical.choose (Classical.choose_spec data)) hallowed
      (Classical.choose_spec (Classical.choose_spec data)).1
      (Classical.choose_spec (Classical.choose_spec data)).2

/-- Left-to-right certificate map. -/
noncomputable def
    profiledRawJointHybridInitialRootPinnedRightMacroOfLeftCertificate
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (target :
      ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy first)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState A
          target) = pairedLeftCloseTarget A scan row physical)
    (hallowed : ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy
      hwin first source.key.state target) :
    ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy hwin
      first :=
  let data :=
    exists_profiledRawJointHybridInitialRootPinnedRightData_of_leftTarget_erasesClose
      A strategy first target scan row physical hclose
  profiledRawJointHybridInitialRootPinnedStageRightOfAllowed A strategy hwin
    first source target (Classical.choose data)
      (Classical.choose (Classical.choose_spec data)) hallowed
      (Classical.choose_spec (Classical.choose_spec data)).1
      (Classical.choose_spec (Classical.choose_spec data)).2

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledRawJointHybridInitialRootPinnedLeftMacroOfRightCertificate_state
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (target :
      ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy first)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose hallowed) :
    (profiledRawJointHybridInitialRootPinnedLeftMacroOfRightCertificate A
      strategy hwin first source target scan row physical hclose hallowed
      ).key.state = target := by
  simp [profiledRawJointHybridInitialRootPinnedLeftMacroOfRightCertificate]

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledRawJointHybridInitialRootPinnedRightMacroOfLeftCertificate_state
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (target :
      ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy first)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose hallowed) :
    (profiledRawJointHybridInitialRootPinnedRightMacroOfLeftCertificate A
      strategy hwin first source target scan row physical hclose hallowed
      ).key.state = target := by
  simp [profiledRawJointHybridInitialRootPinnedRightMacroOfLeftCertificate]

/-! ## Fixed-first monitor and finite local control families -/

abbrev profiledRawJointHybridInitialRootPinnedPersistentRightMonitor
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first) :=
  profiledRawJointTargetRightBlockMonitor A
    (ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy first)
    (profiledRawJointHybridInitialRootPinnedRightTargetProfiledState A)
    (ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin first
      source.key.state) source.slot

abbrev profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first) :=
  profiledRawJointTargetLeftBlockMonitor A
    (ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy first)
    (profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState A)
    (ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin first
      source.key.state) source.slot

abbrev ProfiledRawJointHybridInitialRootPinnedPersistentRightOwnerControl
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first) :=
  Σ source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first,
    ((bank.right source).1).Control

abbrev ProfiledRawJointHybridInitialRootPinnedPersistentLeftOwnerControl
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first) :=
  Σ source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first,
    ((bank.left source).1).Control

abbrev ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverControl :=
  Σ source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first,
    PairedEntryRow ×
      (profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
        hwin first source).State ×
      Option
        (ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
          hwin first)

abbrev ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverControl :=
  Σ source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first,
    PairedEntryRow ×
      (profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
        hwin first source).State ×
      Option
        (ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
          hwin first)

noncomputable instance
    profiledRawJointHybridInitialRootPinnedPersistentRightOwnerControlFintype
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first) :
    Fintype
      (ProfiledRawJointHybridInitialRootPinnedPersistentRightOwnerControl A
        strategy hwin first bank) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridInitialRootPinnedPersistentLeftOwnerControlFintype
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first) :
    Fintype
      (ProfiledRawJointHybridInitialRootPinnedPersistentLeftOwnerControl A
        strategy hwin first bank) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridInitialRootPinnedPersistentRightReceiverControlFintype :
    Fintype
      (ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverControl A
        strategy hwin first) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridInitialRootPinnedPersistentLeftReceiverControlFintype :
    Fintype
      (ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverControl A
        strategy hwin first) := by
  classical
  infer_instance

/-! ## Initialization and owner steps -/

noncomputable def
    initialProfiledRawJointHybridInitialRootPinnedPersistentRightOwner
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first) :
    ProfiledRawJointHybridInitialRootPinnedPersistentRightOwnerControl A
      strategy hwin first bank :=
  ⟨source, ((bank.right source).1).initial⟩

noncomputable def
    initialProfiledRawJointHybridInitialRootPinnedPersistentLeftOwner
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first) :
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftOwnerControl A
      strategy hwin first bank :=
  ⟨source, ((bank.left source).1).initial⟩

noncomputable def
    initialProfiledRawJointHybridInitialRootPinnedPersistentRightReceiver
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverControl A
      strategy hwin first :=
  ⟨source, row,
    (profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
      hwin first source).initial,
    none⟩

noncomputable def
    initialProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiver
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverControl A
      strategy hwin first :=
  ⟨source, row,
    (profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
      hwin first source).initial,
    none⟩

noncomputable def
    stepProfiledRawJointHybridInitialRootPinnedPersistentRightOwner
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (owner :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightOwnerControl A
        strategy hwin first bank)
    (input : In₁) :
    Out₁ ×
      ProfiledRawJointHybridInitialRootPinnedPersistentRightOwnerControl A
        strategy hwin first bank :=
  let controller := (bank.right owner.1).1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

noncomputable def
    stepProfiledRawJointHybridInitialRootPinnedPersistentLeftOwner
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (owner :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftOwnerControl A
        strategy hwin first bank)
    (input : In₂) :
    Out₂ ×
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftOwnerControl A
        strategy hwin first bank :=
  let controller := (bank.left owner.1).1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    stepProfiledRawJointHybridInitialRootPinnedPersistentRightOwner_source
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (owner :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightOwnerControl A
        strategy hwin first bank)
    (input : In₁) :
    (stepProfiledRawJointHybridInitialRootPinnedPersistentRightOwner A strategy
      hwin first bank owner input).2.1 = owner.1 :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    stepProfiledRawJointHybridInitialRootPinnedPersistentLeftOwner_source
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (owner :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftOwnerControl A
        strategy hwin first bank)
    (input : In₂) :
    (stepProfiledRawJointHybridInitialRootPinnedPersistentLeftOwner A strategy
      hwin first bank owner input).2.1 = owner.1 :=
  rfl

/-! ## Checked receiver steps -/

abbrev
    ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverRoundResult
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first) :=
  ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy first)
    ×
    (profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
      hwin first source).State
    × Option
      (ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)

abbrev
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverRoundResult
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first) :=
  ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy first)
    ×
    (profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
      hwin first source).State
    × Option
      (ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)

abbrev ProfiledRawJointHybridInitialRootPinnedPersistentRightCloseSafe
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (ownerControl : ((bank.right source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
        hwin first source).State)
    (move : In₂ × In₁) : Prop :=
  let label := (bank.right source).1.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRawJointTargetRightPhysicalLetter A
    (move, output, label.1 move.2)
  erasePairedProfiledState A
      (profiledRawJointHybridInitialRootPinnedRightTargetProfiledState A
        (output.target row)) =
      pairedRightCloseTarget A monitorState.2.1 row physical ∧
    ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin first
      source.key.state (output.target row)

abbrev ProfiledRawJointHybridInitialRootPinnedPersistentLeftCloseSafe
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (ownerControl : ((bank.left source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
        hwin first source).State)
    (move : In₁ × In₂) : Prop :=
  let label := (bank.left source).1.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRawJointTargetLeftPhysicalLetter A
    (move, output, label.1 move.2)
  erasePairedProfiledState A
      (profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState A
        (output.target row)) =
      pairedLeftCloseTarget A monitorState.2.1 row physical ∧
    ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin first
      source.key.state (output.target row)

noncomputable def
    stepProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverFor
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (ownerControl : ((bank.right source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
        hwin first source).State)
    (move : In₂ × In₁) :
    ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverRoundResult A
      strategy hwin first source := by
  classical
  let monitor :=
    profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
      hwin first source
  let controller := (bank.right source).1
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRawJointTargetRightPhysicalLetter A
    (move, output, label.1 move.2)
  let nextMonitor := monitor.step monitorState
    (move, output, label.1 move.2)
  if hsafe :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightCloseSafe A
        strategy hwin first bank source ownerControl row monitorState move then
    exact (output, nextMonitor,
      some
        (profiledRawJointHybridInitialRootPinnedLeftMacroOfRightCertificate A
          strategy hwin first source (output.target row) monitorState.2.1 row
          physical hsafe.1 hsafe.2))
  else
    exact (output, nextMonitor, none)

noncomputable def
    stepProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverFor
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (ownerControl : ((bank.left source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
        hwin first source).State)
    (move : In₁ × In₂) :
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverRoundResult A
      strategy hwin first source := by
  classical
  let monitor :=
    profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
      hwin first source
  let controller := (bank.left source).1
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRawJointTargetLeftPhysicalLetter A
    (move, output, label.1 move.2)
  let nextMonitor := monitor.step monitorState
    (move, output, label.1 move.2)
  if hsafe :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftCloseSafe A strategy
        hwin first bank source ownerControl row monitorState move then
    exact (output, nextMonitor,
      some
        (profiledRawJointHybridInitialRootPinnedRightMacroOfLeftCertificate A
          strategy hwin first source (output.target row) monitorState.2.1 row
          physical hsafe.1 hsafe.2))
  else
    exact (output, nextMonitor, none)

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem
    stepProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverFor_output
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (ownerControl : ((bank.right source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
        hwin first source).State)
    (move : In₂ × In₁) :
    (stepProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverFor A
      strategy hwin first bank source ownerControl row monitorState move).1 =
      ((bank.right source).1.labelOf ownerControl).2 monitorState move := by
  classical
  simp only [
    stepProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverFor]
  split <;> rfl

@[simp] theorem
    stepProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverFor_output
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (ownerControl : ((bank.left source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
        hwin first source).State)
    (move : In₁ × In₂) :
    (stepProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverFor A
      strategy hwin first bank source ownerControl row monitorState move).1 =
      ((bank.left source).1.labelOf ownerControl).2 monitorState move := by
  classical
  simp only [
    stepProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverFor]
  split <;> rfl

@[simp] theorem
    stepProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverFor_monitor
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (ownerControl : ((bank.right source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
        hwin first source).State)
    (move : In₂ × In₁) :
    (stepProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverFor A
      strategy hwin first bank source ownerControl row monitorState move
      ).2.1 =
      (profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
        hwin first source).step monitorState
        (narrowedRecord
          (profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A
            strategy hwin first source)
          ((bank.right source).1.labelOf ownerControl) monitorState move) := by
  classical
  simp only [
    stepProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverFor,
    narrowedRecord]
  split <;> rfl

@[simp] theorem
    stepProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverFor_monitor
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (ownerControl : ((bank.left source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
        hwin first source).State)
    (move : In₁ × In₂) :
    (stepProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverFor A
      strategy hwin first bank source ownerControl row monitorState move
      ).2.1 =
      (profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
        hwin first source).step monitorState
        (narrowedRecord
          (profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A
            strategy hwin first source)
          ((bank.left source).1.labelOf ownerControl) monitorState move) := by
  classical
  simp only [
    stepProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverFor,
    narrowedRecord]
  split <;> rfl

end

/-! ## Matched local lookup and executable receiver continuation -/

/-- Interpret an owner control at the receiver's stored source.  The fallback
only totalizes the local transition away from the matched-phase invariant. -/
noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentRightOwnerControlFor
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (receiver :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverControl A
        strategy hwin first)
    (owner :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightOwnerControl A
        strategy hwin first bank) :
    ((bank.right receiver.1).1).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else ((bank.right receiver.1).1).initial

noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentLeftOwnerControlFor
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (receiver :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverControl A
        strategy hwin first)
    (owner :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftOwnerControl A
        strategy hwin first bank) :
    ((bank.left receiver.1).1).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else ((bank.left receiver.1).1).initial

noncomputable def
    continueProfiledRawJointHybridInitialRootPinnedPersistentRightReceiver
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (receiver :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverControl A
        strategy hwin first)
    (owner :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightOwnerControl A
        strategy hwin first bank)
    (move : In₂ × In₁) :
    Out₂ ×
      ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverControl A
        strategy hwin first :=
  let result :=
    stepProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverFor A
      strategy hwin first bank receiver.1
        (profiledRawJointHybridInitialRootPinnedPersistentRightOwnerControlFor
          A strategy hwin first bank receiver owner)
        receiver.2.1 receiver.2.2.1 move
  (pairedRightInformedForRow receiver.2.1 result.1.physical,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

noncomputable def
    continueProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiver
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (receiver :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverControl A
        strategy hwin first)
    (owner :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftOwnerControl A
        strategy hwin first bank)
    (move : In₁ × In₂) :
    Out₁ ×
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverControl A
        strategy hwin first :=
  let result :=
    stepProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverFor A
      strategy hwin first bank receiver.1
        (profiledRawJointHybridInitialRootPinnedPersistentLeftOwnerControlFor A
          strategy hwin first bank receiver owner)
        receiver.2.1 receiver.2.2.1 move
  (pairedLeftInformedForRow receiver.2.1 result.1.physical,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    continueProfiledRawJointHybridInitialRootPinnedPersistentRightReceiver_source
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (receiver :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverControl A
        strategy hwin first)
    (owner :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightOwnerControl A
        strategy hwin first bank)
    (move : In₂ × In₁) :
    (continueProfiledRawJointHybridInitialRootPinnedPersistentRightReceiver A
      strategy hwin first bank receiver owner move).2.1 = receiver.1 :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    continueProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiver_source
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (receiver :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverControl A
        strategy hwin first)
    (owner :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftOwnerControl A
        strategy hwin first bank)
    (move : In₁ × In₂) :
    (continueProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiver A
      strategy hwin first bank receiver owner move).2.1 = receiver.1 :=
  rfl

/-! ## Exact staged target on a successful local check -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem
    stepProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverFor_stagesExact_of_safe
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (ownerControl : ((bank.right source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
        hwin first source).State)
    (move : In₂ × In₁)
    (hsafe :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightCloseSafe A
        strategy hwin first bank source ownerControl row monitorState move) :
    ∃ target :
        ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
          hwin first,
      (stepProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverFor A
        strategy hwin first bank source ownerControl row monitorState move
        ).2.2 = some target ∧
      target.key.state =
        (((bank.right source).1.labelOf ownerControl).2 monitorState move
          ).target row := by
  classical
  simp only [
    stepProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverFor]
  split
  · refine ⟨_, rfl, ?_⟩
    exact
      profiledRawJointHybridInitialRootPinnedLeftMacroOfRightCertificate_state
        A strategy hwin first source _ _ row _ _ _
  · contradiction

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem
    stepProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverFor_stagesExact_of_safe
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (ownerControl : ((bank.left source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
        hwin first source).State)
    (move : In₁ × In₂)
    (hsafe :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftCloseSafe A strategy
        hwin first bank source ownerControl row monitorState move) :
    ∃ target :
        ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
          hwin first,
      (stepProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverFor A
        strategy hwin first bank source ownerControl row monitorState move
        ).2.2 = some target ∧
      target.key.state =
        (((bank.left source).1.labelOf ownerControl).2 monitorState move
          ).target row := by
  classical
  simp only [
    stepProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverFor]
  split
  · refine ⟨_, rfl, ?_⟩
    exact
      profiledRawJointHybridInitialRootPinnedRightMacroOfLeftCertificate_state
        A strategy hwin first source _ _ row _ _ _
  · contradiction

/-! ## Narrowed-controller target extraction -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every concrete letter of a selected right controller yields an opposite
macro whose key state is the literal emitted target. -/
theorem
    profiledRawJointHybridInitialRootPinnedPersistentRight_narrowedTargetMacro
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let monitor :=
      profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
        hwin first source
    let controller := (bank.right source).1
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    ∃ target :
        ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
          hwin first,
      target.key.state = (play n).2.1.target row ∧
        ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
          first source.key.state target.key.state := by
  dsimp only
  let monitor :=
    profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
      hwin first source
  let controller := (bank.right source).1
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have hsafe :=
    profiledRawJointTargetRight_narrowedTargetSafe A
      (profiledRawJointHybridInitialRootPinnedRightTargetProfiledState A)
      (ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
        first source.key.state)
      source.slot controller.labeledTree (bank.right source).2 env n row
  let target :=
    profiledRawJointHybridInitialRootPinnedLeftMacroOfRightCertificate A
      strategy hwin first source ((play n).2.1.target row)
        ((monitor.run play n).2.1) row
        (profiledRawJointTargetRightPhysicalLetter A (play n)) hsafe.1 hsafe.2
  refine ⟨target, ?_, ?_⟩
  · exact
      profiledRawJointHybridInitialRootPinnedLeftMacroOfRightCertificate_state
        A strategy hwin first source _ _ row _ hsafe.1 hsafe.2
  · simpa [target] using hsafe.2

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-to-right mirror of narrowed target extraction. -/
theorem
    profiledRawJointHybridInitialRootPinnedPersistentLeft_narrowedTargetMacro
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let monitor :=
      profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
        hwin first source
    let controller := (bank.left source).1
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    ∃ target :
        ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
          hwin first,
      target.key.state = (play n).2.1.target row ∧
        ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
          first source.key.state target.key.state := by
  dsimp only
  let monitor :=
    profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
      hwin first source
  let controller := (bank.left source).1
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have hsafe :=
    profiledRawJointTargetLeft_narrowedTargetSafe A
      (profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState A)
      (ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
        first source.key.state)
      source.slot controller.labeledTree (bank.left source).2 env n row
  let target :=
    profiledRawJointHybridInitialRootPinnedRightMacroOfLeftCertificate A
      strategy hwin first source ((play n).2.1.target row)
        ((monitor.run play n).2.1) row
        (profiledRawJointTargetLeftPhysicalLetter A (play n)) hsafe.1 hsafe.2
  refine ⟨target, ?_, ?_⟩
  · exact
      profiledRawJointHybridInitialRootPinnedRightMacroOfLeftCertificate_state
        A strategy hwin first source _ _ row _ hsafe.1 hsafe.2
  · simpa [target] using hsafe.2

/-! ## Exact opposite-macro restart -/

noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentRestartLeft
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (target :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (row : PairedEntryRow) :=
  (initialProfiledRawJointHybridInitialRootPinnedPersistentLeftOwner A strategy
      hwin first bank target,
    initialProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiver A
      strategy hwin first target row)

noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentRestartRight
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (target :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (row : PairedEntryRow) :=
  (initialProfiledRawJointHybridInitialRootPinnedPersistentRightOwner A
      strategy hwin first bank target,
    initialProfiledRawJointHybridInitialRootPinnedPersistentRightReceiver A
      strategy hwin first target row)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledRawJointHybridInitialRootPinnedPersistentRestartLeft_commonSource
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (target :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (row : PairedEntryRow) :
    (profiledRawJointHybridInitialRootPinnedPersistentRestartLeft A strategy
      hwin first bank target row).1.1 =
      (profiledRawJointHybridInitialRootPinnedPersistentRestartLeft A strategy
        hwin first bank target row).2.1 :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledRawJointHybridInitialRootPinnedPersistentRestartRight_commonSource
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (target :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (row : PairedEntryRow) :
    (profiledRawJointHybridInitialRootPinnedPersistentRestartRight A strategy
      hwin first bank target row).1.1 =
      (profiledRawJointHybridInitialRootPinnedPersistentRestartRight A strategy
        hwin first bank target row).2.1 :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
