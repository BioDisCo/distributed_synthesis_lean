/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerBisimulation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingTargetSynchronization

/-!
# Receiver fibres over a live physical owner

An owner-only suffix advances the sender control but supplies no full input
pair with which to advance a dormant receiver monitor.  Keeping one old
monitor state therefore creates the clock mismatch exposed by the phase-live
audit.  The finite physical table supplies a different invariant.

For a reachable owner control, retain the finite fibre of all receiver
monitor states reached by some full table prefix whose sender projection
reaches that owner.  The fibre is nonempty, is determined by finite runtime
data, and every one of its states emits only targets allowed by the installed
physical table.  A canonical member can consequently be selected without a
history or graph oracle.

Besides target closure, this file proves that a fixed filler input advances an
arbitrary fibre member through every owner-only suffix while preserving the
fibre invariant.  Every resulting member therefore has the exact bank target
and successor promised by the installed table.  The finite endpoint carrier
and its phase-live integration are packaged in the subsequent owner-fibre
modules.
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

/-! ## Right-table fibres -/

/-- A right-table owner control is reachable by its own finite input word. -/
def ProfiledRawJointRightPhysicalSiblingOwnerReachable
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control) : Prop :=
  ∃ word : List In₁,
    owner = (move.memberController A false).controlAt word

/-- A receiver monitor state lies over `owner` when both arise along some
full table prefix.  Different states in the fibre may use different hidden
receiver-input words, but all have the same finite owner control. -/
def ProfiledRawJointRightPhysicalSiblingReceiverFibre
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (receiverState :
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State) :
    Prop :=
  ∃ past : List (In₂ × In₁),
    owner =
        (move.memberController A false).controlAt (senderWord past) ∧
      receiverState =
        narrowedControl
          (profiledRawJointRightPhysicalSiblingMonitor A move.1 false)
          (move.memberController A false).labeledTree past

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The initial owner is reachable. -/
theorem profiledRawJointRightPhysicalSiblingOwnerReachable_initial
    (move : ProfiledRawJointRightPhysicalSiblingMove A) :
    ProfiledRawJointRightPhysicalSiblingOwnerReachable A move
      (move.memberController A false).initial := by
  exact ⟨[], rfl⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Owner-only evolution preserves owner reachability. -/
theorem ProfiledRawJointRightPhysicalSiblingOwnerReachable.step
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (hreachable :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A move owner)
    (input : In₁) :
    ProfiledRawJointRightPhysicalSiblingOwnerReachable A move
      ((move.memberController A false).step owner input) := by
  rcases hreachable with ⟨word, rfl⟩
  refine ⟨word ++ [input], ?_⟩
  rw [TransitionRationalTree.controlAt_append]
  rfl

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every reachable right owner has a nonempty receiver fibre.  Pairing its
own input word with an arbitrary receiver-input word produces one witness. -/
theorem
    ProfiledRawJointRightPhysicalSiblingOwnerReachable.receiverFibre_nonempty
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (hreachable :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A move owner) :
    ∃ receiverState,
      ProfiledRawJointRightPhysicalSiblingReceiverFibre A move owner
        receiverState := by
  rcases hreachable with ⟨word, howner⟩
  let past : List (In₂ × In₁) := word.map fun input ↦ (default, input)
  refine ⟨narrowedControl
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 false)
      (move.memberController A false).labeledTree past, past, ?_, rfl⟩
  simpa [past, senderWord] using howner

/-- Choose one member of the finite fibre.  The fallback totalizes
unreachable owner controls and is eliminated by `receiverFibreChoice_mem`. -/
noncomputable def profiledRawJointRightPhysicalSiblingReceiverFibreChoice
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control) :
    (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State := by
  classical
  exact if h : ∃ receiverState,
      ProfiledRawJointRightPhysicalSiblingReceiverFibre A move owner
        receiverState then
    Classical.choose h
  else
    (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).initial

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRightPhysicalSiblingReceiverFibreChoice_mem
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (hreachable :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A move owner) :
    ProfiledRawJointRightPhysicalSiblingReceiverFibre A move owner
      (profiledRawJointRightPhysicalSiblingReceiverFibreChoice A move
        owner) := by
  have hnonempty := hreachable.receiverFibre_nonempty A move owner
  simp only [profiledRawJointRightPhysicalSiblingReceiverFibreChoice,
    dif_pos hnonempty]
  exact Classical.choose_spec hnonempty

/-- Advance a latent right owner/receiver pair on an owner-only round by
using a fixed filler for the unavailable receiver input.  The emitted
receiver output is discarded; only the two finite successor states are
retained. -/
noncomputable def profiledRawJointRightPhysicalSiblingReceiverFibreNoRecv
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (receiverState :
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State)
    (input : In₁) :
    (move.memberController A false).Control ×
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State :=
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  let fullInput : In₂ × In₁ := (default, input)
  (controller.step owner input,
    monitor.step receiverState
      (narrowedRecord monitor (controller.labelOf owner) receiverState
        fullInput))

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] in
/-- The fixed-filler update preserves the fibre relation exactly.  Hence a
latent pair can be advanced coherently for an arbitrary owner-only suffix;
no state/successor output compatibility is required. -/
theorem ProfiledRawJointRightPhysicalSiblingReceiverFibre.noRecv
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (receiverState :
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State)
    (hfibre :
      ProfiledRawJointRightPhysicalSiblingReceiverFibre A move owner
        receiverState)
    (input : In₁) :
    ProfiledRawJointRightPhysicalSiblingReceiverFibre A move
      (profiledRawJointRightPhysicalSiblingReceiverFibreNoRecv A move owner
        receiverState input).1
      (profiledRawJointRightPhysicalSiblingReceiverFibreNoRecv A move owner
        receiverState input).2 := by
  rcases hfibre with ⟨past, rfl, rfl⟩
  refine ⟨past ++ [(default, input)], ?_, ?_⟩
  · rw [senderWord_append, TransitionRationalTree.controlAt_append]
    rfl
  · rw [narrowedControl_append]
    rfl

noncomputable def profiledRawJointRightPhysicalSiblingReceiverFibreRun
    (move : ProfiledRawJointRightPhysicalSiblingMove A) :
    ((move.memberController A false).Control ×
        (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State) →
      List In₁ →
        ((move.memberController A false).Control ×
          (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State)
  | state, [] => state
  | state, input :: rest =>
      profiledRawJointRightPhysicalSiblingReceiverFibreRun move
        (profiledRawJointRightPhysicalSiblingReceiverFibreNoRecv A move
          state.1 state.2 input) rest

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] in
/-- Arbitrary-prefix closure of the coherent right fibre update. -/
theorem ProfiledRawJointRightPhysicalSiblingReceiverFibre.run
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (receiverState :
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State)
    (hfibre :
      ProfiledRawJointRightPhysicalSiblingReceiverFibre A move owner
        receiverState)
    (inputs : List In₁) :
    ProfiledRawJointRightPhysicalSiblingReceiverFibre A move
      (profiledRawJointRightPhysicalSiblingReceiverFibreRun A move
        (owner, receiverState) inputs).1
      (profiledRawJointRightPhysicalSiblingReceiverFibreRun A move
        (owner, receiverState) inputs).2 := by
  induction inputs generalizing owner receiverState with
  | nil => exact hfibre
  | cons input rest ih =>
      simpa [profiledRawJointRightPhysicalSiblingReceiverFibreRun] using
        ih _ _ (hfibre.noRecv A move owner receiverState input)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Sparse target closure: every state in the fibre of a reachable owner
emits an allowed target on every next full input. -/
theorem ProfiledRawJointRightPhysicalSiblingReceiverFibre.targetSafe
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (receiverState :
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State)
    (hfibre :
      ProfiledRawJointRightPhysicalSiblingReceiverFibre A move owner
        receiverState)
    (input : In₂ × In₁) (row : PairedEntryRow) :
    profiledRawJointRightPhysicalSiblingAllowed A move.1
      ((((move.memberController A false).labelOf owner).2 receiverState input
        ).target row) := by
  rcases hfibre with ⟨past, howner, hreceiver⟩
  subst owner
  subst receiverState
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [input])
  have hsafe := move.memberController_targetSafe A false env past.length row
  have hprefix := profiledRawJointRightPhysicalSibling_treePlay_at_prefix A
    move past input
  dsimp only at hsafe hprefix
  rw [hprefix] at hsafe
  exact hsafe.2

/-- Every coherent right fibre state can hand its next target directly to the
recurrent bank resolver.  This is the one-step closure theorem used after any
number of fixed-filler owner-only updates. -/
theorem ProfiledRawJointRightPhysicalSiblingReceiverFibre.bankTarget
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin)
    (hstate :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : state.2.1.2.1 = some move)
    (owner : (move.memberController A false).Control)
    (receiverState :
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State)
    (hfibre :
      ProfiledRawJointRightPhysicalSiblingReceiverFibre A move owner
        receiverState)
    (input : In₂ × In₁) (row : PairedEntryRow) :
    let target :=
      ((((move.memberController A false).labelOf owner).2 receiverState input
        ).target row)
    let childCode :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
        hwin state target
    childCode.1 = target ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode ∧
      (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state childCode).1 = state.1 ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
          hwin state childCode) := by
  dsimp only
  apply
    profiledRawJointOneSidedPhysicalCompatibleBankResolveRightTarget_spec A
      strategy hwin state hstate currentCode hcurrentCode root hroot move hmove
  exact hfibre.targetSafe A move owner receiverState input row

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The canonical finite choice therefore has the same universal target
safety whenever the owner is reachable. -/
theorem profiledRawJointRightPhysicalSiblingReceiverFibreChoice_targetSafe
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (hreachable :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A move owner)
    (input : In₂ × In₁) (row : PairedEntryRow) :
    profiledRawJointRightPhysicalSiblingAllowed A move.1
      ((((move.memberController A false).labelOf owner).2
          (profiledRawJointRightPhysicalSiblingReceiverFibreChoice A move
            owner) input).target row) := by
  exact
    (profiledRawJointRightPhysicalSiblingReceiverFibreChoice_mem A move owner
      hreachable).targetSafe A move owner _ input row

/-- The recurrent bank can resolve the target emitted from the canonical
right fibre state.  This is the bank-level sparse target-closure theorem: its
hypotheses contain owner reachability, but no matched receiver prefix. -/
theorem profiledRawJointRightPhysicalSiblingReceiverFibreChoice_bankTarget
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin)
    (hstate :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : state.2.1.2.1 = some move)
    (owner : (move.memberController A false).Control)
    (howner :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A move owner)
    (input : In₂ × In₁) (row : PairedEntryRow) :
    let receiverState :=
      profiledRawJointRightPhysicalSiblingReceiverFibreChoice A move owner
    let target :=
      ((((move.memberController A false).labelOf owner).2 receiverState input
        ).target row)
    let childCode :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
        hwin state target
    childCode.1 = target ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode ∧
      (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state childCode).1 = state.1 ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
          hwin state childCode) := by
  dsimp only
  apply
    profiledRawJointOneSidedPhysicalCompatibleBankResolveRightTarget_spec A
      strategy hwin state hstate currentCode hcurrentCode root hroot move hmove
  exact profiledRawJointRightPhysicalSiblingReceiverFibreChoice_targetSafe A
    move owner howner input row

/-! ## Left-table mirror -/

def ProfiledRawJointLeftPhysicalSiblingOwnerReachable
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control) : Prop :=
  ∃ word : List In₂,
    owner = (move.memberController A false).controlAt word

def ProfiledRawJointLeftPhysicalSiblingReceiverFibre
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (receiverState :
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State) :
    Prop :=
  ∃ past : List (In₁ × In₂),
    owner =
        (move.memberController A false).controlAt (senderWord past) ∧
      receiverState =
        narrowedControl
          (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false)
          (move.memberController A false).labeledTree past

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointLeftPhysicalSiblingOwnerReachable_initial
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) :
    ProfiledRawJointLeftPhysicalSiblingOwnerReachable A move
      (move.memberController A false).initial := by
  exact ⟨[], rfl⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointLeftPhysicalSiblingOwnerReachable.step
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (hreachable :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A move owner)
    (input : In₂) :
    ProfiledRawJointLeftPhysicalSiblingOwnerReachable A move
      ((move.memberController A false).step owner input) := by
  rcases hreachable with ⟨word, rfl⟩
  refine ⟨word ++ [input], ?_⟩
  rw [TransitionRationalTree.controlAt_append]
  rfl

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledRawJointLeftPhysicalSiblingOwnerReachable.receiverFibre_nonempty
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (hreachable :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A move owner) :
    ∃ receiverState,
      ProfiledRawJointLeftPhysicalSiblingReceiverFibre A move owner
        receiverState := by
  rcases hreachable with ⟨word, howner⟩
  let past : List (In₁ × In₂) := word.map fun input ↦ (default, input)
  refine ⟨narrowedControl
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false)
      (move.memberController A false).labeledTree past, past, ?_, rfl⟩
  simpa [past, senderWord] using howner

noncomputable def profiledRawJointLeftPhysicalSiblingReceiverFibreChoice
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control) :
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State := by
  classical
  exact if h : ∃ receiverState,
      ProfiledRawJointLeftPhysicalSiblingReceiverFibre A move owner
        receiverState then
    Classical.choose h
  else
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).initial

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointLeftPhysicalSiblingReceiverFibreChoice_mem
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (hreachable :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A move owner) :
    ProfiledRawJointLeftPhysicalSiblingReceiverFibre A move owner
      (profiledRawJointLeftPhysicalSiblingReceiverFibreChoice A move
        owner) := by
  have hnonempty := hreachable.receiverFibre_nonempty A move owner
  simp only [profiledRawJointLeftPhysicalSiblingReceiverFibreChoice,
    dif_pos hnonempty]
  exact Classical.choose_spec hnonempty

noncomputable def profiledRawJointLeftPhysicalSiblingReceiverFibreNoRecv
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (receiverState :
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State)
    (input : In₂) :
    (move.memberController A false).Control ×
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State :=
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  let fullInput : In₁ × In₂ := (default, input)
  (controller.step owner input,
    monitor.step receiverState
      (narrowedRecord monitor (controller.labelOf owner) receiverState
        fullInput))

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointLeftPhysicalSiblingReceiverFibre.noRecv
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (receiverState :
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State)
    (hfibre :
      ProfiledRawJointLeftPhysicalSiblingReceiverFibre A move owner
        receiverState)
    (input : In₂) :
    ProfiledRawJointLeftPhysicalSiblingReceiverFibre A move
      (profiledRawJointLeftPhysicalSiblingReceiverFibreNoRecv A move owner
        receiverState input).1
      (profiledRawJointLeftPhysicalSiblingReceiverFibreNoRecv A move owner
        receiverState input).2 := by
  rcases hfibre with ⟨past, rfl, rfl⟩
  refine ⟨past ++ [(default, input)], ?_, ?_⟩
  · rw [senderWord_append, TransitionRationalTree.controlAt_append]
    rfl
  · rw [narrowedControl_append]
    rfl

noncomputable def profiledRawJointLeftPhysicalSiblingReceiverFibreRun
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) :
    ((move.memberController A false).Control ×
        (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State) →
      List In₂ →
        ((move.memberController A false).Control ×
          (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State)
  | state, [] => state
  | state, input :: rest =>
      profiledRawJointLeftPhysicalSiblingReceiverFibreRun move
        (profiledRawJointLeftPhysicalSiblingReceiverFibreNoRecv A move
          state.1 state.2 input) rest

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointLeftPhysicalSiblingReceiverFibre.run
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (receiverState :
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State)
    (hfibre :
      ProfiledRawJointLeftPhysicalSiblingReceiverFibre A move owner
        receiverState)
    (inputs : List In₂) :
    ProfiledRawJointLeftPhysicalSiblingReceiverFibre A move
      (profiledRawJointLeftPhysicalSiblingReceiverFibreRun A move
        (owner, receiverState) inputs).1
      (profiledRawJointLeftPhysicalSiblingReceiverFibreRun A move
        (owner, receiverState) inputs).2 := by
  induction inputs generalizing owner receiverState with
  | nil => exact hfibre
  | cons input rest ih =>
      simpa [profiledRawJointLeftPhysicalSiblingReceiverFibreRun] using
        ih _ _ (hfibre.noRecv A move owner receiverState input)

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointLeftPhysicalSiblingReceiverFibre.targetSafe
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (receiverState :
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State)
    (hfibre :
      ProfiledRawJointLeftPhysicalSiblingReceiverFibre A move owner
        receiverState)
    (input : In₁ × In₂) (row : PairedEntryRow) :
    profiledRawJointLeftPhysicalSiblingAllowed A move.1
      ((((move.memberController A false).labelOf owner).2 receiverState input
        ).target row) := by
  rcases hfibre with ⟨past, howner, hreceiver⟩
  subst owner
  subst receiverState
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
  have hsafe := move.memberController_targetSafe A false env past.length row
  have hprefix := profiledRawJointLeftPhysicalSibling_treePlay_at_prefix A
    move past input
  dsimp only at hsafe hprefix
  rw [hprefix] at hsafe
  exact hsafe.2

/-- Mirrored one-step bank closure for an arbitrary coherent left fibre
state. -/
theorem ProfiledRawJointLeftPhysicalSiblingReceiverFibre.bankTarget
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin)
    (hstate :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : state.2.1.2.2 = some move)
    (owner : (move.memberController A false).Control)
    (receiverState :
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State)
    (hfibre :
      ProfiledRawJointLeftPhysicalSiblingReceiverFibre A move owner
        receiverState)
    (input : In₁ × In₂) (row : PairedEntryRow) :
    let target :=
      ((((move.memberController A false).labelOf owner).2 receiverState input
        ).target row)
    let childCode :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
        hwin state target
    childCode.1 = target ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode ∧
      (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state childCode).1 = state.1 ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
          hwin state childCode) := by
  dsimp only
  apply
    profiledRawJointOneSidedPhysicalCompatibleBankResolveLeftTarget_spec A
      strategy hwin state hstate currentCode hcurrentCode root hroot move hmove
  exact hfibre.targetSafe A move owner receiverState input row

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointLeftPhysicalSiblingReceiverFibreChoice_targetSafe
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (hreachable :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A move owner)
    (input : In₁ × In₂) (row : PairedEntryRow) :
    profiledRawJointLeftPhysicalSiblingAllowed A move.1
      ((((move.memberController A false).labelOf owner).2
          (profiledRawJointLeftPhysicalSiblingReceiverFibreChoice A move
            owner) input).target row) := by
  exact
    (profiledRawJointLeftPhysicalSiblingReceiverFibreChoice_mem A move owner
      hreachable).targetSafe A move owner _ input row

/-- Mirrored bank-level sparse target closure. -/
theorem profiledRawJointLeftPhysicalSiblingReceiverFibreChoice_bankTarget
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin)
    (hstate :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : state.2.1.2.2 = some move)
    (owner : (move.memberController A false).Control)
    (howner :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A move owner)
    (input : In₁ × In₂) (row : PairedEntryRow) :
    let receiverState :=
      profiledRawJointLeftPhysicalSiblingReceiverFibreChoice A move owner
    let target :=
      ((((move.memberController A false).labelOf owner).2 receiverState input
        ).target row)
    let childCode :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
        hwin state target
    childCode.1 = target ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode ∧
      (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state childCode).1 = state.1 ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
          hwin state childCode) := by
  dsimp only
  apply
    profiledRawJointOneSidedPhysicalCompatibleBankResolveLeftTarget_spec A
      strategy hwin state hstate currentCode hcurrentCode root hroot move hmove
  exact profiledRawJointLeftPhysicalSiblingReceiverFibreChoice_targetSafe A
    move owner howner input row

end

end DetParityAutomaton

end DistributedSynthesis
