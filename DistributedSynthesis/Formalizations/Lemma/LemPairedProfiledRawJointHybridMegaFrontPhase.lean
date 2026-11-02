/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaIndexedKernel
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialOneRoundReplacement
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridLeaderFreeShadowCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridStagedFrontReceivers
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridSelfPoweredStagedReceivers
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialCommonAmbiguityShadow
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingLocalInstallation

/-!
# The finite exceptional front of the hybrid raw-joint kernel

This file is deliberately only a type layer.  It lists the local controls
that can occur before the construction has entered one fixed recurrent
policy.  In particular, it does not invent a transition for any pair of
controls.

The old initial strict phase is represented by its four honest local halves:
the two root owner/receiver controls and the two guarded exceptional
owner/receiver controls. The common phase likewise stores only local
controls and never a graph,
orientation, or strict-leader bit.

The exact initial immediate-reversal controllers remain exceptional until
their root-pinned block closes.  They must not be confused with the older
ordinary immediate-switch policy family: identifying those two sources would
require an equality which has not been proved.  By contrast, a common-shadow
replacement owner is already an ordinary recurrent owner; the two handoff
definitions at the end expose that definitional transition directly.
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
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

/-! ## The root itself -/

/-- Before the first physical round, process one has only its root state. -/
abbrev ProfiledRawJointHybridMegaInitialOne := Unit

/-- Process-two mirror root state. -/
abbrev ProfiledRawJointHybridMegaInitialTwo := Unit

/-! ## Old initial strict controls -/

/-- Every reachable process-one local half of the old initial strict and
guarded-exceptional phases.  The nesting is only a finite coproduct; none of
its tags is a runtime graph or leader observation. -/
abbrev ProfiledRawJointHybridMegaOldInitialOne :=
  ProfiledRawJointRootRightOwnerControl A strategy controllers ⊕
    (ProfiledRawJointRootLeftReceiverControl A strategy ⊕
      (ProfiledRawJointInitialLeftOwnerControl A strategy initialBank ⊕
        ProfiledRawJointHybridPoweredInitialRightReceiver A strategy hwin
          initialBank))

/-- Process-two mirror of the old initial strict front. -/
abbrev ProfiledRawJointHybridMegaOldInitialTwo :=
  ProfiledRawJointRootRightReceiverControl A strategy ⊕
    (ProfiledRawJointRootLeftOwnerControl A strategy controllers ⊕
      (ProfiledRawJointHybridPoweredInitialLeftReceiver A strategy hwin
          initialBank ⊕
        ProfiledRawJointInitialRightOwnerControl A strategy initialBank))

noncomputable instance profiledRawJointHybridMegaOldInitialOneFintype :
    Fintype (ProfiledRawJointHybridMegaOldInitialOne A strategy hwin controllers
      initialBank) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridMegaOldInitialTwoFintype :
    Fintype (ProfiledRawJointHybridMegaOldInitialTwo A strategy hwin controllers
      initialBank) := by
  classical
  infer_instance

/-! ## Generic common and first-strict controls -/

/-- The process-one controls in the generic common/first-strict front:
the common finite policy control, its receive shadow, the strict-right guarded
owner, or the resolved strict-left receiver. -/
abbrev ProfiledRawJointHybridMegaCommonOne :=
  ProfiledRawJointHybridCommonControl A strategy hwin ⊕
    (ProfiledRawJointHybridOneShadow A strategy hwin ⊕
      (ProfiledRawJointHybridRightGuardOwner A strategy hwin ⊕
        ProfiledRawJointHybridPoweredLeftStrictReceiver A strategy hwin))

/-- Process-two mirror of the generic common front. -/
abbrev ProfiledRawJointHybridMegaCommonTwo :=
  ProfiledRawJointHybridCommonControl A strategy hwin ⊕
    (ProfiledRawJointHybridTwoShadow A strategy hwin ⊕
      (ProfiledRawJointHybridLeftGuardOwner A strategy hwin ⊕
        ProfiledRawJointHybridPoweredRightStrictReceiver A strategy hwin))

noncomputable instance profiledRawJointHybridMegaCommonOneFintype :
    Fintype (ProfiledRawJointHybridMegaCommonOne A strategy hwin) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridMegaCommonTwoFintype :
    Fintype (ProfiledRawJointHybridMegaCommonTwo A strategy hwin) := by
  classical
  infer_instance

/-! ## Coupled initial common/strict ambiguity -/

/-- After the second receive, process one retains both pieces of honest local
information: the exact old strict-left receiver contingency and the sender
control of the single pre-rationalized common/strict-left sibling move.  The
full installation index is finite data reconstructed from the two genuinely
received input pairs. -/
abbrev ProfiledRawJointHybridMegaCoupledInitialOne :=
  Σ installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂),
    ProfiledRawJointHybridInitialSecondOneShadow A strategy hwin ×
      ProfiledRawJointHybridInitialRightOwnerAt A strategy hwin installation

/-- Process-two mirror. -/
abbrev ProfiledRawJointHybridMegaCoupledInitialTwo :=
  Σ installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂),
    ProfiledRawJointHybridInitialSecondTwoShadow A strategy hwin ×
      ProfiledRawJointHybridInitialLeftOwnerAt A strategy hwin installation

set_option synthInstance.maxHeartbeats 1000000 in
noncomputable instance profiledRawJointHybridMegaCoupledInitialOneFintype :
    Fintype
      (ProfiledRawJointHybridMegaCoupledInitialOne A strategy hwin) := by
  classical
  infer_instance

set_option synthInstance.maxHeartbeats 1000000 in
noncomputable instance profiledRawJointHybridMegaCoupledInitialTwoFintype :
    Fintype
      (ProfiledRawJointHybridMegaCoupledInitialTwo A strategy hwin) := by
  classical
  infer_instance

/-! ### Honest construction and blind continuation -/

/-- A second receive constructs both the old strict contingency and the one
pre-rationalized sibling sender from the same genuine `(first,current)`
installation. -/
noncomputable def profiledRawJointHybridMegaInitialToCoupledOne
    (delivered : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (own : In₁) (deliveredInput : In₂) :
    Out₁ × ProfiledRawJointHybridMegaCoupledInitialOne A strategy hwin :=
  let strict := profiledRawJointHybridInitialToSecondOneShadow A strategy hwin
    controllers delivered own deliveredInput
  let installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂) :=
    ⟨strict.2.key.1, (own, deliveredInput)⟩
  let move := profiledRawJointHybridInitialRightMoveAt A strategy hwin
    installation
  (strict.1, ⟨installation, strict.2,
    (move.memberController A false).initial⟩)

/-- Process-two mirror. -/
noncomputable def profiledRawJointHybridMegaInitialToCoupledTwo
    (delivered : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (own : In₂) (deliveredInput : In₁) :
    Out₂ × ProfiledRawJointHybridMegaCoupledInitialTwo A strategy hwin :=
  let strict := profiledRawJointHybridInitialToSecondTwoShadow A strategy hwin
    controllers delivered own deliveredInput
  let installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂) :=
    ⟨strict.2.key.1, (deliveredInput, own)⟩
  let move := profiledRawJointHybridInitialLeftMoveAt A strategy hwin
    installation
  (strict.1, ⟨installation, strict.2,
    (move.memberController A false).initial⟩)

/-- A blind process-one round advances the one shared sibling sender.  Its
strict/common proof member is absent from both the state and the function. -/
noncomputable def profiledRawJointHybridMegaCoupledNoRecvOne
    (state : ProfiledRawJointHybridMegaCoupledInitialOne A strategy hwin)
    (input : In₁) :
    Out₁ × ProfiledRawJointHybridMegaCoupledInitialOne A strategy hwin :=
  let move := profiledRawJointHybridInitialRightMoveAt A strategy hwin state.1
  let controller := move.memberController A false
  let label := controller.labelOf state.2.2
  (label.1 input,
    ⟨state.1, state.2.1, controller.step state.2.2 input⟩)

/-- Process-two blind continuation mirror. -/
noncomputable def profiledRawJointHybridMegaCoupledNoRecvTwo
    (state : ProfiledRawJointHybridMegaCoupledInitialTwo A strategy hwin)
    (input : In₂) :
    Out₂ × ProfiledRawJointHybridMegaCoupledInitialTwo A strategy hwin :=
  let move := profiledRawJointHybridInitialLeftMoveAt A strategy hwin state.1
  let controller := move.memberController A false
  let label := controller.labelOf state.2.2
  (label.1 input,
    ⟨state.1, state.2.1, controller.step state.2.2 input⟩)

/-! ### Installed finite sibling front -/

/-- Process one's two local roles while the pre-rationalized initial sibling
block is physically active: sender of the right block or receiver of its left
mirror.  Both controls retain the exact finite installation index. -/
abbrev ProfiledRawJointHybridMegaInitialSiblingFrontOne :=
  ProfiledRawJointHybridInitialRightInstalledOwner A strategy hwin ⊕
    ProfiledRawJointHybridInitialLeftInstalledReceiver A strategy hwin

/-- Process-two mirror: receiver of the right block or sender of the left
block. -/
abbrev ProfiledRawJointHybridMegaInitialSiblingFrontTwo :=
  ProfiledRawJointHybridInitialRightInstalledReceiver A strategy hwin ⊕
    ProfiledRawJointHybridInitialLeftInstalledOwner A strategy hwin

noncomputable instance
    profiledRawJointHybridMegaInitialSiblingFrontOneFintype :
    Fintype
      (ProfiledRawJointHybridMegaInitialSiblingFrontOne A strategy hwin) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridMegaInitialSiblingFrontTwoFintype :
    Fintype
      (ProfiledRawJointHybridMegaInitialSiblingFrontTwo A strategy hwin) := by
  classical
  infer_instance

/-- A coupled process-one non-receive resolves the physical orientation and
enters the installed right sender, dropping only the now-obsolete strict
contingency. -/
noncomputable def profiledRawJointHybridMegaCoupledStartRightOwnerOne
    (state : ProfiledRawJointHybridMegaCoupledInitialOne A strategy hwin)
    (input : In₁) :
    Out₁ × ProfiledRawJointHybridInitialRightInstalledOwner A strategy hwin :=
  let move := profiledRawJointHybridInitialRightMoveAt A strategy hwin state.1
  let controller := move.memberController A false
  let label := controller.labelOf state.2.2
  (label.1 input, ⟨state.1, controller.step state.2.2 input⟩)

/-- Coupled process-two non-receive mirror. -/
noncomputable def profiledRawJointHybridMegaCoupledStartLeftOwnerTwo
    (state : ProfiledRawJointHybridMegaCoupledInitialTwo A strategy hwin)
    (input : In₂) :
    Out₂ × ProfiledRawJointHybridInitialLeftInstalledOwner A strategy hwin :=
  let move := profiledRawJointHybridInitialLeftMoveAt A strategy hwin state.1
  let controller := move.memberController A false
  let label := controller.labelOf state.2.2
  (label.1 input, ⟨state.1, controller.step state.2.2 input⟩)

/-- Receiving a delivered coupled left sender initializes and advances the
matching finite left receiver at the retained `.both` root row. -/
noncomputable def profiledRawJointHybridMegaCoupledStartLeftReceiverOne
    (delivered : ProfiledRawJointHybridMegaCoupledInitialTwo A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ ×
      ProfiledRawJointHybridInitialLeftInstalledReceiver A strategy hwin :=
  let initial :=
    initialProfiledRawJointHybridInitialLeftInstalledReceiver A strategy hwin
      delivered.1 .both
  let next := stepProfiledRawJointHybridInitialLeftReceiverAt A strategy hwin
    delivered.1 delivered.2.2 initial.2 (ownInput, deliveredInput)
  (next.1, ⟨delivered.1, next.2⟩)

/-- Receiving a delivered coupled right sender initializes and advances the
matching finite right receiver. -/
noncomputable def profiledRawJointHybridMegaCoupledStartRightReceiverTwo
    (delivered : ProfiledRawJointHybridMegaCoupledInitialOne A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ ×
      ProfiledRawJointHybridInitialRightInstalledReceiver A strategy hwin :=
  let initial :=
    initialProfiledRawJointHybridInitialRightInstalledReceiver A strategy hwin
      delivered.1 .both
  let next := stepProfiledRawJointHybridInitialRightReceiverAt A strategy hwin
    delivered.1 delivered.2.2 initial.2 (ownInput, deliveredInput)
  (next.1, ⟨delivered.1, next.2⟩)

/-! ### Deterministic checked-target indexing -/

/-- Turn a target emitted by one installed right sibling table into the sixth
mega child exactly when it belongs to that table's shared finite target
relation.  The branch depends only on the retained installation and target. -/
noncomputable def profiledRawJointHybridMegaInitialRightTargetChild?
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointUnitTarget A) :
    Option (ProfiledRawJointHybridInitialSiblingTargetChildCode A strategy) := by
  classical
  exact if htarget : ProfiledRawJointRightSiblingSharedAllowedTarget A
      (profiledRawJointHybridInitialSiblingParentFamily A strategy
        installation.first)
      (profiledRawJointHybridInitialSiblingDirection installation.current)
      target then
    some ⟨installation,
      profiledRawJointSiblingTargetChildOfRight A strategy
        (profiledRawJointHybridInitialSiblingParentFamily A strategy
          installation.first)
        (profiledRawJointHybridInitialSiblingDirection installation.current)
        ⟨target, htarget⟩⟩
  else none

/-- Installed left-table mirror. -/
noncomputable def profiledRawJointHybridMegaInitialLeftTargetChild?
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointUnitTarget A) :
    Option (ProfiledRawJointHybridInitialSiblingTargetChildCode A strategy) := by
  classical
  exact if htarget : ProfiledRawJointLeftSiblingSharedAllowedTarget A
      (profiledRawJointHybridInitialSiblingParentFamily A strategy
        installation.first)
      (profiledRawJointHybridInitialSiblingDirection installation.current)
      target then
    some ⟨installation,
      profiledRawJointSiblingTargetChildOfLeft A strategy
        (profiledRawJointHybridInitialSiblingParentFamily A strategy
          installation.first)
        (profiledRawJointHybridInitialSiblingDirection installation.current)
        ⟨target, htarget⟩⟩
  else none

/-! ## Exact initial immediate-reversal controls -/

/-- Process one's two possible local roles in the exact root-pinned block
entered at the ambiguous round immediately below the physical root. -/
abbrev ProfiledRawJointHybridMegaPinnedInitialOne :=
  (ProfiledRawJointHybridInitialImmediateRightOwner A strategy hwin ⊕
    ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy hwin) ⊕
      (ProfiledRawJointHybridMegaCoupledInitialOne A strategy hwin ⊕
        ProfiledRawJointHybridMegaInitialSiblingFrontOne A strategy hwin)

/-- Process-two mirror exact block roles. -/
abbrev ProfiledRawJointHybridMegaPinnedInitialTwo :=
  (ProfiledRawJointHybridInitialImmediateRightReceiver A strategy hwin ⊕
    ProfiledRawJointHybridInitialImmediateLeftOwner A strategy hwin) ⊕
      (ProfiledRawJointHybridMegaCoupledInitialTwo A strategy hwin ⊕
        ProfiledRawJointHybridMegaInitialSiblingFrontTwo A strategy hwin)

noncomputable instance profiledRawJointHybridMegaPinnedInitialOneFintype :
    Fintype (ProfiledRawJointHybridMegaPinnedInitialOne A strategy hwin) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridMegaPinnedInitialTwoFintype :
    Fintype (ProfiledRawJointHybridMegaPinnedInitialTwo A strategy hwin) := by
  classical
  infer_instance

/-! ## Complete finite exceptional types -/

/-- The complete process-one exceptional carrier.  The middle summand is the
one-round initial receive ambiguity; it disappears after the following
physical round. -/
abbrev ProfiledRawJointHybridMegaExceptionalOne :=
  ProfiledRawJointHybridMegaOldInitialOne A strategy hwin controllers
      initialBank ⊕
    (ProfiledRawJointHybridInitialOneShadow A strategy hwin controllers ⊕
      (ProfiledRawJointHybridMegaCommonOne A strategy hwin ⊕
        ProfiledRawJointHybridMegaPinnedInitialOne A strategy hwin))

/-- Process-two mirror complete exceptional carrier. -/
abbrev ProfiledRawJointHybridMegaExceptionalTwo :=
  ProfiledRawJointHybridMegaOldInitialTwo A strategy hwin controllers
      initialBank ⊕
    (ProfiledRawJointHybridInitialTwoShadow A strategy hwin controllers ⊕
      (ProfiledRawJointHybridMegaCommonTwo A strategy hwin ⊕
        ProfiledRawJointHybridMegaPinnedInitialTwo A strategy hwin))

noncomputable instance profiledRawJointHybridMegaExceptionalOneFintype :
    Fintype (ProfiledRawJointHybridMegaExceptionalOne A strategy hwin
      controllers initialBank) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridMegaExceptionalTwoFintype :
    Fintype (ProfiledRawJointHybridMegaExceptionalTwo A strategy hwin
      controllers initialBank) := by
  classical
  infer_instance

/-! ## Named injections used by the eventual transition table -/

def profiledRawJointHybridMegaExceptionalOneOfOld
    (state : ProfiledRawJointHybridMegaOldInitialOne A strategy hwin controllers
      initialBank) :
    ProfiledRawJointHybridMegaExceptionalOne A strategy hwin controllers
      initialBank :=
  .inl state

def profiledRawJointHybridMegaExceptionalTwoOfOld
    (state : ProfiledRawJointHybridMegaOldInitialTwo A strategy hwin controllers
      initialBank) :
    ProfiledRawJointHybridMegaExceptionalTwo A strategy hwin controllers
      initialBank :=
  .inl state

def profiledRawJointHybridMegaExceptionalOneOfInitialShadow
    (state : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers) :
    ProfiledRawJointHybridMegaExceptionalOne A strategy hwin controllers
      initialBank :=
  .inr (.inl state)

def profiledRawJointHybridMegaExceptionalTwoOfInitialShadow
    (state : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers) :
    ProfiledRawJointHybridMegaExceptionalTwo A strategy hwin controllers
      initialBank :=
  .inr (.inl state)

def profiledRawJointHybridMegaExceptionalOneOfCommon
    (state : ProfiledRawJointHybridMegaCommonOne A strategy hwin) :
    ProfiledRawJointHybridMegaExceptionalOne A strategy hwin controllers
      initialBank :=
  .inr (.inr (.inl state))

def profiledRawJointHybridMegaExceptionalTwoOfCommon
    (state : ProfiledRawJointHybridMegaCommonTwo A strategy hwin) :
    ProfiledRawJointHybridMegaExceptionalTwo A strategy hwin controllers
      initialBank :=
  .inr (.inr (.inl state))

def profiledRawJointHybridMegaExceptionalOneOfPinnedInitial
    (state : ProfiledRawJointHybridMegaPinnedInitialOne A strategy hwin) :
    ProfiledRawJointHybridMegaExceptionalOne A strategy hwin controllers
      initialBank :=
  .inr (.inr (.inr state))

def profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial
    (state : ProfiledRawJointHybridMegaPinnedInitialTwo A strategy hwin) :
    ProfiledRawJointHybridMegaExceptionalTwo A strategy hwin controllers
      initialBank :=
  .inr (.inr (.inr state))

/-! ## Common replacement is already recurrent -/

/-- A process-one common-shadow replacement owner is definitionally a
right-owner control in the mega recurrent family at its replacement tag. -/
noncomputable def profiledRawJointHybridOneReplacementOwnerToMega
    (state : ProfiledRawJointHybridOneReplacementOwner A strategy hwin) :
    Σ child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank,
      ProfiledRawJointHybridMegaRightOwner A strategy hwin initialBank child :=
  let replacement := state.shadow.rightReplacementTag A strategy hwin
  ⟨profiledRawJointHybridMegaChildOfReplacement A strategy hwin initialBank
      replacement,
    state.owner⟩

/-- Process-two left-live replacement mirror. -/
noncomputable def profiledRawJointHybridTwoReplacementOwnerToMega
    (state : ProfiledRawJointHybridTwoReplacementOwner A strategy hwin) :
    Σ child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank,
      ProfiledRawJointHybridMegaLeftOwner A strategy hwin initialBank child :=
  let replacement := state.shadow.leftReplacementTag A strategy hwin
  ⟨profiledRawJointHybridMegaChildOfReplacement A strategy hwin initialBank
      replacement,
    state.owner⟩

end

end DetParityAutomaton

end DistributedSynthesis
