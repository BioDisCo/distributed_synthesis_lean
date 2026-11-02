/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactMirrorTaggedExecutableKernel

/-!
# Finite one-block front carrier for the exact mirror seam

This is the process-swapped companion of the literal right-seam front.  The
mirror seam is a homogeneous right block: process one advances only the
shared blind table sender, while process two advances the member-threaded
receiver.  The exact child is visible only at the receiver.

The carrier intentionally keeps the table controls after the first record.
Installing a recurrent child is a later reversal operation; no blind
transition is asked to recover the row, partner input, graph orientation,
leader, history, or semantic view.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev Key
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin package

private abbrev Installed
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :=
  package.literalLeftSeamInstalled A strategy hwin key

/-! ## Finite dependent local states -/

/-- The blind process-one endpoint stores only the finite seam key and the
shared mirror-table sender control. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralLeftSeamFrontSenderState
    (package : Package A strategy hwin initial) :=
  Σ key : Key A strategy hwin package,
    ProfiledRawJointLiteralLeftBothExactSenderState A strategy hwin
      (Installed A strategy hwin package key)

/-- The process-two receiver stores the same key and its member-threaded
mirror-table state. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverState
    (package : Package A strategy hwin initial) :=
  Σ key : Key A strategy hwin package,
    ProfiledRawJointLiteralLeftBothExactReceiverState A strategy hwin
      (Installed A strategy hwin package key)

/-- Product receiver output tagged by the finite mirror seam key. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverOutput
    (package : Package A strategy hwin initial) :=
  Σ key : Key A strategy hwin package,
    ProfiledRawJointLiteralLeftBothExactProductReceiverOutput A strategy hwin
      (Installed A strategy hwin package key)

noncomputable instance literalLeftSeamFrontSenderStateFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamFrontSenderState A strategy
        hwin package) := by
  classical
  infer_instance

noncomputable instance literalLeftSeamFrontReceiverStateFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverState A
        strategy hwin package) := by
  classical
  infer_instance

noncomputable instance literalLeftSeamFrontReceiverOutputFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverOutput A
        strategy hwin package) := by
  classical
  infer_instance

/-! ## Roots and endpoint-local table steps -/

noncomputable def literalLeftSeamFrontSenderInitial
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamFrontSenderState A strategy
      hwin package :=
  ⟨key,
    profiledRawJointLiteralLeftBothExactSenderInitial A strategy hwin
      (Installed A strategy hwin package key)⟩

noncomputable def literalLeftSeamFrontReceiverInitial
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverState A strategy
      hwin package :=
  ⟨key,
    profiledRawJointLiteralLeftBothExactReceiverInitial A strategy hwin
      (Installed A strategy hwin package key) anchor⟩

/-- Arbitrary-depth no-receive of the blind process-one endpoint. -/
noncomputable def literalLeftSeamFrontSenderNoRecv
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontSenderState A strategy
        hwin package)
    (input : In₁) : Out₁ ×
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontSenderState A strategy
        hwin package :=
  let next := profiledRawJointLiteralLeftBothExactSenderNoRecv A strategy hwin
    (Installed A strategy hwin package state.1) state.2 input
  (next.1, ⟨state.1, next.2⟩)

/-- Member-threaded process-two receive, retaining the key with the exact
product output. -/
noncomputable def literalLeftSeamFrontReceiverRecv
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverState A strategy
        hwin package)
    (own : In₂) (delivered : In₁) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverOutput A strategy
        hwin package ×
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverState A strategy
        hwin package :=
  let next := profiledRawJointLiteralLeftBothExactReceiverRecv A strategy hwin
    (Installed A strategy hwin package state.1) state.2 own delivered
  (⟨state.1, next.1⟩, ⟨state.1, next.2⟩)

@[simp] theorem literalLeftSeamFrontSenderNoRecv_key
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontSenderState A strategy
        hwin package)
    (input : In₁) :
    (package.literalLeftSeamFrontSenderNoRecv A strategy hwin state input
      ).2.1 = state.1 :=
  rfl

@[simp] theorem literalLeftSeamFrontReceiverRecv_key
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverState A strategy
        hwin package)
    (own : In₂) (delivered : In₁) :
    (package.literalLeftSeamFrontReceiverRecv A strategy hwin state own
      delivered).2.1 = state.1 :=
  rfl

/-- Both endpoints start with the same shared mirror-table control. -/
theorem literalLeftSeamFront_initial_controls_eq
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (anchor : Bool) :
    (package.literalLeftSeamFrontSenderInitial A strategy hwin key).2 =
      (package.literalLeftSeamFrontReceiverInitial A strategy hwin key
        anchor).2.2.1 := by
  exact profiledRawJointLiteralLeftBothExact_initial_controls_eq A strategy
    hwin (Installed A strategy hwin package key) anchor

/-- One synchronized right-block letter preserves equality of the shared
table controls. -/
theorem literalLeftSeamFront_step_controls_eq
    (package : Package A strategy hwin initial)
    (sender :
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontSenderState A strategy
        hwin package)
    (receiver :
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverState A strategy
        hwin package)
    (hkey : sender.1 = receiver.1)
    (hsync : HEq sender.2 receiver.2.2.1)
    (own : In₂) (delivered : In₁) :
    HEq
      (package.literalLeftSeamFrontSenderNoRecv A strategy hwin sender
        delivered).2.2
      (package.literalLeftSeamFrontReceiverRecv A strategy hwin receiver own
        delivered).2.2.2.1 := by
  rcases sender with ⟨senderKey, senderControl⟩
  rcases receiver with ⟨receiverKey, receiverState⟩
  dsimp only at hkey
  subst receiverKey
  simp only at hsync
  exact heq_of_eq
    (profiledRawJointLiteralLeftBothExact_step_controls_eq A strategy hwin
      (Installed A strategy hwin package senderKey) senderControl receiverState
      (eq_of_heq hsync) own delivered)

/-! ## Pinned first record -/

/-- Execute the first synchronized mirror-table record and retain both table
states.  The input order follows the exact right-block monitor. -/
noncomputable def literalLeftSeamFrontFirstRound
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (anchor : Bool)
    (input : In₂ × In₁) :=
  let sender := package.literalLeftSeamFrontSenderNoRecv A strategy hwin
    (package.literalLeftSeamFrontSenderInitial A strategy hwin key) input.2
  let receiver := package.literalLeftSeamFrontReceiverRecv A strategy hwin
    (package.literalLeftSeamFrontReceiverInitial A strategy hwin key anchor)
      input.1 input.2
  (receiver.1, sender.1, receiver.2, sender.2)

/-- The receiver target of the pinned true record is exactly the dependent
child stored by the mirror seam tag. -/
theorem literalLeftSeamFrontTrueFirst_target
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (input : In₂ × In₁) :
    let output :=
      (package.literalLeftSeamFrontFirstRound A strategy hwin key true
        input).1
    ⟨key, output.2.2.target row⟩ =
      package.literalLeftSeamTaggedTarget A strategy hwin key row [] input := by
  dsimp only
  let env : Nat → In₂ × In₁ := fun _ ↦ input
  have htarget := package.literalLeftSeamExactTruePlay_zero_target A strategy
    hwin key env row
  apply Sigma.ext
  · rfl
  · exact heq_of_eq htarget

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
