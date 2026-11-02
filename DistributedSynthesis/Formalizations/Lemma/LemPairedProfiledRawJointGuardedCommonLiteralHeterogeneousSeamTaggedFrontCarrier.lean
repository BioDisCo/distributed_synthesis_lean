/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeamTaggedExecutableKernel

/-!
# Finite one-block front carrier for the exact right seam

The exact heterogeneous table must be consumed before the recurrent child is
installed.  This module stores the finite seam key together with the table's
local carrier states and exposes one honest block letter:

* process two advances only the shared sender control from its own input;
* process one advances the member-threaded receiver control from the delivered
  input pair; and
* on the pinned true first record, process one may stage the exact tagged
  recurrent control while process two remains in the advanced shared table
  state until a later receipt delivers that tag.

Thus no blind transition reconstructs the entry row, partner input, hidden
member, graph, orientation, or strict leader.
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
  ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin package

private abbrev Installed
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :=
  package.literalRightSeamInstalled A strategy hwin key

/-! ## Finite dependent local states -/

/-- The blind endpoint stores the finite seam key and the one shared sender
control.  There is deliberately no member Boolean in this type. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralRightSeamFrontSenderState
    (package : Package A strategy hwin initial) :=
  Σ key : Key A strategy hwin package,
    ProfiledRawJointLiteralRightBothExactSenderState A strategy hwin
      (Installed A strategy hwin package key)

/-- The receiver stores the same key and a candidate-member-threaded monitor
state.  The member is part of the delayed candidate, not a graph input. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverState
    (package : Package A strategy hwin initial) :=
  Σ key : Key A strategy hwin package,
    ProfiledRawJointLiteralRightBothExactReceiverState A strategy hwin
      (Installed A strategy hwin package key)

/-- Dependent product receiver output tagged by the finite seam key. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverOutput
    (package : Package A strategy hwin initial) :=
  Σ key : Key A strategy hwin package,
    ProfiledRawJointLiteralRightBothExactProductReceiverOutput A strategy hwin
      (Installed A strategy hwin package key)

noncomputable instance literalRightSeamFrontSenderStateFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamFrontSenderState A strategy
        hwin package) := by
  classical
  infer_instance

noncomputable instance literalRightSeamFrontReceiverStateFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverState A
        strategy hwin package) := by
  classical
  infer_instance

noncomputable instance literalRightSeamFrontReceiverOutputFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverOutput A
        strategy hwin package) := by
  classical
  infer_instance

/-! ## Initial roots and endpoint-local steps -/

noncomputable def literalRightSeamFrontSenderInitial
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :
    ProfiledRawJointGuardedCommonLiteralRightSeamFrontSenderState A strategy
      hwin package :=
  ⟨key,
    profiledRawJointLiteralRightBothExactSenderInitial A strategy hwin
      (Installed A strategy hwin package key)⟩

noncomputable def literalRightSeamFrontReceiverInitial
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverState A strategy
      hwin package :=
  ⟨key,
    profiledRawJointLiteralRightBothExactReceiverInitial A strategy hwin
      (Installed A strategy hwin package key) anchor⟩

/-- Arbitrary-depth local non-receive of the blind seam endpoint. -/
noncomputable def literalRightSeamFrontSenderNoRecv
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontSenderState A strategy
        hwin package)
    (input : In₂) : Out₂ ×
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontSenderState A strategy
        hwin package :=
  let next := profiledRawJointLiteralRightBothExactSenderNoRecv A strategy hwin
    (Installed A strategy hwin package state.1) state.2 input
  (next.1, ⟨state.1, next.2⟩)

/-- Member-threaded receive.  Its output retains the key, so the exact child
can be tagged without a code-level representative lookup. -/
noncomputable def literalRightSeamFrontReceiverRecv
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverOutput A strategy
        hwin package ×
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverState A
        strategy hwin package :=
  let next := profiledRawJointLiteralRightBothExactReceiverRecv A strategy hwin
    (Installed A strategy hwin package state.1) state.2 own delivered
  (⟨state.1, next.1⟩, ⟨state.1, next.2⟩)

@[simp] theorem literalRightSeamFrontSenderNoRecv_key
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontSenderState A strategy
        hwin package)
    (input : In₂) :
    (package.literalRightSeamFrontSenderNoRecv A strategy hwin state input
      ).2.1 = state.1 :=
  rfl

@[simp] theorem literalRightSeamFrontReceiverRecv_key
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) :
    (package.literalRightSeamFrontReceiverRecv A strategy hwin state own
      delivered).2.1 = state.1 :=
  rfl

/-- The two local roots contain the same shared table control. -/
theorem literalRightSeamFront_initial_controls_eq
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (anchor : Bool) :
    (package.literalRightSeamFrontSenderInitial A strategy hwin key).2 =
      (package.literalRightSeamFrontReceiverInitial A strategy hwin key
        anchor).2.2.1 := by
  exact profiledRawJointLiteralRightBothExact_initial_controls_eq A strategy
    hwin (Installed A strategy hwin package key) anchor

/-- A synchronized physical letter preserves the shared table control while
the receiver keeps its candidate member. -/
theorem literalRightSeamFront_step_controls_eq
    (package : Package A strategy hwin initial)
    (sender :
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontSenderState A strategy
        hwin package)
    (receiver :
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverState A
        strategy hwin package)
    (hkey : sender.1 = receiver.1)
    (hsync : HEq sender.2 receiver.2.2.1)
    (own : In₁) (delivered : In₂) :
    HEq
      (package.literalRightSeamFrontSenderNoRecv A strategy hwin sender
        delivered).2.2
      (package.literalRightSeamFrontReceiverRecv A strategy hwin receiver own
        delivered).2.2.2.1 := by
  rcases sender with ⟨senderKey, senderControl⟩
  rcases receiver with ⟨receiverKey, receiverState⟩
  dsimp only at hkey
  subst receiverKey
  simp only at hsync
  exact heq_of_eq
    (profiledRawJointLiteralRightBothExact_step_controls_eq A strategy hwin
      (Installed A strategy hwin package senderKey) senderControl receiverState
      (eq_of_heq hsync) own delivered)

/-! ## The pinned true first record and mixed post-shape -/

/-- Evaluate the one jointly synchronized first record, retaining both next
table states. -/
noncomputable def literalRightSeamFrontFirstRound
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (anchor : Bool)
    (input : In₁ × In₂) :=
  let sender := package.literalRightSeamFrontSenderNoRecv A strategy hwin
    (package.literalRightSeamFrontSenderInitial A strategy hwin key) input.2
  let receiver := package.literalRightSeamFrontReceiverRecv A strategy hwin
    (package.literalRightSeamFrontReceiverInitial A strategy hwin key anchor)
      input.1 input.2
  (receiver.1, sender.1, receiver.2, sender.2)

/-- On the true first record, the informed endpoint can stage the exact
recurrent control.  The blind endpoint deliberately remains in the advanced
shared table state; it is not given the row or partner input. -/
noncomputable def literalRightSeamFrontTrueFirstMixed
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
        package ×
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontSenderState A strategy
        hwin package :=
  ((package.literalRightSeamTaggedMatched A strategy hwin key row [] input).1,
    (package.literalRightSeamFrontFirstRound A strategy hwin key true input).2.2.2)

/-- The proof-side matching process-two recurrent control is exposed only as
the target delivered later; it is not installed by the blind no-receive. -/
noncomputable def literalRightSeamFrontTrueFirstExpectedTwo
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
      package :=
  (package.literalRightSeamTaggedMatched A strategy hwin key row [] input).2

@[simp] theorem literalRightSeamFrontTrueFirstMixed_informed
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (input : In₁ × In₂) :
    (package.literalRightSeamFrontTrueFirstMixed A strategy hwin key row
      input).1 =
      (package.literalRightSeamTaggedMatched A strategy hwin key row []
        input).1 :=
  rfl

@[simp] theorem literalRightSeamFrontTrueFirstMixed_blind
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (input : In₁ × In₂) :
    (package.literalRightSeamFrontTrueFirstMixed A strategy hwin key row
      input).2 =
      (package.literalRightSeamFrontFirstRound A strategy hwin key true
        input).2.2.2 :=
  rfl

/-- The exact receiver target of the pinned first record is the child stored
by the staged recurrent control. -/
theorem literalRightSeamFrontTrueFirst_target
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (input : In₁ × In₂) :
    let output :=
      (package.literalRightSeamFrontFirstRound A strategy hwin key true
        input).1
    ⟨key, output.2.2.target row⟩ =
      package.literalRightSeamTaggedTarget A strategy hwin key row [] input := by
  dsimp only
  let env : Nat → In₁ × In₂ := fun _ ↦ input
  have htarget := package.literalRightSeamExactTruePlay_zero_target A strategy
    hwin key env row
  apply Sigma.ext
  · rfl
  · exact heq_of_eq htarget

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
