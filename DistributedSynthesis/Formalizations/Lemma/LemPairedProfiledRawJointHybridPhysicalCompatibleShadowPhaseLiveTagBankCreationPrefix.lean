/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTagBankTrackedBootstrap

/-!
# Current one-live tag state through the creation-direction prefix

A tag can be created long before the opposite strict receive that delivers it.
Resetting the tail fibre at delivery would therefore be unsound.  During the
intervening one-way block the informed endpoint knows both inputs.  It stores
the complete finite owner/receiver pair of the unique live table and advances
both halves locally.

For a strict-left tag this is the right table; for a strict-right tag it is the
left table.  The executable carrier below stores only finite controls.  The
`Tracked` predicates occur solely in preservation theorems and are not runtime
fields.  No transition receives a graph, hierarchy side, leader bit, history,
or semantic view.

The step exposes the selected owner's candidate output for the later seam
proof.  This file does not identify that candidate with the pre-existing
leader-free shadow controller's public output; that cross-controller equality
is a separate required interface law.  In particular, the carrier solves the
current-state/full-input problem without silently solving the output mosaic.

This module concerns a persistent one-sided block up to its opposite strict
delivery.  A `.both` round leaves this regime and is handled by the separate
common/reset construction; no `.both` bootstrap is claimed here.
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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev OnePending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailOnePending.{u, v, x, y, s, 0, 0}
    A strategy hwin tag

private abbrev TwoPending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailTwoPending.{u, v, x, y, s, 0, 0}
    A strategy hwin tag

private abbrev CurrentPair (tag : Tag A strategy hwin) :=
  OnePending A strategy hwin tag × TwoPending A strategy hwin tag

private abbrev RightReceiver (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiver A strategy hwin tag

private abbrev LeftReceiver (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiver A strategy hwin tag

/-! ## Updating exactly the selected receiver-fork cell -/

/-- Replace the right receiver selected by `member`, leaving every other
process-two field unchanged. -/
def profiledRawJointHybridShadowPhaseLiveReplaceRightReceiver
    {tag : Tag A strategy hwin}
    (shared : ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy hwin
      tag)
    (member : Bool) (receiver : RightReceiver A strategy hwin tag) :
    ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy hwin tag :=
  { shared with
    receiverFork :=
      if member then
        ⟨shared.receiverFork.openControl, receiver⟩
      else
        ⟨receiver, shared.receiverFork.closedControl⟩ }

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveReplaceRightReceiver_selected
    {tag : Tag A strategy hwin}
    (shared : ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy hwin
      tag)
    (member : Bool) (receiver : RightReceiver A strategy hwin tag) :
    (profiledRawJointHybridShadowPhaseLiveReplaceRightReceiver A strategy hwin
      shared member receiver).receiver member = receiver := by
  cases member <;> rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveReplaceRightReceiver_phase
    {tag : Tag A strategy hwin}
    (shared : ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy hwin
      tag)
    (member : Bool) (receiver : RightReceiver A strategy hwin tag) :
    (profiledRawJointHybridShadowPhaseLiveReplaceRightReceiver A strategy hwin
      shared member receiver).localPhase = shared.localPhase := by
  rfl

/-- Process-one mirror for the selected left receiver. -/
def profiledRawJointHybridShadowPhaseLiveReplaceLeftReceiver
    {tag : Tag A strategy hwin}
    (shared : ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy hwin
      tag)
    (member : Bool) (receiver : LeftReceiver A strategy hwin tag) :
    ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy hwin tag :=
  { shared with
    receiverFork :=
      if member then
        ⟨shared.receiverFork.openControl, receiver⟩
      else
        ⟨receiver, shared.receiverFork.closedControl⟩ }

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveReplaceLeftReceiver_selected
    {tag : Tag A strategy hwin}
    (shared : ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy hwin
      tag)
    (member : Bool) (receiver : LeftReceiver A strategy hwin tag) :
    (profiledRawJointHybridShadowPhaseLiveReplaceLeftReceiver A strategy hwin
      shared member receiver).receiver member = receiver := by
  cases member <;> rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveReplaceLeftReceiver_phase
    {tag : Tag A strategy hwin}
    (shared : ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy hwin
      tag)
    (member : Bool) (receiver : LeftReceiver A strategy hwin tag) :
    (profiledRawJointHybridShadowPhaseLiveReplaceLeftReceiver A strategy hwin
      shared member receiver).localPhase = shared.localPhase := by
  rfl

/-! ## One informed creation-direction step -/

/-- Advance the current right table during a strict-left creation block.
Process one knows `input` completely.  The returned candidate is the selected
right owner's output; the predicted process-two receiver is retained for
delivery.  Equality with the surrounding controller's public output is not
asserted here. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveLeftTagCreationStep
    (tag : Tag A strategy hwin) (current : CurrentPair A strategy hwin tag)
    (input : In₁ × In₂) : CurrentPair A strategy hwin tag × Out₁ :=
  let one := current.1
  let two := current.2
  let owner := one.2.1.baseShared
  let receiver := two.2.1.receiver two.1
  let ownerResult :=
    profiledRawJointHybridShadowPhaseLiveTailRightSharedStep A strategy hwin tag
      owner.1 one.1 owner.2 input.1
  let receiverResult :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy hwin
      tag (tag.fallbackRightOutput A strategy hwin) owner receiver
        (input.2, input.1)
  let oneShared := { one.2.1 with
    baseShared := ⟨owner.1, ownerResult.1⟩ }
  let twoShared :=
    profiledRawJointHybridShadowPhaseLiveReplaceRightReceiver A strategy hwin
      two.2.1 two.1 receiverResult.2
  (((one.1, oneShared, one.2.2), (two.1, twoShared, two.2.2)), ownerResult.2)

/-- Strict-right creation mirror. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveRightTagCreationStep
    (tag : Tag A strategy hwin) (current : CurrentPair A strategy hwin tag)
    (input : In₁ × In₂) : CurrentPair A strategy hwin tag × Out₂ :=
  let one := current.1
  let two := current.2
  let owner := two.2.1.baseShared
  let receiver := one.2.1.receiver one.1
  let ownerResult :=
    profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep A strategy hwin tag
      owner.1 two.1 owner.2 input.2
  let receiverResult :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy hwin
      tag (tag.fallbackLeftOutput A strategy hwin) owner receiver input
  let twoShared := { two.2.1 with
    baseShared := ⟨owner.1, ownerResult.1⟩ }
  let oneShared :=
    profiledRawJointHybridShadowPhaseLiveReplaceLeftReceiver A strategy hwin
      one.2.1 one.1 receiverResult.2
  (((one.1, oneShared, one.2.2), (two.1, twoShared, two.2.2)), ownerResult.2)

@[simp] theorem profiledRawJointHybridShadowPhaseLiveLeftTagCreationStep_onePhase
    (tag : Tag A strategy hwin) (current : CurrentPair A strategy hwin tag)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveLeftTagCreationStep A strategy hwin
      tag current input).1.1.2.1.localPhase = current.1.2.1.localPhase := by
  rfl

@[simp] theorem profiledRawJointHybridShadowPhaseLiveLeftTagCreationStep_twoPhase
    (tag : Tag A strategy hwin) (current : CurrentPair A strategy hwin tag)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveLeftTagCreationStep A strategy hwin
      tag current input).1.2.2.1.localPhase = current.2.2.1.localPhase := by
  rfl

@[simp] theorem profiledRawJointHybridShadowPhaseLiveRightTagCreationStep_onePhase
    (tag : Tag A strategy hwin) (current : CurrentPair A strategy hwin tag)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveRightTagCreationStep A strategy hwin
      tag current input).1.1.2.1.localPhase = current.1.2.1.localPhase := by
  rfl

@[simp] theorem profiledRawJointHybridShadowPhaseLiveRightTagCreationStep_twoPhase
    (tag : Tag A strategy hwin) (current : CurrentPair A strategy hwin tag)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveRightTagCreationStep A strategy hwin
      tag current input).1.2.2.1.localPhase = current.2.2.1.localPhase := by
  rfl

/-! ## The one-live relation is preserved -/

theorem profiledRawJointHybridShadowPhaseLiveLeftTagCreationStep_rightTracked
    {tag : Tag A strategy hwin} {current : CurrentPair A strategy hwin tag}
    (tracked :
      ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked A strategy
        hwin tag current.1 current.2)
    (input : In₁ × In₂) :
    let next :=
      (profiledRawJointHybridShadowPhaseLiveLeftTagCreationStep A strategy hwin
        tag current input).1
    ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked A strategy
      hwin tag next.1 next.2 := by
  dsimp only
  unfold ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked at tracked ⊢
  have advanced := tracked.step A strategy hwin
    (tag.fallbackRightOutput A strategy hwin) current.1.1
      (input.2, input.1)
  simpa [profiledRawJointHybridShadowPhaseLiveLeftTagCreationStep] using
    advanced

theorem profiledRawJointHybridShadowPhaseLiveRightTagCreationStep_leftTracked
    {tag : Tag A strategy hwin} {current : CurrentPair A strategy hwin tag}
    (tracked :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked A strategy
        hwin tag current.1 current.2)
    (input : In₁ × In₂) :
    let next :=
      (profiledRawJointHybridShadowPhaseLiveRightTagCreationStep A strategy hwin
        tag current input).1
    ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked A strategy
      hwin tag next.1 next.2 := by
  dsimp only
  unfold ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked at tracked ⊢
  have advanced := tracked.step A strategy hwin
    (tag.fallbackLeftOutput A strategy hwin) current.2.1 input
  simpa [profiledRawJointHybridShadowPhaseLiveRightTagCreationStep] using
    advanced

/-! ## Arbitrary finite creation prefixes -/

/-- The canonical pending pair selected when the informed endpoint creates a
tag.  Subsequent steps evolve this value; it is never recreated at delivery. -/
noncomputable def ProfiledRawJointHybridShadowPhaseLiveTag.creationInitial
    (tag : Tag A strategy hwin) : CurrentPair A strategy hwin tag :=
  (tag.initialOne A strategy hwin, tag.initialTwo A strategy hwin)

def profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun
    (tag : Tag A strategy hwin) :
    CurrentPair A strategy hwin tag → List (In₁ × In₂) →
      CurrentPair A strategy hwin tag
  | current, [] => current
  | current, input :: tail =>
      profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun tag
        (profiledRawJointHybridShadowPhaseLiveLeftTagCreationStep A strategy
          hwin tag current input).1 tail

def profiledRawJointHybridShadowPhaseLiveRightTagCreationRun
    (tag : Tag A strategy hwin) :
    CurrentPair A strategy hwin tag → List (In₁ × In₂) →
      CurrentPair A strategy hwin tag
  | current, [] => current
  | current, input :: tail =>
      profiledRawJointHybridShadowPhaseLiveRightTagCreationRun tag
        (profiledRawJointHybridShadowPhaseLiveRightTagCreationStep A strategy
          hwin tag current input).1 tail

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun_nil
    (tag : Tag A strategy hwin) (current : CurrentPair A strategy hwin tag) :
    profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun A strategy hwin tag
      current [] = current :=
  rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun_cons
    (tag : Tag A strategy hwin) (current : CurrentPair A strategy hwin tag)
    (input : In₁ × In₂) (tail : List (In₁ × In₂)) :
    profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun A strategy hwin tag
        current (input :: tail) =
      profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun A strategy hwin
        tag
        (profiledRawJointHybridShadowPhaseLiveLeftTagCreationStep A strategy
          hwin tag current input).1 tail :=
  rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveRightTagCreationRun_nil
    (tag : Tag A strategy hwin) (current : CurrentPair A strategy hwin tag) :
    profiledRawJointHybridShadowPhaseLiveRightTagCreationRun A strategy hwin tag
      current [] = current :=
  rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveRightTagCreationRun_cons
    (tag : Tag A strategy hwin) (current : CurrentPair A strategy hwin tag)
    (input : In₁ × In₂) (tail : List (In₁ × In₂)) :
    profiledRawJointHybridShadowPhaseLiveRightTagCreationRun A strategy hwin tag
        current (input :: tail) =
      profiledRawJointHybridShadowPhaseLiveRightTagCreationRun A strategy hwin
        tag
        (profiledRawJointHybridShadowPhaseLiveRightTagCreationStep A strategy
          hwin tag current input).1 tail :=
  rfl

theorem profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun_rightTracked
    {tag : Tag A strategy hwin} {current : CurrentPair A strategy hwin tag}
    (tracked :
      ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked A strategy
        hwin tag current.1 current.2)
    (word : List (In₁ × In₂)) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun A strategy hwin
        tag current word
    ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked A strategy
      hwin tag next.1 next.2 := by
  induction word generalizing current with
  | nil => exact tracked
  | cons input tail ih =>
      exact ih
        (profiledRawJointHybridShadowPhaseLiveLeftTagCreationStep_rightTracked
          A strategy hwin tracked input)

theorem profiledRawJointHybridShadowPhaseLiveRightTagCreationRun_leftTracked
    {tag : Tag A strategy hwin} {current : CurrentPair A strategy hwin tag}
    (tracked :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked A strategy
        hwin tag current.1 current.2)
    (word : List (In₁ × In₂)) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveRightTagCreationRun A strategy hwin
        tag current word
    ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked A strategy
      hwin tag next.1 next.2 := by
  induction word generalizing current with
  | nil => exact tracked
  | cons input tail ih =>
      exact ih
        (profiledRawJointHybridShadowPhaseLiveRightTagCreationStep_leftTracked
          A strategy hwin tracked input)

theorem profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun_phase
    (tag : Tag A strategy hwin) (current : CurrentPair A strategy hwin tag)
    (word : List (In₁ × In₂)) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun A strategy hwin
        tag current word
    next.1.2.1.localPhase = current.1.2.1.localPhase ∧
      next.2.2.1.localPhase = current.2.2.1.localPhase := by
  induction word generalizing current with
  | nil => exact ⟨rfl, rfl⟩
  | cons input tail ih =>
      simpa using ih
        (profiledRawJointHybridShadowPhaseLiveLeftTagCreationStep A strategy
          hwin tag current input).1

theorem profiledRawJointHybridShadowPhaseLiveRightTagCreationRun_phase
    (tag : Tag A strategy hwin) (current : CurrentPair A strategy hwin tag)
    (word : List (In₁ × In₂)) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveRightTagCreationRun A strategy hwin
        tag current word
    next.1.2.1.localPhase = current.1.2.1.localPhase ∧
      next.2.2.1.localPhase = current.2.2.1.localPhase := by
  induction word generalizing current with
  | nil => exact ⟨rfl, rfl⟩
  | cons input tail ih =>
      simpa using ih
        (profiledRawJointHybridShadowPhaseLiveRightTagCreationStep A strategy
          hwin tag current input).1

/-! ## Concrete tag sides start and remain tracked -/

theorem profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun_initial_tracked
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (first : In₁ × In₂) (word : List (In₁ × In₂)) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin first
    let next :=
      profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun A strategy hwin
        tag (tag.creationInitial A strategy hwin) word
    ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked A strategy
      hwin tag next.1 next.2 := by
  dsimp only
  apply profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun_rightTracked A
    strategy hwin
  exact profiledRawJointHybridShadowPhaseLiveLeftTag_initial_rightTracked A
    strategy hwin origin first

theorem profiledRawJointHybridShadowPhaseLiveRightTagCreationRun_initial_tracked
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (first : In₁ × In₂) (word : List (In₁ × In₂)) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin first
    let next :=
      profiledRawJointHybridShadowPhaseLiveRightTagCreationRun A strategy hwin
        tag (tag.creationInitial A strategy hwin) word
    ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked A strategy
      hwin tag next.1 next.2 := by
  dsimp only
  apply profiledRawJointHybridShadowPhaseLiveRightTagCreationRun_leftTracked A
    strategy hwin
  exact profiledRawJointHybridShadowPhaseLiveRightTag_initial_leftTracked A
    strategy hwin origin first

theorem profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun_initial_phase
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (first : In₁ × In₂) (word : List (In₁ × In₂)) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin first
    let next :=
      profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun A strategy hwin
        tag (tag.creationInitial A strategy hwin) word
    next.1.2.1.localPhase = true ∧ next.2.2.1.localPhase = false := by
  dsimp only
  simpa [ProfiledRawJointHybridShadowPhaseLiveTag.creationInitial] using
    (profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun_phase A strategy
      hwin
      (profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin
        first)
      ((profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin
        first).creationInitial A strategy hwin) word)

theorem profiledRawJointHybridShadowPhaseLiveRightTagCreationRun_initial_phase
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (first : In₁ × In₂) (word : List (In₁ × In₂)) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin first
    let next :=
      profiledRawJointHybridShadowPhaseLiveRightTagCreationRun A strategy hwin
        tag (tag.creationInitial A strategy hwin) word
    next.1.2.1.localPhase = true ∧ next.2.2.1.localPhase = false := by
  dsimp only
  simpa [ProfiledRawJointHybridShadowPhaseLiveTag.creationInitial] using
    (profiledRawJointHybridShadowPhaseLiveRightTagCreationRun_phase A strategy
      hwin
      (profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin
        first)
      ((profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin
        first).creationInitial A strategy hwin) word)

/-! ## Finite executable informed-endpoint carriers -/

/-- Process one stores such a selected current fibre during a strict-left
creation block. -/
abbrev ProfiledRawJointHybridShadowPhaseLiveLeftTagCreationControl :=
  Σ tag : Tag A strategy hwin, CurrentPair A strategy hwin tag

/-- Process-two mirror during a strict-right creation block. -/
abbrev ProfiledRawJointHybridShadowPhaseLiveRightTagCreationControl :=
  Σ tag : Tag A strategy hwin, CurrentPair A strategy hwin tag

noncomputable instance : Fintype
    (ProfiledRawJointHybridShadowPhaseLiveLeftTagCreationControl A strategy
      hwin) := by
  classical infer_instance

noncomputable instance : Fintype
    (ProfiledRawJointHybridShadowPhaseLiveRightTagCreationControl A strategy
      hwin) := by
  classical infer_instance

noncomputable def profiledRawJointHybridShadowPhaseLiveLeftTagCreationInitial
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridShadowPhaseLiveLeftTagCreationControl A strategy
      hwin :=
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
  ⟨tag, tag.creationInitial A strategy hwin⟩

noncomputable def profiledRawJointHybridShadowPhaseLiveRightTagCreationInitial
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridShadowPhaseLiveRightTagCreationControl A strategy
      hwin :=
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
  ⟨tag, tag.creationInitial A strategy hwin⟩

/-- One executable informed process-one step. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveLeftTagCreationControlStep
    (control :
      ProfiledRawJointHybridShadowPhaseLiveLeftTagCreationControl A strategy
        hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridShadowPhaseLiveLeftTagCreationControl A strategy
        hwin × Out₁ :=
  let next :=
    profiledRawJointHybridShadowPhaseLiveLeftTagCreationStep A strategy hwin
      control.1 control.2 input
  (⟨control.1, next.1⟩, next.2)

/-- Process-two mirror. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveRightTagCreationControlStep
    (control :
      ProfiledRawJointHybridShadowPhaseLiveRightTagCreationControl A strategy
        hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridShadowPhaseLiveRightTagCreationControl A strategy
        hwin × Out₂ :=
  let next :=
    profiledRawJointHybridShadowPhaseLiveRightTagCreationStep A strategy hwin
      control.1 control.2 input
  (⟨control.1, next.1⟩, next.2)

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveLeftTagCreationControlStep_key
    (control :
      ProfiledRawJointHybridShadowPhaseLiveLeftTagCreationControl A strategy
        hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveLeftTagCreationControlStep A strategy
      hwin control input).1.1 = control.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveRightTagCreationControlStep_key
    (control :
      ProfiledRawJointHybridShadowPhaseLiveRightTagCreationControl A strategy
        hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveRightTagCreationControlStep A strategy
      hwin control input).1.1 = control.1 :=
  rfl

/-! ## Opposite strict delivery uses the current pair -/

/-- A later strict-right delivery of a process-one left tag advances the
current pair immediately and installs the resulting common tag fibre. -/
noncomputable def
    profiledRawJointHybridActivateCurrentLeftTagCreationStrictRight
    (control :
      ProfiledRawJointHybridShadowPhaseLiveLeftTagCreationControl A strategy
        hwin)
    (input : In₁ × In₂) :
    (ProfiledRawJointHybridShadowPhaseLiveTagBankOneControl A strategy hwin ×
        ProfiledRawJointHybridShadowPhaseLiveTagBankTwoControl A strategy
          hwin) ×
      (Out₁ × Out₂) :=
  let tag := control.1
  let one := control.2.1
  let two := control.2.2
  let oneResult :=
    FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy hwin
        tag) one input.1
  let fresh :=
    profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s, 0, 0,
      0, 0, 0, 0, 0, 0} A strategy hwin tag
      (tag.fallbackLeftOutput A strategy hwin)
      (tag.fallbackRightOutput A strategy hwin) one two input
  ((⟨tag, .inl oneResult.1⟩, ⟨tag, .inl fresh.1.2.openControl⟩),
    (oneResult.2, fresh.2.2))

/-- Strict-left mirror. -/
noncomputable def
    profiledRawJointHybridActivateCurrentRightTagCreationStrictLeft
    (control :
      ProfiledRawJointHybridShadowPhaseLiveRightTagCreationControl A strategy
        hwin)
    (input : In₁ × In₂) :
    (ProfiledRawJointHybridShadowPhaseLiveTagBankOneControl A strategy hwin ×
        ProfiledRawJointHybridShadowPhaseLiveTagBankTwoControl A strategy
          hwin) ×
      (Out₁ × Out₂) :=
  let tag := control.1
  let one := control.2.1
  let two := control.2.2
  let fresh :=
    profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s, 0, 0,
      0, 0, 0, 0, 0, 0} A strategy hwin tag
      (tag.fallbackLeftOutput A strategy hwin)
      (tag.fallbackRightOutput A strategy hwin) one two input
  let twoResult :=
    FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy hwin
        tag) two input.2
  ((⟨tag, .inl fresh.1.1.openControl⟩, ⟨tag, .inl twoResult.1⟩),
    (fresh.2.1, twoResult.2))

@[simp] theorem
    profiledRawJointHybridActivateCurrentLeftTagCreationStrictRight_keys
    (control :
      ProfiledRawJointHybridShadowPhaseLiveLeftTagCreationControl A strategy
        hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridActivateCurrentLeftTagCreationStrictRight A strategy
      hwin control input).1.1.1 =
      (profiledRawJointHybridActivateCurrentLeftTagCreationStrictRight A
        strategy hwin control input).1.2.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridActivateCurrentRightTagCreationStrictLeft_keys
    (control :
      ProfiledRawJointHybridShadowPhaseLiveRightTagCreationControl A strategy
        hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridActivateCurrentRightTagCreationStrictLeft A strategy
      hwin control input).1.1.1 =
      (profiledRawJointHybridActivateCurrentRightTagCreationStrictLeft A
        strategy hwin control input).1.2.1 :=
  rfl

/-! ## Operational activation preserves the current live occurrence -/

/-- The controls returned by a strict-right activation of a current
strict-left creation carrier are not fresh roots.  They are exactly the two
pending controls obtained by advancing the carried current pair, and those
controls satisfy the full tracked tail invariant.

This is the operational form of the one-live bootstrap theorem: a later
controller may install `activated.1` directly, without reconstructing the
tag fibre at delivery. -/
theorem
    profiledRawJointHybridActivateCurrentLeftTagCreationStrictRight_tracked
    (control :
      ProfiledRawJointHybridShadowPhaseLiveLeftTagCreationControl A strategy
        hwin)
    (tracked :
      ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked A strategy
        hwin control.1 control.2.1 control.2.2)
    (hphase : control.2.2.2.1.localPhase = false)
    (input : In₁ × In₂) :
    let activated :=
      profiledRawJointHybridActivateCurrentLeftTagCreationStrictRight A
        strategy hwin control input
    ∃ oneNext : OnePending A strategy hwin control.1,
      ∃ twoNext : TwoPending A strategy hwin control.1,
        activated.1 =
            (⟨control.1, .inl oneNext⟩, ⟨control.1, .inl twoNext⟩) ∧
          ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy
            hwin control.1 oneNext twoNext := by
  dsimp only
  let oneNext :=
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy hwin
        control.1) control.2.1 input.1).1
  let fresh :=
    profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s, 0, 0,
      0, 0, 0, 0, 0, 0} A strategy hwin control.1
      (control.1.fallbackLeftOutput A strategy hwin)
      (control.1.fallbackRightOutput A strategy hwin) control.2.1 control.2.2
        input
  let twoNext := fresh.1.2.openControl
  refine ⟨oneNext, twoNext, rfl, ?_⟩
  exact
    ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked.strictRight.{u,
      v, x, y, s, 0, 0, 0, 0, 0, 0, 0, 0}
      (A := A) (strategy := strategy) (hwin := hwin) tracked hphase
      (control.1.fallbackLeftOutput A strategy hwin)
      (control.1.fallbackRightOutput A strategy hwin) input

/-- Strict-left activation mirror. -/
theorem
    profiledRawJointHybridActivateCurrentRightTagCreationStrictLeft_tracked
    (control :
      ProfiledRawJointHybridShadowPhaseLiveRightTagCreationControl A strategy
        hwin)
    (tracked :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked A strategy
        hwin control.1 control.2.1 control.2.2)
    (hphase : control.2.1.2.1.localPhase = true)
    (input : In₁ × In₂) :
    let activated :=
      profiledRawJointHybridActivateCurrentRightTagCreationStrictLeft A
        strategy hwin control input
    ∃ oneNext : OnePending A strategy hwin control.1,
      ∃ twoNext : TwoPending A strategy hwin control.1,
        activated.1 =
            (⟨control.1, .inl oneNext⟩, ⟨control.1, .inl twoNext⟩) ∧
          ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy
            hwin control.1 oneNext twoNext := by
  dsimp only
  let fresh :=
    profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s, 0, 0,
      0, 0, 0, 0, 0, 0} A strategy hwin control.1
      (control.1.fallbackLeftOutput A strategy hwin)
      (control.1.fallbackRightOutput A strategy hwin) control.2.1 control.2.2
        input
  let oneNext := fresh.1.1.openControl
  let twoNext :=
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy hwin
        control.1) control.2.2 input.2).1
  refine ⟨oneNext, twoNext, rfl, ?_⟩
  exact
    ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked.strictLeft.{u,
      v, x, y, s, 0, 0, 0, 0, 0, 0, 0, 0}
      (A := A) (strategy := strategy) (hwin := hwin) tracked hphase
      (control.1.fallbackLeftOutput A strategy hwin)
      (control.1.fallbackRightOutput A strategy hwin) input

/-! ## Arbitrary-prefix delivery enters the full invariant -/

theorem
    profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun_bootstrap_strictRight
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (first : In₁ × In₂) (word : List (In₁ × In₂))
    (input : In₁ × In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin first
    let current :=
      profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun A strategy hwin
        tag (tag.creationInitial A strategy hwin) word
    let oneNext :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy hwin
          tag) current.1 input.1).1
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s, 0, 0,
        0, 0, 0, 0, 0, 0} A strategy hwin tag
        (tag.fallbackLeftOutput A strategy hwin)
        (tag.fallbackRightOutput A strategy hwin) current.1 current.2 input
    let twoNext := fresh.1.2.openControl
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant.{u, v, x, y, s,
      0, 0, 0, 0} A strategy hwin tag oneNext twoNext := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin first
  let current :=
    profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun A strategy hwin tag
      (tag.creationInitial A strategy hwin) word
  have tracked :=
    profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun_initial_tracked A
      strategy hwin origin first word
  have phase :=
    profiledRawJointHybridShadowPhaseLiveLeftTagCreationRun_initial_phase A
      strategy hwin origin first word
  simpa only [tag, current] using
    ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked.strictRight.{u,
      v, x, y, s, 0, 0, 0, 0, 0, 0, 0, 0}
      (A := A) (strategy := strategy) (hwin := hwin) (tag := tag)
      (one := current.1) (two := current.2) tracked phase.2
      (tag.fallbackLeftOutput A strategy hwin)
      (tag.fallbackRightOutput A strategy hwin) input

theorem
    profiledRawJointHybridShadowPhaseLiveRightTagCreationRun_bootstrap_strictLeft
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (first : In₁ × In₂) (word : List (In₁ × In₂))
    (input : In₁ × In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin first
    let current :=
      profiledRawJointHybridShadowPhaseLiveRightTagCreationRun A strategy hwin
        tag (tag.creationInitial A strategy hwin) word
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s, 0, 0,
        0, 0, 0, 0, 0, 0} A strategy hwin tag
        (tag.fallbackLeftOutput A strategy hwin)
        (tag.fallbackRightOutput A strategy hwin) current.1 current.2 input
    let oneNext := fresh.1.1.openControl
    let twoNext :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy hwin
          tag) current.2 input.2).1
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant.{u, v, x, y, s,
      0, 0, 0, 0} A strategy hwin tag oneNext twoNext := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin first
  let current :=
    profiledRawJointHybridShadowPhaseLiveRightTagCreationRun A strategy hwin tag
      (tag.creationInitial A strategy hwin) word
  have tracked :=
    profiledRawJointHybridShadowPhaseLiveRightTagCreationRun_initial_tracked A
      strategy hwin origin first word
  have phase :=
    profiledRawJointHybridShadowPhaseLiveRightTagCreationRun_initial_phase A
      strategy hwin origin first word
  simpa only [tag, current] using
    ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked.strictLeft.{u,
      v, x, y, s, 0, 0, 0, 0, 0, 0, 0, 0}
      (A := A) (strategy := strategy) (hwin := hwin) (tag := tag)
      (one := current.1) (two := current.2) tracked phase.1
      (tag.fallbackLeftOutput A strategy hwin)
      (tag.fallbackRightOutput A strategy hwin) input

end

end DetParityAutomaton

end DistributedSynthesis
