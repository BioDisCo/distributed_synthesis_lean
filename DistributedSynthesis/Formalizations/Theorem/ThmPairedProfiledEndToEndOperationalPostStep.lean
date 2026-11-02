/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOverlapInvariant

/-!
# Operational overlap carrier for the end-to-end package

This is the executable finite carrier for the post-initial phase.  A resolved
local control contains one phase projection; an overlap control contains the
two projections that remain possible after an indistinguishable receive.
The Boolean stored with an overlap is the retained past anchor used to refresh
the pair.  It is not the current graph and is not a strict-leader bit.

The decoders below are used only when the two finite summaries meet at a
receive.  They reconstruct the proof-only matched phase or candidate pair and
therefore avoid asking either process to identify the current orientation.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-! ## Decoding matched projections -/

/-- Recover a right-oriented matched phase after the two local projections
meet. -/
noncomputable def endToEndMatchedRightOfControls
    (one : EndToEndPhaseOneControl A package)
    (two : EndToEndPhaseTwoControl A package) :
    Option (EndToEndMatchedPhase A package) := by
  classical
  exact match one, two with
    | .inl owner, .inl receiver =>
        if h : owner.1 = receiver.1 then
          some (.firstRight owner receiver h)
        else none
    | .inr (.inr (.inl owner)), .inr (.inr (.inl receiver)) =>
        if h : owner.1 = receiver.1 then
          some (.rightOriginRight owner receiver h)
        else none
    | .inr (.inr (.inr (.inr (.inl owner)))),
        .inr (.inr (.inr (.inr (.inl receiver)))) =>
        if h : owner.1 = receiver.1 then
          some (.leftOriginRight owner receiver h)
        else none
    | _, _ => none

/-- Left-oriented mirror. -/
noncomputable def endToEndMatchedLeftOfControls
    (one : EndToEndPhaseOneControl A package)
    (two : EndToEndPhaseTwoControl A package) :
    Option (EndToEndMatchedPhase A package) := by
  classical
  exact match one, two with
    | .inr (.inl receiver), .inr (.inl owner) =>
        if h : receiver.1 = owner.1 then
          some (.firstLeft receiver owner h)
        else none
    | .inr (.inr (.inr (.inl receiver))),
        .inr (.inr (.inr (.inl owner))) =>
        if h : receiver.1 = owner.1 then
          some (.rightOriginLeft receiver owner h)
        else none
    | .inr (.inr (.inr (.inr (.inr receiver)))),
        .inr (.inr (.inr (.inr (.inr owner)))) =>
        if h : receiver.1 = owner.1 then
          some (.leftOriginLeft receiver owner h)
        else none
    | _, _ => none

theorem endToEndMatchedRightOfControls_of_phase
    (phase : EndToEndMatchedPhase A package) (h : phase.IsRight) :
    endToEndMatchedRightOfControls A package phase.oneControl
        phase.twoControl = some phase := by
  classical
  cases phase <;>
    simp_all [endToEndMatchedRightOfControls,
      EndToEndMatchedPhase.oneControl, EndToEndMatchedPhase.twoControl,
      EndToEndMatchedPhase.IsRight]

theorem endToEndMatchedLeftOfControls_of_phase
    (phase : EndToEndMatchedPhase A package) (h : phase.IsLeft) :
    endToEndMatchedLeftOfControls A package phase.oneControl
        phase.twoControl = some phase := by
  classical
  cases phase <;>
    simp_all [endToEndMatchedLeftOfControls,
      EndToEndMatchedPhase.oneControl, EndToEndMatchedPhase.twoControl,
      EndToEndMatchedPhase.IsLeft]

/-! ## Orientation of successful reversals -/

theorem endToEndReverseRightToLeft_isLeft_of_eq_some
    (phase next : EndToEndMatchedPhase A package)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (hnext : (phase.reverseRightToLeft A package move
      previouslyReceived).2 = some next) :
    next.IsLeft := by
  cases phase with
  | firstRight owner receiver sameSource =>
      simp only [EndToEndMatchedPhase.reverseRightToLeft] at hnext
      split at hnext
      next hOne hTwo =>
        cases Option.some.inj hnext
        simp [EndToEndMatchedPhase.IsLeft]
      all_goals simp at hnext
  | rightOriginRight owner receiver sameSource =>
      simp only [EndToEndMatchedPhase.reverseRightToLeft] at hnext
      split at hnext
      next hOne hTwo =>
        cases Option.some.inj hnext
        simp [EndToEndMatchedPhase.IsLeft]
      all_goals simp at hnext
  | leftOriginRight owner receiver sameSource =>
      simp only [EndToEndMatchedPhase.reverseRightToLeft] at hnext
      split at hnext
      next hOne hTwo =>
        cases Option.some.inj hnext
        simp [EndToEndMatchedPhase.IsLeft]
      all_goals simp at hnext
  | firstLeft receiver owner sameSource =>
      simp [EndToEndMatchedPhase.reverseRightToLeft] at hnext
  | rightOriginLeft receiver owner sameSource =>
      simp [EndToEndMatchedPhase.reverseRightToLeft] at hnext
  | leftOriginLeft receiver owner sameSource =>
      simp [EndToEndMatchedPhase.reverseRightToLeft] at hnext

theorem endToEndReverseLeftToRight_isRight_of_eq_some
    (phase next : EndToEndMatchedPhase A package)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (hnext : (phase.reverseLeftToRight A package (move.2, move.1)
      previouslyReceived).2 = some next) :
    next.IsRight := by
  cases phase with
  | firstRight owner receiver sameSource =>
      simp [EndToEndMatchedPhase.reverseLeftToRight] at hnext
  | rightOriginRight owner receiver sameSource =>
      simp [EndToEndMatchedPhase.reverseLeftToRight] at hnext
  | leftOriginRight owner receiver sameSource =>
      simp [EndToEndMatchedPhase.reverseLeftToRight] at hnext
  | firstLeft receiver owner sameSource =>
      simp only [EndToEndMatchedPhase.reverseLeftToRight] at hnext
      split at hnext
      next hOne hTwo =>
        cases Option.some.inj hnext
        simp [EndToEndMatchedPhase.IsRight]
      all_goals simp at hnext
  | rightOriginLeft receiver owner sameSource =>
      simp only [EndToEndMatchedPhase.reverseLeftToRight] at hnext
      split at hnext
      next hOne hTwo =>
        cases Option.some.inj hnext
        simp [EndToEndMatchedPhase.IsRight]
      all_goals simp at hnext
  | leftOriginLeft receiver owner sameSource =>
      simp only [EndToEndMatchedPhase.reverseLeftToRight] at hnext
      split at hnext
      next hOne hTwo =>
        cases Option.some.inj hnext
        simp [EndToEndMatchedPhase.IsRight]
      all_goals simp at hnext

/-! ## Finite two-shadow carrier -/

abbrev EndToEndOperationalOverlapOne :=
  Bool ×
    (EndToEndPhaseOneControl A package ×
      EndToEndPhaseOneControl A package)

abbrev EndToEndOperationalOverlapTwo :=
  Bool ×
    (EndToEndPhaseTwoControl A package ×
      EndToEndPhaseTwoControl A package)

abbrev EndToEndOperationalPostOne :=
  EndToEndPhaseOneControl A package ⊕
    EndToEndOperationalOverlapOne A package

abbrev EndToEndOperationalPostTwo :=
  EndToEndPhaseTwoControl A package ⊕
    EndToEndOperationalOverlapTwo A package

noncomputable instance : Fintype (EndToEndOperationalPostOne A package) := by
  classical
  infer_instance

noncomputable instance : Fintype (EndToEndOperationalPostTwo A package) := by
  classical
  infer_instance

/-- Reassemble the proof-only candidate pair when the two overlap summaries
meet. -/
noncomputable def endToEndBothOfOverlapControls
    (one : EndToEndOperationalOverlapOne A package)
    (two : EndToEndOperationalOverlapTwo A package) :
    Option (EndToEndBothCandidates A package) := by
  classical
  exact if hanchor : one.1 = two.1 then
    match endToEndMatchedRightOfControls A package one.2.1 two.2.1,
        endToEndMatchedLeftOfControls A package one.2.2 two.2.2 with
    | some right, some left =>
        if hright : right.IsRight then
          if hleft : left.IsLeft then
            some ⟨right, left, hright, hleft⟩
          else none
        else none
    | _, _ => none
  else none

/-- Package a proof-level candidate pair into the two independent local
overlap summaries. -/
def endToEndOperationalPostOfCandidates
    (anchor : Bool) (candidates : EndToEndBothCandidates A package) :
    EndToEndOperationalPostOne A package ×
      EndToEndOperationalPostTwo A package :=
  (.inr (anchor, candidates.oneControl A package),
    .inr (anchor, candidates.twoControl A package))

theorem endToEndBothOfOverlapControls_of_candidates
    (anchor : Bool) (candidates : EndToEndBothCandidates A package) :
    endToEndBothOfOverlapControls A package
        (anchor, candidates.oneControl A package)
        (anchor, candidates.twoControl A package) = some candidates := by
  classical
  unfold endToEndBothOfOverlapControls
  simp only [Prod.fst, Prod.snd, if_pos rfl,
    EndToEndBothCandidates.oneControl, EndToEndBothCandidates.twoControl]
  rw [endToEndMatchedRightOfControls_of_phase A package candidates.right
      candidates.right_oriented,
    endToEndMatchedLeftOfControls_of_phase A package candidates.left
      candidates.left_oriented]
  simp [candidates.right_oriented, candidates.left_oriented]

/-! ## Strict no-receive operations -/

/-- Process one's local strict-right step.  Right owners continue; left
receivers consume their already staged target and become right owners. -/
noncomputable def endToEndPostNoRecvOne
    (one : EndToEndPhaseOneControl A package) (input : In₁) :
    Out₁ × Option (EndToEndPhaseOneControl A package) :=
  match one with
  | .inl owner =>
      let next := stepEndToEndGuardedFirstRightOwner A package owner input
      (next.1, some (.inl next.2))
  | .inr (.inl receiver) =>
      let next := switchEndToEndFirstLeftReceiverToRecurrentRightOwner A
        package receiver input
      (next.1, next.2.map fun owner =>
        .inr (.inr (.inr (.inr (.inl owner)))))
  | .inr (.inr (.inl owner)) =>
      let next := stepEndToEndRightOriginRecurrentRightOwner A package owner
        input
      (next.1, some (.inr (.inr (.inl next.2))))
  | .inr (.inr (.inr (.inl receiver))) =>
      let next := switchEndToEndRightOriginLeftReceiverToRightOwner A package
        receiver input
      (next.1, next.2.map fun owner => .inr (.inr (.inl owner)))
  | .inr (.inr (.inr (.inr (.inl owner)))) =>
      let next := stepEndToEndLeftOriginRecurrentRightOwner A package owner
        input
      (next.1, some (.inr (.inr (.inr (.inr (.inl next.2))))))
  | .inr (.inr (.inr (.inr (.inr receiver)))) =>
      let next := switchEndToEndLeftOriginLeftReceiverToRightOwner A package
        receiver input
      (next.1, next.2.map fun owner =>
        .inr (.inr (.inr (.inr (.inl owner)))))

/-- Process-two mirror. -/
noncomputable def endToEndPostNoRecvTwo
    (two : EndToEndPhaseTwoControl A package) (input : In₂) :
    Out₂ × Option (EndToEndPhaseTwoControl A package) :=
  match two with
  | .inl receiver =>
      let next := switchEndToEndFirstRightReceiverToRecurrentLeftOwner A
        package receiver input
      (next.1, next.2.map fun owner =>
        .inr (.inr (.inr (.inl owner))))
  | .inr (.inl owner) =>
      let next := stepEndToEndGuardedFirstLeftOwner A package owner input
      (next.1, some (.inr (.inl next.2)))
  | .inr (.inr (.inl receiver)) =>
      let next := switchEndToEndRightOriginRightReceiverToLeftOwner A package
        receiver input
      (next.1, next.2.map fun owner =>
        .inr (.inr (.inr (.inl owner))))
  | .inr (.inr (.inr (.inl owner))) =>
      let next := stepEndToEndRightOriginRecurrentLeftOwner A package owner
        input
      (next.1, some (.inr (.inr (.inr (.inl next.2)))))
  | .inr (.inr (.inr (.inr (.inl receiver)))) =>
      let next := switchEndToEndLeftOriginRightReceiverToLeftOwner A package
        receiver input
      (next.1, next.2.map fun owner =>
        .inr (.inr (.inr (.inr (.inr owner)))))
  | .inr (.inr (.inr (.inr (.inr owner)))) =>
      let next := stepEndToEndLeftOriginRecurrentLeftOwner A package owner
        input
      (next.1, some (.inr (.inr (.inr (.inr (.inr next.2))))))

/-! ## Receive operations -/

noncomputable def endToEndPostRecvFromRight
    (one : EndToEndPhaseOneControl A package)
    (two : EndToEndPhaseTwoControl A package) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (EndToEndOperationalOverlapOne A package ×
        EndToEndOperationalOverlapTwo A package) :=
  match endToEndMatchedRightOfControls A package one two with
  | none => ((default, default), none)
  | some phase =>
      let next := phase.enterBothFromRight A package move
      (next.1, next.2.map fun candidates =>
        ((false, candidates.oneControl A package),
          (false, candidates.twoControl A package)))

noncomputable def endToEndPostRecvFromLeft
    (one : EndToEndPhaseOneControl A package)
    (two : EndToEndPhaseTwoControl A package) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (EndToEndOperationalOverlapOne A package ×
        EndToEndOperationalOverlapTwo A package) :=
  match endToEndMatchedLeftOfControls A package one two with
  | none => ((default, default), none)
  | some phase =>
      let next := phase.enterBothFromLeft A package move
      (next.1, next.2.map fun candidates =>
        ((true, candidates.oneControl A package),
          (true, candidates.twoControl A package)))

noncomputable def endToEndOperationalPostRecvRight
    (one : EndToEndPhaseOneControl A package)
    (two : EndToEndPhaseTwoControl A package) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (EndToEndOperationalPostOne A package ×
        EndToEndOperationalPostTwo A package) :=
  let next := endToEndPostRecvFromRight A package one two move
  (next.1, next.2.map fun pair => (.inr pair.1, .inr pair.2))

noncomputable def endToEndOperationalPostRecvLeft
    (one : EndToEndPhaseOneControl A package)
    (two : EndToEndPhaseTwoControl A package) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (EndToEndOperationalPostOne A package ×
        EndToEndOperationalPostTwo A package) :=
  let next := endToEndPostRecvFromLeft A package one two move
  (next.1, next.2.map fun pair => (.inr pair.1, .inr pair.2))

/-- Repeat a receive from two overlap summaries.  The common past anchor
selects the shadow from which the refreshed candidate pair is built. -/
noncomputable def endToEndOperationalPostRecvOverlap
    (one : EndToEndOperationalOverlapOne A package)
    (two : EndToEndOperationalOverlapTwo A package) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (EndToEndOperationalPostOne A package ×
        EndToEndOperationalPostTwo A package) :=
  match endToEndBothOfOverlapControls A package one two with
  | none => ((default, default), none)
  | some candidates =>
      let next := if one.1 then
        candidates.repeatBothFromLeft A package move
      else
        candidates.repeatBothFromRight A package move
      (next.1, next.2.map fun c =>
        endToEndOperationalPostOfCandidates A package one.1 c)

/-- Complete recurrent receive table, including the two mixed shapes that
arise after only one process has resolved an overlap. -/
noncomputable def endToEndOperationalPostRecv
    (one : EndToEndOperationalPostOne A package)
    (two : EndToEndOperationalPostTwo A package) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (EndToEndOperationalPostOne A package ×
        EndToEndOperationalPostTwo A package) :=
  match one, two with
  | .inl one, .inl two =>
      match endToEndMatchedRightOfControls A package one two with
      | some _ => endToEndOperationalPostRecvRight A package one two move
      | none => endToEndOperationalPostRecvLeft A package one two move
  | .inl one, .inr two =>
      endToEndOperationalPostRecvRight A package one two.2.1 move
  | .inr one, .inl two =>
      endToEndOperationalPostRecvLeft A package one.2.2 two move
  | .inr one, .inr two =>
      endToEndOperationalPostRecvOverlap A package one two move

/-- Process one's complete post-initial no-receive table. -/
noncomputable def endToEndOperationalPostNoRecvOne
    (one : EndToEndOperationalPostOne A package) (input : In₁) :
    Out₁ × Option (EndToEndOperationalPostOne A package) :=
  let next := match one with
    | .inl one => endToEndPostNoRecvOne A package one input
    | .inr one => endToEndPostNoRecvOne A package
        (if one.1 then one.2.2 else one.2.1) input
  (next.1, next.2.map Sum.inl)

/-- Process-two mirror. -/
noncomputable def endToEndOperationalPostNoRecvTwo
    (two : EndToEndOperationalPostTwo A package) (input : In₂) :
    Out₂ × Option (EndToEndOperationalPostTwo A package) :=
  let next := match two with
    | .inl two => endToEndPostNoRecvTwo A package two input
    | .inr two => endToEndPostNoRecvTwo A package
        (if two.1 then two.2.2 else two.2.1) input
  (next.1, next.2.map Sum.inl)

end

end DetParityAutomaton

end DistributedSynthesis
