/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalPostStep

/-!
# Reconstruction of the end-to-end distributed pair

These lemmas prove that the total finite local receive table reconstructs the
latent matched phase or two-shadow candidate pair exactly on every valid
input shape.  The matched phase and its orientation remain proof objects;
runtime states contain only the independent projections and the past overlap
anchor.
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

theorem endToEndOperationalPostRecvRight_of_phase
    (phase : EndToEndMatchedPhase A package) (h : phase.IsRight)
    (move : In₁ × In₂) (candidates : EndToEndBothCandidates A package)
    (hnext : (phase.enterBothFromRight A package move).2 = some candidates) :
    endToEndOperationalPostRecvRight A package phase.oneControl
        phase.twoControl move =
      ((phase.enterBothFromRight A package move).1,
        some (endToEndOperationalPostOfCandidates A package false
          candidates)) := by
  unfold endToEndOperationalPostRecvRight endToEndPostRecvFromRight
  rw [endToEndMatchedRightOfControls_of_phase A package phase h]
  simp [hnext, endToEndOperationalPostOfCandidates]

theorem endToEndOperationalPostRecvLeft_of_phase
    (phase : EndToEndMatchedPhase A package) (h : phase.IsLeft)
    (move : In₁ × In₂) (candidates : EndToEndBothCandidates A package)
    (hnext : (phase.enterBothFromLeft A package move).2 = some candidates) :
    endToEndOperationalPostRecvLeft A package phase.oneControl
        phase.twoControl move =
      ((phase.enterBothFromLeft A package move).1,
        some (endToEndOperationalPostOfCandidates A package true
          candidates)) := by
  unfold endToEndOperationalPostRecvLeft endToEndPostRecvFromLeft
  rw [endToEndMatchedLeftOfControls_of_phase A package phase h]
  simp [hnext, endToEndOperationalPostOfCandidates]

theorem endToEndOperationalPostRecvOverlap_of_candidates
    (anchor : Bool) (candidates next : EndToEndBothCandidates A package)
    (move : In₁ × In₂)
    (hnext : (if anchor then
        candidates.repeatBothFromLeft A package move
      else candidates.repeatBothFromRight A package move).2 = some next) :
    endToEndOperationalPostRecvOverlap A package
        (anchor, candidates.oneControl A package)
        (anchor, candidates.twoControl A package) move =
      ((if anchor then
          candidates.repeatBothFromLeft A package move
        else candidates.repeatBothFromRight A package move).1,
        some (endToEndOperationalPostOfCandidates A package anchor next)) := by
  unfold endToEndOperationalPostRecvOverlap
  rw [endToEndBothOfOverlapControls_of_candidates A package anchor candidates]
  simp [hnext]

theorem endToEndMatchedRightOfControls_eq_none_of_left
    (phase : EndToEndMatchedPhase A package) (h : phase.IsLeft) :
    endToEndMatchedRightOfControls A package phase.oneControl
        phase.twoControl = none := by
  classical
  cases phase <;>
    simp_all [endToEndMatchedRightOfControls,
      EndToEndMatchedPhase.oneControl, EndToEndMatchedPhase.twoControl,
      EndToEndMatchedPhase.IsLeft]

theorem endToEndOperationalPostRecv_of_resolvedRight
    (phase : EndToEndMatchedPhase A package) (h : phase.IsRight)
    (move : In₁ × In₂) (candidates : EndToEndBothCandidates A package)
    (hnext : (phase.enterBothFromRight A package move).2 = some candidates) :
    endToEndOperationalPostRecv A package (.inl phase.oneControl)
        (.inl phase.twoControl) move =
      ((phase.enterBothFromRight A package move).1,
        some (endToEndOperationalPostOfCandidates A package false
          candidates)) := by
  simp only [endToEndOperationalPostRecv]
  rw [endToEndMatchedRightOfControls_of_phase A package phase h]
  exact endToEndOperationalPostRecvRight_of_phase A package phase h move
    candidates hnext

theorem endToEndOperationalPostRecv_of_resolvedLeft
    (phase : EndToEndMatchedPhase A package) (h : phase.IsLeft)
    (move : In₁ × In₂) (candidates : EndToEndBothCandidates A package)
    (hnext : (phase.enterBothFromLeft A package move).2 = some candidates) :
    endToEndOperationalPostRecv A package (.inl phase.oneControl)
        (.inl phase.twoControl) move =
      ((phase.enterBothFromLeft A package move).1,
        some (endToEndOperationalPostOfCandidates A package true
          candidates)) := by
  simp only [endToEndOperationalPostRecv]
  rw [endToEndMatchedRightOfControls_eq_none_of_left A package phase h]
  exact endToEndOperationalPostRecvLeft_of_phase A package phase h move
    candidates hnext

theorem endToEndOperationalPostRecv_of_mixedRight
    (anchor : Bool) (candidates next : EndToEndBothCandidates A package)
    (move : In₁ × In₂)
    (hnext : (candidates.right.enterBothFromRight A package move).2 =
      some next) :
    endToEndOperationalPostRecv A package
        (.inl candidates.right.oneControl)
        (.inr (anchor, candidates.twoControl A package)) move =
      ((candidates.right.enterBothFromRight A package move).1,
        some (endToEndOperationalPostOfCandidates A package false next)) := by
  unfold endToEndOperationalPostRecv
  exact endToEndOperationalPostRecvRight_of_phase A package candidates.right
    candidates.right_oriented move next hnext

theorem endToEndOperationalPostRecv_of_mixedLeft
    (anchor : Bool) (candidates next : EndToEndBothCandidates A package)
    (move : In₁ × In₂)
    (hnext : (candidates.left.enterBothFromLeft A package move).2 =
      some next) :
    endToEndOperationalPostRecv A package
        (.inr (anchor, candidates.oneControl A package))
        (.inl candidates.left.twoControl) move =
      ((candidates.left.enterBothFromLeft A package move).1,
        some (endToEndOperationalPostOfCandidates A package true next)) := by
  unfold endToEndOperationalPostRecv
  exact endToEndOperationalPostRecvLeft_of_phase A package candidates.left
    candidates.left_oriented move next hnext

/-! ## Strict local resolutions -/

theorem endToEndPostNoRecvOne_of_rightPhase
    (phase : EndToEndMatchedPhase A package) (h : phase.IsRight)
    (input : In₁) (inputTwo : In₂) :
    endToEndPostNoRecvOne A package phase.oneControl input =
      ((phase.continue A package (input, inputTwo)).1.1,
        some (phase.continue A package (input, inputTwo)).2.oneControl) := by
  cases phase <;>
    simp_all [endToEndPostNoRecvOne, EndToEndMatchedPhase.oneControl,
      EndToEndMatchedPhase.continue, EndToEndMatchedPhase.IsRight]

theorem endToEndPostNoRecvTwo_of_leftPhase
    (phase : EndToEndMatchedPhase A package) (h : phase.IsLeft)
    (inputOne : In₁) (input : In₂) :
    endToEndPostNoRecvTwo A package phase.twoControl input =
      ((phase.continue A package (inputOne, input)).1.2,
        some (phase.continue A package (inputOne, input)).2.twoControl) := by
  cases phase <;>
    simp_all [endToEndPostNoRecvTwo, EndToEndMatchedPhase.twoControl,
      EndToEndMatchedPhase.continue, EndToEndMatchedPhase.IsLeft]

theorem endToEndPostNoRecvTwo_of_reverseRightToLeft
    (phase next : EndToEndMatchedPhase A package) (h : phase.IsRight)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (hnext : (phase.reverseRightToLeft A package move
      previouslyReceived).2 = some next) :
    endToEndPostNoRecvTwo A package phase.twoControl move.2 =
      ((phase.reverseRightToLeft A package move previouslyReceived).1.2,
        some next.twoControl) := by
  cases phase with
  | firstRight owner receiver sameSource =>
      simp only [EndToEndMatchedPhase.reverseRightToLeft,
        EndToEndMatchedPhase.twoControl] at hnext ⊢
      split at hnext
      · cases Option.some.inj hnext
        simp [endToEndPostNoRecvTwo, *]
      · simp at hnext
  | rightOriginRight owner receiver sameSource =>
      simp only [EndToEndMatchedPhase.reverseRightToLeft,
        EndToEndMatchedPhase.twoControl] at hnext ⊢
      split at hnext
      · cases Option.some.inj hnext
        simp [endToEndPostNoRecvTwo, *]
      · simp at hnext
  | leftOriginRight owner receiver sameSource =>
      simp only [EndToEndMatchedPhase.reverseRightToLeft,
        EndToEndMatchedPhase.twoControl] at hnext ⊢
      split at hnext
      · cases Option.some.inj hnext
        simp [endToEndPostNoRecvTwo, *]
      · simp at hnext
  | firstLeft receiver owner sameSource =>
      simp [EndToEndMatchedPhase.IsRight] at h
  | rightOriginLeft receiver owner sameSource =>
      simp [EndToEndMatchedPhase.IsRight] at h
  | leftOriginLeft receiver owner sameSource =>
      simp [EndToEndMatchedPhase.IsRight] at h

theorem endToEndPostNoRecvOne_of_reverseLeftToRight
    (phase next : EndToEndMatchedPhase A package) (h : phase.IsLeft)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (hnext : (phase.reverseLeftToRight A package (move.2, move.1)
      previouslyReceived).2 = some next) :
    endToEndPostNoRecvOne A package phase.oneControl move.1 =
      ((phase.reverseLeftToRight A package (move.2, move.1)
          previouslyReceived).1.1,
        some next.oneControl) := by
  cases phase with
  | firstRight owner receiver sameSource =>
      simp [EndToEndMatchedPhase.IsLeft] at h
  | rightOriginRight owner receiver sameSource =>
      simp [EndToEndMatchedPhase.IsLeft] at h
  | leftOriginRight owner receiver sameSource =>
      simp [EndToEndMatchedPhase.IsLeft] at h
  | firstLeft receiver owner sameSource =>
      simp only [EndToEndMatchedPhase.reverseLeftToRight,
        EndToEndMatchedPhase.oneControl] at hnext ⊢
      split at hnext
      · cases Option.some.inj hnext
        simp [endToEndPostNoRecvOne, *]
      · simp at hnext
  | rightOriginLeft receiver owner sameSource =>
      simp only [EndToEndMatchedPhase.reverseLeftToRight,
        EndToEndMatchedPhase.oneControl] at hnext ⊢
      split at hnext
      · cases Option.some.inj hnext
        simp [endToEndPostNoRecvOne, *]
      · simp at hnext
  | leftOriginLeft receiver owner sameSource =>
      simp only [EndToEndMatchedPhase.reverseLeftToRight,
        EndToEndMatchedPhase.oneControl] at hnext ⊢
      split at hnext
      · cases Option.some.inj hnext
        simp [endToEndPostNoRecvOne, *]
      · simp at hnext

/-! ## Candidate identification -/

theorem endToEndEnterBothFromRight_candidate_right
    (phase : EndToEndMatchedPhase A package) (h : phase.IsRight)
    (move : In₁ × In₂) (candidates : EndToEndBothCandidates A package)
    (hnext : (phase.enterBothFromRight A package move).2 = some candidates) :
    candidates.right = (phase.continue A package move).2 := by
  unfold EndToEndMatchedPhase.enterBothFromRight at hnext
  dsimp only at hnext
  generalize hleft :
      (phase.reverseRightToLeft A package move false).2 = left at hnext
  cases left with
  | none => simp [hleft] at hnext
  | some left =>
      have hright := phase.continue_isRight A package move h
      by_cases hleftOriented : left.IsLeft
      · simp [hleft, hright, hleftOriented] at hnext
        cases hnext
        rfl
      · simp [hleft, hright, hleftOriented] at hnext

theorem endToEndEnterBothFromLeft_candidate_left
    (phase : EndToEndMatchedPhase A package) (h : phase.IsLeft)
    (move : In₁ × In₂) (candidates : EndToEndBothCandidates A package)
    (hnext : (phase.enterBothFromLeft A package move).2 = some candidates) :
    candidates.left = (phase.continue A package move).2 := by
  unfold EndToEndMatchedPhase.enterBothFromLeft at hnext
  dsimp only at hnext
  generalize hright :
      (phase.reverseLeftToRight A package (move.2, move.1) false).2 = right
        at hnext
  cases right with
  | none => simp [hright] at hnext
  | some right =>
      have hleft := phase.continue_isLeft A package move h
      by_cases hrightOriented : right.IsRight
      · simp [hright, hleft, hrightOriented] at hnext
        cases hnext
        rfl
      · simp [hright, hleft, hrightOriented] at hnext

end

end DetParityAutomaton

end DistributedSynthesis
