/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalSeamReality

/-!
# Executable post-seam round closure

This file lifts the proof-only recurrent reality invariant through the actual
`LocalSummaryAutomaton` tables.  Orientation is used only to relate the two
finite local controls in the proof; it is not stored by either process.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

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

variable (bundle : EndToEndOperationalControllerPackage A)

/-- The executable joint receive table agrees with the abstract post table
on every real post-seam pair. -/
theorem endToEndOperationalRecvPair_real_post
    (shape : EndToEndOperationalPostShape A bundle.rational)
    (hreal : shape.Real A bundle.rational) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      endToEndOperationalRecvPair A bundle
          (.post shape.oneControl) (.post shape.twoControl) move =
        ((.post next.oneControl, output.1),
          (.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨output, next, hrecv, hnext⟩ :=
    endToEndOperationalPostRecv_realShape A bundle.rational shape hreal move
  refine ⟨output, next, ?_, hnext⟩
  simp only [endToEndOperationalRecvPair]
  rw [hrecv]

/-- A synchronized round (`Graph.both`) preserves the real post-seam
invariant in the actual local-summary automaton. -/
theorem endToEndOperationalAdvance_both_real_post
    (shape : EndToEndOperationalPostShape A bundle.rational)
    (hreal : shape.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post shape.oneControl, oldOutput.1),
            (EndToEndOperationalTwoControl.post shape.twoControl, oldOutput.2))
          .both move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨output, next, hrecv, hnext⟩ :=
    endToEndOperationalRecvPair_real_post A bundle shape hreal move
  refine ⟨output, next, ?_, hnext⟩
  simpa [LocalSummaryAutomaton.advance,
    endToEndOperationalSummaryAutomaton] using hrecv

/-! ## Strict rounds from a resolved phase -/

/-- A strict-right round from a real right phase leaves process one resolved
and process two carrying the refreshed two-shadow state. -/
theorem endToEndOperationalAdvance_right_real_resolvedRight
    (phase : EndToEndMatchedPhase A bundle.rational)
    (horiented : phase.IsRight)
    (hreal : IsRealEndToEndPhase A bundle.rational phase)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post (.inl phase.oneControl),
              oldOutput.1),
            (EndToEndOperationalTwoControl.post (.inl phase.twoControl),
              oldOutput.2)) .right move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨candidates, hcandidates, hright, hleft⟩ :=
    exists_real_endToEnd_candidates_enterBothFromRight A bundle.rational
      phase hreal horiented move
  have hcandidateRight :=
    endToEndEnterBothFromRight_candidate_right A bundle.rational phase
      horiented move candidates hcandidates
  have hno := endToEndPostNoRecvOne_of_rightPhase A bundle.rational phase
    horiented move.1 move.2
  have hrecv := endToEndOperationalPostRecv_of_resolvedRight A
    bundle.rational phase horiented move candidates hcandidates
  let next : EndToEndOperationalPostShape A bundle.rational :=
    .mixedRight false candidates
  refine ⟨(phase.continue A bundle.rational move).1, next, ?_, ?_⟩
  · simp only [LocalSummaryAutomaton.advance,
      endToEndOperationalSummaryAutomaton]
    simp only [endToEndOperationalNoRecvOne,
      endToEndOperationalPostNoRecvOne]
    rw [hno]
    simp only [endToEndOperationalRecvPair]
    rw [hrecv]
    simp [next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl,
      endToEndOperationalPostOfCandidates,
      EndToEndBothCandidates.repeatBothFromRight, hcandidateRight]
  · exact ⟨hright, hleft⟩

/-- A strict-left round from a real right phase performs the genuine
right-to-left reversal on the nonreceiving process and retains both shadows
on the receiver. -/
theorem endToEndOperationalAdvance_left_real_resolvedRight
    (phase : EndToEndMatchedPhase A bundle.rational)
    (horiented : phase.IsRight)
    (hreal : IsRealEndToEndPhase A bundle.rational phase)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post (.inl phase.oneControl),
              oldOutput.1),
            (EndToEndOperationalTwoControl.post (.inl phase.twoControl),
              oldOutput.2)) .left move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨candidates, hcandidates, hright, hleft⟩ :=
    exists_real_endToEnd_candidates_enterBothFromRight A bundle.rational
      phase hreal horiented move
  have hcandidateLeft :=
    endToEndEnterBothFromRight_candidate_left A bundle.rational phase move
      candidates hcandidates
  have hno := endToEndPostNoRecvTwo_of_reverseRightToLeft A bundle.rational
    phase candidates.left horiented move false hcandidateLeft
  have hrecv := endToEndOperationalPostRecv_of_resolvedRight A
    bundle.rational phase horiented move candidates hcandidates
  let next : EndToEndOperationalPostShape A bundle.rational :=
    .mixedLeft false candidates
  refine ⟨(phase.reverseRightToLeft A bundle.rational move false).1,
    next, ?_, ?_⟩
  · simp only [LocalSummaryAutomaton.advance,
      endToEndOperationalSummaryAutomaton]
    simp only [endToEndOperationalRecvPair]
    rw [hrecv]
    simp only [endToEndOperationalNoRecvTwo,
      endToEndOperationalPostNoRecvTwo]
    rw [hno]
    simp [next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl,
      endToEndOperationalPostOfCandidates]
  · exact ⟨hright, hleft⟩

/-- Left-oriented continuation mirror. -/
theorem endToEndOperationalAdvance_left_real_resolvedLeft
    (phase : EndToEndMatchedPhase A bundle.rational)
    (horiented : phase.IsLeft)
    (hreal : IsRealEndToEndPhase A bundle.rational phase)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post (.inl phase.oneControl),
              oldOutput.1),
            (EndToEndOperationalTwoControl.post (.inl phase.twoControl),
              oldOutput.2)) .left move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨candidates, hcandidates, hright, hleft⟩ :=
    exists_real_endToEnd_candidates_enterBothFromLeft A bundle.rational
      phase hreal horiented move
  have hcandidateLeft :=
    endToEndEnterBothFromLeft_candidate_left A bundle.rational phase
      horiented move candidates hcandidates
  have hno := endToEndPostNoRecvTwo_of_leftPhase A bundle.rational phase
    horiented move.1 move.2
  have hrecv := endToEndOperationalPostRecv_of_resolvedLeft A
    bundle.rational phase horiented move candidates hcandidates
  let next : EndToEndOperationalPostShape A bundle.rational :=
    .mixedLeft true candidates
  refine ⟨(phase.continue A bundle.rational move).1, next, ?_, ?_⟩
  · simp only [LocalSummaryAutomaton.advance,
      endToEndOperationalSummaryAutomaton]
    simp only [endToEndOperationalRecvPair]
    rw [hrecv]
    simp only [endToEndOperationalNoRecvTwo,
      endToEndOperationalPostNoRecvTwo]
    rw [hno]
    simp [next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl,
      endToEndOperationalPostOfCandidates, hcandidateLeft]
  · exact ⟨hright, hleft⟩

/-- Left-to-right strict reversal mirror. -/
theorem endToEndOperationalAdvance_right_real_resolvedLeft
    (phase : EndToEndMatchedPhase A bundle.rational)
    (horiented : phase.IsLeft)
    (hreal : IsRealEndToEndPhase A bundle.rational phase)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post (.inl phase.oneControl),
              oldOutput.1),
            (EndToEndOperationalTwoControl.post (.inl phase.twoControl),
              oldOutput.2)) .right move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨candidates, hcandidates, hright, hleft⟩ :=
    exists_real_endToEnd_candidates_enterBothFromLeft A bundle.rational
      phase hreal horiented move
  have hcandidateRight :=
    endToEndEnterBothFromLeft_candidate_right A bundle.rational phase move
      candidates hcandidates
  have hno := endToEndPostNoRecvOne_of_reverseLeftToRight A bundle.rational
    phase candidates.right horiented move false hcandidateRight
  have hrecv := endToEndOperationalPostRecv_of_resolvedLeft A
    bundle.rational phase horiented move candidates hcandidates
  let next : EndToEndOperationalPostShape A bundle.rational :=
    .mixedRight true candidates
  refine ⟨(phase.reverseLeftToRight A bundle.rational (move.2, move.1)
      false).1, next, ?_, ?_⟩
  · simp only [LocalSummaryAutomaton.advance,
      endToEndOperationalSummaryAutomaton]
    simp only [endToEndOperationalNoRecvOne,
      endToEndOperationalPostNoRecvOne]
    rw [hno]
    simp only [endToEndOperationalRecvPair]
    rw [hrecv]
    simp [next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl,
      endToEndOperationalPostOfCandidates]
  · exact ⟨hright, hleft⟩

/-! ## Strict rounds from a synchronized overlap -/

/-- With a retained right anchor, a strict-right round resolves process one
to the right continuation while process two refreshes the two shadows. -/
theorem endToEndOperationalAdvance_right_real_overlap_false
    (candidates : EndToEndBothCandidates A bundle.rational)
    (hreal : candidates.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post
              ((.overlap false candidates :
                EndToEndOperationalPostShape A bundle.rational).oneControl),
              oldOutput.1),
            (EndToEndOperationalTwoControl.post
              ((.overlap false candidates :
                EndToEndOperationalPostShape A bundle.rational).twoControl),
              oldOutput.2)) .right move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨fresh, hfresh, hright, hleft⟩ :=
    exists_real_endToEnd_candidates_repeatBoth A bundle.rational false
      candidates hreal.1 hreal.2 move
  have hfresh' :
      (candidates.right.enterBothFromRight A bundle.rational move).2 =
        some fresh := by
    simpa [EndToEndBothCandidates.repeatBothFromRight] using hfresh
  have hcandidateRight :=
    endToEndEnterBothFromRight_candidate_right A bundle.rational
      candidates.right candidates.right_oriented move fresh hfresh'
  have hno := endToEndPostNoRecvOne_of_rightPhase A bundle.rational
    candidates.right candidates.right_oriented move.1 move.2
  have hnoFull :
      endToEndOperationalNoRecvOne A bundle
          (.post (.inr (false,
            candidates.oneControl A bundle.rational))) move.1 =
        ((candidates.right.continue A bundle.rational move).1.1,
          .post (.inl
            (candidates.right.continue A bundle.rational move).2.oneControl)) := by
    simp [endToEndOperationalNoRecvOne,
      endToEndOperationalPostNoRecvOne,
      EndToEndBothCandidates.oneControl, hno]
  have hrecv := endToEndOperationalPostRecvOverlap_of_candidates A
    bundle.rational false candidates fresh move hfresh
  have hrecvFull :
      endToEndOperationalPostRecv A bundle.rational
          (.inr (false, candidates.oneControl A bundle.rational))
          (.inr (false, candidates.twoControl A bundle.rational)) move =
        ((candidates.repeatBothFromRight A bundle.rational move).1,
          some (endToEndOperationalPostOfCandidates A bundle.rational false
            fresh)) := by
    simpa [endToEndOperationalPostRecv,
      EndToEndBothCandidates.repeatBothFromRight] using hrecv
  have hrecvPair :
      endToEndOperationalRecvPair A bundle
          (.post (.inr (false, candidates.oneControl A bundle.rational)))
          (.post (.inr (false, candidates.twoControl A bundle.rational)))
          move =
        ((.post (endToEndOperationalPostOfCandidates A bundle.rational false
              fresh).1,
            (candidates.repeatBothFromRight A bundle.rational move).1.1),
          (.post (endToEndOperationalPostOfCandidates A bundle.rational false
              fresh).2,
            (candidates.repeatBothFromRight A bundle.rational move).1.2)) := by
    simp only [endToEndOperationalRecvPair]
    rw [hrecvFull]
  let next : EndToEndOperationalPostShape A bundle.rational :=
    .mixedRight false fresh
  refine ⟨(candidates.right.continue A bundle.rational move).1,
    next, ?_, ?_⟩
  · simp only [LocalSummaryAutomaton.advance,
      endToEndOperationalSummaryAutomaton]
    simp only [EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl]
    rw [hnoFull]
    rw [hrecvPair]
    simp [next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl,
      endToEndOperationalPostOfCandidates,
      EndToEndBothCandidates.repeatBothFromRight, hcandidateRight]
  · exact ⟨hright, hleft⟩

/-- The opposite strict edge from a right-anchored overlap selects the
freshly reversed left shadow on process two. -/
theorem endToEndOperationalAdvance_left_real_overlap_false
    (candidates : EndToEndBothCandidates A bundle.rational)
    (hreal : candidates.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post
              ((.overlap false candidates :
                EndToEndOperationalPostShape A bundle.rational).oneControl),
              oldOutput.1),
            (EndToEndOperationalTwoControl.post
              ((.overlap false candidates :
                EndToEndOperationalPostShape A bundle.rational).twoControl),
              oldOutput.2)) .left move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨fresh, hfresh, hright, hleft⟩ :=
    exists_real_endToEnd_candidates_repeatBoth A bundle.rational false
      candidates hreal.1 hreal.2 move
  have hfresh' :
      (candidates.right.enterBothFromRight A bundle.rational move).2 =
        some fresh := by
    simpa [EndToEndBothCandidates.repeatBothFromRight] using hfresh
  have hcandidateLeft :=
    endToEndEnterBothFromRight_candidate_left A bundle.rational
      candidates.right move fresh hfresh'
  have hno := endToEndPostNoRecvTwo_of_reverseRightToLeft A bundle.rational
    candidates.right fresh.left candidates.right_oriented move false
      hcandidateLeft
  have hnoFull :
      endToEndOperationalNoRecvTwo A bundle
          (.post (.inr (false,
            candidates.twoControl A bundle.rational))) move.2 =
        ((candidates.right.reverseRightToLeft A bundle.rational move
            false).1.2,
          .post (.inl fresh.left.twoControl)) := by
    simp [endToEndOperationalNoRecvTwo,
      endToEndOperationalPostNoRecvTwo,
      EndToEndBothCandidates.twoControl, hno]
  have hrecv := endToEndOperationalPostRecvOverlap_of_candidates A
    bundle.rational false candidates fresh move hfresh
  have hrecvFull :
      endToEndOperationalPostRecv A bundle.rational
          (.inr (false, candidates.oneControl A bundle.rational))
          (.inr (false, candidates.twoControl A bundle.rational)) move =
        ((candidates.repeatBothFromRight A bundle.rational move).1,
          some (endToEndOperationalPostOfCandidates A bundle.rational false
            fresh)) := by
    simpa [endToEndOperationalPostRecv,
      EndToEndBothCandidates.repeatBothFromRight] using hrecv
  have hrecvPair :
      endToEndOperationalRecvPair A bundle
          (.post (.inr (false, candidates.oneControl A bundle.rational)))
          (.post (.inr (false, candidates.twoControl A bundle.rational)))
          move =
        ((.post (endToEndOperationalPostOfCandidates A bundle.rational false
              fresh).1,
            (candidates.repeatBothFromRight A bundle.rational move).1.1),
          (.post (endToEndOperationalPostOfCandidates A bundle.rational false
              fresh).2,
            (candidates.repeatBothFromRight A bundle.rational move).1.2)) := by
    simp only [endToEndOperationalRecvPair]
    rw [hrecvFull]
  let next : EndToEndOperationalPostShape A bundle.rational :=
    .mixedLeft false fresh
  refine ⟨(candidates.right.reverseRightToLeft A bundle.rational move
      false).1, next, ?_, ?_⟩
  · simp only [LocalSummaryAutomaton.advance,
      endToEndOperationalSummaryAutomaton]
    simp only [EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl]
    rw [hrecvPair]
    rw [hnoFull]
    simp [next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl,
      endToEndOperationalPostOfCandidates,
      EndToEndBothCandidates.repeatBothFromRight]
  · exact ⟨hright, hleft⟩

/-- Left-anchored overlap continuation. -/
theorem endToEndOperationalAdvance_left_real_overlap_true
    (candidates : EndToEndBothCandidates A bundle.rational)
    (hreal : candidates.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post
              ((.overlap true candidates :
                EndToEndOperationalPostShape A bundle.rational).oneControl),
              oldOutput.1),
            (EndToEndOperationalTwoControl.post
              ((.overlap true candidates :
                EndToEndOperationalPostShape A bundle.rational).twoControl),
              oldOutput.2)) .left move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨fresh, hfresh, hright, hleft⟩ :=
    exists_real_endToEnd_candidates_repeatBoth A bundle.rational true
      candidates hreal.1 hreal.2 move
  have hfresh' :
      (candidates.left.enterBothFromLeft A bundle.rational move).2 =
        some fresh := by
    simpa [EndToEndBothCandidates.repeatBothFromLeft] using hfresh
  have hcandidateLeft :=
    endToEndEnterBothFromLeft_candidate_left A bundle.rational
      candidates.left candidates.left_oriented move fresh hfresh'
  have hno := endToEndPostNoRecvTwo_of_leftPhase A bundle.rational
    candidates.left candidates.left_oriented move.1 move.2
  have hnoFull :
      endToEndOperationalNoRecvTwo A bundle
          (.post (.inr (true,
            candidates.twoControl A bundle.rational))) move.2 =
        ((candidates.left.continue A bundle.rational move).1.2,
          .post (.inl
            (candidates.left.continue A bundle.rational move).2.twoControl)) := by
    simp [endToEndOperationalNoRecvTwo,
      endToEndOperationalPostNoRecvTwo,
      EndToEndBothCandidates.twoControl, hno]
  have hrecv := endToEndOperationalPostRecvOverlap_of_candidates A
    bundle.rational true candidates fresh move hfresh
  have hrecvFull :
      endToEndOperationalPostRecv A bundle.rational
          (.inr (true, candidates.oneControl A bundle.rational))
          (.inr (true, candidates.twoControl A bundle.rational)) move =
        ((candidates.repeatBothFromLeft A bundle.rational move).1,
          some (endToEndOperationalPostOfCandidates A bundle.rational true
            fresh)) := by
    simpa [endToEndOperationalPostRecv,
      EndToEndBothCandidates.repeatBothFromLeft] using hrecv
  have hrecvPair :
      endToEndOperationalRecvPair A bundle
          (.post (.inr (true, candidates.oneControl A bundle.rational)))
          (.post (.inr (true, candidates.twoControl A bundle.rational)))
          move =
        ((.post (endToEndOperationalPostOfCandidates A bundle.rational true
              fresh).1,
            (candidates.repeatBothFromLeft A bundle.rational move).1.1),
          (.post (endToEndOperationalPostOfCandidates A bundle.rational true
              fresh).2,
            (candidates.repeatBothFromLeft A bundle.rational move).1.2)) := by
    simp only [endToEndOperationalRecvPair]
    rw [hrecvFull]
  let next : EndToEndOperationalPostShape A bundle.rational :=
    .mixedLeft true fresh
  refine ⟨(candidates.left.continue A bundle.rational move).1,
    next, ?_, ?_⟩
  · simp only [LocalSummaryAutomaton.advance,
      endToEndOperationalSummaryAutomaton]
    simp only [EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl]
    rw [hrecvPair]
    rw [hnoFull]
    simp [next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl,
      endToEndOperationalPostOfCandidates,
      EndToEndBothCandidates.repeatBothFromLeft, hcandidateLeft]
  · exact ⟨hright, hleft⟩

/-- Left-anchored overlap reversal. -/
theorem endToEndOperationalAdvance_right_real_overlap_true
    (candidates : EndToEndBothCandidates A bundle.rational)
    (hreal : candidates.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post
              ((.overlap true candidates :
                EndToEndOperationalPostShape A bundle.rational).oneControl),
              oldOutput.1),
            (EndToEndOperationalTwoControl.post
              ((.overlap true candidates :
                EndToEndOperationalPostShape A bundle.rational).twoControl),
              oldOutput.2)) .right move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨fresh, hfresh, hright, hleft⟩ :=
    exists_real_endToEnd_candidates_repeatBoth A bundle.rational true
      candidates hreal.1 hreal.2 move
  have hfresh' :
      (candidates.left.enterBothFromLeft A bundle.rational move).2 =
        some fresh := by
    simpa [EndToEndBothCandidates.repeatBothFromLeft] using hfresh
  have hcandidateRight :=
    endToEndEnterBothFromLeft_candidate_right A bundle.rational
      candidates.left move fresh hfresh'
  have hno := endToEndPostNoRecvOne_of_reverseLeftToRight A bundle.rational
    candidates.left fresh.right candidates.left_oriented move false
      hcandidateRight
  have hnoFull :
      endToEndOperationalNoRecvOne A bundle
          (.post (.inr (true,
            candidates.oneControl A bundle.rational))) move.1 =
        ((candidates.left.reverseLeftToRight A bundle.rational
            (move.2, move.1) false).1.1,
          .post (.inl fresh.right.oneControl)) := by
    simp [endToEndOperationalNoRecvOne,
      endToEndOperationalPostNoRecvOne,
      EndToEndBothCandidates.oneControl, hno]
  have hrecv := endToEndOperationalPostRecvOverlap_of_candidates A
    bundle.rational true candidates fresh move hfresh
  have hrecvFull :
      endToEndOperationalPostRecv A bundle.rational
          (.inr (true, candidates.oneControl A bundle.rational))
          (.inr (true, candidates.twoControl A bundle.rational)) move =
        ((candidates.repeatBothFromLeft A bundle.rational move).1,
          some (endToEndOperationalPostOfCandidates A bundle.rational true
            fresh)) := by
    simpa [endToEndOperationalPostRecv,
      EndToEndBothCandidates.repeatBothFromLeft] using hrecv
  have hrecvPair :
      endToEndOperationalRecvPair A bundle
          (.post (.inr (true, candidates.oneControl A bundle.rational)))
          (.post (.inr (true, candidates.twoControl A bundle.rational)))
          move =
        ((.post (endToEndOperationalPostOfCandidates A bundle.rational true
              fresh).1,
            (candidates.repeatBothFromLeft A bundle.rational move).1.1),
          (.post (endToEndOperationalPostOfCandidates A bundle.rational true
              fresh).2,
            (candidates.repeatBothFromLeft A bundle.rational move).1.2)) := by
    simp only [endToEndOperationalRecvPair]
    rw [hrecvFull]
  let next : EndToEndOperationalPostShape A bundle.rational :=
    .mixedRight true fresh
  refine ⟨(candidates.left.reverseLeftToRight A bundle.rational
      (move.2, move.1) false).1, next, ?_, ?_⟩
  · simp only [LocalSummaryAutomaton.advance,
      endToEndOperationalSummaryAutomaton]
    simp only [EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl]
    rw [hnoFull]
    rw [hrecvPair]
    simp [next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl,
      endToEndOperationalPostOfCandidates,
      EndToEndBothCandidates.repeatBothFromLeft]
  · exact ⟨hright, hleft⟩

/-! ## Orientation-compatible exits from mixed states -/

/-- A strict-right round from a mixed-right state is independent of the old
overlap anchor: process one already carries the right projection and process
two reconstructs that same phase at receive. -/
theorem endToEndOperationalAdvance_right_real_mixedRight
    (anchor : Bool)
    (candidates : EndToEndBothCandidates A bundle.rational)
    (hreal : candidates.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post
              ((.mixedRight anchor candidates :
                EndToEndOperationalPostShape A bundle.rational).oneControl),
              oldOutput.1),
            (EndToEndOperationalTwoControl.post
              ((.mixedRight anchor candidates :
                EndToEndOperationalPostShape A bundle.rational).twoControl),
              oldOutput.2)) .right move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨fresh, hfresh, hright, hleft⟩ :=
    exists_real_endToEnd_candidates_enterBothFromRight A bundle.rational
      candidates.right hreal.1 candidates.right_oriented move
  have hcandidateRight :=
    endToEndEnterBothFromRight_candidate_right A bundle.rational
      candidates.right candidates.right_oriented move fresh hfresh
  have hno := endToEndPostNoRecvOne_of_rightPhase A bundle.rational
    candidates.right candidates.right_oriented move.1 move.2
  have hnoFull :
      endToEndOperationalNoRecvOne A bundle
          (.post (.inl candidates.right.oneControl)) move.1 =
        ((candidates.right.continue A bundle.rational move).1.1,
          .post (.inl
            (candidates.right.continue A bundle.rational move).2.oneControl)) := by
    simp [endToEndOperationalNoRecvOne,
      endToEndOperationalPostNoRecvOne, hno]
  have hrecv := endToEndOperationalPostRecv_of_mixedRight A bundle.rational
    anchor candidates fresh move hfresh
  have hrecvPair :
      endToEndOperationalRecvPair A bundle
          (.post (.inl candidates.right.oneControl))
          (.post (.inr (anchor,
            candidates.twoControl A bundle.rational))) move =
        ((.post (endToEndOperationalPostOfCandidates A bundle.rational false
              fresh).1,
            (candidates.right.enterBothFromRight A bundle.rational move).1.1),
          (.post (endToEndOperationalPostOfCandidates A bundle.rational false
              fresh).2,
            (candidates.right.enterBothFromRight A bundle.rational move).1.2)) := by
    simp only [endToEndOperationalRecvPair]
    rw [hrecv]
  let next : EndToEndOperationalPostShape A bundle.rational :=
    .mixedRight false fresh
  refine ⟨(candidates.right.continue A bundle.rational move).1,
    next, ?_, ?_⟩
  · simp only [LocalSummaryAutomaton.advance,
      endToEndOperationalSummaryAutomaton]
    simp only [EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl]
    rw [hnoFull]
    rw [hrecvPair]
    simp [next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl,
      endToEndOperationalPostOfCandidates, hcandidateRight]
  · exact ⟨hright, hleft⟩

/-- Strict-left mirror for a mixed-left state. -/
theorem endToEndOperationalAdvance_left_real_mixedLeft
    (anchor : Bool)
    (candidates : EndToEndBothCandidates A bundle.rational)
    (hreal : candidates.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post
              ((.mixedLeft anchor candidates :
                EndToEndOperationalPostShape A bundle.rational).oneControl),
              oldOutput.1),
            (EndToEndOperationalTwoControl.post
              ((.mixedLeft anchor candidates :
                EndToEndOperationalPostShape A bundle.rational).twoControl),
              oldOutput.2)) .left move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨fresh, hfresh, hright, hleft⟩ :=
    exists_real_endToEnd_candidates_enterBothFromLeft A bundle.rational
      candidates.left hreal.2 candidates.left_oriented move
  have hcandidateLeft :=
    endToEndEnterBothFromLeft_candidate_left A bundle.rational
      candidates.left candidates.left_oriented move fresh hfresh
  have hno := endToEndPostNoRecvTwo_of_leftPhase A bundle.rational
    candidates.left candidates.left_oriented move.1 move.2
  have hnoFull :
      endToEndOperationalNoRecvTwo A bundle
          (.post (.inl candidates.left.twoControl)) move.2 =
        ((candidates.left.continue A bundle.rational move).1.2,
          .post (.inl
            (candidates.left.continue A bundle.rational move).2.twoControl)) := by
    simp [endToEndOperationalNoRecvTwo,
      endToEndOperationalPostNoRecvTwo, hno]
  have hrecv := endToEndOperationalPostRecv_of_mixedLeft A bundle.rational
    anchor candidates fresh move hfresh
  have hrecvPair :
      endToEndOperationalRecvPair A bundle
          (.post (.inr (anchor,
            candidates.oneControl A bundle.rational)))
          (.post (.inl candidates.left.twoControl)) move =
        ((.post (endToEndOperationalPostOfCandidates A bundle.rational true
              fresh).1,
            (candidates.left.enterBothFromLeft A bundle.rational move).1.1),
          (.post (endToEndOperationalPostOfCandidates A bundle.rational true
              fresh).2,
            (candidates.left.enterBothFromLeft A bundle.rational move).1.2)) := by
    simp only [endToEndOperationalRecvPair]
    rw [hrecv]
  let next : EndToEndOperationalPostShape A bundle.rational :=
    .mixedLeft true fresh
  refine ⟨(candidates.left.continue A bundle.rational move).1,
    next, ?_, ?_⟩
  · simp only [LocalSummaryAutomaton.advance,
      endToEndOperationalSummaryAutomaton]
    simp only [EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl]
    rw [hrecvPair]
    rw [hnoFull]
    simp [next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl,
      endToEndOperationalPostOfCandidates, hcandidateLeft]
  · exact ⟨hright, hleft⟩

/-- Alternating away from a mixed-right state whose retained anchor is
already right uses the ordinary right-to-left pair test. -/
theorem endToEndOperationalAdvance_left_real_mixedRight_false
    (candidates : EndToEndBothCandidates A bundle.rational)
    (hreal : candidates.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post
              ((.mixedRight false candidates :
                EndToEndOperationalPostShape A bundle.rational).oneControl),
              oldOutput.1),
            (EndToEndOperationalTwoControl.post
              ((.mixedRight false candidates :
                EndToEndOperationalPostShape A bundle.rational).twoControl),
              oldOutput.2)) .left move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨fresh, hfresh, hright, hleft⟩ :=
    exists_real_endToEnd_candidates_enterBothFromRight A bundle.rational
      candidates.right hreal.1 candidates.right_oriented move
  have hcandidateLeft :=
    endToEndEnterBothFromRight_candidate_left A bundle.rational
      candidates.right move fresh hfresh
  have hno := endToEndPostNoRecvTwo_of_reverseRightToLeft A bundle.rational
    candidates.right fresh.left candidates.right_oriented move false
      hcandidateLeft
  have hnoFull :
      endToEndOperationalNoRecvTwo A bundle
          (.post (.inr (false,
            candidates.twoControl A bundle.rational))) move.2 =
        ((candidates.right.reverseRightToLeft A bundle.rational move
            false).1.2,
          .post (.inl fresh.left.twoControl)) := by
    simp [endToEndOperationalNoRecvTwo,
      endToEndOperationalPostNoRecvTwo,
      EndToEndBothCandidates.twoControl, hno]
  have hrecv := endToEndOperationalPostRecv_of_mixedRight A bundle.rational
    false candidates fresh move hfresh
  have hrecvPair :
      endToEndOperationalRecvPair A bundle
          (.post (.inl candidates.right.oneControl))
          (.post (.inr (false,
            candidates.twoControl A bundle.rational))) move =
        ((.post (endToEndOperationalPostOfCandidates A bundle.rational false
              fresh).1,
            (candidates.right.enterBothFromRight A bundle.rational move).1.1),
          (.post (endToEndOperationalPostOfCandidates A bundle.rational false
              fresh).2,
            (candidates.right.enterBothFromRight A bundle.rational move).1.2)) := by
    simp only [endToEndOperationalRecvPair]
    rw [hrecv]
  let next : EndToEndOperationalPostShape A bundle.rational :=
    .mixedLeft false fresh
  refine ⟨(candidates.right.reverseRightToLeft A bundle.rational move
      false).1, next, ?_, ?_⟩
  · simp only [LocalSummaryAutomaton.advance,
      endToEndOperationalSummaryAutomaton]
    simp only [EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl]
    rw [hrecvPair]
    rw [hnoFull]
    simp [next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl,
      endToEndOperationalPostOfCandidates]
  · exact ⟨hright, hleft⟩

/-- Process-swapped compatible alternating case. -/
theorem endToEndOperationalAdvance_right_real_mixedLeft_true
    (candidates : EndToEndBothCandidates A bundle.rational)
    (hreal : candidates.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post
              ((.mixedLeft true candidates :
                EndToEndOperationalPostShape A bundle.rational).oneControl),
              oldOutput.1),
            (EndToEndOperationalTwoControl.post
              ((.mixedLeft true candidates :
                EndToEndOperationalPostShape A bundle.rational).twoControl),
              oldOutput.2)) .right move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨fresh, hfresh, hright, hleft⟩ :=
    exists_real_endToEnd_candidates_enterBothFromLeft A bundle.rational
      candidates.left hreal.2 candidates.left_oriented move
  have hcandidateRight :=
    endToEndEnterBothFromLeft_candidate_right A bundle.rational
      candidates.left move fresh hfresh
  have hno := endToEndPostNoRecvOne_of_reverseLeftToRight A bundle.rational
    candidates.left fresh.right candidates.left_oriented move false
      hcandidateRight
  have hnoFull :
      endToEndOperationalNoRecvOne A bundle
          (.post (.inr (true,
            candidates.oneControl A bundle.rational))) move.1 =
        ((candidates.left.reverseLeftToRight A bundle.rational
            (move.2, move.1) false).1.1,
          .post (.inl fresh.right.oneControl)) := by
    simp [endToEndOperationalNoRecvOne,
      endToEndOperationalPostNoRecvOne,
      EndToEndBothCandidates.oneControl, hno]
  have hrecv := endToEndOperationalPostRecv_of_mixedLeft A bundle.rational
    true candidates fresh move hfresh
  have hrecvPair :
      endToEndOperationalRecvPair A bundle
          (.post (.inr (true,
            candidates.oneControl A bundle.rational)))
          (.post (.inl candidates.left.twoControl)) move =
        ((.post (endToEndOperationalPostOfCandidates A bundle.rational true
              fresh).1,
            (candidates.left.enterBothFromLeft A bundle.rational move).1.1),
          (.post (endToEndOperationalPostOfCandidates A bundle.rational true
              fresh).2,
            (candidates.left.enterBothFromLeft A bundle.rational move).1.2)) := by
    simp only [endToEndOperationalRecvPair]
    rw [hrecv]
  let next : EndToEndOperationalPostShape A bundle.rational :=
    .mixedRight true fresh
  refine ⟨(candidates.left.reverseLeftToRight A bundle.rational
      (move.2, move.1) false).1, next, ?_, ?_⟩
  · simp only [LocalSummaryAutomaton.advance,
      endToEndOperationalSummaryAutomaton]
    simp only [EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl]
    rw [hnoFull]
    rw [hrecvPair]
    simp [next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl,
      endToEndOperationalPostOfCandidates]
  · exact ⟨hright, hleft⟩

/-! ## Cross-anchor alternating exits -/

/-- The remaining right-to-left alternating case needs only the equality of
the nonreceiving process-two transition selected by the old left anchor with
the right anchor's genuine reversal transition.  The hypothesis is stated
at exactly the local phase-table projection consumed by `advance`; it asks
for neither equality of the latent phases nor an orientation signal in local
state. -/
theorem endToEndOperationalAdvance_left_real_mixedRight_true_of_crossAnchor
    (candidates : EndToEndBothCandidates A bundle.rational)
    (hreal : candidates.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂)
    (hcross :
      endToEndPostNoRecvTwo A bundle.rational candidates.left.twoControl
          move.2 =
        ((candidates.right.reverseRightToLeft A bundle.rational move
            false).1.2,
          (candidates.right.reverseRightToLeft A bundle.rational move
            false).2.map fun phase => phase.twoControl)) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post
              ((.mixedRight true candidates :
                EndToEndOperationalPostShape A bundle.rational).oneControl),
              oldOutput.1),
            (EndToEndOperationalTwoControl.post
              ((.mixedRight true candidates :
                EndToEndOperationalPostShape A bundle.rational).twoControl),
              oldOutput.2)) .left move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨fresh, hfresh, hright, hleft⟩ :=
    exists_real_endToEnd_candidates_enterBothFromRight A bundle.rational
      candidates.right hreal.1 candidates.right_oriented move
  have hcandidateLeft :=
    endToEndEnterBothFromRight_candidate_left A bundle.rational
      candidates.right move fresh hfresh
  have hno :
      endToEndPostNoRecvTwo A bundle.rational candidates.left.twoControl
          move.2 =
        ((candidates.right.reverseRightToLeft A bundle.rational move
            false).1.2,
          some fresh.left.twoControl) := by
    simpa [hcandidateLeft] using hcross
  have hnoFull :
      endToEndOperationalNoRecvTwo A bundle
          (.post (.inr (true,
            candidates.twoControl A bundle.rational))) move.2 =
        ((candidates.right.reverseRightToLeft A bundle.rational move
            false).1.2,
          .post (.inl fresh.left.twoControl)) := by
    simp [endToEndOperationalNoRecvTwo,
      endToEndOperationalPostNoRecvTwo,
      EndToEndBothCandidates.twoControl, hno]
  have hrecv := endToEndOperationalPostRecv_of_mixedRight A bundle.rational
    true candidates fresh move hfresh
  have hrecvPair :
      endToEndOperationalRecvPair A bundle
          (.post (.inl candidates.right.oneControl))
          (.post (.inr (true,
            candidates.twoControl A bundle.rational))) move =
        ((.post (endToEndOperationalPostOfCandidates A bundle.rational false
              fresh).1,
            (candidates.right.enterBothFromRight A bundle.rational move).1.1),
          (.post (endToEndOperationalPostOfCandidates A bundle.rational false
              fresh).2,
            (candidates.right.enterBothFromRight A bundle.rational move).1.2)) := by
    simp only [endToEndOperationalRecvPair]
    rw [hrecv]
  let next : EndToEndOperationalPostShape A bundle.rational :=
    .mixedLeft false fresh
  refine ⟨(candidates.right.reverseRightToLeft A bundle.rational move
      false).1, next, ?_, ?_⟩
  · simp only [LocalSummaryAutomaton.advance,
      endToEndOperationalSummaryAutomaton]
    simp only [EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl]
    rw [hrecvPair]
    rw [hnoFull]
    simp [next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl,
      endToEndOperationalPostOfCandidates]
  · exact ⟨hright, hleft⟩

/-- Process-swapped cross-anchor case.  Its sole extra premise is equality of
the process-one transition selected by the old right anchor with the genuine
left-to-right reversal projection. -/
theorem endToEndOperationalAdvance_right_real_mixedLeft_false_of_crossAnchor
    (candidates : EndToEndBothCandidates A bundle.rational)
    (hreal : candidates.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂)
    (hcross :
      endToEndPostNoRecvOne A bundle.rational candidates.right.oneControl
          move.1 =
        ((candidates.left.reverseLeftToRight A bundle.rational
            (move.2, move.1) false).1.1,
          (candidates.left.reverseLeftToRight A bundle.rational
            (move.2, move.1) false).2.map fun phase => phase.oneControl)) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      (endToEndOperationalSummaryAutomaton A bundle).advance
          ((EndToEndOperationalOneControl.post
              ((.mixedLeft false candidates :
                EndToEndOperationalPostShape A bundle.rational).oneControl),
              oldOutput.1),
            (EndToEndOperationalTwoControl.post
              ((.mixedLeft false candidates :
                EndToEndOperationalPostShape A bundle.rational).twoControl),
              oldOutput.2)) .right move.1 move.2 =
        ((EndToEndOperationalOneControl.post next.oneControl, output.1),
          (EndToEndOperationalTwoControl.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  obtain ⟨fresh, hfresh, hright, hleft⟩ :=
    exists_real_endToEnd_candidates_enterBothFromLeft A bundle.rational
      candidates.left hreal.2 candidates.left_oriented move
  have hcandidateRight :=
    endToEndEnterBothFromLeft_candidate_right A bundle.rational
      candidates.left move fresh hfresh
  have hno :
      endToEndPostNoRecvOne A bundle.rational candidates.right.oneControl
          move.1 =
        ((candidates.left.reverseLeftToRight A bundle.rational
            (move.2, move.1) false).1.1,
          some fresh.right.oneControl) := by
    simpa [hcandidateRight] using hcross
  have hnoFull :
      endToEndOperationalNoRecvOne A bundle
          (.post (.inr (false,
            candidates.oneControl A bundle.rational))) move.1 =
        ((candidates.left.reverseLeftToRight A bundle.rational
            (move.2, move.1) false).1.1,
          .post (.inl fresh.right.oneControl)) := by
    simp [endToEndOperationalNoRecvOne,
      endToEndOperationalPostNoRecvOne,
      EndToEndBothCandidates.oneControl, hno]
  have hrecv := endToEndOperationalPostRecv_of_mixedLeft A bundle.rational
    false candidates fresh move hfresh
  have hrecvPair :
      endToEndOperationalRecvPair A bundle
          (.post (.inr (false,
            candidates.oneControl A bundle.rational)))
          (.post (.inl candidates.left.twoControl)) move =
        ((.post (endToEndOperationalPostOfCandidates A bundle.rational true
              fresh).1,
            (candidates.left.enterBothFromLeft A bundle.rational move).1.1),
          (.post (endToEndOperationalPostOfCandidates A bundle.rational true
              fresh).2,
            (candidates.left.enterBothFromLeft A bundle.rational move).1.2)) := by
    simp only [endToEndOperationalRecvPair]
    rw [hrecv]
  let next : EndToEndOperationalPostShape A bundle.rational :=
    .mixedRight true fresh
  refine ⟨(candidates.left.reverseLeftToRight A bundle.rational
      (move.2, move.1) false).1, next, ?_, ?_⟩
  · simp only [LocalSummaryAutomaton.advance,
      endToEndOperationalSummaryAutomaton]
    simp only [EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl]
    rw [hnoFull]
    rw [hrecvPair]
    simp [next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl,
      endToEndOperationalPostOfCandidates]
  · exact ⟨hright, hleft⟩

end

end DetParityAutomaton

end DistributedSynthesis
