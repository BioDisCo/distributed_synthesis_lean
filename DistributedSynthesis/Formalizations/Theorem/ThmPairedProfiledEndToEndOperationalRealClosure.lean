/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalRealInvariant

/-!
# Real closure of the end-to-end operational pair

The proof-only reality invariant is lifted to the two-shadow carrier used on
ambiguous communication rounds.  Hence every synchronized receive from a
reachable post-initial shape has a genuine successor and the executable
totalization fallback is unreachable.

No orientation is added to either local state: it occurs only in witnesses
that relate the two independently updated finite summaries.
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

variable (package : PairedInitialProfiledRationalPackage A)

/-! ## Exact identities of the two refreshed shadows -/

/-- The left shadow installed by a right-origin ambiguous receive is exactly
the strict right-to-left successor computed on that round. -/
theorem endToEndEnterBothFromRight_candidate_left
    (phase : EndToEndMatchedPhase A package) (move : In₁ × In₂)
    (candidates : EndToEndBothCandidates A package)
    (hnext : (phase.enterBothFromRight A package move).2 =
      some candidates) :
    (phase.reverseRightToLeft A package move false).2 =
      some candidates.left := by
  unfold EndToEndMatchedPhase.enterBothFromRight at hnext
  dsimp only at hnext
  generalize hleft :
      (phase.reverseRightToLeft A package move false).2 = left at hnext
  cases left with
  | none => simp [hleft] at hnext
  | some left =>
      by_cases hright : (phase.continue A package move).2.IsRight
      · by_cases horiented : left.IsLeft
        · simp [hleft, hright, horiented] at hnext
          cases hnext
          rfl
        · simp [hleft, hright, horiented] at hnext
      · simp [hleft, hright] at hnext

/-- Right-shadow mirror for a left-origin ambiguous receive. -/
theorem endToEndEnterBothFromLeft_candidate_right
    (phase : EndToEndMatchedPhase A package) (move : In₁ × In₂)
    (candidates : EndToEndBothCandidates A package)
    (hnext : (phase.enterBothFromLeft A package move).2 =
      some candidates) :
    (phase.reverseLeftToRight A package (move.2, move.1) false).2 =
      some candidates.right := by
  unfold EndToEndMatchedPhase.enterBothFromLeft at hnext
  dsimp only at hnext
  generalize hright :
      (phase.reverseLeftToRight A package (move.2, move.1) false).2 = right
        at hnext
  cases right with
  | none => simp [hright] at hnext
  | some right =>
      by_cases horiented : right.IsRight
      · by_cases hleft : (phase.continue A package move).2.IsLeft
        · simp [hright, horiented, hleft] at hnext
          cases hnext
          rfl
        · simp [hright, horiented, hleft] at hnext
      · simp [hright, horiented] at hnext

/-- Entering an ambiguous round from a real right phase produces two real
shadows. -/
theorem exists_real_endToEnd_candidates_enterBothFromRight
    (phase : EndToEndMatchedPhase A package)
    (hreal : IsRealEndToEndPhase A package phase)
    (hright : phase.IsRight) (move : In₁ × In₂) :
    ∃ candidates,
      (phase.enterBothFromRight A package move).2 = some candidates ∧
      IsRealEndToEndPhase A package candidates.right ∧
      IsRealEndToEndPhase A package candidates.left := by
  obtain ⟨left, hleft, hrealLeft⟩ :=
    isRealEndToEndPhase_reverseRightToLeft A package phase hreal hright move
      false
  have horientLeft : left.IsLeft :=
    endToEndReverseRightToLeft_isLeft_of_eq_some A package phase left move
      false hleft
  have horientRight : (phase.continue A package move).2.IsRight :=
    phase.continue_isRight A package move hright
  let candidates : EndToEndBothCandidates A package :=
    ⟨(phase.continue A package move).2, left, horientRight, horientLeft⟩
  refine ⟨candidates, ?_,
    isRealEndToEndPhase_continue A package phase hreal move, hrealLeft⟩
  simp [EndToEndMatchedPhase.enterBothFromRight, hleft, horientRight,
    horientLeft, candidates]

/-- Left-oriented mirror. -/
theorem exists_real_endToEnd_candidates_enterBothFromLeft
    (phase : EndToEndMatchedPhase A package)
    (hreal : IsRealEndToEndPhase A package phase)
    (hleft : phase.IsLeft) (move : In₁ × In₂) :
    ∃ candidates,
      (phase.enterBothFromLeft A package move).2 = some candidates ∧
      IsRealEndToEndPhase A package candidates.right ∧
      IsRealEndToEndPhase A package candidates.left := by
  obtain ⟨right, hright, hrealRight⟩ :=
    isRealEndToEndPhase_reverseLeftToRight A package phase hreal hleft move
      false
  have horientRight : right.IsRight :=
    endToEndReverseLeftToRight_isRight_of_eq_some A package phase right move
      false hright
  have horientLeft : (phase.continue A package move).2.IsLeft :=
    phase.continue_isLeft A package move hleft
  let candidates : EndToEndBothCandidates A package :=
    ⟨right, (phase.continue A package move).2, horientRight, horientLeft⟩
  refine ⟨candidates, ?_, hrealRight,
    isRealEndToEndPhase_continue A package phase hreal move⟩
  simp [EndToEndMatchedPhase.enterBothFromLeft, hright, horientRight,
    horientLeft, candidates]

/-- A consecutive synchronized round refreshes both real shadows from the
retained anchor. -/
theorem exists_real_endToEnd_candidates_repeatBoth
    (anchor : Bool) (candidates : EndToEndBothCandidates A package)
    (hrealRight : IsRealEndToEndPhase A package candidates.right)
    (hrealLeft : IsRealEndToEndPhase A package candidates.left)
    (move : In₁ × In₂) :
    ∃ next,
      (if anchor then candidates.repeatBothFromLeft A package move
        else candidates.repeatBothFromRight A package move).2 = some next ∧
      IsRealEndToEndPhase A package next.right ∧
      IsRealEndToEndPhase A package next.left := by
  cases anchor with
  | false =>
      simpa [EndToEndBothCandidates.repeatBothFromRight] using
        exists_real_endToEnd_candidates_enterBothFromRight A package
          candidates.right hrealRight candidates.right_oriented move
  | true =>
      simpa [EndToEndBothCandidates.repeatBothFromLeft] using
        exists_real_endToEnd_candidates_enterBothFromLeft A package
          candidates.left hrealLeft candidates.left_oriented move

/-- Both shadows of an overlap are real controller prefixes. -/
def EndToEndBothCandidates.Real
    (candidates : EndToEndBothCandidates A package) : Prop :=
  IsRealEndToEndPhase A package candidates.right ∧
    IsRealEndToEndPhase A package candidates.left

/-- Semantic reachability predicate for the five post-initial joint shapes. -/
def EndToEndOperationalPostShape.Real :
    EndToEndOperationalPostShape A package → Prop
  | .resolvedRight phase _ => IsRealEndToEndPhase A package phase
  | .resolvedLeft phase _ => IsRealEndToEndPhase A package phase
  | .mixedRight _ candidates => candidates.Real A package
  | .mixedLeft _ candidates => candidates.Real A package
  | .overlap _ candidates => candidates.Real A package

/-- A real joint shape satisfies the successful-staging premise of every
synchronized receive. -/
theorem EndToEndOperationalPostShape.receiveReady_of_real
    (shape : EndToEndOperationalPostShape A package)
    (hreal : shape.Real A package) (move : In₁ × In₂) :
    shape.ReceiveReady A package move := by
  cases shape with
  | resolvedRight phase oriented =>
      obtain ⟨next, hnext, _⟩ :=
        exists_real_endToEnd_candidates_enterBothFromRight A package phase
          hreal oriented move
      simp [EndToEndOperationalPostShape.ReceiveReady, hnext]
  | resolvedLeft phase oriented =>
      obtain ⟨next, hnext, _⟩ :=
        exists_real_endToEnd_candidates_enterBothFromLeft A package phase
          hreal oriented move
      simp [EndToEndOperationalPostShape.ReceiveReady, hnext]
  | mixedRight anchor candidates =>
      obtain ⟨next, hnext, _⟩ :=
        exists_real_endToEnd_candidates_enterBothFromRight A package
          candidates.right hreal.1 candidates.right_oriented move
      simp [EndToEndOperationalPostShape.ReceiveReady, hnext]
  | mixedLeft anchor candidates =>
      obtain ⟨next, hnext, _⟩ :=
        exists_real_endToEnd_candidates_enterBothFromLeft A package
          candidates.left hreal.2 candidates.left_oriented move
      simp [EndToEndOperationalPostShape.ReceiveReady, hnext]
  | overlap anchor candidates =>
      obtain ⟨next, hnext, _⟩ :=
        exists_real_endToEnd_candidates_repeatBoth A package anchor candidates
          hreal.1 hreal.2 move
      simp [EndToEndOperationalPostShape.ReceiveReady, hnext]

/-- Every synchronized receive from a real joint shape returns another real
overlap.  Thus the totalized executable receive table never falls back on a
reachable post-initial run. -/
theorem endToEndOperationalPostRecv_realShape
    (shape : EndToEndOperationalPostShape A package)
    (hreal : shape.Real A package) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A package),
      endToEndOperationalPostRecv A package shape.oneControl
          shape.twoControl move =
        (output, some (next.oneControl, next.twoControl)) ∧
      next.Real A package := by
  cases shape with
  | resolvedRight phase oriented =>
      obtain ⟨candidates, hcandidates, hright, hleft⟩ :=
        exists_real_endToEnd_candidates_enterBothFromRight A package phase
          hreal oriented move
      refine ⟨(phase.enterBothFromRight A package move).1,
        .overlap false candidates, ?_, ?_⟩
      · simpa [EndToEndOperationalPostShape.oneControl,
          EndToEndOperationalPostShape.twoControl,
          endToEndOperationalPostOfCandidates] using
          (endToEndOperationalPostRecv_of_resolvedRight A package phase
            oriented move candidates hcandidates)
      · exact ⟨hright, hleft⟩
  | resolvedLeft phase oriented =>
      obtain ⟨candidates, hcandidates, hright, hleft⟩ :=
        exists_real_endToEnd_candidates_enterBothFromLeft A package phase
          hreal oriented move
      refine ⟨(phase.enterBothFromLeft A package move).1,
        .overlap true candidates, ?_, ?_⟩
      · simpa [EndToEndOperationalPostShape.oneControl,
          EndToEndOperationalPostShape.twoControl,
          endToEndOperationalPostOfCandidates] using
          (endToEndOperationalPostRecv_of_resolvedLeft A package phase
            oriented move candidates hcandidates)
      · exact ⟨hright, hleft⟩
  | mixedRight anchor candidates =>
      obtain ⟨fresh, hfresh, hright, hleft⟩ :=
        exists_real_endToEnd_candidates_enterBothFromRight A package
          candidates.right hreal.1 candidates.right_oriented move
      refine ⟨(candidates.right.enterBothFromRight A package move).1,
        .overlap false fresh, ?_, ?_⟩
      · simpa [EndToEndOperationalPostShape.oneControl,
          EndToEndOperationalPostShape.twoControl,
          endToEndOperationalPostOfCandidates] using
          (endToEndOperationalPostRecv_of_mixedRight A package anchor
            candidates fresh move hfresh)
      · exact ⟨hright, hleft⟩
  | mixedLeft anchor candidates =>
      obtain ⟨fresh, hfresh, hright, hleft⟩ :=
        exists_real_endToEnd_candidates_enterBothFromLeft A package
          candidates.left hreal.2 candidates.left_oriented move
      refine ⟨(candidates.left.enterBothFromLeft A package move).1,
        .overlap true fresh, ?_, ?_⟩
      · simpa [EndToEndOperationalPostShape.oneControl,
          EndToEndOperationalPostShape.twoControl,
          endToEndOperationalPostOfCandidates] using
          (endToEndOperationalPostRecv_of_mixedLeft A package anchor
            candidates fresh move hfresh)
      · exact ⟨hright, hleft⟩
  | overlap anchor candidates =>
      obtain ⟨fresh, hfresh, hright, hleft⟩ :=
        exists_real_endToEnd_candidates_repeatBoth A package anchor candidates
          hreal.1 hreal.2 move
      refine ⟨(if anchor then
          candidates.repeatBothFromLeft A package move
        else candidates.repeatBothFromRight A package move).1,
        .overlap anchor fresh, ?_, ?_⟩
      · cases anchor <;>
          simpa [EndToEndOperationalPostShape.oneControl,
            EndToEndOperationalPostShape.twoControl,
            endToEndOperationalPostRecv,
            endToEndOperationalPostOfCandidates] using
            (endToEndOperationalPostRecvOverlap_of_candidates A package _
              candidates fresh move hfresh)
      · exact ⟨hright, hleft⟩

end

end DetParityAutomaton

end DistributedSynthesis
