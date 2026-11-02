/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndPhaseCarrier

/-!
# The two-shadow invariant for ambiguous synchronizations

On a `both` round no process is told which strict orientation follows.  The
finite implementation therefore keeps two shadows: a right-oriented matched
phase and a left-oriented matched phase.  Process one retains the two process-
one projections and process two retains the two process-two projections.
The proof-only orientation witnesses are not part of either local carrier.
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

/-- Proof-only right-orientation predicate. -/
def EndToEndMatchedPhase.IsRight : EndToEndMatchedPhase A package → Prop
  | .firstRight .. => True
  | .rightOriginRight .. => True
  | .leftOriginRight .. => True
  | .firstLeft .. => False
  | .rightOriginLeft .. => False
  | .leftOriginLeft .. => False

/-- Proof-only left-orientation predicate. -/
def EndToEndMatchedPhase.IsLeft : EndToEndMatchedPhase A package → Prop
  | .firstRight .. => False
  | .rightOriginRight .. => False
  | .leftOriginRight .. => False
  | .firstLeft .. => True
  | .rightOriginLeft .. => True
  | .leftOriginLeft .. => True

theorem EndToEndMatchedPhase.continue_isRight
    (phase : EndToEndMatchedPhase A package) (move : In₁ × In₂)
    (h : phase.IsRight) :
    (phase.continue A package move).2.IsRight := by
  cases phase <;> simp_all [EndToEndMatchedPhase.IsRight,
    EndToEndMatchedPhase.continue]

theorem EndToEndMatchedPhase.continue_isLeft
    (phase : EndToEndMatchedPhase A package) (move : In₁ × In₂)
    (h : phase.IsLeft) :
    (phase.continue A package move).2.IsLeft := by
  cases phase <;> simp_all [EndToEndMatchedPhase.IsLeft,
    EndToEndMatchedPhase.continue]

/-- The proof-level two-shadow invariant. -/
structure EndToEndBothCandidates where
  right : EndToEndMatchedPhase A package
  left : EndToEndMatchedPhase A package
  right_oriented : right.IsRight
  left_oriented : left.IsLeft

/-- The pair of finite shadows stored by process one. -/
def EndToEndBothCandidates.oneControl
    (candidates : EndToEndBothCandidates A package) :
    EndToEndPhaseOneControl A package × EndToEndPhaseOneControl A package :=
  (candidates.right.oneControl, candidates.left.oneControl)

/-- The pair of finite shadows stored by process two. -/
def EndToEndBothCandidates.twoControl
    (candidates : EndToEndBothCandidates A package) :
    EndToEndPhaseTwoControl A package × EndToEndPhaseTwoControl A package :=
  (candidates.right.twoControl, candidates.left.twoControl)

/-- Assemble the physical output locally: process one's left-shadow output
and process two's right-shadow output. -/
def endToEndBothPhysicalOutput
    (rightOutput leftOutput : Out₁ × Out₂) : Out₁ × Out₂ :=
  (leftOutput.1, rightOutput.2)

/-- Advance both hypothetical strict continuations on one ambiguous round. -/
noncomputable def EndToEndBothCandidates.advanceShadows
    (candidates : EndToEndBothCandidates A package) (move : In₁ × In₂) :
    (Out₁ × Out₂) × EndToEndBothCandidates A package :=
  let rightStep := candidates.right.continue A package move
  let leftStep := candidates.left.continue A package move
  (endToEndBothPhysicalOutput rightStep.1 leftStep.1,
    ⟨rightStep.2, leftStep.2,
      candidates.right.continue_isRight A package move
        candidates.right_oriented,
      candidates.left.continue_isLeft A package move
        candidates.left_oriented⟩)

@[simp] theorem EndToEndBothCandidates.advanceShadows_output_one
    (candidates : EndToEndBothCandidates A package) (move : In₁ × In₂) :
    (candidates.advanceShadows A package move).1.1 =
      (candidates.left.continue A package move).1.1 := rfl

@[simp] theorem EndToEndBothCandidates.advanceShadows_output_two
    (candidates : EndToEndBothCandidates A package) (move : In₁ × In₂) :
    (candidates.advanceShadows A package move).1.2 =
      (candidates.right.continue A package move).1.2 := rfl

/-- A following strict-right round selects the right shadow. -/
noncomputable def EndToEndBothCandidates.resolveRight
    (candidates : EndToEndBothCandidates A package) (move : In₁ × In₂) :
    (Out₁ × Out₂) × EndToEndMatchedPhase A package :=
  candidates.right.continue A package move

/-- A following strict-left round selects the left shadow. -/
noncomputable def EndToEndBothCandidates.resolveLeft
    (candidates : EndToEndBothCandidates A package) (move : In₁ × In₂) :
    (Out₁ × Out₂) × EndToEndMatchedPhase A package :=
  candidates.left.continue A package move

theorem EndToEndBothCandidates.resolveRight_oriented
    (candidates : EndToEndBothCandidates A package) (move : In₁ × In₂) :
    (candidates.resolveRight A package move).2.IsRight :=
  candidates.right.continue_isRight A package move candidates.right_oriented

theorem EndToEndBothCandidates.resolveLeft_oriented
    (candidates : EndToEndBothCandidates A package) (move : In₁ × In₂) :
    (candidates.resolveLeft A package move).2.IsLeft :=
  candidates.left.continue_isLeft A package move candidates.left_oriented

/-! ## Entering and repeating an ambiguous interval -/

noncomputable def EndToEndMatchedPhase.enterBothFromRight
    (phase : EndToEndMatchedPhase A package) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option (EndToEndBothCandidates A package) := by
  classical
  exact
    let rightStep := phase.continue A package move
    let leftStep := phase.reverseRightToLeft A package move false
    let candidates := leftStep.2.bind fun left =>
      if hright : rightStep.2.IsRight then
        if hleft : left.IsLeft then
          some ⟨rightStep.2, left, hright, hleft⟩
        else none
      else none
    (endToEndBothPhysicalOutput rightStep.1 leftStep.1, candidates)

noncomputable def EndToEndMatchedPhase.enterBothFromLeft
    (phase : EndToEndMatchedPhase A package) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option (EndToEndBothCandidates A package) := by
  classical
  exact
    let leftStep := phase.continue A package move
    let rightStep := phase.reverseLeftToRight A package (move.2, move.1) false
    let candidates := rightStep.2.bind fun right =>
      if hright : right.IsRight then
        if hleft : leftStep.2.IsLeft then
          some ⟨right, leftStep.2, hright, hleft⟩
        else none
      else none
    (endToEndBothPhysicalOutput rightStep.1 leftStep.1, candidates)

noncomputable def EndToEndBothCandidates.repeatBothFromRight
    (candidates : EndToEndBothCandidates A package) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option (EndToEndBothCandidates A package) :=
  candidates.right.enterBothFromRight A package move

noncomputable def EndToEndBothCandidates.repeatBothFromLeft
    (candidates : EndToEndBothCandidates A package) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option (EndToEndBothCandidates A package) :=
  candidates.left.enterBothFromLeft A package move

@[simp] theorem EndToEndMatchedPhase.enterBothFromRight_output_one
    (phase : EndToEndMatchedPhase A package) (move : In₁ × In₂) :
    (phase.enterBothFromRight A package move).1.1 =
      (phase.reverseRightToLeft A package move false).1.1 := rfl

@[simp] theorem EndToEndMatchedPhase.enterBothFromRight_output_two
    (phase : EndToEndMatchedPhase A package) (move : In₁ × In₂) :
    (phase.enterBothFromRight A package move).1.2 =
      (phase.continue A package move).1.2 := rfl

@[simp] theorem EndToEndMatchedPhase.enterBothFromLeft_output_one
    (phase : EndToEndMatchedPhase A package) (move : In₁ × In₂) :
    (phase.enterBothFromLeft A package move).1.1 =
      (phase.continue A package move).1.1 := rfl

@[simp] theorem EndToEndMatchedPhase.enterBothFromLeft_output_two
    (phase : EndToEndMatchedPhase A package) (move : In₁ × In₂) :
    (phase.enterBothFromLeft A package move).1.2 =
      (phase.reverseLeftToRight A package (move.2, move.1) false).1.2 := rfl

end


end DetParityAutomaton

end DistributedSynthesis
