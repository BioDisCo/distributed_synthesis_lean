/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRootFamilyLocalOverlay
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalPostRoundClosure

/-!
# Adapting simultaneous family overlays to the alternating seam

The root-family overlay already proves the mathematical fact needed at the
two cross-anchor seams: two hidden member projections have the same blind
output and successor control.  This file is deliberately only an adapter.
It assumes explicit identifications of the two end-to-end phase transitions
with those two member steps, transports the overlay equality through their
common local-control projection, and feeds the resulting equality to the
conditional post-round closure theorems.
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

/-! ## A compact member-step interface -/

/-- The common finite control type of all projections of one right-family
overlay. -/
abbrev ProfiledRightFamilyPairOverlay.MemberControl
    (state : ProfiledRightFamilyPairOverlay A) :=
  (finiteRootMemberController
    (profiledRightFamilyRootMonitors A state.1.1)
    state.1.2.toTransitionRationalTree false).Control

/-- The corresponding common control type for a left-family overlay. -/
abbrev ProfiledLeftFamilyPairOverlay.MemberControl
    (state : ProfiledLeftFamilyPairOverlay A) :=
  (finiteRootMemberController
    (profiledLeftFamilyRootMonitors A state.1.1)
    state.1.2.toTransitionRationalTree false).Control

/-- Output and successor control of one hidden right-family member. -/
def ProfiledRightFamilyPairOverlay.memberStep
    (state : ProfiledRightFamilyPairOverlay A) (member : Bool)
    (input : In₁) : Out₁ × state.MemberControl A :=
  let monitors := profiledRightFamilyRootMonitors A state.1.1
  let family := state.1.2.toTransitionRationalTree
  let shared := state.2
  (((finiteRootMemberController monitors family member).labelOf
      (shared.memberControl monitors family member)).1 input,
    (finiteRootMemberController monitors family member).step
      (shared.memberControl monitors family member) input)

/-- Process-two mirror. -/
def ProfiledLeftFamilyPairOverlay.memberStep
    (state : ProfiledLeftFamilyPairOverlay A) (member : Bool)
    (input : In₂) : Out₂ × state.MemberControl A :=
  let monitors := profiledLeftFamilyRootMonitors A state.1.1
  let family := state.1.2.toTransitionRationalTree
  let shared := state.2
  (((finiteRootMemberController monitors family member).labelOf
      (shared.memberControl monitors family member)).1 input,
    (finiteRootMemberController monitors family member).step
      (shared.memberControl monitors family member) input)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Equality of member steps, packaged without the internal monitor and
family-table names. -/
theorem ProfiledRightFamilyPairOverlay.memberStep_eq
    (state : ProfiledRightFamilyPairOverlay A) (left right : Bool)
    (input : In₁) :
    state.memberStep A left input = state.memberStep A right input := by
  exact state.localStep_eq A left right input

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-family mirror. -/
theorem ProfiledLeftFamilyPairOverlay.memberStep_eq
    (state : ProfiledLeftFamilyPairOverlay A) (left right : Bool)
    (input : In₂) :
    state.memberStep A left input = state.memberStep A right input := by
  exact state.localStep_eq A left right input

/-! ## Exact adapters to the two cross-anchor premises -/

variable (bundle : EndToEndOperationalControllerPackage A)

/-- A left-family overlay supplies the process-two cross-anchor equality as
soon as the current and target phase-table transitions are identified with
two of its member steps through one common control projection. -/
theorem endToEndCrossAnchorTwo_of_leftFamilyOverlay
    (candidates : EndToEndBothCandidates A bundle.rational)
    (move : In₁ × In₂)
    (overlay : ProfiledLeftFamilyPairOverlay A)
    (currentMember targetMember : Bool)
    (project : overlay.MemberControl A →
      Option (EndToEndPhaseTwoControl A bundle.rational))
    (hcurrent :
      endToEndPostNoRecvTwo A bundle.rational candidates.left.twoControl
          move.2 =
        let step := overlay.memberStep A currentMember move.2
        (step.1, project step.2))
    (htarget :
      ((candidates.right.reverseRightToLeft A bundle.rational move
          false).1.2,
        (candidates.right.reverseRightToLeft A bundle.rational move
          false).2.map fun phase => phase.twoControl) =
        let step := overlay.memberStep A targetMember move.2
        (step.1, project step.2)) :
    endToEndPostNoRecvTwo A bundle.rational candidates.left.twoControl
          move.2 =
      ((candidates.right.reverseRightToLeft A bundle.rational move
          false).1.2,
        (candidates.right.reverseRightToLeft A bundle.rational move
          false).2.map fun phase => phase.twoControl) := by
  have hmembers := overlay.memberStep_eq A currentMember targetMember move.2
  have hprojected := congrArg (fun step => (step.1, project step.2)) hmembers
  exact hcurrent.trans (hprojected.trans htarget.symm)

/-- A right-family overlay supplies the process-one mirror. -/
theorem endToEndCrossAnchorOne_of_rightFamilyOverlay
    (candidates : EndToEndBothCandidates A bundle.rational)
    (move : In₁ × In₂)
    (overlay : ProfiledRightFamilyPairOverlay A)
    (currentMember targetMember : Bool)
    (project : overlay.MemberControl A →
      Option (EndToEndPhaseOneControl A bundle.rational))
    (hcurrent :
      endToEndPostNoRecvOne A bundle.rational candidates.right.oneControl
          move.1 =
        let step := overlay.memberStep A currentMember move.1
        (step.1, project step.2))
    (htarget :
      ((candidates.left.reverseLeftToRight A bundle.rational
          (move.2, move.1) false).1.1,
        (candidates.left.reverseLeftToRight A bundle.rational
          (move.2, move.1) false).2.map fun phase => phase.oneControl) =
        let step := overlay.memberStep A targetMember move.1
        (step.1, project step.2)) :
    endToEndPostNoRecvOne A bundle.rational candidates.right.oneControl
          move.1 =
      ((candidates.left.reverseLeftToRight A bundle.rational
          (move.2, move.1) false).1.1,
        (candidates.left.reverseLeftToRight A bundle.rational
          (move.2, move.1) false).2.map fun phase => phase.oneControl) := by
  have hmembers := overlay.memberStep_eq A currentMember targetMember move.1
  have hprojected := congrArg (fun step => (step.1, project step.2)) hmembers
  exact hcurrent.trans (hprojected.trans htarget.symm)

/-! ## Direct post-round closure corollaries -/

/-- Close the right-to-left dangerous seam directly from a simultaneous
left-family overlay and the two definitional transition identifications. -/
theorem endToEndOperationalAdvance_left_real_mixedRight_true_of_leftFamilyOverlay
    (candidates : EndToEndBothCandidates A bundle.rational)
    (hreal : candidates.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂)
    (overlay : ProfiledLeftFamilyPairOverlay A)
    (currentMember targetMember : Bool)
    (project : overlay.MemberControl A →
      Option (EndToEndPhaseTwoControl A bundle.rational))
    (hcurrent :
      endToEndPostNoRecvTwo A bundle.rational candidates.left.twoControl
          move.2 =
        let step := overlay.memberStep A currentMember move.2
        (step.1, project step.2))
    (htarget :
      ((candidates.right.reverseRightToLeft A bundle.rational move
          false).1.2,
        (candidates.right.reverseRightToLeft A bundle.rational move
          false).2.map fun phase => phase.twoControl) =
        let step := overlay.memberStep A targetMember move.2
        (step.1, project step.2)) :
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
  apply endToEndOperationalAdvance_left_real_mixedRight_true_of_crossAnchor
    A bundle candidates hreal oldOutput move
  exact endToEndCrossAnchorTwo_of_leftFamilyOverlay A bundle candidates move
    overlay currentMember targetMember project hcurrent htarget

/-- Process-one mirror. -/
theorem endToEndOperationalAdvance_right_real_mixedLeft_false_of_rightFamilyOverlay
    (candidates : EndToEndBothCandidates A bundle.rational)
    (hreal : candidates.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂)
    (overlay : ProfiledRightFamilyPairOverlay A)
    (currentMember targetMember : Bool)
    (project : overlay.MemberControl A →
      Option (EndToEndPhaseOneControl A bundle.rational))
    (hcurrent :
      endToEndPostNoRecvOne A bundle.rational candidates.right.oneControl
          move.1 =
        let step := overlay.memberStep A currentMember move.1
        (step.1, project step.2))
    (htarget :
      ((candidates.left.reverseLeftToRight A bundle.rational
          (move.2, move.1) false).1.1,
        (candidates.left.reverseLeftToRight A bundle.rational
          (move.2, move.1) false).2.map fun phase => phase.oneControl) =
        let step := overlay.memberStep A targetMember move.1
        (step.1, project step.2)) :
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
  apply endToEndOperationalAdvance_right_real_mixedLeft_false_of_crossAnchor
    A bundle candidates hreal oldOutput move
  exact endToEndCrossAnchorOne_of_rightFamilyOverlay A bundle candidates move
    overlay currentMember targetMember project hcurrent htarget

end

end DetParityAutomaton

end DistributedSynthesis
