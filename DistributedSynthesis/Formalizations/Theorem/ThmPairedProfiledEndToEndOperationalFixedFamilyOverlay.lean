/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRootFamilyOverlay
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalPostRoundClosure

/-!
# Fixed-policy overlay adapters for the two alternating exits

This is the end-to-end replacement for the earlier generic profiled-family
adapter.  Its overlays are indexed by exact restart roots below the one common
package policy, so installing one cannot silently select another recurrent
policy.  The two premises at each seam are only representation equations:
they identify the operational projection with the corresponding member of the
shared table.  All mathematical equality is supplied by `memberStep_eq`.
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

/-- A fixed-policy left overlay supplies the exact process-two cross-anchor
premise after projecting its shared control into the operational carrier. -/
theorem endToEndCrossAnchorTwo_of_fixedLeftFamilyOverlay
    (candidates : EndToEndBothCandidates A bundle.rational)
    (move : In₁ × In₂)
    (overlay : EndToEndLeftFamilyPairOverlay A bundle.rational)
    (currentMember targetMember : Bool)
    (project : overlay.MemberControl A bundle.rational →
      Option (EndToEndPhaseTwoControl A bundle.rational))
    (hcurrent :
      endToEndPostNoRecvTwo A bundle.rational candidates.left.twoControl
          move.2 =
        let step := overlay.memberStep A bundle.rational currentMember move.2
        (step.1, project step.2))
    (htarget :
      ((candidates.right.reverseRightToLeft A bundle.rational move
          false).1.2,
        (candidates.right.reverseRightToLeft A bundle.rational move
          false).2.map fun phase => phase.twoControl) =
        let step := overlay.memberStep A bundle.rational targetMember move.2
        (step.1, project step.2)) :
    endToEndPostNoRecvTwo A bundle.rational candidates.left.twoControl
          move.2 =
      ((candidates.right.reverseRightToLeft A bundle.rational move
          false).1.2,
        (candidates.right.reverseRightToLeft A bundle.rational move
          false).2.map fun phase => phase.twoControl) := by
  have hmembers := overlay.memberStep_eq A bundle.rational currentMember
    targetMember move.2
  have hprojected := congrArg (fun step => (step.1, project step.2)) hmembers
  exact hcurrent.trans (hprojected.trans htarget.symm)

/-- Fixed-policy process-one mirror. -/
theorem endToEndCrossAnchorOne_of_fixedRightFamilyOverlay
    (candidates : EndToEndBothCandidates A bundle.rational)
    (move : In₁ × In₂)
    (overlay : EndToEndRightFamilyPairOverlay A bundle.rational)
    (currentMember targetMember : Bool)
    (project : overlay.MemberControl A bundle.rational →
      Option (EndToEndPhaseOneControl A bundle.rational))
    (hcurrent :
      endToEndPostNoRecvOne A bundle.rational candidates.right.oneControl
          move.1 =
        let step := overlay.memberStep A bundle.rational currentMember move.1
        (step.1, project step.2))
    (htarget :
      ((candidates.left.reverseLeftToRight A bundle.rational
          (move.2, move.1) false).1.1,
        (candidates.left.reverseLeftToRight A bundle.rational
          (move.2, move.1) false).2.map fun phase => phase.oneControl) =
        let step := overlay.memberStep A bundle.rational targetMember move.1
        (step.1, project step.2)) :
    endToEndPostNoRecvOne A bundle.rational candidates.right.oneControl
          move.1 =
      ((candidates.left.reverseLeftToRight A bundle.rational
          (move.2, move.1) false).1.1,
        (candidates.left.reverseLeftToRight A bundle.rational
          (move.2, move.1) false).2.map fun phase => phase.oneControl) := by
  have hmembers := overlay.memberStep_eq A bundle.rational currentMember
    targetMember move.1
  have hprojected := congrArg (fun step => (step.1, project step.2)) hmembers
  exact hcurrent.trans (hprojected.trans htarget.symm)

/-- Close `.mixedRight true → .left` from the installed fixed-policy left
family table. -/
theorem endToEndOperationalAdvance_left_real_mixedRight_true_of_fixedFamily
    (candidates : EndToEndBothCandidates A bundle.rational)
    (hreal : candidates.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂)
    (overlay : EndToEndLeftFamilyPairOverlay A bundle.rational)
    (currentMember targetMember : Bool)
    (project : overlay.MemberControl A bundle.rational →
      Option (EndToEndPhaseTwoControl A bundle.rational))
    (hcurrent :
      endToEndPostNoRecvTwo A bundle.rational candidates.left.twoControl
          move.2 =
        let step := overlay.memberStep A bundle.rational currentMember move.2
        (step.1, project step.2))
    (htarget :
      ((candidates.right.reverseRightToLeft A bundle.rational move
          false).1.2,
        (candidates.right.reverseRightToLeft A bundle.rational move
          false).2.map fun phase => phase.twoControl) =
        let step := overlay.memberStep A bundle.rational targetMember move.2
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
  exact endToEndCrossAnchorTwo_of_fixedLeftFamilyOverlay A bundle candidates
    move overlay currentMember targetMember project hcurrent htarget

/-- Close `.mixedLeft false → .right` from the fixed-policy right table. -/
theorem endToEndOperationalAdvance_right_real_mixedLeft_false_of_fixedFamily
    (candidates : EndToEndBothCandidates A bundle.rational)
    (hreal : candidates.Real A bundle.rational)
    (oldOutput : Out₁ × Out₂) (move : In₁ × In₂)
    (overlay : EndToEndRightFamilyPairOverlay A bundle.rational)
    (currentMember targetMember : Bool)
    (project : overlay.MemberControl A bundle.rational →
      Option (EndToEndPhaseOneControl A bundle.rational))
    (hcurrent :
      endToEndPostNoRecvOne A bundle.rational candidates.right.oneControl
          move.1 =
        let step := overlay.memberStep A bundle.rational currentMember move.1
        (step.1, project step.2))
    (htarget :
      ((candidates.left.reverseLeftToRight A bundle.rational
          (move.2, move.1) false).1.1,
        (candidates.left.reverseLeftToRight A bundle.rational
          (move.2, move.1) false).2.map fun phase => phase.oneControl) =
        let step := overlay.memberStep A bundle.rational targetMember move.1
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
  exact endToEndCrossAnchorOne_of_fixedRightFamilyOverlay A bundle candidates
    move overlay currentMember targetMember project hcurrent htarget

end


end DetParityAutomaton

end DistributedSynthesis
