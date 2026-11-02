/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCrossReceiverPhysicalProjection
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonPairCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailPolicy

/-!
# A tag-coherent simultaneous physical close

A delayed phase-live tag names one concrete common semantic occurrence before
it names either strict child.  From that one occurrence we extract the two
guarded local tables together.  Their simultaneous receiver projections form
both the right closing record and the left closing record.  This is the
anti-mosaic output seam needed by a tag-indexed recurrent tail.

The orientation occurs only in the proof predicate
`SelectsClosingOutputAt`.  The executable pair `bothPhysicalOutputAt` does not
inspect a graph, a leader bit, the tag side, a history, or the other endpoint's
local state.

This file intentionally does not identify the guarded pair with the
unguarded physical annotation stored by the parent-linked tail.  That is the
next, separate ID bridge; keeping it separate prevents a policy/table equality
from being smuggled into the output argument.
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

/-! ## The one common occurrence carried by a tag -/

/-- The guarded pair extracted from the tag's one installed common world.
Both tables therefore retain one semantic occurrence and cannot mosaic two
independently chosen representatives. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.guardedCommonPair
    (tag : Tag A strategy hwin) :
    ProfiledRawJointGuardedCommonPair A strategy hwin :=
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
  profiledRawJointGuardedCommonPairOfWorld A strategy hwin installed.world
    tag.input

/-- The process-local simultaneous outputs read from the two guarded root
records.  Process one reads the left receiver and process two reads the right
receiver; neither projection receives the tag side. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.bothPhysicalOutputAt
    (tag : Tag A strategy hwin) (input : In₁ × In₂) : Out₁ × Out₂ :=
  let pair := tag.guardedCommonPair A strategy hwin
  let rightRecord := pair.rightRootRecord A strategy hwin input
  let leftRecord := pair.leftRootRecord A strategy hwin input
  (profiledRawJointTargetLeftReceiverBothPhysicalOutput leftRecord.2.1,
    profiledRawJointTargetRightReceiverBothPhysicalOutput rightRecord.2.1)

/-- The same cut interpreted as the closing record of the right table. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.rightClosingOutputAt
    (tag : Tag A strategy hwin) (input : In₁ × In₂) : Out₁ × Out₂ :=
  let physical :=
    (tag.guardedCommonPair A strategy hwin).rightRootRecord A strategy hwin
      input |>.2.1.physical
  (pairedRightClosingForRow .both physical,
    pairedRightInformedForRow .both physical)

/-- The same cut interpreted as the closing record of the left table. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.leftClosingOutputAt
    (tag : Tag A strategy hwin) (input : In₁ × In₂) : Out₁ × Out₂ :=
  let physical :=
    (tag.guardedCommonPair A strategy hwin).leftRootRecord A strategy hwin
      input |>.2.1.physical
  (pairedLeftInformedForRow .both physical,
    pairedLeftClosingForRow .both physical)

/-! ## The anti-mosaic equality -/

/-- One tag-coherent simultaneous output is simultaneously the checked close
of either guarded local table.  This stronger conjunction is what makes the
subsequent proof-side orientation selection harmless. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.bothPhysicalOutputAt_eq_closings
    (tag : Tag A strategy hwin) (input : In₁ × In₂) :
    tag.bothPhysicalOutputAt A strategy hwin input =
        tag.rightClosingOutputAt A strategy hwin input ∧
      tag.bothPhysicalOutputAt A strategy hwin input =
        tag.leftClosingOutputAt A strategy hwin input := by
  let pair := tag.guardedCommonPair A strategy hwin
  have hone := pair.root_outputOne A strategy hwin input
  have htwo := pair.root_outputTwo A strategy hwin input
  constructor
  · apply Prod.ext
    · exact hone.symm
    · rfl
  · apply Prod.ext
    · rfl
    · exact htwo.symm

/-- Proof-only statement that an output is the closing record selected by the
tag orientation.  Since this is a `Prop`, its side case split is erased and
does not give either local controller a leader/orientation oracle. -/
def ProfiledRawJointHybridShadowPhaseLiveTag.SelectsClosingOutputAt
    (tag : Tag A strategy hwin) (input : In₁ × In₂)
    (output : Out₁ × Out₂) : Prop :=
  match tag.side with
  | .right => output = tag.rightClosingOutputAt A strategy hwin input
  | .left => output = tag.leftClosingOutputAt A strategy hwin input

/-- The actually projected local output satisfies the side-selected closing
record specification.  The case split is confined to this proof. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.bothPhysicalOutputAt_selectsClosing
    (tag : Tag A strategy hwin) (input : In₁ × In₂) :
    tag.SelectsClosingOutputAt A strategy hwin input
      (tag.bothPhysicalOutputAt A strategy hwin input) := by
  rcases tag.bothPhysicalOutputAt_eq_closings A strategy hwin input with
    ⟨hright, hleft⟩
  cases hside : tag.side with
  | right =>
      simpa [
        ProfiledRawJointHybridShadowPhaseLiveTag.SelectsClosingOutputAt,
        hside] using hright
  | left =>
      simpa [
        ProfiledRawJointHybridShadowPhaseLiveTag.SelectsClosingOutputAt,
        hside] using hleft

end

end DetParityAutomaton

end DistributedSynthesis
