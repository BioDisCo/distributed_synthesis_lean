/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartFirstThenBothProfiledTarget

/-!
# Profile seam for the first-then-both target

The exact mixed target and the old constant-row child generally have different
automaton states and compressed priorities.  Their finite boundary profile is
nevertheless the same when the old child is selected at the mixed scan's
closing row.  This is the precise part of the old target representation that
can be reused without identifying the two targets.
-/

namespace DistributedSynthesis

universe u v x y s t

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

/-- The right mixed target and the old child at its closing row carry the same
finite left-boundary profile. -/
theorem profiledRawJointRightFirstThenBothProfiledStateExtension_profileSeam
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    let letters := profiledRawJointRightBlockLetters activation.lambda past
    let scan := profiledRawJointRightFirstThenBothScan A source.1.1 letters
    let row := profiledRawJointFirstThenBothScanRow A scan
    ∃ mixedSlot oldSlot : ProfiledRawLeftSlot A,
      (profiledRawJointRightFirstThenBothProfiledStateExtension A activation
          ).target past input = .inr (.inr mixedSlot) ∧
        (profiledRawJointRightProfiledStateActivation A activation).target
            row past input = .inr (.inr oldSlot) ∧
          mixedSlot.2 = oldSlot.2 := by
  dsimp
  exact ⟨_, _, rfl, rfl, rfl⟩

/-- The left mixed target and the old child at its closing row carry the same
finite right-boundary profile. -/
theorem profiledRawJointLeftFirstThenBothProfiledStateExtension_profileSeam
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let letters := profiledRawJointLeftBlockLetters activation.lambda past
    let scan := profiledRawJointLeftFirstThenBothScan A source.1.1 letters
    let row := profiledRawJointFirstThenBothScanRow A scan
    ∃ mixedSlot oldSlot : ProfiledRawRightSlot A,
      (profiledRawJointLeftFirstThenBothProfiledStateExtension A activation
          ).target past input = .inr (.inl mixedSlot) ∧
        (profiledRawJointLeftProfiledStateActivation A activation).target
            row past input = .inr (.inl oldSlot) ∧
          mixedSlot.2 = oldSlot.2 := by
  dsimp
  exact ⟨_, _, rfl, rfl, rfl⟩

end

end DetParityAutomaton

end DistributedSynthesis
