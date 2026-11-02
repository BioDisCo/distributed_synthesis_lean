/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemLocalSummaryReceiptTag
import DistributedSynthesis.Formalizations.Lemma.LemNoorientationconsensus
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenFixedStrategySafetyKernel

/-!
# The local-measurability gate for public open-family controllers

The fixed-strategy safety kernel chooses a finite whole-block move at a
finite public observation.  Legality and successor closure do not by
themselves make that public choice executable by the two processes.  A local
summary adapter must additionally be constant on every fibre of the local
summary read: two global histories represented by the same local summary
must receive the same process-local projection of the chosen whole-block
move.

This file records that exact necessary law and checks it against the standard
hidden-orientation pair.  Adding the locally visible receipt tag does not
separate the histories `left,right` and `both,right` for process one, because
their complete process-one views are already equal.  Consequently any direct
adapter for a public `.right`/`.left` controller must prove equality of its
process-one table projections on this pair; branching on the public
orientation is not an implementation.

This is a fail-fast interface result, not a counterexample to the synthesis
theorem.  A simultaneous two-shadow extraction can satisfy the law by making
the relevant projections equal.  The current safety-kernel fields, however,
state only legality and closure and therefore do not discharge it.
-/

namespace DistributedSynthesis

universe u v x y o a s

namespace LocalSummaryAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- A history-dependent value is constant on every fibre of a finite local
summary read.  This is the exact local-measurability law needed before the
value can be read from that summary. -/
def HistoryProjectionReadFiberUniform
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) (d : Proc)
    {Value : Type a}
    (projection : History In₁ In₂ Graph Out₁ Out₂ → Value) : Prop :=
  ∀ left right,
    M.read (currentView d left) = M.read (currentView d right) →
      projection left = projection right

/-- A history-dependent value is actually decoded from a finite local
summary.  The theorem below records the unavoidable fibre law of every such
decoder. -/
def HistoryProjectionDecodedBy
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) (d : Proc)
    {Value : Type a}
    (projection : History In₁ In₂ Graph Out₁ Out₂ → Value) : Prop :=
  ∃ decode : M.Summary d → Value,
    ∀ history, decode (M.read (currentView d history)) = projection history

/-- Every summary decoder is constant on equal-summary histories. -/
theorem historyProjection_readFiberUniform_of_decodedBy
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) (d : Proc)
    {Value : Type a}
    (projection : History In₁ In₂ Graph Out₁ Out₂ → Value)
    (hdecoded : M.HistoryProjectionDecodedBy d projection) :
    M.HistoryProjectionReadFiberUniform d projection := by
  rcases hdecoded with ⟨decode, hdecode⟩
  intro left right hread
  rw [← hdecode left, ← hdecode right, hread]

/-- Equal exact local views remain equal after *any* finite local-summary
read, including after adding the receipt-tag wrapper. -/
theorem read_eq_of_currentView_eq
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) (d : Proc)
    (left right : History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView d left = currentView d right) :
    M.read (currentView d left) = M.read (currentView d right) := by
  rw [hview]

/-- The receipt-tagged summary still identifies the standard hidden-
orientation pair for process one. -/
theorem withReceiptTag_read_leftRight_eq_bothRight
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (x₁₀ : In₁) (x₂₀ : In₂) (x₁₁ : In₁) (x₂₁ : In₂)
    (y₁₀ : Out₁) (y₂₀ : Out₂) (y₁₁ : Out₁) (y₂₁ : Out₂) :
    M.withReceiptTag.read
        (currentView Proc.one
          (twoRoundOrientationHistory .left
            x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)) =
      M.withReceiptTag.read
        (currentView Proc.one
          (twoRoundOrientationHistory .both
            x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)) := by
  rw [no_orientation_consensus_procOne_same_view]

/-- No receipt-tagged summary decoder can realize a projection that separates
the hidden-orientation pair. -/
theorem not_historyProjectionDecodedBy_withReceiptTag_of_left_both_ne
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    {Value : Type a}
    (projection : History In₁ In₂ Graph Out₁ Out₂ → Value)
    (x₁₀ : In₁) (x₂₀ : In₂) (x₁₁ : In₁) (x₂₁ : In₂)
    (y₁₀ : Out₁) (y₂₀ : Out₂) (y₁₁ : Out₁) (y₂₁ : Out₂)
    (hseparates :
      projection
          (twoRoundOrientationHistory .left
            x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁) ≠
        projection
          (twoRoundOrientationHistory .both
            x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)) :
    ¬ M.withReceiptTag.HistoryProjectionDecodedBy Proc.one projection := by
  intro hdecoded
  apply hseparates
  exact historyProjection_readFiberUniform_of_decodedBy
    M.withReceiptTag Proc.one projection hdecoded _ _
      (withReceiptTag_read_leftRight_eq_bothRight M
        x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)

end LocalSummaryAutomaton

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- The complete process-one blind behavior carried by a public right move.
The harmless fallback only totalizes the other constructors.  Equality of
this projection is the behavioral cross-anchor law needed by a process-one
local implementation; equality of the dependent whole-table values would be
unnecessarily strong. -/
noncomputable def ProfiledOpenRepresentableMove.rightSenderBehavior
    (move : ProfiledOpenRepresentableMove A) :
    List In₁ → In₁ → Out₁ :=
  match move with
  | .right _ table => fun word =>
      (table.toTransitionRationalTree.labeledTree word).1
  | .sink | .left _ _ => fun _ _ => default

/-- Process-two blind behavior of a public left move. -/
noncomputable def ProfiledOpenRepresentableMove.leftSenderBehavior
    (move : ProfiledOpenRepresentableMove A) :
    List In₂ → In₂ → Out₂ :=
  match move with
  | .left _ table => fun word =>
      (table.toTransitionRationalTree.labeledTree word).1
  | .sink | .right _ _ => fun _ _ => default

/-- The exact missing adapter law for one process-local projection of the
public open-family move.  `moveAt` is the whole-table move selected by the
public safety controller along a concrete global history; `project` forgets
everything except the local runtime datum consumed by process `d`.

The law deliberately quantifies over equal *summary reads*, rather than over
public observations.  This is what a `LocalSummaryAutomaton` implementation
must respect. -/
def ProfiledOpenPublicMoveProjectionUniform
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) (d : Proc)
    (moveAt : History In₁ In₂ Graph Out₁ Out₂ →
      ProfiledOpenRepresentableMove A)
    {LocalValue : Type a}
    (project : ProfiledOpenRepresentableMove A → LocalValue) : Prop :=
  ∀ left right,
    M.read (currentView d left) = M.read (currentView d right) →
      project (moveAt left) = project (moveAt right)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A genuine local-summary readout of a public move projection implies the
missing projection-uniformity law. -/
theorem profiledOpenPublicMoveProjectionUniform_of_decodedBy
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) (d : Proc)
    (moveAt : History In₁ In₂ Graph Out₁ Out₂ →
      ProfiledOpenRepresentableMove A)
    {LocalValue : Type a}
    (project : ProfiledOpenRepresentableMove A → LocalValue)
    (hdecoded : M.HistoryProjectionDecodedBy d (fun history =>
      project (moveAt history))) :
    ProfiledOpenPublicMoveProjectionUniform A M d moveAt project := by
  exact M.historyProjection_readFiberUniform_of_decodedBy d
    (fun history => project (moveAt history)) hdecoded

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- On the concrete hidden-orientation pair, the adapter law forces equality
of the process-one projections.  Hence a safety controller that selects
locally different tables there cannot be compiled merely by adding receipt
tags. -/
theorem profiledOpenPublicMoveProjection_leftRight_eq_bothRight
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (moveAt : History In₁ In₂ Graph Out₁ Out₂ →
      ProfiledOpenRepresentableMove A)
    {LocalValue : Type a}
    (project : ProfiledOpenRepresentableMove A → LocalValue)
    (huniform : ProfiledOpenPublicMoveProjectionUniform A M.withReceiptTag
      Proc.one moveAt project)
    (x₁₀ : In₁) (x₂₀ : In₂) (x₁₁ : In₁) (x₂₁ : In₂)
    (y₁₀ : Out₁) (y₂₀ : Out₂) (y₁₁ : Out₁) (y₂₁ : Out₂) :
    project
        (moveAt
          (twoRoundOrientationHistory .left
            x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)) =
      project
        (moveAt
          (twoRoundOrientationHistory .both
            x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)) := by
  exact huniform _ _
    (LocalSummaryAutomaton.withReceiptTag_read_leftRight_eq_bothRight M
      x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)

omit [Inhabited Out₂] in
/-- Concrete specialization of the gate to the entire future process-one
blind sender behavior carried by the selected whole-block table. -/
theorem profiledOpenRightSenderBehavior_leftRight_eq_bothRight
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (moveAt : History In₁ In₂ Graph Out₁ Out₂ →
      ProfiledOpenRepresentableMove A)
    (huniform : ProfiledOpenPublicMoveProjectionUniform A M.withReceiptTag
      Proc.one moveAt
        (ProfiledOpenRepresentableMove.rightSenderBehavior A))
    (x₁₀ : In₁) (x₂₀ : In₂) (x₁₁ : In₁) (x₂₁ : In₂)
    (y₁₀ : Out₁) (y₂₀ : Out₂) (y₁₁ : Out₁) (y₂₁ : Out₂) :
    (moveAt
        (twoRoundOrientationHistory .left
          x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)).rightSenderBehavior A =
      (moveAt
        (twoRoundOrientationHistory .both
          x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁)).rightSenderBehavior A := by
  exact profiledOpenPublicMoveProjection_leftRight_eq_bothRight A M moveAt
    (ProfiledOpenRepresentableMove.rightSenderBehavior A) huniform
      x₁₀ x₂₀ x₁₁ x₂₁ y₁₀ y₂₀ y₁₁ y₂₁

end

end DetParityAutomaton

end DistributedSynthesis
