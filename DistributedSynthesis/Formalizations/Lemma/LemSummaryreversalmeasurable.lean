/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmJournalPlayCorrespondence
import DistributedSynthesis.Formalizations.Lemma.LemSummaryblockplan

/-!
# The summary-controlled plan family: `ReversalMeasurable` obligations

Its block plans carry the summary state as control (`LemSummaryblockplan`), so the block-long
blind agreements are exactly the shared-summary trace lemmas
(`oneBlindTraceMeasurable_of_sharedSummary` and mirror), all hypotheses `rfl`; and the
reversal-entry agreement (`prop:entrysound`, the `blind` field `PlanBlindMeasurable`) holds by
`rfl` too, because the reversal output is *derived* as the block-opening output
(`summaryPlanFamily`): a reversal round is the reversing process's first send, so its
send-summary is fresh `init` and its output is the opening output -- the `b_old`-invariance
built into the construction.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

variable (S₁ S₂ : Type max u v x y s)
variable (init₁ : S₁) (step₁ : S₁ -> In₁ -> S₁)
variable (blindR : S₁ -> In₁ -> Out₁)
variable (informedR : S₁ -> (A.State × A.State) -> In₂ × In₁ -> Out₂)
variable (closeR : S₁ -> (A.State × A.State) -> In₂ × In₁ -> Out₁)
variable (init₂ : S₂) (step₂ : S₂ -> In₂ -> S₂)
variable (blindL : S₂ -> In₂ -> Out₂)
variable (informedL : S₂ -> (A.State × A.State) -> In₁ × In₂ -> Out₁)
variable (closeL : S₂ -> (A.State × A.State) -> In₁ × In₂ -> Out₂)

/-- Abbreviation for the summary plan family with the ambient tables. -/
private abbrev spf :=
  summaryPlanFamily (A := A) S₁ S₂ init₁ step₁ blindR informedR closeR
    init₂ step₂ blindL informedL closeL

/-- The `leftTrace` obligation of `ReversalMeasurable`, discharged by
`oneBlindTraceMeasurable_of_sharedSummary`: the process-one blind block plan and the chain share
the process-one summary control, so the block-long agreement holds by construction. -/
theorem summaryPlanFamily_leftTrace
    (plan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A S₂)
    (control : S₂) (state minState : A.State)
    (candBoundary openBoundary : A.State × A.State) (move : In₁ × In₂) :
    OneBlindTraceMeasurable
      ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          candBoundary).2.1)
      (((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          candBoundary).2.1).step
        ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
            candBoundary).2.1).init move.1)
      ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          openBoundary).2.2)
      (((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          openBoundary).2.2).step
        (((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
            openBoundary).2.2).enterL control)
        (Sum.inr move.1))
      (leftReverseEntry plan control state minState move) := by
  apply oneBlindTraceMeasurable_of_sharedSummary.{u, v, x, y, s} (C_L := S₂) (S := S₁)
    (C_V := S₂ ⊕ S₁)
    (rightplan :=
      summaryRightBlockPlan.{u, v, x, y, s} (A := A) S₁ init₁ step₁ blindR informedR closeR
        (fun _ _ i => blindL init₂ i))
    (chain := summaryChain.{u, v, x, y, s}
      (summaryLeftBlockPlan.{u, v, x, y, s} (A := A) S₂ init₂ step₂ blindL informedL closeL
        (fun _ _ i => blindR init₁ i))
      (summaryRightBlockPlan.{u, v, x, y, s} (A := A) S₁ init₁ step₁ blindR informedR closeR
        (fun _ _ i => blindL init₂ i)))
    (stepS := step₁) (b := blindR)
    (π := summaryChainProjOne.{u, v, x, y, s} (S₂ := S₂) init₁)
  · intro cc i; rfl
  · intro cc; rfl
  · rintro (c | c) i <;> rfl
  · rintro (c | c) entry <;> rfl
  · rfl

/-- The `rightTrace` obligation, the orientation mirror, via
`twoBlindTraceMeasurable_of_sharedSummary`. -/
theorem summaryPlanFamily_rightTrace
    (plan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A S₁)
    (control : S₁) (state minState : A.State)
    (candBoundary openBoundary : A.State × A.State) (move : In₂ × In₁) :
    TwoBlindTraceMeasurable
      ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          candBoundary).1)
      (((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          candBoundary).1).step
        ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
            candBoundary).1).init move.1)
      ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          openBoundary).2.2)
      (((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          openBoundary).2.2).step
        (((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
            openBoundary).2.2).enterR control)
        (Sum.inl move.1))
      (rightReverseEntry plan control state minState move) := by
  apply twoBlindTraceMeasurable_of_sharedSummary.{u, v, x, y, s} (S := S₂) (C_R := S₁)
    (C_V := S₂ ⊕ S₁)
    (leftplan :=
      summaryLeftBlockPlan.{u, v, x, y, s} (A := A) S₂ init₂ step₂ blindL informedL closeL
        (fun _ _ i => blindR init₁ i))
    (chain := summaryChain.{u, v, x, y, s}
      (summaryLeftBlockPlan.{u, v, x, y, s} (A := A) S₂ init₂ step₂ blindL informedL closeL
        (fun _ _ i => blindR init₁ i))
      (summaryRightBlockPlan.{u, v, x, y, s} (A := A) S₁ init₁ step₁ blindR informedR closeR
        (fun _ _ i => blindL init₂ i)))
    (stepS := step₂) (b := blindL)
    (π := summaryChainProjTwo.{u, v, x, y, s} (S₁ := S₁) init₂)
  · intro cc i; rfl
  · intro cc; rfl
  · rintro (c | c) i <;> rfl
  · rintro (c | c) entry <;> rfl
  · rfl

/-- **The `blind` field (`prop:entrysound`) holds by construction.**  Because the reversal output
is derived as the block-opening output (`summaryPlanFamily`'s `revL`/`revR`), the reversal-entry
agreement `blindLeftReversalOutput = blindRightOpenOutput` (and mirror) is `rfl` for every
within-block datum and boundary: both sides reduce to `blindR init₁` (resp. `blindL init₂`). -/
theorem summaryPlanFamily_blind :
    PlanBlindMeasurable
      (spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL) :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

/-- **The `rightReReverseBlind` field holds by construction.**  `summaryChain` overrides the
right chain's re-reversal blind slot (`labelR.2.2.1`) to the *constant fresh-opening* output
`(L.label L.init).1 = blindL init₂`, which is exactly the left block's opening blind
`((spf boundary).1).label init .1` (the family's first component is the left block plan).  Both
sides reduce to `blindL init₂ i`, so the agreement is `rfl` at every control -- no cross-reading
hypothesis is needed. -/
theorem summaryPlanFamily_rightReReverseBlind
    (control : S₂ ⊕ S₁) (entry : A.State × A.State) (state minState : A.State)
    (boundary openBoundary : A.State × A.State) (i : In₂) :
    (((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          boundary).1).label
        ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          boundary).1).init).1 i =
      (((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          openBoundary).2.2).labelR control).2.2.1 (entry, state, minState) i := rfl

/-- **The `leftReReverseBlind` field holds by construction.**  The orientation mirror: the left
chain's re-reversal blind slot (`labelL.2.1`) is overridden to `(R.label R.init).1 = blindR init₁`,
the right block's opening blind (the family's second component); both sides reduce to
`blindR init₁ i`. -/
theorem summaryPlanFamily_leftReReverseBlind
    (control : S₂ ⊕ S₁) (entry : A.State × A.State) (state minState : A.State)
    (boundary openBoundary : A.State × A.State) (i : In₁) :
    (((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          boundary).2.1).label
        ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          boundary).2.1).init).1 i =
      (((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          openBoundary).2.2).labelL control).2.1 (entry, state, minState) i := rfl

/-- **The `rightReReverseTrace` obligation holds by construction, given reset-parity.**  A
re-reversal is consumed only at a `RightResetControl` control (paper `cor:folddischarge`: it
"restarts the other block plan from its initial control"; `arenaFoldSeq_reset` supplies this at
the consumption site).  A right-reset control is a process-one (`Sum.inr`) chain step, so the
subsequent re-reversal step on the `Sum.inl` round deterministically resets the chain to the
left block's initial summary -- exactly the fresh trace start on the block side.  Both branches
of the reset then reduce to the shared-summary agreement (`twoBlindTraceMeasurable_of_sharedSummary`,
all hypotheses `rfl`), so no cross-reading hypothesis is needed. -/
theorem summaryPlanFamily_rightReReverseTrace
    (control : S₂ ⊕ S₁) (entry : A.State × A.State) (state minState : A.State)
    (boundary openBoundary : A.State × A.State) (move : In₁ × In₂)
    (hreset :
      RightResetControl
        ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
            openBoundary).2.2)
        control) :
    TwoBlindTraceMeasurable
      ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
        boundary).1)
      (((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
        boundary).1).step
        ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          boundary).1).init move.2)
      ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
        openBoundary).2.2)
      (((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
        openBoundary).2.2).step control (Sum.inl move.2))
      (revRightReverseEntry
        ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          openBoundary).2.2)
        control entry state minState move) := by
  obtain ⟨pre, pm, hpre⟩ := hreset
  subst hpre
  rcases pre with pre | pre <;>
    (apply twoBlindTraceMeasurable_of_sharedSummary.{u, v, x, y, s} (S := S₂) (C_R := S₁)
        (C_V := S₂ ⊕ S₁)
        (leftplan :=
          summaryLeftBlockPlan.{u, v, x, y, s} (A := A) S₂ init₂ step₂ blindL informedL closeL
            (fun _ _ i => blindR init₁ i))
        (chain := summaryChain.{u, v, x, y, s}
          (summaryLeftBlockPlan.{u, v, x, y, s} (A := A) S₂ init₂ step₂ blindL informedL closeL
            (fun _ _ i => blindR init₁ i))
          (summaryRightBlockPlan.{u, v, x, y, s} (A := A) S₁ init₁ step₁ blindR informedR closeR
            (fun _ _ i => blindL init₂ i)))
        (stepS := step₂) (b := blindL)
        (π := summaryChainProjTwo.{u, v, x, y, s} (S₁ := S₁) init₂) <;>
      first
        | (intro cc i; rfl)
        | (intro cc; rfl)
        | (rintro (cc | cc) i <;> rfl)
        | rfl)

/-- **The `leftReReverseTrace` obligation holds by construction, given reset-parity.**  The
orientation mirror of `summaryPlanFamily_rightReReverseTrace`, on a `LeftResetControl` control
(process-two chain step) reset by the `Sum.inr` re-reversal round. -/
theorem summaryPlanFamily_leftReReverseTrace
    (control : S₂ ⊕ S₁) (entry : A.State × A.State) (state minState : A.State)
    (boundary openBoundary : A.State × A.State) (move : In₁ × In₂)
    (hreset :
      LeftResetControl
        ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
            openBoundary).2.2)
        control) :
    OneBlindTraceMeasurable
      ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
        boundary).2.1)
      (((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
        boundary).2.1).step
        ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          boundary).2.1).init move.1)
      ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
        openBoundary).2.2)
      (((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
        openBoundary).2.2).step control (Sum.inr move.1))
      (revLeftReverseEntry
        ((spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL
          openBoundary).2.2)
        control entry state minState move) := by
  obtain ⟨pre, pm, hpre⟩ := hreset
  subst hpre
  rcases pre with pre | pre <;>
    (apply oneBlindTraceMeasurable_of_sharedSummary.{u, v, x, y, s} (C_L := S₂) (S := S₁)
        (C_V := S₂ ⊕ S₁)
        (rightplan :=
          summaryRightBlockPlan.{u, v, x, y, s} (A := A) S₁ init₁ step₁ blindR informedR closeR
            (fun _ _ i => blindL init₂ i))
        (chain := summaryChain.{u, v, x, y, s}
          (summaryLeftBlockPlan.{u, v, x, y, s} (A := A) S₂ init₂ step₂ blindL informedL closeL
            (fun _ _ i => blindR init₁ i))
          (summaryRightBlockPlan.{u, v, x, y, s} (A := A) S₁ init₁ step₁ blindR informedR closeR
            (fun _ _ i => blindL init₂ i)))
        (stepS := step₁) (b := blindR)
        (π := summaryChainProjOne.{u, v, x, y, s} (S₂ := S₂) init₁) <;>
      first
        | (intro cc i; rfl)
        | (intro cc; rfl)
        | (rintro (cc | cc) i <;> rfl)
        | rfl)

/-- **`ReversalMeasurable` for the summary plan family, fully by construction.**  All seven
obligations are discharged without any cross-reading hypothesis: `blind` (`prop:entrysound`)
and the two re-reversal *blind* agreements (`rfl` via the derived reversal/fresh-opening
output), the two block-long `leftTrace`/`rightTrace` (via `sharedSummary`), and the two
re-reversal *trace* agreements (via `sharedSummary` after the reset-parity restriction reduces
the re-reversal to a fresh block start).  This is the realizing θ̄-fold's `hmeas`, unconditional. -/
theorem summaryPlanFamily_reversalMeasurable :
    ReversalMeasurable
      (spf S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL informedL closeL) where
  blind :=
    summaryPlanFamily_blind S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL
      informedL closeL
  leftTrace :=
    summaryPlanFamily_leftTrace S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL
      informedL closeL
  rightTrace :=
    summaryPlanFamily_rightTrace S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂ blindL
      informedL closeL
  rightReReverseBlind :=
    summaryPlanFamily_rightReReverseBlind S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂
      blindL informedL closeL
  rightReReverseTrace :=
    summaryPlanFamily_rightReReverseTrace S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂
      blindL informedL closeL
  leftReReverseBlind :=
    summaryPlanFamily_leftReReverseBlind S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂
      blindL informedL closeL
  leftReReverseTrace :=
    summaryPlanFamily_leftReReverseTrace S₁ S₂ init₁ step₁ blindR informedR closeR init₂ step₂
      blindL informedL closeL

end DetParityAutomaton

end DistributedSynthesis
