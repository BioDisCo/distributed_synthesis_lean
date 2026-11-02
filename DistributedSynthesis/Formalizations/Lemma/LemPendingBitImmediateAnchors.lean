/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedEntryTransitionFactorMirror

/-!
# Immediate semantic anchors for the pending-bit construction

The cross-anchor table is installed immediately after a locally ambiguous
receive.  At that point the two semantic histories differ only in the graph
of the last round: `left` versus `both` for process one, or `right` versus
`both` for process two.  This file packages those two literal overlaps.

These are proof-side history facts.  They are used to select one finite table
before the hidden bit is resolved; no executable transition receives either
a graph or a history.
-/

namespace DistributedSynthesis

universe u v x y

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- A literal `left`/`both` pair at one strategy-generated base is a
process-one pending overlap with empty strict suffix. -/
theorem procOnePendingOverlap_immediate
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (input : In₁ × In₂) :
    ProcOnePendingOverlap
      (History.append base
        (nextRound strategy base ⟨input.1, input.2, .left⟩))
      (History.append base
        (nextRound strategy base ⟨input.1, input.2, .both⟩)) := by
  refine ⟨base,
    nextRound strategy base ⟨input.1, input.2, .left⟩,
    nextRound strategy base ⟨input.1, input.2, .both⟩, [], ?_⟩
  simp [nextRound]

/-- Mirror: a literal `right`/`both` pair is the immediate process-two
pending overlap. -/
theorem procTwoPendingOverlap_immediate
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (input : In₁ × In₂) :
    ProcTwoPendingOverlap
      (History.append base
        (nextRound strategy base ⟨input.1, input.2, .right⟩))
      (History.append base
        (nextRound strategy base ⟨input.1, input.2, .both⟩)) := by
  refine ⟨base,
    nextRound strategy base ⟨input.1, input.2, .right⟩,
    nextRound strategy base ⟨input.1, input.2, .both⟩, [], ?_⟩
  simp [nextRound]

/-- Hence the complete process-one sender fragment chosen by the original
strategy is shared by the two immediate anchors. -/
theorem blockSenderOne_immediate_left_eq_both
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (input : In₁ × In₂) :
    blockSenderOne strategy
        (History.append base
          (nextRound strategy base ⟨input.1, input.2, .left⟩)) =
      blockSenderOne strategy
        (History.append base
          (nextRound strategy base ⟨input.1, input.2, .both⟩)) :=
  DetParityAutomaton.blockSenderOne_eq_of_view_eq strategy
    (procOnePendingOverlap_immediate strategy base input).view_eq

/-- Process-two mirror. -/
theorem blockSenderTwo_immediate_right_eq_both
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (input : In₁ × In₂) :
    blockSenderTwo strategy
        (History.append base
          (nextRound strategy base ⟨input.1, input.2, .right⟩)) =
      blockSenderTwo strategy
        (History.append base
          (nextRound strategy base ⟨input.1, input.2, .both⟩)) :=
  DetParityAutomaton.blockSenderTwo_eq_of_view_eq strategy
    (procTwoPendingOverlap_immediate strategy base input).view_eq

/-! ### The immediate overlap is consumed by the next receive -/

/-- The literal `left`/`both` ambiguity is resolved on process one's next
receive even when the two continuations are generated separately by the
strategy and the receive itself may introduce a fresh `left`/`both` bit.

This is the concrete strategy-generated form of replace-not-accumulate.  In
particular, locality does *not* require the two receiver outputs at this point
to be equal: their local views are already distinct. -/
theorem procOne_immediate_old_bit_resolved_despite_fresh_receive
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (openingInput nextInputLeft nextInputBoth : In₁ × In₂)
    (nextGraphLeft nextGraphBoth : Graph)
    (hnextLeft : nextGraphLeft = .left ∨ nextGraphLeft = .both)
    (hnextBoth : nextGraphBoth = .left ∨ nextGraphBoth = .both) :
    let rLeft :=
      nextRound strategy base
        ⟨openingInput.1, openingInput.2, .left⟩
    let rBoth :=
      nextRound strategy base
        ⟨openingInput.1, openingInput.2, .both⟩
    let nextLeft :=
      nextRound strategy (History.append base rLeft)
        ⟨nextInputLeft.1, nextInputLeft.2, nextGraphLeft⟩
    let nextBoth :=
      nextRound strategy (History.append base rBoth)
        ⟨nextInputBoth.1, nextInputBoth.2, nextGraphBoth⟩
    currentView Proc.one
        (History.append (History.append base rLeft) nextLeft) ≠
      currentView Proc.one
        (History.append (History.append base rBoth) nextBoth) := by
  dsimp only
  have hresolved :=
    procOne_old_bit_resolved_despite_fresh_receive
      base
      (nextRound strategy base
        ⟨openingInput.1, openingInput.2, .left⟩)
      (nextRound strategy base
        ⟨openingInput.1, openingInput.2, .both⟩)
      []
      (nextRound strategy
        (History.append base
          (nextRound strategy base
            ⟨openingInput.1, openingInput.2, .left⟩))
        ⟨nextInputLeft.1, nextInputLeft.2, nextGraphLeft⟩)
      (nextRound strategy
        (History.append base
          (nextRound strategy base
            ⟨openingInput.1, openingInput.2, .both⟩))
        ⟨nextInputBoth.1, nextInputBoth.2, nextGraphBoth⟩)
      (by simp [nextRound]) (by simp [nextRound]) (by simp)
      (by simpa [nextRound] using hnextLeft)
      (by simpa [nextRound] using hnextBoth)
  simpa using hresolved

/-- Process-two mirror of
`procOne_immediate_old_bit_resolved_despite_fresh_receive`. -/
theorem procTwo_immediate_old_bit_resolved_despite_fresh_receive
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (openingInput nextInputRight nextInputBoth : In₁ × In₂)
    (nextGraphRight nextGraphBoth : Graph)
    (hnextRight : nextGraphRight = .right ∨ nextGraphRight = .both)
    (hnextBoth : nextGraphBoth = .right ∨ nextGraphBoth = .both) :
    let rRight :=
      nextRound strategy base
        ⟨openingInput.1, openingInput.2, .right⟩
    let rBoth :=
      nextRound strategy base
        ⟨openingInput.1, openingInput.2, .both⟩
    let nextRight :=
      nextRound strategy (History.append base rRight)
        ⟨nextInputRight.1, nextInputRight.2, nextGraphRight⟩
    let nextBoth :=
      nextRound strategy (History.append base rBoth)
        ⟨nextInputBoth.1, nextInputBoth.2, nextGraphBoth⟩
    currentView Proc.two
        (History.append (History.append base rRight) nextRight) ≠
      currentView Proc.two
        (History.append (History.append base rBoth) nextBoth) := by
  dsimp only
  have hresolved :=
    procTwo_old_bit_resolved_despite_fresh_receive
      base
      (nextRound strategy base
        ⟨openingInput.1, openingInput.2, .right⟩)
      (nextRound strategy base
        ⟨openingInput.1, openingInput.2, .both⟩)
      []
      (nextRound strategy
        (History.append base
          (nextRound strategy base
            ⟨openingInput.1, openingInput.2, .right⟩))
        ⟨nextInputRight.1, nextInputRight.2, nextGraphRight⟩)
      (nextRound strategy
        (History.append base
          (nextRound strategy base
            ⟨openingInput.1, openingInput.2, .both⟩))
        ⟨nextInputBoth.1, nextInputBoth.2, nextGraphBoth⟩)
      (by simp [nextRound]) (by simp [nextRound]) (by simp)
      (by simpa [nextRound] using hnextRight)
      (by simpa [nextRound] using hnextBoth)
  simpa using hresolved

end DistributedSynthesis
