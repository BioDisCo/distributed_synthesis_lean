/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyNarrowing
import DistributedSynthesis.Formalizations.Lemma.LemPairedEntryTransitionFactorMirror

/-!
# Finite narrowing of two locally indistinguishable anchors

This is the strategy-level bridge used at the dangerous mixed-overlap seam.
The two proof anchors may have different histories, receiver continuations,
monitors, and current monitor states.  Equality of the blind process's actual
local views makes their complete future sender strategies equal.  The finite
cross-anchor construction can therefore narrow both obligations at once.

The anchor bit is an index in the proof and in the receiver table only.  It is
never passed to the shared sender strategy or to the sender projection of the
extracted controller.
-/

namespace DistributedSynthesis

universe u v x y w

namespace DetParityAutomaton

section

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
variable [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Process one is blind during a right block.  Two equal process-one views
therefore supply the common semantic sender required by simultaneous finite
narrowing, even when the receiver continuations and monitor states differ. -/
noncomputable def finiteCrossAnchorOneOfViewEq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.one (history false) =
      currentView Proc.one (history true))
    (base : Bool → BlockRecordMonitor.{v, u, y, x, w}
      In₂ In₁ Out₂ Out₁)
    (start : ∀ anchor, (base anchor).State)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₂ In₁ Out₂)
    (hwin : ∀ anchor env,
      ((base anchor).restartAt (start anchor)).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history anchor)) env)) :
    FiniteCrossAnchorPairController base start := by
  apply finiteCrossAnchorPairController base start receiver
    (blockSenderOne strategy (history false))
  intro anchor env
  cases anchor with
  | false => exact hwin false env
  | true =>
      rw [blockSenderOne_eq_of_view_eq strategy hview]
      exact hwin true env

/-- Process-two mirror for a left block. -/
noncomputable def finiteCrossAnchorTwoOfViewEq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.two (history false) =
      currentView Proc.two (history true))
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      In₁ In₂ Out₁ Out₂)
    (start : ∀ anchor, (base anchor).State)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₁ In₂ Out₁)
    (hwin : ∀ anchor env,
      ((base anchor).restartAt (start anchor)).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history anchor)) env)) :
    FiniteCrossAnchorPairController base start := by
  apply finiteCrossAnchorPairController base start receiver
    (blockSenderTwo strategy (history false))
  intro anchor env
  cases anchor with
  | false => exact hwin false env
  | true =>
      rw [blockSenderTwo_eq_of_view_eq strategy hview]
      exact hwin true env

end

end DetParityAutomaton

end DistributedSynthesis
