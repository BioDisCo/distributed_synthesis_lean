/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRootFamilyOverlay
import DistributedSynthesis.Formalizations.Theorem.ThmCrossAnchorLocalNarrowing

/-!
# Semantic producer for fixed-policy end-to-end family moves

The simultaneous table must be chosen before two locally indistinguishable
anchors are rationalized separately.  Equal blind-side views identify the
complete semantic sender strategy.  Universal-thread narrowing can therefore
be applied once to that sender and the two receiver continuations.

Unlike the older family producer, the roots here are the exact restart roots
of the one-policy end-to-end carrier.  The construction consequently changes
neither the guarded child nor its rational policy.  The Boolean index remains
proof-side and is never passed to the shared sender.
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

/-! ## Right-oriented producer -/

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] in
/-- Equal process-one views replace both semantic senders by one common
sender without changing either restarted monitor's winning property. -/
private theorem endToEndRight_sharedSender_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.one (history false) =
      currentView Proc.one (history true))
    (source : Bool → EndToEndRightRestartRoot A package)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₂ In₁
      (ProfiledRightReceiverOutput A))
    (hwin : ∀ anchor env,
      (endToEndRightFamilyRootMonitors A package source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history anchor)) env)) :
    ∀ anchor env,
      (endToEndRightFamilyRootMonitors A package source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history false)) env) := by
  intro anchor env
  cases anchor with
  | false => exact hwin false env
  | true =>
      rw [blockSenderOne_eq_of_view_eq strategy hview]
      exact hwin true env

/-- Materialize the shared right table directly in the fixed-policy finite
move alphabet. -/
noncomputable def endToEndRightFamilyPairMoveOfViewEq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.one (history false) =
      currentView Proc.one (history true))
    (source : Bool → EndToEndRightRestartRoot A package)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₂ In₁
      (ProfiledRightReceiverOutput A))
    (hwin : ∀ anchor env,
      (endToEndRightFamilyRootMonitors A package source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history anchor)) env)) :
    EndToEndRightFamilyPairMove A package :=
  ⟨source,
    finiteRootFamilyTable
      (endToEndRightFamilyRootMonitors A package source) receiver
      (blockSenderOne strategy (history false))
      (endToEndRight_sharedSender_wins A package strategy history hview source
        receiver hwin)⟩

/-- The produced table wins the simultaneous two-root monitor. -/
theorem endToEndRightFamilyPairMoveOfViewEq_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.one (history false) =
      currentView Proc.one (history true))
    (source : Bool → EndToEndRightRestartRoot A package)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₂ In₁
      (ProfiledRightReceiverOutput A))
    (hwin : ∀ anchor env,
      (endToEndRightFamilyRootMonitors A package source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history anchor)) env)) :
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (endToEndRightFamilyRootMonitors A package source))
      (endToEndRightFamilyPairMoveOfViewEq A package strategy history hview
        source receiver hwin).2.toTransitionRationalTree.labeledTree := by
  simpa [endToEndRightFamilyPairMoveOfViewEq] using
    (finiteRootFamilyTable_wins
      (endToEndRightFamilyRootMonitors A package source) receiver
      (blockSenderOne strategy (history false))
      (endToEndRight_sharedSender_wins A package strategy history hview source
        receiver hwin))

/-! ## Left-oriented producer -/

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
private theorem endToEndLeft_sharedSender_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.two (history false) =
      currentView Proc.two (history true))
    (source : Bool → EndToEndLeftRestartRoot A package)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₁ In₂
      (ProfiledLeftReceiverOutput A))
    (hwin : ∀ anchor env,
      (endToEndLeftFamilyRootMonitors A package source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history anchor)) env)) :
    ∀ anchor env,
      (endToEndLeftFamilyRootMonitors A package source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history false)) env) := by
  intro anchor env
  cases anchor with
  | false => exact hwin false env
  | true =>
      rw [blockSenderTwo_eq_of_view_eq strategy hview]
      exact hwin true env

/-- Left-oriented fixed-policy table producer. -/
noncomputable def endToEndLeftFamilyPairMoveOfViewEq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.two (history false) =
      currentView Proc.two (history true))
    (source : Bool → EndToEndLeftRestartRoot A package)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₁ In₂
      (ProfiledLeftReceiverOutput A))
    (hwin : ∀ anchor env,
      (endToEndLeftFamilyRootMonitors A package source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history anchor)) env)) :
    EndToEndLeftFamilyPairMove A package :=
  ⟨source,
    finiteRootFamilyTable
      (endToEndLeftFamilyRootMonitors A package source) receiver
      (blockSenderTwo strategy (history false))
      (endToEndLeft_sharedSender_wins A package strategy history hview source
        receiver hwin)⟩

/-- The left table also wins its simultaneous family monitor. -/
theorem endToEndLeftFamilyPairMoveOfViewEq_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.two (history false) =
      currentView Proc.two (history true))
    (source : Bool → EndToEndLeftRestartRoot A package)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₁ In₂
      (ProfiledLeftReceiverOutput A))
    (hwin : ∀ anchor env,
      (endToEndLeftFamilyRootMonitors A package source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history anchor)) env)) :
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (endToEndLeftFamilyRootMonitors A package source))
      (endToEndLeftFamilyPairMoveOfViewEq A package strategy history hview
        source receiver hwin).2.toTransitionRationalTree.labeledTree := by
  simpa [endToEndLeftFamilyPairMoveOfViewEq] using
    (finiteRootFamilyTable_wins
      (endToEndLeftFamilyRootMonitors A package source) receiver
      (blockSenderTwo strategy (history false))
      (endToEndLeft_sharedSender_wins A package strategy history hview source
        receiver hwin))

end


end DetParityAutomaton

end DistributedSynthesis
