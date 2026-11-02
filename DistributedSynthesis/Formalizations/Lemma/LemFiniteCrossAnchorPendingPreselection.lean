/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorPairTable
import DistributedSynthesis.Formalizations.Lemma.LemPendingBitResolution

/-!
# Finite preselection at a pending-bit cross anchor

The charged common/strict seam must not rationalize its two possible future
senders independently and then ask them to agree.  A pending overlap already
says that both proof-side histories have the same local view for the blind
sender.  This file uses that fact *before* narrowing: the two restarted
monitor obligations are put in one finite root family and one sender table is
extracted for both of them.

The optional first-two-record guard pins the two physical seam records while
the family construction supplies equality at every later sender word.  The
Boolean anchor remains confined to the receiver/monitor projection and is
never an input of the sender table.
-/

namespace DistributedSynthesis

universe u v x y w

namespace DetParityAutomaton

noncomputable section

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
variable [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Unguarded pending-overlap preselection -/

/-- A process-one pending overlap produces one finite table for two arbitrary
right-block restart obligations.  The two monitors, states, and informed
receiver continuations may differ; only the blind sender is shared. -/
noncomputable def finiteCrossAnchorPairTableOneOfPendingOverlap
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (historyFalse historyTrue : History In₁ In₂ Graph Out₁ Out₂)
    (hoverlap : ProcOnePendingOverlap historyFalse historyTrue)
    (base : Bool → BlockRecordMonitor.{v, u, y, x, w}
      In₂ In₁ Out₂ Out₁)
    (start : ∀ anchor, (base anchor).State)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₂ In₁ Out₂)
    (hwin : ∀ anchor env,
      (finiteCrossAnchorRestartFamily base start anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy
            (if anchor then historyTrue else historyFalse)) env)) :
    FiniteCrossAnchorPairTable base start :=
  finiteCrossAnchorPairTableOneOfViewEq strategy
    (fun anchor ↦ if anchor then historyTrue else historyFalse)
    hoverlap.view_eq base start receiver (by
      intro anchor env
      exact hwin anchor env)

/-- Process-two mirror. -/
noncomputable def finiteCrossAnchorPairTableTwoOfPendingOverlap
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (historyFalse historyTrue : History In₁ In₂ Graph Out₁ Out₂)
    (hoverlap : ProcTwoPendingOverlap historyFalse historyTrue)
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      In₁ In₂ Out₁ Out₂)
    (start : ∀ anchor, (base anchor).State)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₁ In₂ Out₁)
    (hwin : ∀ anchor env,
      (finiteCrossAnchorRestartFamily base start anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy
            (if anchor then historyTrue else historyFalse)) env)) :
    FiniteCrossAnchorPairTable base start :=
  finiteCrossAnchorPairTableTwoOfViewEq strategy
    (fun anchor ↦ if anchor then historyTrue else historyFalse)
    hoverlap.view_eq base start receiver (by
      intro anchor env
      exact hwin anchor env)

/-! ## Prefix-pinned constructors -/

/-- View-equality form of the first-two-record construction for a blind
process-one sender. -/
noncomputable def finiteCrossAnchorFirstTwoTableOneOfViewEq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.one (history false) =
      currentView Proc.one (history true))
    (base : Bool → BlockRecordMonitor.{v, u, y, x, w}
      In₂ In₁ Out₂ Out₁)
    (start : ∀ anchor, (base anchor).State)
    (firstAllowed : ∀ anchor,
      RealizedBlockRound In₂ In₁ Out₂ Out₁ → Bool)
    (secondAllowed : ∀ anchor,
      RealizedBlockRound In₂ In₁ Out₂ Out₁ →
        RealizedBlockRound In₂ In₁ Out₂ Out₁ → Bool)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₂ In₁ Out₂)
    (hbase : ∀ anchor env,
      (finiteCrossAnchorRestartFamily base start anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history anchor)) env))
    (hfirst : ∀ anchor env,
      firstAllowed anchor
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history anchor)) env 0) = true)
    (hsecond : ∀ anchor env,
      secondAllowed anchor
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history anchor)) env 0)
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history anchor)) env 1) = true) :
    FiniteCrossAnchorFirstTwoTable base start firstAllowed secondAllowed := by
  let sender := blockSenderOne strategy (history false)
  apply finiteCrossAnchorFirstTwoTable base start firstAllowed secondAllowed
    receiver sender
  · intro anchor env
    cases anchor with
    | false => exact hbase false env
    | true =>
        change (finiteCrossAnchorRestartFamily base start true).WinsPlay
          (pairPlay (receiver true)
            (blockSenderOne strategy (history false)) env)
        rw [blockSenderOne_eq_of_view_eq strategy hview]
        exact hbase true env
  · intro anchor env
    cases anchor with
    | false => exact hfirst false env
    | true =>
        change firstAllowed true
          (pairPlay (receiver true)
            (blockSenderOne strategy (history false)) env 0) = true
        rw [blockSenderOne_eq_of_view_eq strategy hview]
        exact hfirst true env
  · intro anchor env
    cases anchor with
    | false => exact hsecond false env
    | true =>
        change secondAllowed true
          (pairPlay (receiver true)
            (blockSenderOne strategy (history false)) env 0)
          (pairPlay (receiver true)
            (blockSenderOne strategy (history false)) env 1) = true
        rw [blockSenderOne_eq_of_view_eq strategy hview]
        exact hsecond true env

/-- Process-two mirror of prefix-pinned simultaneous preselection. -/
noncomputable def finiteCrossAnchorFirstTwoTableTwoOfViewEq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.two (history false) =
      currentView Proc.two (history true))
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      In₁ In₂ Out₁ Out₂)
    (start : ∀ anchor, (base anchor).State)
    (firstAllowed : ∀ anchor,
      RealizedBlockRound In₁ In₂ Out₁ Out₂ → Bool)
    (secondAllowed : ∀ anchor,
      RealizedBlockRound In₁ In₂ Out₁ Out₂ →
        RealizedBlockRound In₁ In₂ Out₁ Out₂ → Bool)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₁ In₂ Out₁)
    (hbase : ∀ anchor env,
      (finiteCrossAnchorRestartFamily base start anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history anchor)) env))
    (hfirst : ∀ anchor env,
      firstAllowed anchor
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history anchor)) env 0) = true)
    (hsecond : ∀ anchor env,
      secondAllowed anchor
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history anchor)) env 0)
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history anchor)) env 1) = true) :
    FiniteCrossAnchorFirstTwoTable base start firstAllowed secondAllowed := by
  let sender := blockSenderTwo strategy (history false)
  apply finiteCrossAnchorFirstTwoTable base start firstAllowed secondAllowed
    receiver sender
  · intro anchor env
    cases anchor with
    | false => exact hbase false env
    | true =>
        change (finiteCrossAnchorRestartFamily base start true).WinsPlay
          (pairPlay (receiver true)
            (blockSenderTwo strategy (history false)) env)
        rw [blockSenderTwo_eq_of_view_eq strategy hview]
        exact hbase true env
  · intro anchor env
    cases anchor with
    | false => exact hfirst false env
    | true =>
        change firstAllowed true
          (pairPlay (receiver true)
            (blockSenderTwo strategy (history false)) env 0) = true
        rw [blockSenderTwo_eq_of_view_eq strategy hview]
        exact hfirst true env
  · intro anchor env
    cases anchor with
    | false => exact hsecond false env
    | true =>
        change secondAllowed true
          (pairPlay (receiver true)
            (blockSenderTwo strategy (history false)) env 0)
          (pairPlay (receiver true)
            (blockSenderTwo strategy (history false)) env 1) = true
        rw [blockSenderTwo_eq_of_view_eq strategy hview]
        exact hsecond true env

/-- Pending-overlap specialization of the process-one prefix-pinned table. -/
noncomputable def finiteCrossAnchorFirstTwoTableOneOfPendingOverlap
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (historyFalse historyTrue : History In₁ In₂ Graph Out₁ Out₂)
    (hoverlap : ProcOnePendingOverlap historyFalse historyTrue)
    (base : Bool → BlockRecordMonitor.{v, u, y, x, w}
      In₂ In₁ Out₂ Out₁)
    (start : ∀ anchor, (base anchor).State)
    (firstAllowed : ∀ anchor,
      RealizedBlockRound In₂ In₁ Out₂ Out₁ → Bool)
    (secondAllowed : ∀ anchor,
      RealizedBlockRound In₂ In₁ Out₂ Out₁ →
        RealizedBlockRound In₂ In₁ Out₂ Out₁ → Bool)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₂ In₁ Out₂)
    (hbase : ∀ anchor env,
      (finiteCrossAnchorRestartFamily base start anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy
            (if anchor then historyTrue else historyFalse)) env))
    (hfirst : ∀ anchor env,
      firstAllowed anchor
        (pairPlay (receiver anchor)
          (blockSenderOne strategy
            (if anchor then historyTrue else historyFalse)) env 0) = true)
    (hsecond : ∀ anchor env,
      secondAllowed anchor
        (pairPlay (receiver anchor)
          (blockSenderOne strategy
            (if anchor then historyTrue else historyFalse)) env 0)
        (pairPlay (receiver anchor)
          (blockSenderOne strategy
            (if anchor then historyTrue else historyFalse)) env 1) = true) :
    FiniteCrossAnchorFirstTwoTable base start firstAllowed secondAllowed :=
  finiteCrossAnchorFirstTwoTableOneOfViewEq strategy
    (fun anchor ↦ if anchor then historyTrue else historyFalse)
    hoverlap.view_eq base start firstAllowed secondAllowed receiver hbase hfirst
      hsecond

/-- Process-two pending-overlap specialization. -/
noncomputable def finiteCrossAnchorFirstTwoTableTwoOfPendingOverlap
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (historyFalse historyTrue : History In₁ In₂ Graph Out₁ Out₂)
    (hoverlap : ProcTwoPendingOverlap historyFalse historyTrue)
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      In₁ In₂ Out₁ Out₂)
    (start : ∀ anchor, (base anchor).State)
    (firstAllowed : ∀ anchor,
      RealizedBlockRound In₁ In₂ Out₁ Out₂ → Bool)
    (secondAllowed : ∀ anchor,
      RealizedBlockRound In₁ In₂ Out₁ Out₂ →
        RealizedBlockRound In₁ In₂ Out₁ Out₂ → Bool)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₁ In₂ Out₁)
    (hbase : ∀ anchor env,
      (finiteCrossAnchorRestartFamily base start anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy
            (if anchor then historyTrue else historyFalse)) env))
    (hfirst : ∀ anchor env,
      firstAllowed anchor
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy
            (if anchor then historyTrue else historyFalse)) env 0) = true)
    (hsecond : ∀ anchor env,
      secondAllowed anchor
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy
            (if anchor then historyTrue else historyFalse)) env 0)
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy
            (if anchor then historyTrue else historyFalse)) env 1) = true) :
    FiniteCrossAnchorFirstTwoTable base start firstAllowed secondAllowed :=
  finiteCrossAnchorFirstTwoTableTwoOfViewEq strategy
    (fun anchor ↦ if anchor then historyTrue else historyFalse)
    hoverlap.view_eq base start firstAllowed secondAllowed receiver hbase hfirst
      hsecond

/-! ## The all-future dangerous-pair law -/

omit [Inhabited Out₁] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₂] in
/-- Once preselected, the two process-one anchor interpretations emit the
same blind output after every finite no-receive input history. -/
theorem finiteCrossAnchorFirstTwoTableOne_pending_sender_step_eq
    {base : Bool → BlockRecordMonitor.{v, u, y, x, w}
      In₂ In₁ Out₂ Out₁}
    {start : ∀ anchor, (base anchor).State}
    {firstAllowed : ∀ anchor,
      RealizedBlockRound In₂ In₁ Out₂ Out₁ → Bool}
    {secondAllowed : ∀ anchor,
      RealizedBlockRound In₂ In₁ Out₂ Out₁ →
        RealizedBlockRound In₂ In₁ Out₂ Out₁ → Bool}
    (table : FiniteCrossAnchorFirstTwoTable base start firstAllowed
      secondAllowed) (past : List In₁) (input : In₁) :
    ((table.memberController false).labeledTree past).1 input =
      ((table.memberController true).labeledTree past).1 input := by
  rw [table.memberController_sender_eq false true past]

omit [Inhabited Out₂] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] in
/-- Process-two mirror. -/
theorem finiteCrossAnchorFirstTwoTableTwo_pending_sender_step_eq
    {base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      In₁ In₂ Out₁ Out₂}
    {start : ∀ anchor, (base anchor).State}
    {firstAllowed : ∀ anchor,
      RealizedBlockRound In₁ In₂ Out₁ Out₂ → Bool}
    {secondAllowed : ∀ anchor,
      RealizedBlockRound In₁ In₂ Out₁ Out₂ →
        RealizedBlockRound In₁ In₂ Out₁ Out₂ → Bool}
    (table : FiniteCrossAnchorFirstTwoTable base start firstAllowed
      secondAllowed) (past : List In₂) (input : In₂) :
    ((table.memberController false).labeledTree past).1 input =
      ((table.memberController true).labeledTree past).1 input := by
  rw [table.memberController_sender_eq false true past]

end

end DetParityAutomaton

end DistributedSynthesis
