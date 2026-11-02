/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorHeterogeneousPreselection

/-!
# Heterogeneous preselection with a pinned unused coordinate

The ordinary heterogeneous product receiver fills the coordinate ignored by
the current monitor with an arbitrary default.  That is sufficient for
acceptance, but it is insufficient when a later finite stage reads the
ignored coordinate as semantic data.

This file records the smallest positive repair.  On the `false` member the
first-record predicate additionally pins the unused `true` coordinate to the
root value of the true receiver.  The semantic witness runs both receiver
strategies in parallel, so the strengthened table exists under exactly the
same two monitor-realizability and shared-sender hypotheses as the ordinary
heterogeneous table.  No cross-history equality or leader information is
used.
-/

namespace DistributedSynthesis

universe u v x₀ x₁ y w

noncomputable section

variable {RIn : Type u} {SIn : Type v}
variable {ROut₀ : Type x₀} {ROut₁ : Type x₁} {SOut : Type y}
variable [Inhabited RIn] [Inhabited SIn]
variable [Inhabited ROut₀] [Inhabited ROut₁]
variable [Fintype RIn] [Fintype SIn]
variable [Fintype ROut₀] [Fintype ROut₁] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

/-- Run both semantic receivers in the product, independently of which
monitor projection is currently selected.  The hidden Boolean still affects
only the proof-side monitor; it is not an argument of either receiver. -/
def finiteCrossAnchorHeterogeneousCoupledReceiver
    (falseReceiver : ReceiverBlockStrategy RIn SIn ROut₀)
    (trueReceiver : ReceiverBlockStrategy RIn SIn ROut₁) :
    ∀ _anchor : Bool, ReceiverBlockStrategy RIn SIn (ROut₀ × ROut₁) :=
  fun _ past input =>
    (falseReceiver past input, trueReceiver past input)

/-- The ordinary heterogeneous first-record law, strengthened only on the
false member by fixing the otherwise ignored true coordinate to the true
receiver's root output at the same input. -/
noncomputable def finiteCrossAnchorHeterogeneousFalsePinnedFirstAllowed
    (falseAllowed : RealizedBlockRound RIn SIn ROut₀ SOut → Bool)
    (trueAllowed : RealizedBlockRound RIn SIn ROut₁ SOut → Bool)
    (trueReceiver : ReceiverBlockStrategy RIn SIn ROut₁) :
    ∀ _anchor : Bool,
      RealizedBlockRound RIn SIn (ROut₀ × ROut₁) SOut → Bool
  | false => fun record =>
      finiteCrossAnchorHeterogeneousFirstAllowed falseAllowed trueAllowed
          false record &&
        by
          classical
          exact decide (record.2.1.2 = trueReceiver [] record.1)
  | true => finiteCrossAnchorHeterogeneousFirstAllowed falseAllowed
      trueAllowed true

omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut₀] [Inhabited ROut₁] [Fintype RIn]
    [Fintype SIn] [Fintype ROut₀] [Fintype ROut₁] [Fintype SOut] [DecidableEq RIn]
    [DecidableEq SIn] in
/-- The strengthened false predicate exposes exactly the desired unused
coordinate equality. -/
theorem finiteCrossAnchorHeterogeneousFalsePinnedFirstAllowed_eq_true_iff
    (falseAllowed : RealizedBlockRound RIn SIn ROut₀ SOut → Bool)
    (trueAllowed : RealizedBlockRound RIn SIn ROut₁ SOut → Bool)
    (trueReceiver : ReceiverBlockStrategy RIn SIn ROut₁)
    (record : RealizedBlockRound RIn SIn (ROut₀ × ROut₁) SOut) :
    finiteCrossAnchorHeterogeneousFalsePinnedFirstAllowed falseAllowed
        trueAllowed trueReceiver false record = true ↔
      falseAllowed (finiteCrossAnchorProjectReceiverRound Prod.fst record) =
          true ∧
        record.2.1.2 = trueReceiver [] record.1 := by
  classical
  simp [finiteCrossAnchorHeterogeneousFalsePinnedFirstAllowed,
    finiteCrossAnchorHeterogeneousFirstAllowed]

/-- Heterogeneous two-record preselection with the unused true coordinate of
every false first record pinned to the semantic true receiver.  Both
receivers can be evaluated at the same public input word, so the stronger
guard costs no uniformization premise. -/
noncomputable def finiteCrossAnchorHeterogeneousFalsePinnedFirstTwoTable
    (falseMonitor : BlockRecordMonitor.{u, v, x₀, y, w}
      RIn SIn ROut₀ SOut)
    (trueMonitor : BlockRecordMonitor.{u, v, x₁, y, w}
      RIn SIn ROut₁ SOut)
    (falseStart : falseMonitor.State) (trueStart : trueMonitor.State)
    (falseFirstAllowed : RealizedBlockRound RIn SIn ROut₀ SOut → Bool)
    (trueFirstAllowed : RealizedBlockRound RIn SIn ROut₁ SOut → Bool)
    (falseSecondAllowed : RealizedBlockRound RIn SIn ROut₀ SOut →
      RealizedBlockRound RIn SIn ROut₀ SOut → Bool)
    (trueSecondAllowed : RealizedBlockRound RIn SIn ROut₁ SOut →
      RealizedBlockRound RIn SIn ROut₁ SOut → Bool)
    (falseReceiver : ReceiverBlockStrategy RIn SIn ROut₀)
    (trueReceiver : ReceiverBlockStrategy RIn SIn ROut₁)
    (sender : SenderBlockStrategy SIn SOut)
    (hfalse : ∀ env,
      (falseMonitor.restartAt falseStart).WinsPlay
        (pairPlay falseReceiver sender env))
    (htrue : ∀ env,
      (trueMonitor.restartAt trueStart).WinsPlay
        (pairPlay trueReceiver sender env))
    (hfalseFirst : ∀ env,
      falseFirstAllowed (pairPlay falseReceiver sender env 0) = true)
    (htrueFirst : ∀ env,
      trueFirstAllowed (pairPlay trueReceiver sender env 0) = true)
    (hfalseSecond : ∀ env,
      falseSecondAllowed (pairPlay falseReceiver sender env 0)
        (pairPlay falseReceiver sender env 1) = true)
    (htrueSecond : ∀ env,
      trueSecondAllowed (pairPlay trueReceiver sender env 0)
        (pairPlay trueReceiver sender env 1) = true) :
    FiniteCrossAnchorFirstTwoTable
      (finiteCrossAnchorHeterogeneousMonitor falseMonitor trueMonitor)
      (finiteCrossAnchorHeterogeneousStart falseMonitor trueMonitor
        falseStart trueStart)
      (finiteCrossAnchorHeterogeneousFalsePinnedFirstAllowed falseFirstAllowed
        trueFirstAllowed trueReceiver)
      (finiteCrossAnchorHeterogeneousSecondAllowed falseSecondAllowed
        trueSecondAllowed) := by
  let base := finiteCrossAnchorHeterogeneousMonitor falseMonitor trueMonitor
  let start := finiteCrossAnchorHeterogeneousStart falseMonitor trueMonitor
    falseStart trueStart
  let firstAllowed := finiteCrossAnchorHeterogeneousFalsePinnedFirstAllowed
    falseFirstAllowed trueFirstAllowed trueReceiver
  let secondAllowed := finiteCrossAnchorHeterogeneousSecondAllowed
    falseSecondAllowed trueSecondAllowed
  let receiver := finiteCrossAnchorHeterogeneousCoupledReceiver falseReceiver
    trueReceiver
  apply finiteCrossAnchorFirstTwoTable base start firstAllowed secondAllowed
    receiver sender
  · intro anchor env
    cases anchor with
    | false =>
        apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
          (falseMonitor.restartAt falseStart) Prod.fst _).mpr
        simpa [base, start, receiver,
          finiteCrossAnchorHeterogeneousMonitor,
          finiteCrossAnchorHeterogeneousStart,
          finiteCrossAnchorHeterogeneousCoupledReceiver,
          BlockRecordMonitor.projectReceiverPlay] using hfalse env
    | true =>
        apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
          (trueMonitor.restartAt trueStart) Prod.snd _).mpr
        simpa [base, start, receiver,
          finiteCrossAnchorHeterogeneousMonitor,
          finiteCrossAnchorHeterogeneousStart,
          finiteCrossAnchorHeterogeneousCoupledReceiver,
          BlockRecordMonitor.projectReceiverPlay] using htrue env
  · intro anchor env
    cases anchor with
    | false =>
        classical
        simpa [firstAllowed, receiver,
          finiteCrossAnchorHeterogeneousFalsePinnedFirstAllowed,
          finiteCrossAnchorHeterogeneousFirstAllowed,
          finiteCrossAnchorHeterogeneousCoupledReceiver,
          finiteCrossAnchorProjectReceiverRound, pairPlay, treePlay,
          treeOfPair, blockLabelApply, branchNode, senderWord] using
            hfalseFirst env
    | true =>
        simpa [firstAllowed, receiver,
          finiteCrossAnchorHeterogeneousFalsePinnedFirstAllowed,
          finiteCrossAnchorHeterogeneousFirstAllowed,
          finiteCrossAnchorHeterogeneousCoupledReceiver,
          finiteCrossAnchorProjectReceiverRound] using htrueFirst env
  · intro anchor env
    cases anchor with
    | false =>
        simpa [secondAllowed, receiver,
          finiteCrossAnchorHeterogeneousSecondAllowed,
          finiteCrossAnchorHeterogeneousCoupledReceiver,
          finiteCrossAnchorProjectReceiverRound] using hfalseSecond env
    | true =>
        simpa [secondAllowed, receiver,
          finiteCrossAnchorHeterogeneousSecondAllowed,
          finiteCrossAnchorHeterogeneousCoupledReceiver,
          finiteCrossAnchorProjectReceiverRound] using htrueSecond env

end

end DistributedSynthesis
