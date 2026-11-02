/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorPendingPreselection
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenClassifiedMove

/-!
# Preselection for two monitors with different receiver alphabets

The two charged-anchor obligations need not expose the same receiver output:
the old guarded controller returns a target-parametric record, while the
recurrent controller returns a policy-state-parametric record.  This file
puts both in the product output alphabet and projects each monitor back to its
own coordinate.  The blind sender is unchanged.

Consequently the heterogeneous output types are only a typing issue.  Once
the two semantic obligations are realized by the two histories of one pending
overlap, they produce one finite preselected table with a literally shared
sender transition at every future control.  The product coordinate and the
hidden Boolean are confined to the receiver/monitor side; neither is an
argument of the executable sender transition.
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

/-- Put two monitors with different receiver outputs in one product-output
family. -/
noncomputable def finiteCrossAnchorHeterogeneousMonitor
    (falseMonitor : BlockRecordMonitor.{u, v, x₀, y, w}
      RIn SIn ROut₀ SOut)
    (trueMonitor : BlockRecordMonitor.{u, v, x₁, y, w}
      RIn SIn ROut₁ SOut) :
    Bool → BlockRecordMonitor RIn SIn (ROut₀ × ROut₁) SOut
  | false => falseMonitor.comapReceiverOutput Prod.fst
  | true => trueMonitor.comapReceiverOutput Prod.snd

/-- Dependent restart states for the product-output family. -/
noncomputable def finiteCrossAnchorHeterogeneousStart
    (falseMonitor : BlockRecordMonitor.{u, v, x₀, y, w}
      RIn SIn ROut₀ SOut)
    (trueMonitor : BlockRecordMonitor.{u, v, x₁, y, w}
      RIn SIn ROut₁ SOut)
    (falseStart : falseMonitor.State) (trueStart : trueMonitor.State) :
    ∀ anchor,
      (finiteCrossAnchorHeterogeneousMonitor falseMonitor trueMonitor
        anchor).State
  | false => falseStart
  | true => trueStart

/-- Lift the two semantic receivers to the common product alphabet.  The
unused coordinate is an arbitrary default and is erased by the corresponding
monitor projection. -/
noncomputable def finiteCrossAnchorHeterogeneousReceiver
    (falseReceiver : ReceiverBlockStrategy RIn SIn ROut₀)
    (trueReceiver : ReceiverBlockStrategy RIn SIn ROut₁) :
    ∀ _anchor : Bool, ReceiverBlockStrategy RIn SIn (ROut₀ × ROut₁)
  | false => fun past input => (falseReceiver past input, default)
  | true => fun past input => (default, trueReceiver past input)

/-- The two heterogeneous restarted obligations can be narrowed
simultaneously whenever one semantic sender realizes both of them. -/
noncomputable def finiteCrossAnchorHeterogeneousPairTable
    (falseMonitor : BlockRecordMonitor.{u, v, x₀, y, w}
      RIn SIn ROut₀ SOut)
    (trueMonitor : BlockRecordMonitor.{u, v, x₁, y, w}
      RIn SIn ROut₁ SOut)
    (falseStart : falseMonitor.State) (trueStart : trueMonitor.State)
    (falseReceiver : ReceiverBlockStrategy RIn SIn ROut₀)
    (trueReceiver : ReceiverBlockStrategy RIn SIn ROut₁)
    (sender : SenderBlockStrategy SIn SOut)
    (hfalse : ∀ env,
      (falseMonitor.restartAt falseStart).WinsPlay
        (pairPlay falseReceiver sender env))
    (htrue : ∀ env,
      (trueMonitor.restartAt trueStart).WinsPlay
        (pairPlay trueReceiver sender env)) :
    FiniteCrossAnchorPairTable
      (finiteCrossAnchorHeterogeneousMonitor falseMonitor trueMonitor)
      (finiteCrossAnchorHeterogeneousStart falseMonitor trueMonitor
        falseStart trueStart) := by
  let base := finiteCrossAnchorHeterogeneousMonitor falseMonitor trueMonitor
  let start := finiteCrossAnchorHeterogeneousStart falseMonitor trueMonitor
    falseStart trueStart
  let receiver := finiteCrossAnchorHeterogeneousReceiver falseReceiver
    trueReceiver
  apply finiteCrossAnchorPairTable base start receiver sender
  intro anchor env
  cases anchor with
  | false =>
      apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
        (falseMonitor.restartAt falseStart) Prod.fst _).mpr
      simpa [base, start, receiver,
        finiteCrossAnchorHeterogeneousMonitor,
        finiteCrossAnchorHeterogeneousStart,
        finiteCrossAnchorHeterogeneousReceiver,
        BlockRecordMonitor.projectReceiverPlay] using hfalse env
  | true =>
      apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
        (trueMonitor.restartAt trueStart) Prod.snd _).mpr
      simpa [base, start, receiver,
        finiteCrossAnchorHeterogeneousMonitor,
        finiteCrossAnchorHeterogeneousStart,
        finiteCrossAnchorHeterogeneousReceiver,
        BlockRecordMonitor.projectReceiverPlay] using htrue env

/-! ## Prefix-pinned heterogeneous tables -/

/-- Project one product-output record to the receiver alphabet of one member. -/
def finiteCrossAnchorProjectReceiverRound
    {ROut : Type x₀} {ROut' : Type x₁}
    (project : ROut' → ROut)
    (record : RealizedBlockRound RIn SIn ROut' SOut) :
    RealizedBlockRound RIn SIn ROut SOut :=
  (record.1, project record.2.1, record.2.2)

/-- Lift the two first-record predicates to the common product alphabet. -/
def finiteCrossAnchorHeterogeneousFirstAllowed
    (falseAllowed : RealizedBlockRound RIn SIn ROut₀ SOut → Bool)
    (trueAllowed : RealizedBlockRound RIn SIn ROut₁ SOut → Bool) :
    ∀ _anchor : Bool,
      RealizedBlockRound RIn SIn (ROut₀ × ROut₁) SOut → Bool
  | false => fun record ↦ falseAllowed
      (finiteCrossAnchorProjectReceiverRound Prod.fst record)
  | true => fun record ↦ trueAllowed
      (finiteCrossAnchorProjectReceiverRound Prod.snd record)

/-- Lift the two second-record predicates. -/
def finiteCrossAnchorHeterogeneousSecondAllowed
    (falseAllowed : RealizedBlockRound RIn SIn ROut₀ SOut →
      RealizedBlockRound RIn SIn ROut₀ SOut → Bool)
    (trueAllowed : RealizedBlockRound RIn SIn ROut₁ SOut →
      RealizedBlockRound RIn SIn ROut₁ SOut → Bool) :
    ∀ _anchor : Bool,
      RealizedBlockRound RIn SIn (ROut₀ × ROut₁) SOut →
        RealizedBlockRound RIn SIn (ROut₀ × ROut₁) SOut → Bool
  | false => fun first second ↦ falseAllowed
      (finiteCrossAnchorProjectReceiverRound Prod.fst first)
      (finiteCrossAnchorProjectReceiverRound Prod.fst second)
  | true => fun first second ↦ trueAllowed
      (finiteCrossAnchorProjectReceiverRound Prod.snd first)
      (finiteCrossAnchorProjectReceiverRound Prod.snd second)

/-- Heterogeneous, prefix-pinned simultaneous narrowing.  This is the exact
typing bridge used at the charged seam: both semantic blocks keep their own
monitor and their own two physical prefix laws, while the extracted sender
table is one shared finite transition system. -/
noncomputable def finiteCrossAnchorHeterogeneousFirstTwoTable
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
      (finiteCrossAnchorHeterogeneousFirstAllowed falseFirstAllowed
        trueFirstAllowed)
      (finiteCrossAnchorHeterogeneousSecondAllowed falseSecondAllowed
        trueSecondAllowed) := by
  let base := finiteCrossAnchorHeterogeneousMonitor falseMonitor trueMonitor
  let start := finiteCrossAnchorHeterogeneousStart falseMonitor trueMonitor
    falseStart trueStart
  let firstAllowed := finiteCrossAnchorHeterogeneousFirstAllowed
    falseFirstAllowed trueFirstAllowed
  let secondAllowed := finiteCrossAnchorHeterogeneousSecondAllowed
    falseSecondAllowed trueSecondAllowed
  let receiver := finiteCrossAnchorHeterogeneousReceiver falseReceiver
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
          finiteCrossAnchorHeterogeneousReceiver,
          BlockRecordMonitor.projectReceiverPlay] using hfalse env
    | true =>
        apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
          (trueMonitor.restartAt trueStart) Prod.snd _).mpr
        simpa [base, start, receiver,
          finiteCrossAnchorHeterogeneousMonitor,
          finiteCrossAnchorHeterogeneousStart,
          finiteCrossAnchorHeterogeneousReceiver,
          BlockRecordMonitor.projectReceiverPlay] using htrue env
  · intro anchor env
    cases anchor with
    | false =>
        simpa [firstAllowed, receiver,
          finiteCrossAnchorHeterogeneousFirstAllowed,
          finiteCrossAnchorHeterogeneousReceiver,
          finiteCrossAnchorProjectReceiverRound] using hfalseFirst env
    | true =>
        simpa [firstAllowed, receiver,
          finiteCrossAnchorHeterogeneousFirstAllowed,
          finiteCrossAnchorHeterogeneousReceiver,
          finiteCrossAnchorProjectReceiverRound] using htrueFirst env
  · intro anchor env
    cases anchor with
    | false =>
        simpa [secondAllowed, receiver,
          finiteCrossAnchorHeterogeneousSecondAllowed,
          finiteCrossAnchorHeterogeneousReceiver,
          finiteCrossAnchorProjectReceiverRound] using hfalseSecond env
    | true =>
        simpa [secondAllowed, receiver,
          finiteCrossAnchorHeterogeneousSecondAllowed,
          finiteCrossAnchorHeterogeneousReceiver,
          finiteCrossAnchorProjectReceiverRound] using htrueSecond env

namespace DetParityAutomaton

universe a b c d

variable {In₁ : Type a} {In₂ : Type b} {Out₁ : Type c} {Out₂ : Type d}
variable [Inhabited In₁] [Inhabited In₂]
variable [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂]
variable [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Model-facing process-one form.  Its only semantic compatibility premise is
the genuine pending overlap between the old and staged anchor histories. -/
noncomputable def finiteCrossAnchorHeterogeneousPairTableOneOfPendingOverlap
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (historyFalse historyTrue : History In₁ In₂ Graph Out₁ Out₂)
    (hoverlap : ProcOnePendingOverlap historyFalse historyTrue)
    (falseMonitor : BlockRecordMonitor.{b, a, x₀, c, w}
      In₂ In₁ ROut₀ Out₁)
    (trueMonitor : BlockRecordMonitor.{b, a, x₁, c, w}
      In₂ In₁ ROut₁ Out₁)
    (falseStart : falseMonitor.State) (trueStart : trueMonitor.State)
    (falseReceiver : ReceiverBlockStrategy In₂ In₁ ROut₀)
    (trueReceiver : ReceiverBlockStrategy In₂ In₁ ROut₁)
    (hfalse : ∀ env,
      (falseMonitor.restartAt falseStart).WinsPlay
        (pairPlay falseReceiver (blockSenderOne strategy historyFalse) env))
    (htrue : ∀ env,
      (trueMonitor.restartAt trueStart).WinsPlay
        (pairPlay trueReceiver (blockSenderOne strategy historyTrue) env)) :
    FiniteCrossAnchorPairTable
      (finiteCrossAnchorHeterogeneousMonitor falseMonitor trueMonitor)
      (finiteCrossAnchorHeterogeneousStart falseMonitor trueMonitor
        falseStart trueStart) := by
  apply finiteCrossAnchorHeterogeneousPairTable falseMonitor trueMonitor
    falseStart trueStart falseReceiver trueReceiver
    (blockSenderOne strategy historyFalse) hfalse
  intro env
  rw [blockSenderOne_eq_of_view_eq strategy hoverlap.view_eq]
  exact htrue env

/-- Process-two mirror. -/
noncomputable def finiteCrossAnchorHeterogeneousPairTableTwoOfPendingOverlap
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (historyFalse historyTrue : History In₁ In₂ Graph Out₁ Out₂)
    (hoverlap : ProcTwoPendingOverlap historyFalse historyTrue)
    (falseMonitor : BlockRecordMonitor.{a, b, x₀, d, w}
      In₁ In₂ ROut₀ Out₂)
    (trueMonitor : BlockRecordMonitor.{a, b, x₁, d, w}
      In₁ In₂ ROut₁ Out₂)
    (falseStart : falseMonitor.State) (trueStart : trueMonitor.State)
    (falseReceiver : ReceiverBlockStrategy In₁ In₂ ROut₀)
    (trueReceiver : ReceiverBlockStrategy In₁ In₂ ROut₁)
    (hfalse : ∀ env,
      (falseMonitor.restartAt falseStart).WinsPlay
        (pairPlay falseReceiver (blockSenderTwo strategy historyFalse) env))
    (htrue : ∀ env,
      (trueMonitor.restartAt trueStart).WinsPlay
        (pairPlay trueReceiver (blockSenderTwo strategy historyTrue) env)) :
    FiniteCrossAnchorPairTable
      (finiteCrossAnchorHeterogeneousMonitor falseMonitor trueMonitor)
      (finiteCrossAnchorHeterogeneousStart falseMonitor trueMonitor
        falseStart trueStart) := by
  apply finiteCrossAnchorHeterogeneousPairTable falseMonitor trueMonitor
    falseStart trueStart falseReceiver trueReceiver
    (blockSenderTwo strategy historyFalse) hfalse
  intro env
  rw [blockSenderTwo_eq_of_view_eq strategy hoverlap.view_eq]
  exact htrue env

/-! ## Prefix-pinned pending-overlap wrappers -/

/-- Process-one pending-overlap form of the heterogeneous two-record table.
The two monitors and receivers retain their different output alphabets and
their own prefix laws.  Only the blind sender is identified, using the
genuine local-view equality carried by the pending overlap. -/
noncomputable def
    finiteCrossAnchorHeterogeneousFirstTwoTableOneOfPendingOverlap
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (historyFalse historyTrue : History In₁ In₂ Graph Out₁ Out₂)
    (hoverlap : ProcOnePendingOverlap historyFalse historyTrue)
    (falseMonitor : BlockRecordMonitor.{b, a, x₀, c, w}
      In₂ In₁ ROut₀ Out₁)
    (trueMonitor : BlockRecordMonitor.{b, a, x₁, c, w}
      In₂ In₁ ROut₁ Out₁)
    (falseStart : falseMonitor.State) (trueStart : trueMonitor.State)
    (falseFirstAllowed :
      RealizedBlockRound In₂ In₁ ROut₀ Out₁ → Bool)
    (trueFirstAllowed :
      RealizedBlockRound In₂ In₁ ROut₁ Out₁ → Bool)
    (falseSecondAllowed : RealizedBlockRound In₂ In₁ ROut₀ Out₁ →
      RealizedBlockRound In₂ In₁ ROut₀ Out₁ → Bool)
    (trueSecondAllowed : RealizedBlockRound In₂ In₁ ROut₁ Out₁ →
      RealizedBlockRound In₂ In₁ ROut₁ Out₁ → Bool)
    (falseReceiver : ReceiverBlockStrategy In₂ In₁ ROut₀)
    (trueReceiver : ReceiverBlockStrategy In₂ In₁ ROut₁)
    (hfalse : ∀ env,
      (falseMonitor.restartAt falseStart).WinsPlay
        (pairPlay falseReceiver (blockSenderOne strategy historyFalse) env))
    (htrue : ∀ env,
      (trueMonitor.restartAt trueStart).WinsPlay
        (pairPlay trueReceiver (blockSenderOne strategy historyTrue) env))
    (hfalseFirst : ∀ env,
      falseFirstAllowed
        (pairPlay falseReceiver (blockSenderOne strategy historyFalse) env 0) =
          true)
    (htrueFirst : ∀ env,
      trueFirstAllowed
        (pairPlay trueReceiver (blockSenderOne strategy historyTrue) env 0) =
          true)
    (hfalseSecond : ∀ env,
      falseSecondAllowed
        (pairPlay falseReceiver (blockSenderOne strategy historyFalse) env 0)
        (pairPlay falseReceiver (blockSenderOne strategy historyFalse) env 1) =
          true)
    (htrueSecond : ∀ env,
      trueSecondAllowed
        (pairPlay trueReceiver (blockSenderOne strategy historyTrue) env 0)
        (pairPlay trueReceiver (blockSenderOne strategy historyTrue) env 1) =
          true) :
    FiniteCrossAnchorFirstTwoTable
      (finiteCrossAnchorHeterogeneousMonitor falseMonitor trueMonitor)
      (finiteCrossAnchorHeterogeneousStart falseMonitor trueMonitor
        falseStart trueStart)
      (finiteCrossAnchorHeterogeneousFirstAllowed falseFirstAllowed
        trueFirstAllowed)
      (finiteCrossAnchorHeterogeneousSecondAllowed falseSecondAllowed
        trueSecondAllowed) := by
  apply finiteCrossAnchorHeterogeneousFirstTwoTable falseMonitor trueMonitor
    falseStart trueStart falseFirstAllowed trueFirstAllowed
    falseSecondAllowed trueSecondAllowed falseReceiver trueReceiver
    (blockSenderOne strategy historyFalse) hfalse
  · intro env
    rw [blockSenderOne_eq_of_view_eq strategy hoverlap.view_eq]
    exact htrue env
  · exact hfalseFirst
  · intro env
    rw [blockSenderOne_eq_of_view_eq strategy hoverlap.view_eq]
    exact htrueFirst env
  · exact hfalseSecond
  · intro env
    rw [blockSenderOne_eq_of_view_eq strategy hoverlap.view_eq]
    exact htrueSecond env

/-- Process-two mirror of
`finiteCrossAnchorHeterogeneousFirstTwoTableOneOfPendingOverlap`. -/
noncomputable def
    finiteCrossAnchorHeterogeneousFirstTwoTableTwoOfPendingOverlap
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (historyFalse historyTrue : History In₁ In₂ Graph Out₁ Out₂)
    (hoverlap : ProcTwoPendingOverlap historyFalse historyTrue)
    (falseMonitor : BlockRecordMonitor.{a, b, x₀, d, w}
      In₁ In₂ ROut₀ Out₂)
    (trueMonitor : BlockRecordMonitor.{a, b, x₁, d, w}
      In₁ In₂ ROut₁ Out₂)
    (falseStart : falseMonitor.State) (trueStart : trueMonitor.State)
    (falseFirstAllowed :
      RealizedBlockRound In₁ In₂ ROut₀ Out₂ → Bool)
    (trueFirstAllowed :
      RealizedBlockRound In₁ In₂ ROut₁ Out₂ → Bool)
    (falseSecondAllowed : RealizedBlockRound In₁ In₂ ROut₀ Out₂ →
      RealizedBlockRound In₁ In₂ ROut₀ Out₂ → Bool)
    (trueSecondAllowed : RealizedBlockRound In₁ In₂ ROut₁ Out₂ →
      RealizedBlockRound In₁ In₂ ROut₁ Out₂ → Bool)
    (falseReceiver : ReceiverBlockStrategy In₁ In₂ ROut₀)
    (trueReceiver : ReceiverBlockStrategy In₁ In₂ ROut₁)
    (hfalse : ∀ env,
      (falseMonitor.restartAt falseStart).WinsPlay
        (pairPlay falseReceiver (blockSenderTwo strategy historyFalse) env))
    (htrue : ∀ env,
      (trueMonitor.restartAt trueStart).WinsPlay
        (pairPlay trueReceiver (blockSenderTwo strategy historyTrue) env))
    (hfalseFirst : ∀ env,
      falseFirstAllowed
        (pairPlay falseReceiver (blockSenderTwo strategy historyFalse) env 0) =
          true)
    (htrueFirst : ∀ env,
      trueFirstAllowed
        (pairPlay trueReceiver (blockSenderTwo strategy historyTrue) env 0) =
          true)
    (hfalseSecond : ∀ env,
      falseSecondAllowed
        (pairPlay falseReceiver (blockSenderTwo strategy historyFalse) env 0)
        (pairPlay falseReceiver (blockSenderTwo strategy historyFalse) env 1) =
          true)
    (htrueSecond : ∀ env,
      trueSecondAllowed
        (pairPlay trueReceiver (blockSenderTwo strategy historyTrue) env 0)
        (pairPlay trueReceiver (blockSenderTwo strategy historyTrue) env 1) =
          true) :
    FiniteCrossAnchorFirstTwoTable
      (finiteCrossAnchorHeterogeneousMonitor falseMonitor trueMonitor)
      (finiteCrossAnchorHeterogeneousStart falseMonitor trueMonitor
        falseStart trueStart)
      (finiteCrossAnchorHeterogeneousFirstAllowed falseFirstAllowed
        trueFirstAllowed)
      (finiteCrossAnchorHeterogeneousSecondAllowed falseSecondAllowed
        trueSecondAllowed) := by
  apply finiteCrossAnchorHeterogeneousFirstTwoTable falseMonitor trueMonitor
    falseStart trueStart falseFirstAllowed trueFirstAllowed
    falseSecondAllowed trueSecondAllowed falseReceiver trueReceiver
    (blockSenderTwo strategy historyFalse) hfalse
  · intro env
    rw [blockSenderTwo_eq_of_view_eq strategy hoverlap.view_eq]
    exact htrue env
  · exact hfalseFirst
  · intro env
    rw [blockSenderTwo_eq_of_view_eq strategy hoverlap.view_eq]
    exact htrueFirst env
  · exact hfalseSecond
  · intro env
    rw [blockSenderTwo_eq_of_view_eq strategy hoverlap.view_eq]
    exact htrueSecond env

end DetParityAutomaton

end

end DistributedSynthesis
