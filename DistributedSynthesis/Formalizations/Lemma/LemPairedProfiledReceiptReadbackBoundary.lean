/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemReadbackUpgradeQuantifierAudit
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyReceiveActivation

/-!
# Receipt-carrier readback boundary

The shape-free candidate table is a finite proof object, but its exact cursor
is not local run-time data.  The closest existing executable carrier is the
receipt-tagged family automaton: its two finite summaries are updated only by
the corresponding local observation, and its receive transition is one joint
graph-blind table.

This file records the exact final adapter into the already proved existential
readback bridge.  The premise is intentionally an all-environment theorem for
the concrete receipt carrier.  A candidate-table branch theorem, projected
class readout, or acceptance by the hidden-policy monitor does not satisfy it.
In particular, neither output projection receives a graph, orientation,
strict-leader flag, or a permanently hidden bit.
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

/-- The process-one output already stored in the executable receipt carrier.
The locally observable receipt tag is not inspected. -/
def endToEndFamilyReceiptOutputOne
    (package : PairedInitialProfiledRationalPackage A) :
    EndToEndFamilyReceiptOneSummary A package → Out₁ :=
  fun summary ↦ summary.1.2

/-- Process-two mirror. -/
def endToEndFamilyReceiptOutputTwo
    (package : PairedInitialProfiledRationalPackage A) :
    EndToEndFamilyReceiptTwoSummary A package → Out₂ :=
  fun summary ↦ summary.1.2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- An all-environment winning realization by the concrete receipt carrier is
exactly sufficient for the strategy-indexed readback endpoint.  This is the
smallest honest adapter after the local family-controller construction: the
remaining mathematical theorem must establish the premise, uniformly over
the graph sequence, without reading a hidden side or leader bit. -/
theorem perStrategyWinningReadback_of_endToEndFamilyReceipt
    (fallback : LocalSummaryAutomaton.{u, v, max 1 u v x y s} In₁ In₂)
    (hextract :
      ∀ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        (∀ environment : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy environment)) →
        ∃ (package : PairedInitialProfiledRationalPackage A)
          (initialOne : EndToEndFamilyReceiptOneSummary A package)
          (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
          (receive : EndToEndFamilyReceiptReceivePairTable A package),
          ∀ environment : EnvironmentSequence In₁ In₂,
            A.Accepts
              (execution
                ((endToEndFamilyReceiptSummaryAutomaton A package initialOne
                    initialTwo receive).readbackStrategy
                  (endToEndFamilyReceiptOutputOne A package)
                  (endToEndFamilyReceiptOutputTwo A package))
                environment)) :
    PerStrategyWinningReadback A fallback := by
  intro strategy hstrategy
  obtain ⟨package, initialOne, initialTwo, receive, hwins⟩ :=
    hextract strategy hstrategy
  exact
    ⟨endToEndFamilyReceiptSummaryAutomaton A package initialOne initialTwo
        receive,
      endToEndFamilyReceiptOutputOne A package,
      endToEndFamilyReceiptOutputTwo A package,
      hwins⟩

end

end DetParityAutomaton

end DistributedSynthesis
