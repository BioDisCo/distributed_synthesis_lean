/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmMain
import DistributedSynthesis.Formalizations.Theorem.ThmMainCanonical
import DistributedSynthesis.Formalizations.Lemma.LemFullSynthesisFromSummaryWinner

/-!
# Full-model LTL synthesis, gated on the principled summary-observable winner certificate

`main_result_for_ltl_dpa_full_synthesis` (`ThmMain`) decides full `{←,→,↔}` LTL synthesis conditional
on the ad-hoc boundary-game `EntryIndexedCertificate`. This file gives the **principled** LTL synthesis endpoint:
it decides the same problem conditional on a fixed summary automaton `M` together with
`SummaryObservableWinnerCertificate (compiler.compile formula) M` -- the finite-summary winner
obligation stated at the game-abstraction level (`LemReadbackUpgradeReduction`).  It is a useful
principled boundary, but a checked derivation from Berwanger Theorem 10 still requires the
model-specific finite retraction/hierarchy adapter.

It is `main_result_for_ltl_dpa_full_synthesis` verbatim, except the DPA-level decidability is the
principled `dpa_full_synthesis_decidable_of_summaryObservableWinner`; the LTL correctness wrapper
(`compiler.correct`) is shared. So the full-model LTL synthesis endpoint rests provably on exactly the
finite-game-level summary-observable winner, with no ad-hoc boundary-game certificate.
-/

namespace DistributedSynthesis

universe u v x y ap

/-- **Full `{←,→,↔}` LTL synthesis decidability, gated on the summary-observable winner
certificate.**  Identical to `main_result_for_ltl_dpa_full_synthesis`, but the DPA decidability is
supplied by `dpa_full_synthesis_decidable_of_summaryObservableWinner` for a fixed summary automaton
`M` and `hcert : SummaryObservableWinnerCertificate (compiler.compile formula) M` -- the principled
finite-summary boundary -- in place of the ad-hoc `EntryIndexedCertificate`.  The LTL
compiler-correctness wrapper is shared. -/
noncomputable def main_result_for_ltl_dpa_full_synthesis_of_summaryObservableWinner
    {AP : Type ap}
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y)
    [DecidableEq AP]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, max u v x y} AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (Branch : Proc -> Type (max u v x y))
    (Label : Proc -> Type (max u v x y))
    (target :
      (d : Proc) ->
        InputFreeParityTreeAutomaton.{max u v x y, max u v x y,
          max u v x y} (Branch d) (Label d))
    (targetNonempty :
      ∀ d : Proc,
        ∃ tree : LabeledTree (Branch d) (Label d),
          (target d).acceptsTree tree)
    [DecidableEq (compiler.compile formula).State]
    (M : LocalSummaryAutomaton.{u, v, max u v x y} In₁ In₂)
    (hcert :
      DetParityAutomaton.SummaryObservableWinnerCertificate
        (compiler.compile formula) M) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies compiler.interp (execution σ env) formula) :=
  letI :
      Decidable
        (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
          ∀ env : EnvironmentSequence In₁ In₂,
            (compiler.compile formula).Accepts (execution σ env)) :=
    DetParityAutomaton.dpa_full_synthesis_decidable_of_summaryObservableWinner
      (compiler.compile formula) Branch Label target targetNonempty M hcert
  decidable_of_iff
    (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        (compiler.compile formula).Accepts (execution σ env))
    (exists_congr fun σ =>
      forall_congr' fun env =>
        compiler.correct formula (execution σ env))

/-- Full LTL synthesis from an extracted finite-state controller after its
private Moore memories have been folded into an existentially chosen summary
automaton.  This is the conclusion supplied by the dynamic-hierarchy theorem;
unlike the fixed-summary endpoint above, it does not require the controller to
be memoryless on the pre-extraction summary. -/
noncomputable def main_result_for_ltl_dpa_full_synthesis_of_existsReadbackUpgrade
    {AP : Type ap}
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y)
    [DecidableEq AP]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, max u v x y} AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (Branch : Proc -> Type (max u v x y))
    (Label : Proc -> Type (max u v x y))
    (target :
      (d : Proc) ->
        InputFreeParityTreeAutomaton.{max u v x y, max u v x y,
          max u v x y} (Branch d) (Label d))
    (targetNonempty :
      ∀ d : Proc,
        ∃ tree : LabeledTree (Branch d) (Label d),
          (target d).acceptsTree tree)
    [DecidableEq (compiler.compile formula).State]
    (hexists :
      ∃ M : LocalSummaryAutomaton.{u, v, max u v x y} In₁ In₂,
        M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) (compiler.compile formula)) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies compiler.interp (execution σ env) formula) :=
  letI :
      Decidable
        (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
          ∀ env : EnvironmentSequence In₁ In₂,
            (compiler.compile formula).Accepts (execution σ env)) :=
    DetParityAutomaton.dpa_full_synthesis_decidable_of_existsReadbackUpgrade
      (compiler.compile formula) Branch Label target targetNonempty hexists
  decidable_of_iff
    (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        (compiler.compile formula).Accepts (execution σ env))
    (exists_congr fun σ =>
      forall_congr' fun env =>
        compiler.correct formula (execution σ env))

/-- **Canonical full-model LTL synthesis, gated on the summary-observable winner certificate.**
`main_result_for_canonical_ltl_full_synthesis` with the principled certificate: the canonical
LTL→DPA compiler  discharges the compiler, and the decision is the principled
`main_result_for_ltl_dpa_full_synthesis_of_summaryObservableWinner`. -/
noncomputable def main_result_for_canonical_ltl_full_synthesis_of_summaryObservableWinner
    {AP : Type (max u v x y)}
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y)
    [DecidableEq AP]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (formula : LTL AP)
    (Branch : Proc -> Type (max u v x y))
    (Label : Proc -> Type (max u v x y))
    (target :
      (d : Proc) ->
        InputFreeParityTreeAutomaton.{max u v x y, max u v x y,
          max u v x y} (Branch d) (Label d))
    (targetNonempty :
      ∀ d : Proc,
        ∃ tree : LabeledTree (Branch d) (Label d),
          (target d).acceptsTree tree)
    [DecidableEq
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
          formula).State]
    (M : LocalSummaryAutomaton.{u, v, max u v x y} In₁ In₂)
    (hcert :
      DetParityAutomaton.SummaryObservableWinnerCertificate
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula) M) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution σ env) formula) :=
  main_result_for_ltl_dpa_full_synthesis_of_summaryObservableWinner
    In₁ In₂ Out₁ Out₂
    (PositiveLTL.canonicalLTLToDPACompiler interp dec)
    formula Branch Label target targetNonempty M hcert

/-- Canonical LTL specialization of the existential enriched-summary route. -/
noncomputable def main_result_for_canonical_ltl_full_synthesis_of_existsReadbackUpgrade
    {AP : Type (max u v x y)}
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y)
    [DecidableEq AP]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (formula : LTL AP)
    (Branch : Proc -> Type (max u v x y))
    (Label : Proc -> Type (max u v x y))
    (target :
      (d : Proc) ->
        InputFreeParityTreeAutomaton.{max u v x y, max u v x y,
          max u v x y} (Branch d) (Label d))
    (targetNonempty :
      ∀ d : Proc,
        ∃ tree : LabeledTree (Branch d) (Label d),
          (target d).acceptsTree tree)
    [DecidableEq
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
          formula).State]
    (hexists :
      ∃ M : LocalSummaryAutomaton.{u, v, max u v x y} In₁ In₂,
        M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂)
          ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution σ env) formula) :=
  main_result_for_ltl_dpa_full_synthesis_of_existsReadbackUpgrade
    In₁ In₂ Out₁ Out₂
    (PositiveLTL.canonicalLTLToDPACompiler interp dec)
    formula Branch Label target targetNonempty hexists

/-- **The full `{←,→,↔}` main theorem for finite alphabets, gated on the principled certificate.**
The exact analogue of `main_result_for_ltl_full_synthesis_finiteAlphabets`, but its *only* extra
hypothesis beyond the fragment synthesis endpoint is a fixed summary automaton `M` plus
`SummaryObservableWinnerCertificate … M` -- the finite-game-level Berwanger obligation, grounded in
the proved `prop_dynhier` -- in place of the ad-hoc `EntryIndexedCertificate`.  The canonical
compiler and the administrative trivial target are discharged identically to the fragment. -/
noncomputable def main_result_for_ltl_full_synthesis_finiteAlphabets_of_summaryObservableWinner
    {AP : Type}
    (In₁ In₂ Out₁ Out₂ : Type)
    [DecidableEq AP]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (formula : LTL AP)
    [DecidableEq
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
          formula).State]
    (M : LocalSummaryAutomaton.{0, 0, 0} In₁ In₂)
    (hcert :
      DetParityAutomaton.SummaryObservableWinnerCertificate
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula) M) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution σ env) formula) :=
  main_result_for_canonical_ltl_full_synthesis_of_summaryObservableWinner
    In₁ In₂ Out₁ Out₂ interp dec formula
    (fun _ => PUnit) (fun _ => PUnit)
    (fun _ => InputFreeParityTreeAutomaton.trivialAccepted)
    (fun _ => InputFreeParityTreeAutomaton.trivialAccepted_nonempty)
    M hcert

/-- The finite-alphabet full `{←,→,↔}` LTL endpoint from an existentially
enriched local summary automaton. -/
noncomputable def main_result_for_ltl_full_synthesis_finiteAlphabets_of_existsReadbackUpgrade
    {AP : Type}
    (In₁ In₂ Out₁ Out₂ : Type)
    [DecidableEq AP]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (formula : LTL AP)
    [DecidableEq
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
          formula).State]
    (hexists :
      ∃ M : LocalSummaryAutomaton.{0, 0, 0} In₁ In₂,
        M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂)
          ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution σ env) formula) :=
  main_result_for_canonical_ltl_full_synthesis_of_existsReadbackUpgrade
    In₁ In₂ Out₁ Out₂ interp dec formula
    (fun _ => PUnit) (fun _ => PUnit)
    (fun _ => InputFreeParityTreeAutomaton.trivialAccepted)
    (fun _ => InputFreeParityTreeAutomaton.trivialAccepted_nonempty)
    hexists

end DistributedSynthesis
