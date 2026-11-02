/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmMain
import DistributedSynthesis.Formalizations.Theorem.ThmLTLAPASemanticBridge

/-!
# Synthesis certificates with the canonical LTL backend

These constructions instantiate the LTL-to-DPA translation with
`PositiveLTL.canonicalLTLToDPACompiler`. Finite-game and entry-indexed
certificates remain explicit parameters where required.
The declarations returning `Decidable` are noncomputable; the executable
no-direct-reversal solver is exposed by `Results.NoDirectReversal`.
-/

namespace DistributedSynthesis

universe ap u v x y a

/--
The main theorem for arbitrary full LTL with the canonical automata
backend: only the finite-game compiler remains as an input.
-/
noncomputable def main_result_for_canonical_ltl_finite_game_compiler
    {AP : Type ap}
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y)
    [DecidableEq AP]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (formula : LTL AP)
    (gameCompiler :
      DPAFiniteGameCompiler.{u, v, x, y, a} In₁ In₂ Out₁ Out₂) :
    Decidable
      (SynthesisProblem
        (fun word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) =>
          LTL.Satisfies interp word formula)) :=
  main_result_for_ltl_dpa_finite_game_compiler
    In₁ In₂ Out₁ Out₂
    (PositiveLTL.canonicalLTLToDPACompiler interp dec)
    formula
    gameCompiler

/--
The fragment main theorem with the canonical automata backend: distributed
synthesis of arbitrary full LTL over the no-direct-reversal fragment is
decidable, with **no LTL/automata input** — the LTL-to-DPA compiler is the
unconditional canonical one and the finite-game compiler is
discharged inside the fragment endpoint by the reversal-forgiving companion.

The sole remaining input is the input-free tree-automaton target family for
the compiled objective's block games (`target`/`targetNonempty`).  Its
nonemptiness is realizability of the journal block monitor
(`DeterministicBlockMonitor.toInputFree_acceptsTree_nonempty`), so this is the
one genuine obligation between the fragment result and unconditionality.
-/
noncomputable def main_result_for_canonical_ltl_noDirect_fragment_synthesis
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
          (target d).acceptsTree tree) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          NoDirectReversalSequence env ->
            LTL.Satisfies interp (execution σ env) formula) :=
  main_result_for_ltl_dpa_noDirect_fragment_synthesis
    In₁ In₂ Out₁ Out₂
    (PositiveLTL.canonicalLTLToDPACompiler interp dec)
    formula Branch Label target targetNonempty

/--
The full `{←,→,↔}` main theorem through the canonical compiler: distributed
synthesis of arbitrary full LTL over *every* environment (direct reversals
included) is decidable, given the entry-indexed measurability certificate
`hcert` for the canonically compiled objective.  The LTL-to-DPA compiler
is the canonical one; the reversal handling is the entry-indexed route of
`full_readbackUpgrade`, whose sole hypothesis is `hcert` (paper
`prop:starcomplete`).
-/
noncomputable def main_result_for_canonical_ltl_full_synthesis
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
    (hcert :
      DetParityAutomaton.EntryIndexedCertificate (In₁ := In₁)
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution σ env) formula) :=
  main_result_for_ltl_dpa_full_synthesis
    In₁ In₂ Out₁ Out₂
    (PositiveLTL.canonicalLTLToDPACompiler interp dec)
    formula Branch Label target targetNonempty hcert

/--
Noncomputable no-direct-reversal endpoint for finite input/output alphabets,
with no remaining external compiler or target-certificate parameters.

Computability audit: this is a noncomputable `Decidable` value, not a verified
decision algorithm. Its summary construction `reversalForgivingSummaries`
branches on realizability and chooses a winning witness. The independent
`DistributedSynthesis.NoDirectJournal` API instead reduces the problem semantically to
journal tree nonemptiness; `Results.NoDirectReversal` exposes the encoded solver.

Every prior hypothesis is discharged: the LTL-to-DPA compiler is the canonical
one, the finite-game compiler is the reversal-forgiving companion,
and the input-free tree-automaton target family is
`InputFreeParityTreeAutomaton.trivialAccepted` — the target is administrative
(the epoch decidability route reads only the finite summary transformer, never
`target`), so the canonical trivial target discharges `target`/`targetNonempty`
without changing the result. Stated at `Type 0`, matching the paper's finite
input/output alphabets.
-/
noncomputable def main_result_for_ltl_noDirect_fragment_synthesis_finiteAlphabets
    {AP : Type}
    (In₁ In₂ Out₁ Out₂ : Type)
    [DecidableEq AP]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (formula : LTL AP) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          NoDirectReversalSequence env ->
            LTL.Satisfies interp (execution σ env) formula) :=
  main_result_for_canonical_ltl_noDirect_fragment_synthesis
    In₁ In₂ Out₁ Out₂ interp dec formula
    (fun _ => PUnit) (fun _ => PUnit)
    (fun _ => InputFreeParityTreeAutomaton.trivialAccepted)
    (fun _ => InputFreeParityTreeAutomaton.trivialAccepted_nonempty)

/--
The **full `{←,→,↔}` main theorem** for finite input/output alphabets, modulo the
entry-indexed certificate: distributed synthesis of arbitrary full LTL over
*every* environment (direct reversals included) is decidable, given `hcert`.

Every hypothesis of the fragment synthesis endpoint
`main_result_for_ltl_noDirect_fragment_synthesis_finiteAlphabets` is discharged
identically (canonical compiler, trivial administrative target); the *only*
addition is `hcert`, the θ̄-measurability of the boundary-game plan families
(the summary-fold certificate). This construction assumes `hcert`; it does
not establish that certificate for arbitrary objectives.
-/
noncomputable def main_result_for_ltl_full_synthesis_finiteAlphabets
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
    (hcert :
      DetParityAutomaton.EntryIndexedCertificate (In₁ := In₁)
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution σ env) formula) :=
  main_result_for_canonical_ltl_full_synthesis
    In₁ In₂ Out₁ Out₂ interp dec formula
    (fun _ => PUnit) (fun _ => PUnit)
    (fun _ => InputFreeParityTreeAutomaton.trivialAccepted)
    (fun _ => InputFreeParityTreeAutomaton.trivialAccepted_nonempty)
    hcert

/-- **Route B** canonical full-model synthesis, conditional on the
summary-soundness certificate (true, `lem:fringe`) instead of the entry-indexed
certificate. -/
noncomputable def main_result_for_canonical_ltl_full_synthesis_route_b
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
    (hcert :
      DetParityAutomaton.SummarySoundnessCertificate (In₁ := In₁)
        (A := (PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution σ env) formula) :=
  main_result_for_ltl_dpa_full_synthesis_route_b
    In₁ In₂ Out₁ Out₂
    (PositiveLTL.canonicalLTLToDPACompiler interp dec)
    formula Branch Label target targetNonempty hcert

/--
The **full `{←,→,↔}` main theorem** for finite input/output alphabets, via
**Route B**: distributed synthesis of arbitrary full LTL over *every* environment
is decidable, conditional only on the summary-soundness certificate
`SummarySoundnessCertificate` -- the honest summary-level `prop:starsound`, true
by the fringe-elimination reduction (`delayed_dynamic.tex`, `lem:fringe`), in
place of the entry-indexed certificate that was stuck at the atom-indexing wall.
Discharging `SummarySoundnessCertificate` makes the full model unconditional.
-/
noncomputable def main_result_for_ltl_full_synthesis_finiteAlphabets_route_b
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
    (hcert :
      DetParityAutomaton.SummarySoundnessCertificate (In₁ := In₁)
        (A := (PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution σ env) formula) :=
  main_result_for_canonical_ltl_full_synthesis_route_b
    In₁ In₂ Out₁ Out₂ interp dec formula
    (fun _ => PUnit) (fun _ => PUnit)
    (fun _ => InputFreeParityTreeAutomaton.trivialAccepted)
    (fun _ => InputFreeParityTreeAutomaton.trivialAccepted_nonempty)
    hcert

end DistributedSynthesis
