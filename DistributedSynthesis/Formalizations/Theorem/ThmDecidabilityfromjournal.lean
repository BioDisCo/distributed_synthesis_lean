/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmMain

/-!
# Decidability from the journal and handoff route
-/

namespace DistributedSynthesis

universe u v x y ap a b

/--
Paper-facing theorem `thm:decidabilityfromjournal`, routed through the current
formal journal/handoff boundary.

The statement is intentionally not an alias for `main_result`: it composes the
proved LTL-to-APA frontend, the support-witness APA obligations,
compatible-execution representability, and finite-game controller completeness
into the decidability conclusion for the original full-LTL formula.
-/
noncomputable def decidability_from_journal
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    [Inhabited In₁]
    [Inhabited In₂]
    [Fintype In₁]
    [Fintype In₂]
    [Fintype Out₁]
    [Fintype Out₂]
    (formula : LTL AP)
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (interpDecidable : ∀ ap letter, Decidable (interp ap letter))
    (hsound :
      let A :=
        (PositiveLTL.subformulaClosure
          (AP := AP)
          (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
          (PositiveLTL.ofLTL formula)).toAPA interp interpDecidable
      A.SupportWitnessSound)
    (hrealizable :
      let A :=
        (PositiveLTL.subformulaClosure
          (AP := AP)
          (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
          (PositiveLTL.ofLTL formula)).toAPA interp interpDecidable
      A.SupportWitnessTailBranchRealizable)
    (transformer :
      FiniteEpochTransformer.{max u v x y, u, v, x, y, max u v x y}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    [DecidableEq (FiniteEpochTransformer.GameState transformer)]
    (initialBoundary : transformer.boundary)
    (hautomaton :
      let A :=
        (PositiveLTL.subformulaClosure
          (AP := AP)
          (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
          (PositiveLTL.ofLTL formula)).toAPA interp interpDecidable
      ∀ word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂),
        transformer.automaton.Accepts word ↔
          (A.supportWitnessDPAStateCompilationOfSoundAndTailBranchRealizable
            (LTL.canonicalRunLanguageCertificate
              formula interp interpDecidable)
            hsound hrealizable).dpa.Accepts word)
    (dynamicHierarchy parityObjective : Prop)
    (dynamicHierarchy_proof : dynamicHierarchy)
    (parityObjective_proof : parityObjective)
    (representable :
      ∀ controller : transformer.ControllerCode,
        FiniteEpochTransformer.CompatibleDecodedExecutionRepresentable
          transformer initialBoundary controller)
    (completeBoundary :
      let A :=
        (PositiveLTL.subformulaClosure
          (AP := AP)
          (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
          (PositiveLTL.ofLTL formula)).toAPA interp interpDecidable
      FiniteEpochTransformer.GameExecutionControllerComplete
        transformer initialBoundary
        (A.supportWitnessDPAStateCompilationOfSoundAndTailBranchRealizable
          (LTL.canonicalRunLanguageCertificate
            formula interp interpDecidable)
          hsound hrealizable).dpa) :
    Decidable
      (SynthesisProblem
        (fun word => LTL.Satisfies interp word formula)) :=
  CanonicalLTLStateRunBackendCompilation.synthesisDecidableOfCanonicalFrontendSupportWitnessSoundAndTailBranchRealizableAndRepresentableSoundAndGameComplete
    formula
    interp
    interpDecidable
    hsound
    hrealizable
    transformer
    initialBoundary
    hautomaton
    dynamicHierarchy
    parityObjective
    dynamicHierarchy_proof
    parityObjective_proof
    representable
    completeBoundary

/--
Paper-facing journal handoff for the current preferred support-witness route.

Compared with `decidability_from_journal`, this no longer routes through the
older `SupportWitnessTailBranchRealizable` endpoint.  The automata side is the
operational-prefix plus pruned-guided support graph target, and the game side
is a family of rotating rational-run journal certificates, one for each DPA
objective of the state universe produced by the support-witness/LAR backend.
-/
noncomputable def decidability_from_journal_operational_prefix_pruned
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    [Inhabited In₁]
    [Inhabited In₂]
    [Fintype In₁]
    [Fintype In₂]
    [Fintype Out₁]
    [Fintype Out₂]
    (formula : LTL AP)
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (interpDecidable : ∀ ap letter, Decidable (interp ap letter))
    (hpref :
      let A :=
        (PositiveLTL.subformulaClosure
          (AP := AP)
          (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
          (PositiveLTL.ofLTL formula)).toAPA interp interpDecidable
      ∀ (state : A.State)
        (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hpruned :
      PositiveLTL.SubformulaClosurePrunedGuidedRunSubgraphTailBranchRealizable
        (PositiveLTL.ofLTL formula) interp interpDecidable)
    (certificates :
      ∀ A : DetParityAutomaton.{max u v x y, ap}
          (RoundRecord In₁ In₂ Graph Out₁ Out₂),
        RotatingRationalRunEpochBackendCertificate.{u, v, x, y, ap, a, b} A) :
    Decidable
      (SynthesisProblem
        (fun word => LTL.Satisfies interp word formula)) :=
  CanonicalLTLStateRunBackendCompilation.synthesisDecidableOfCanonicalFrontendSupportWitnessPrefixAndPrunedGuidedRunSubgraphTailBranchRealizableRationalRunCompiler
      formula
      interp
      interpDecidable
      hpref
      hpruned
      (DPARotatingRationalRunEpochCompiler.ofCertificates certificates)

/--
Paper-facing journal handoff for the accepting-descent form of the preferred
support-witness route.

This exposes the current fixed-point-facing automata obligation at the journal
boundary.  The accepting/descent/tail-coherent graph is converted through the
semantic open-release bridge before using the already verified pruned-guided
support-witness route.
-/
noncomputable def decidability_from_journal_operational_prefix_accepting_descent
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    [Inhabited In₁]
    [Inhabited In₂]
    [Fintype In₁]
    [Fintype In₂]
    [Fintype Out₁]
    [Fintype Out₂]
    (formula : LTL AP)
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (interpDecidable : ∀ ap letter, Decidable (interp ap letter))
    (hpref :
      let A :=
        (PositiveLTL.subformulaClosure
          (AP := AP)
          (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
          (PositiveLTL.ofLTL formula)).toAPA interp interpDecidable
      ∀ (state : A.State)
        (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hgraph :
      PositiveLTL.SubformulaClosurePrunedGuidedRunSubgraphAcceptingDescentTailCoherent
        (PositiveLTL.ofLTL formula) interp interpDecidable)
    (certificates :
      ∀ A : DetParityAutomaton.{max u v x y, ap}
          (RoundRecord In₁ In₂ Graph Out₁ Out₂),
        RotatingRationalRunEpochBackendCertificate.{u, v, x, y, ap, a, b} A) :
    Decidable
      (SynthesisProblem
        (fun word => LTL.Satisfies interp word formula)) :=
  decidability_from_journal_operational_prefix_pruned
    formula
    interp
    interpDecidable
    hpref
    (PositiveLTL.subformulaClosure_prunedGuidedRunSubgraphTailBranchRealizable_of_tailCoherent
      (PositiveLTL.ofLTL formula)
      interp
      interpDecidable
      (PositiveLTL.subformulaClosure_prunedGuidedRunSubgraphTailCoherent_of_eventualOpenReleaseLocalEdges
        (PositiveLTL.ofLTL formula)
        interp
        interpDecidable
        (PositiveLTL.subformulaClosure_prunedGuidedRunSubgraphEventualOpenReleaseLocalEdges_of_acceptingDescentTailCoherent
          (PositiveLTL.ofLTL formula)
          interp
          interpDecidable
          hgraph)))
    certificates

/--
Paper-facing journal handoff for the semantic operational-witness form of the
accepting-descent support-witness route.
-/
noncomputable def decidability_from_journal_operational_semantic_accepting_descent
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    [Inhabited In₁]
    [Inhabited In₂]
    [Fintype In₁]
    [Fintype In₂]
    [Fintype Out₁]
    [Fintype Out₂]
    (formula : LTL AP)
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (interpDecidable : ∀ ap letter, Decidable (interp ap letter))
    (hsemantic :
      let A :=
        (PositiveLTL.subformulaClosure
          (AP := AP)
          (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
          (PositiveLTL.ofLTL formula)).toAPA interp interpDecidable
      ∀ (state : A.State)
        (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hgraph :
      PositiveLTL.SubformulaClosurePrunedGuidedRunSubgraphAcceptingDescentTailCoherent
        (PositiveLTL.ofLTL formula) interp interpDecidable)
    (certificates :
      ∀ A : DetParityAutomaton.{max u v x y, ap}
          (RoundRecord In₁ In₂ Graph Out₁ Out₂),
        RotatingRationalRunEpochBackendCertificate.{u, v, x, y, ap, a, b} A) :
    Decidable
      (SynthesisProblem
        (fun word => LTL.Satisfies interp word formula)) :=
  decidability_from_journal_operational_prefix_accepting_descent
    formula
    interp
    interpDecidable
    (let A :=
        (PositiveLTL.subformulaClosure
          (AP := AP)
          (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
          (PositiveLTL.ofLTL formula)).toAPA interp interpDecidable;
      (A.operationalWitness_semanticMacroRun_iff_prefix_accepts).mp hsemantic)
    hgraph
    certificates

end DistributedSynthesis
