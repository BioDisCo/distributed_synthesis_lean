/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmMain

/-!
# Support-witness soundness

Support-witness invariants and acceptance follow from the recurrent-formula
and recurring-edge hypotheses stated in each theorem.
-/

namespace DistributedSynthesis

universe u v x y ap a b c d aut br lab tr h1 h2 r1 r2

/--
Canonical root-bound recurrent-source invariant for the subformula-closure
support-witness construction.

The recurrence property states that every
state in a recurring source macro-state, below the root-size bound, satisfies
its formula at the corresponding suffix.  The downstream compiler already
proves support-witness soundness from this exact invariant.
-/
abbrev PositiveLTL.SubformulaClosureRootBoundRecurrentSourceInvariant
    {AP : Type ap}
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y)
    [DecidableEq AP]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter)) : Prop :=
  ∀ formula : LTL AP,
    let root := PositiveLTL.ofLTL formula
    let A :=
      (PositiveLTL.subformulaClosure
        (AP := AP)
        (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
        root).toAPA interp dec
    ∀ (state : A.State)
      (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)),
      ∀ haccepts :
        (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
        let witness :=
          A.supportOperationalWitness_of_supportWitnessMuller_accepts
            (initialStates := ({state} : Finset A.State))
            haccepts
        ∀ targetStates,
          targetStates ∈ witness.macroStates ->
            ∀ j : Nat,
              targetStates ∈
                A.macroConfigurationRun ({state} : Finset A.State) word j ->
                ∀ nextState, nextState ∈ targetStates ->
                  nextState.1.size < root.size + 1 ->
                    PositiveLTL.Satisfies interp
                      (OmegaWord.drop word j) nextState.1

theorem PositiveLTL.subformulaClosure_rootBoundRecurrentSourceInvariant
    {AP : Type ap}
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y)
    [DecidableEq AP]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (hrecurrent :
      ∀ formula : LTL AP,
        let root := PositiveLTL.ofLTL formula
        let A :=
          (PositiveLTL.subformulaClosure
            (AP := AP)
            (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
            root).toAPA interp dec
        ∀ (state : A.State)
          (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)),
          ∀ haccepts :
            (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
            let witness :=
              A.supportOperationalWitness_of_supportWitnessMuller_accepts
                (initialStates := ({state} : Finset A.State))
                haccepts
            ∀ targetStates,
              targetStates ∈ witness.macroStates ->
                ∀ j : Nat,
                  targetStates ∈
                    A.macroConfigurationRun ({state} : Finset A.State) word j ->
                    ∀ nextState, nextState ∈ targetStates ->
                      nextState.1.size < root.size + 1 ->
                        PositiveLTL.Satisfies interp
                          (OmegaWord.drop word j) nextState.1) :
    ∀ formula : LTL AP,
      let root := PositiveLTL.ofLTL formula
      let A :=
        (PositiveLTL.subformulaClosure
          (AP := AP)
          (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
          root).toAPA interp dec
      ∀ (state : A.State)
        (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          let witness :=
            A.supportOperationalWitness_of_supportWitnessMuller_accepts
              (initialStates := ({state} : Finset A.State))
              haccepts
          ∀ targetStates,
            targetStates ∈ witness.macroStates ->
              ∀ j : Nat,
                targetStates ∈
                  A.macroConfigurationRun ({state} : Finset A.State) word j ->
                  ∀ nextState, nextState ∈ targetStates ->
                    nextState.1.size < root.size + 1 ->
                      PositiveLTL.Satisfies interp
                        (OmegaWord.drop word j) nextState.1 := by
  exact hrecurrent

/--
Canonical recurrent formula-truth invariant for support-witness soundness.

This is the semantic recurrence anchor: every state in every selected recurrent
support macro-state satisfies its represented formula at the corresponding
suffix.  The existing support-witness machinery then extracts a finite
formula-true frontier from it.
-/
theorem PositiveLTL.subformulaClosure_canonicalRecurrentFormulaInvariant
    {AP : Type ap}
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y)
    [DecidableEq AP]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (hrecurrent :
      PositiveLTL.SubformulaClosureRootBoundRecurrentSourceInvariant
        In₁ In₂ Out₁ Out₂ interp dec) :
    ∀ formula : LTL AP,
      let A :=
        (PositiveLTL.subformulaClosure
          (AP := AP)
          (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
          (PositiveLTL.ofLTL formula)).toAPA interp dec
      ∀ (state : A.State)
        (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          let witness :=
            A.supportOperationalWitness_of_supportWitnessMuller_accepts
              (initialStates := ({state} : Finset A.State))
              haccepts
          ∀ targetStates,
            targetStates ∈ witness.macroStates ->
              ∀ j : Nat,
                targetStates ∈
                  A.macroConfigurationRun ({state} : Finset A.State) word j ->
                ∀ nextState, nextState ∈ targetStates ->
                PositiveLTL.Satisfies interp
                  (OmegaWord.drop word j) nextState.1 := by
  intro formula
  dsimp only
  let root := PositiveLTL.ofLTL formula
  let A :=
    (PositiveLTL.subformulaClosure
      (AP := AP)
      (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
      root).toAPA interp dec
  intro state word haccepts targetStates htargetStates j htargetConfig
    nextState hnextState
  exact
    PositiveLTL.subformulaClosure_rootBoundRecurrentSourceInvariant
      In₁ In₂ Out₁ Out₂ interp dec hrecurrent formula state word haccepts
      targetStates htargetStates j htargetConfig nextState hnextState
      (Nat.lt_succ_of_le
        (PositiveLTL.size_le_of_mem_subformulas nextState.2))

/--
Canonical finite-prefix formula frontier for support-witness soundness.

This is now a checked extraction from the recurrent formula-truth invariant.
-/
theorem PositiveLTL.subformulaClosure_canonicalSupportWitnessPrefixSatisfies
    {AP : Type ap}
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y)
    [DecidableEq AP]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (hrecurrent :
      PositiveLTL.SubformulaClosureRootBoundRecurrentSourceInvariant
        In₁ In₂ Out₁ Out₂ interp dec) :
    ∀ formula : LTL AP,
      let A :=
        (PositiveLTL.subformulaClosure
          (AP := AP)
          (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
          (PositiveLTL.ofLTL formula)).toAPA interp dec
      ∀ (state : A.State)
        (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)),
        ∀ _haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                PositiveLTL.Satisfies interp
                  (OmegaWord.drop word offset) nextState.1 := by
  intro formula
  dsimp only
  let root := PositiveLTL.ofLTL formula
  let A :=
    (PositiveLTL.subformulaClosure
      (AP := AP)
      (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
      root).toAPA interp dec
  intro state word haccepts
  exact
    PositiveLTL.subformulaClosure_supportWitnessMuller_prefixSatisfies_of_recurrent_invariant
      root interp dec haccepts
      (PositiveLTL.subformulaClosure_canonicalRecurrentFormulaInvariant
        In₁ In₂ Out₁ Out₂ interp dec hrecurrent formula state word haccepts)

/--
Canonical finite-prefix continuation for support-witness soundness.

This checked bridge converts the formula-level frontier theorem above into the
APA continuation form required by the generic support-witness soundness lemma.
-/
theorem PositiveLTL.subformulaClosure_canonicalSupportWitnessPrefixAccepts
    {AP : Type ap}
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y)
    [DecidableEq AP]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (hrecurrent :
      PositiveLTL.SubformulaClosureRootBoundRecurrentSourceInvariant
        In₁ In₂ Out₁ Out₂ interp dec) :
    ∀ formula : LTL AP,
      let A :=
        (PositiveLTL.subformulaClosure
          (AP := AP)
          (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
          (PositiveLTL.ofLTL formula)).toAPA interp dec
      ∀ (state : A.State)
        (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)),
        ∀ _haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset) := by
  exact
    PositiveLTL.subformulaClosure_supportWitnessPrefixAccepts_of_prefixSatisfies
      interp dec
      (PositiveLTL.subformulaClosure_canonicalSupportWitnessPrefixSatisfies
        In₁ In₂ Out₁ Out₂ interp dec hrecurrent)

/--
Canonical support-witness soundness for the subformula-closure APA.

This is the compiler-facing soundness theorem actually required by the main
route.  It is now a checked reduction to the concrete finite-prefix
continuation theorem above.
-/
theorem PositiveLTL.subformulaClosure_canonicalSupportWitnessSound
    {AP : Type ap}
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y)
    [DecidableEq AP]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (hrecurrent :
      PositiveLTL.SubformulaClosureRootBoundRecurrentSourceInvariant
        In₁ In₂ Out₁ Out₂ interp dec) :
    ∀ formula : LTL AP,
      let A :=
        (PositiveLTL.subformulaClosure
          (AP := AP)
          (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
          (PositiveLTL.ofLTL formula)).toAPA interp dec
      A.SupportWitnessSound := by
  intro formula
  dsimp only
  let A :=
    (PositiveLTL.subformulaClosure
      (AP := AP)
      (Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂)
      (PositiveLTL.ofLTL formula)).toAPA interp dec
  exact
    A.supportWitnessSound_of_operationalWitness_prefix_accepts
      (PositiveLTL.subformulaClosure_canonicalSupportWitnessPrefixAccepts
        In₁ In₂ Out₁ Out₂ interp dec hrecurrent formula)

/--
Atom-completeness plus the timed recurring-target atom condition is a thinner
surface for proving node-local recurring-edge completeness of the concrete
guided run.
-/
theorem PositiveLTL.subformulaClosure_guidedRecurringEdgesNodeLocal_of_atomComplete_and_recurringTargetAtoms
    {AP : Type ap}
    {Letter : Type u}
    [DecidableEq AP]
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (hatomComplete :
      ∀ formula : LTL AP,
        ∀ (state : (PositiveLTL.ofLTL formula).Subformula)
          (word : OmegaWord Letter),
          ∀ hsat : PositiveLTL.Satisfies interp word state.1,
            (PositiveLTL.subformulaClosure_guidedRunFrom
              (PositiveLTL.ofLTL formula)
              interp dec word state hsat).AtomComplete)
    (hrecurringTargetAtoms :
      ∀ formula : LTL AP,
        ∀ (state : (PositiveLTL.ofLTL formula).Subformula)
          (word : OmegaWord Letter),
          ∀ hsat : PositiveLTL.Satisfies interp word state.1,
            let run :=
              PositiveLTL.subformulaClosure_guidedRunFrom
                (PositiveLTL.ofLTL formula)
                interp dec word state hsat
            ∀ edge : APAStateEdge
              (((PositiveLTL.subformulaClosure
                (AP := AP)
                (Letter := Letter)
                (PositiveLTL.ofLTL formula)).toAPA
                  interp dec).withInitial state),
              edge ∈ run.realizedEdgeWitnessedMacroRun.infStateEdgeFinset ->
                ∀ node : AlternatingParityAutomaton.Node,
                  run.PathActive node ->
                    run.stateAt node = edge.1 ->
                      edge.2 ∈
                        ((((PositiveLTL.subformulaClosure
                          (AP := AP)
                          (Letter := Letter)
                          (PositiveLTL.ofLTL formula)).toAPA
                            interp dec).withInitial state).step
                              (run.stateAt node) (word node.length)).atoms) :
    ∀ formula : LTL AP,
      ∀ (state : (PositiveLTL.ofLTL formula).Subformula)
        (word : OmegaWord Letter),
        ∀ hsat : PositiveLTL.Satisfies interp word state.1,
          (PositiveLTL.subformulaClosure_guidedRunFrom
            (PositiveLTL.ofLTL formula)
            interp dec word state hsat).RecurringStateEdgesNodeLocalComplete := by
  intro formula state word hsat
  let run :=
    PositiveLTL.subformulaClosure_guidedRunFrom
      (PositiveLTL.ofLTL formula)
      interp dec word state hsat
  exact
    run.recurringStateEdgesNodeLocalComplete_of_atomComplete_and_recurringTargetAtoms
      (hatomComplete formula state word hsat)
      (by
        intro edge hedge node hpath hstate
        simpa [run] using
          hrecurringTargetAtoms formula state word hsat edge hedge node hpath hstate)


end DistributedSynthesis
