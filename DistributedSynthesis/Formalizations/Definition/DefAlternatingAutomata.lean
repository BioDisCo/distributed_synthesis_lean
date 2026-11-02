/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefOmegaAutomata
import DistributedSynthesis.Formalizations.Definition.DefPositiveBoolean
import Mathlib.Data.Finset.Union

/-!
# Alternating parity automata

This file defines the finite alternating parity automaton target used on the
route from LTL to deterministic parity automata.  The transition condition is a
positive Boolean formula over successor states.
-/

namespace DistributedSynthesis

universe u v

/-- A finite alternating parity automaton over infinite words. -/
structure AlternatingParityAutomaton (Alphabet : Type u) where
  State : Type v
  stateFinite : Fintype State
  initial : State
  step : State -> Alphabet -> PosBool State
  priority : State -> Nat

attribute [instance] AlternatingParityAutomaton.stateFinite

namespace AlternatingParityAutomaton

/--
The finite set of successor atoms syntactically mentioned by the transition
formula from `state` on `letter`.
-/
noncomputable def stepAtoms {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (letter : Alphabet) :
    Finset A.State := by
  classical
  exact (A.step state letter).atoms.toFinset

@[simp]
theorem mem_stepAtoms {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state nextState : A.State)
    (letter : Alphabet) :
    nextState ∈ A.stepAtoms state letter ↔
      nextState ∈ (A.step state letter).atoms := by
  classical
  simp [stepAtoms]

/--
The one-step syntactic successor set of a finite set of APA states.

This is the powerset carrier used by deterministic subset-style constructions:
from a macro-state `states`, collect every APA state that appears as an atom in
one of the outgoing positive Boolean transition formulas.
-/
noncomputable def subsetStepAtoms {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (states : Finset A.State)
    (letter : Alphabet) :
    Finset A.State := by
  classical
  exact states.biUnion (fun state => A.stepAtoms state letter)

@[simp]
theorem mem_subsetStepAtoms {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (states : Finset A.State)
    (nextState : A.State)
    (letter : Alphabet) :
    nextState ∈ A.subsetStepAtoms states letter ↔
      ∃ state ∈ states, nextState ∈ (A.step state letter).atoms := by
  classical
  simp [subsetStepAtoms]

/-- Every syntactic successor of a member of `states` is in the subset successor set. -/
theorem mem_subsetStepAtoms_of_mem_atoms {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {states : Finset A.State}
    {state nextState : A.State}
    {letter : Alphabet}
    (hstate : state ∈ states)
    (hnext : nextState ∈ (A.step state letter).atoms) :
    nextState ∈ A.subsetStepAtoms states letter := by
  exact (A.mem_subsetStepAtoms states nextState letter).mpr
    ⟨state, hstate, hnext⟩

/--
The subset successor set is the least finite set containing all transition atoms
of the current finite macro-state.
-/
theorem subsetStepAtoms_subset_iff {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (states target : Finset A.State)
    (letter : Alphabet) :
    A.subsetStepAtoms states letter ⊆ target ↔
      ∀ state ∈ states,
        ∀ nextState,
          nextState ∈ (A.step state letter).atoms ->
            nextState ∈ target := by
  classical
  constructor
  · intro hsubset state hstate nextState hnext
    exact hsubset (A.mem_subsetStepAtoms_of_mem_atoms hstate hnext)
  · intro htarget nextState hnext
    rcases (A.mem_subsetStepAtoms states nextState letter).mp hnext with
      ⟨state, hstate, hatom⟩
    exact htarget state hstate nextState hatom

/--
A finite support witnessing one positive-Boolean APA transition.

For an alternating transition, conjunction forces all states in the chosen
support, while disjunction allows one satisfying branch.  The support is also
trimmed to actual syntactic atoms of the transition formula.
-/
structure StepSupport {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (letter : Alphabet) where
  support : Finset A.State
  support_satisfies :
    PosBool.Eval (fun nextState => nextState ∈ support) (A.step state letter)
  support_atoms :
    ∀ nextState, nextState ∈ support -> nextState ∈ (A.step state letter).atoms

namespace StepSupport

/-- Every member of a step support is a syntactic successor atom. -/
theorem mem_stepAtoms {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {state nextState : A.State}
    {letter : Alphabet}
    (support : A.StepSupport state letter)
    (hmem : nextState ∈ support.support) :
    nextState ∈ A.stepAtoms state letter :=
  (A.mem_stepAtoms state nextState letter).mpr
    (support.support_atoms nextState hmem)

/-- A step support is contained in the syntactic successor set. -/
theorem support_subset_stepAtoms {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {state : A.State}
    {letter : Alphabet}
    (support : A.StepSupport state letter) :
    support.support ⊆ A.stepAtoms state letter := by
  intro nextState hmem
  exact support.mem_stepAtoms hmem

end StepSupport

/--
Extract a finite exact support from any valuation satisfying the APA transition.

The returned support contains only transition atoms, satisfies the positive
Boolean transition on its own, and every supported successor satisfies the
original valuation.
-/
theorem stepSupport_exists_of_eval {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (valuation : A.State -> Prop)
    (state : A.State)
    (letter : Alphabet)
    (hstep : PosBool.Eval valuation (A.step state letter)) :
    ∃ support : A.StepSupport state letter,
      ∀ nextState, nextState ∈ support.support -> valuation nextState := by
  classical
  rcases
    (PosBool.eval_iff_exists_support_subset_atoms
      valuation (A.step state letter)).mp hstep with
    ⟨supportList, hvaluation, hatoms, hsatisfies⟩
  refine
    ⟨
      { support := supportList.toFinset
        support_satisfies := ?_
        support_atoms := ?_ },
      ?_⟩
  · exact
      (PosBool.eval_congr
        (fun nextState => by simp)
        (A.step state letter)).mp hsatisfies
  · intro nextState hmem
    exact hatoms nextState (by simpa using hmem)
  · intro nextState hmem
    exact hvaluation nextState (by simpa using hmem)

/-- A finite exact support is enough to satisfy the transition under any larger valuation. -/
theorem eval_of_stepSupport_subset {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {valuation : A.State -> Prop}
    {state : A.State}
    {letter : Alphabet}
    (support : A.StepSupport state letter)
    (hvaluation :
      ∀ nextState, nextState ∈ support.support -> valuation nextState) :
    PosBool.Eval valuation (A.step state letter) := by
  exact
    PosBool.eval_mono
      (fun nextState hmem => hvaluation nextState hmem)
      (A.step state letter)
      support.support_satisfies

/--
A simultaneous finite support choice for every APA state in a finite macro-state.

This is the local object used by subset-style determinization: each active
alternating state chooses one finite positive-Boolean support, and the next
macro-state is the union of all chosen supports.
-/
structure MacroStepSupport {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (states : Finset A.State)
    (letter : Alphabet) where
  choice : ∀ state : {state // state ∈ states}, A.StepSupport state.1 letter

namespace MacroStepSupport

/-- The next finite macro-state induced by simultaneous support choices. -/
noncomputable def support {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states : Finset A.State}
    {letter : Alphabet}
    (supportChoice : A.MacroStepSupport states letter) :
    Finset A.State := by
  classical
  exact states.attach.biUnion (fun state => (supportChoice.choice state).support)

@[simp]
theorem mem_support {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states : Finset A.State}
    {letter : Alphabet}
    {supportChoice : A.MacroStepSupport states letter}
    {nextState : A.State} :
    nextState ∈ supportChoice.support ↔
      ∃ state : {state // state ∈ states},
        nextState ∈ (supportChoice.choice state).support := by
  classical
  simp [support]

/-- A macro support is contained in the syntactic subset successor set. -/
theorem support_subset_subsetStepAtoms {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states : Finset A.State}
    {letter : Alphabet}
    (supportChoice : A.MacroStepSupport states letter) :
    supportChoice.support ⊆ A.subsetStepAtoms states letter := by
  intro nextState hnext
  rcases
      (mem_support
        (supportChoice := supportChoice)
        (nextState := nextState)).mp hnext with
    ⟨state, hstate⟩
  exact
    A.mem_subsetStepAtoms_of_mem_atoms
      (states := states)
      (state := state.1)
      (nextState := nextState)
      (letter := letter)
      state.2
      ((supportChoice.choice state).support_atoms nextState hstate)

/--
The individual APA state-edges induced by a simultaneous macro support choice.

Unlike a macro edge `S -> T`, this remembers which source state generated which
successor state.  This is the finite graph data needed for the eventual Muller
condition over branches.
-/
noncomputable def stateEdges {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states : Finset A.State}
    {letter : Alphabet}
    (supportChoice : A.MacroStepSupport states letter) :
    Finset (A.State × A.State) := by
  classical
  exact states.attach.biUnion (fun state =>
    (supportChoice.choice state).support.image
      (fun nextState => (state.1, nextState)))

@[simp]
theorem mem_stateEdges {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states : Finset A.State}
    {letter : Alphabet}
    {supportChoice : A.MacroStepSupport states letter}
    {edge : A.State × A.State} :
    edge ∈ supportChoice.stateEdges ↔
      ∃ state : {state // state ∈ states},
        edge.1 = state.1 ∧
          edge.2 ∈ (supportChoice.choice state).support := by
  classical
  constructor
  · intro hedge
    rcases Finset.mem_biUnion.mp hedge with ⟨state, _hstate, hedgeState⟩
    rcases Finset.mem_image.mp hedgeState with ⟨nextState, hnext, hedgeEq⟩
    have hsource : edge.1 = state.1 := by
      simpa using (congrArg Prod.fst hedgeEq).symm
    have htarget : edge.2 = nextState := by
      simpa using (congrArg Prod.snd hedgeEq).symm
    exact ⟨state, hsource, by simpa [htarget] using hnext⟩
  · intro hedge
    rcases hedge with ⟨state, hsource, htarget⟩
    exact Finset.mem_biUnion.mpr
      ⟨state, by simp,
        Finset.mem_image.mpr
          ⟨edge.2, htarget, by
            ext <;> simp [hsource]⟩⟩

theorem stateEdges_source_mem {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states : Finset A.State}
    {letter : Alphabet}
    {supportChoice : A.MacroStepSupport states letter}
    {edge : A.State × A.State}
    (hedge : edge ∈ supportChoice.stateEdges) :
    edge.1 ∈ states := by
  rcases (mem_stateEdges (supportChoice := supportChoice)).mp hedge with
    ⟨state, hsource, _htarget⟩
  simpa [hsource] using state.2

theorem stateEdges_target_mem_support {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states : Finset A.State}
    {letter : Alphabet}
    {supportChoice : A.MacroStepSupport states letter}
    {edge : A.State × A.State}
    (hedge : edge ∈ supportChoice.stateEdges) :
    edge.2 ∈ supportChoice.support := by
  rcases (mem_stateEdges (supportChoice := supportChoice)).mp hedge with
    ⟨state, _hsource, htarget⟩
  exact
    (mem_support
      (supportChoice := supportChoice)
      (nextState := edge.2)).mpr
      ⟨state, htarget⟩

end MacroStepSupport

/--
Extract simultaneous finite supports from valuations satisfying every transition
of a finite macro-state.
-/
theorem macroStepSupport_exists_of_eval_all {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (valuation : A.State -> Prop)
    (states : Finset A.State)
    (letter : Alphabet)
    (hstep :
      ∀ state, state ∈ states ->
        PosBool.Eval valuation (A.step state letter)) :
    ∃ supportChoice : A.MacroStepSupport states letter,
      ∀ nextState, nextState ∈ supportChoice.support -> valuation nextState := by
  classical
  let supportChoice :
      ∀ state : {state // state ∈ states}, A.StepSupport state.1 letter :=
    fun state =>
      Classical.choose
        (A.stepSupport_exists_of_eval valuation state.1 letter
          (hstep state.1 state.2))
  have hsupportChoice :
      ∀ state : {state // state ∈ states},
        ∀ nextState,
          nextState ∈ (supportChoice state).support -> valuation nextState := by
    intro state nextState hmem
    exact
      (Classical.choose_spec
        (A.stepSupport_exists_of_eval valuation state.1 letter
          (hstep state.1 state.2))) nextState hmem
  let macroSupport : A.MacroStepSupport states letter := { choice := supportChoice }
  refine ⟨macroSupport, ?_⟩
  intro nextState hnext
  rcases
    (MacroStepSupport.mem_support
      (supportChoice := macroSupport)
      (nextState := nextState)).mp hnext with
    ⟨state, hstate⟩
  exact hsupportChoice state nextState hstate

/--
The finite one-step transition relation between APA macro-states induced by
simultaneous positive-Boolean support choices.
-/
def MacroTransition {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (states : Finset A.State)
    (letter : Alphabet)
    (nextStates : Finset A.State) :
    Prop :=
  ∃ supportChoice : A.MacroStepSupport states letter,
    supportChoice.support = nextStates

/--
A finite macro transition together with the individual support edges that
generated it.
-/
def MacroTransitionWithStateEdges {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (states : Finset A.State)
    (letter : Alphabet)
    (nextStates : Finset A.State)
    (stateEdges : Finset (A.State × A.State)) :
    Prop :=
  ∃ supportChoice : A.MacroStepSupport states letter,
    supportChoice.support = nextStates ∧
      supportChoice.stateEdges = stateEdges

theorem MacroTransitionWithStateEdges.to_macroTransition {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states nextStates : Finset A.State}
    {letter : Alphabet}
    {stateEdges : Finset (A.State × A.State)}
    (htransition :
      A.MacroTransitionWithStateEdges states letter nextStates stateEdges) :
    A.MacroTransition states letter nextStates := by
  rcases htransition with ⟨supportChoice, hsupport, _hedges⟩
  exact ⟨supportChoice, hsupport⟩

theorem MacroTransitionWithStateEdges.eval_source {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states nextStates : Finset A.State}
    {letter : Alphabet}
    {stateEdges : Finset (A.State × A.State)}
    (htransition :
      A.MacroTransitionWithStateEdges states letter nextStates stateEdges)
    {state : A.State}
    (hstate : state ∈ states) :
    PosBool.Eval (fun nextState => nextState ∈ nextStates)
      (A.step state letter) := by
  rcases htransition with ⟨supportChoice, hsupport, _hedges⟩
  exact
    PosBool.eval_mono
      (fun nextState hnextState => by
        rw [← hsupport]
        exact
          (MacroStepSupport.mem_support
            (supportChoice := supportChoice)
            (nextState := nextState)).mpr
            ⟨⟨state, hstate⟩, hnextState⟩)
      (A.step state letter)
      (supportChoice.choice ⟨state, hstate⟩).support_satisfies

theorem exists_stateEdges_of_macroTransition {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {states nextStates : Finset A.State}
    {letter : Alphabet}
    (htransition : A.MacroTransition states letter nextStates) :
    ∃ stateEdges : Finset (A.State × A.State),
      A.MacroTransitionWithStateEdges states letter nextStates stateEdges := by
  rcases htransition with ⟨supportChoice, hsupport⟩
  exact ⟨supportChoice.stateEdges, supportChoice, hsupport, rfl⟩

theorem MacroTransitionWithStateEdges.edge_source_mem {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states nextStates : Finset A.State}
    {letter : Alphabet}
    {stateEdges : Finset (A.State × A.State)}
    (htransition :
      A.MacroTransitionWithStateEdges states letter nextStates stateEdges)
    {edge : A.State × A.State}
    (hedge : edge ∈ stateEdges) :
    edge.1 ∈ states := by
  rcases htransition with ⟨supportChoice, _hsupport, hedges⟩
  rw [← hedges] at hedge
  exact supportChoice.stateEdges_source_mem hedge

theorem MacroTransitionWithStateEdges.edge_target_mem {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states nextStates : Finset A.State}
    {letter : Alphabet}
    {stateEdges : Finset (A.State × A.State)}
    (htransition :
      A.MacroTransitionWithStateEdges states letter nextStates stateEdges)
    {edge : A.State × A.State}
    (hedge : edge ∈ stateEdges) :
    edge.2 ∈ nextStates := by
  rcases htransition with ⟨supportChoice, hsupport, hedges⟩
  rw [← hedges] at hedge
  rw [← hsupport]
  exact supportChoice.stateEdges_target_mem_support hedge

/--
Every target state of a macro-transition-with-edges is generated by one of
the recorded state edges.
-/
theorem MacroTransitionWithStateEdges.exists_edge_of_target_mem {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states nextStates : Finset A.State}
    {letter : Alphabet}
    {stateEdges : Finset (A.State × A.State)}
    (htransition :
      A.MacroTransitionWithStateEdges states letter nextStates stateEdges)
    {nextState : A.State}
    (hnext : nextState ∈ nextStates) :
    ∃ sourceState,
      sourceState ∈ states ∧
        (sourceState, nextState) ∈ stateEdges := by
  rcases htransition with ⟨supportChoice, hsupport, hstateEdges⟩
  have hnextSupport : nextState ∈ supportChoice.support := by
    simpa [hsupport] using hnext
  rcases
    (MacroStepSupport.mem_support
      (supportChoice := supportChoice)
      (nextState := nextState)).mp hnextSupport with
    ⟨source, hnextChoice⟩
  refine ⟨source.1, source.2, ?_⟩
  rw [← hstateEdges]
  exact
    (MacroStepSupport.mem_stateEdges
      (supportChoice := supportChoice)
      (edge := (source.1, nextState))).mpr
      ⟨source, rfl, hnextChoice⟩

/-- Every finite macro transition stays inside the syntactic successor set. -/
theorem MacroTransition.subset_subsetStepAtoms {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states nextStates : Finset A.State}
    {letter : Alphabet}
    (htransition : A.MacroTransition states letter nextStates) :
    nextStates ⊆ A.subsetStepAtoms states letter := by
  rcases htransition with ⟨supportChoice, rfl⟩
  exact supportChoice.support_subset_subsetStepAtoms

/--
A macro transition is semantically sound: if all states of the next macro-state
satisfy a valuation, then every active APA transition is satisfied by that
valuation.
-/
theorem eval_all_of_macroTransition {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {valuation : A.State -> Prop}
    {states nextStates : Finset A.State}
    {letter : Alphabet}
    (htransition : A.MacroTransition states letter nextStates)
    (hvaluation : ∀ nextState, nextState ∈ nextStates -> valuation nextState) :
    ∀ state, state ∈ states ->
      PosBool.Eval valuation (A.step state letter) := by
  rcases htransition with ⟨supportChoice, rfl⟩
  intro state hstate
  refine
    A.eval_of_stepSupport_subset
      (supportChoice.choice ⟨state, hstate⟩)
      ?_
  intro nextState hnext
  exact hvaluation nextState
    ((MacroStepSupport.mem_support
      (supportChoice := supportChoice)
      (nextState := nextState)).mpr
      ⟨⟨state, hstate⟩, hnext⟩)

/--
Semantic completeness of finite macro transitions: whenever all active APA
transitions are satisfied by a valuation, there is a finite macro successor
whose states satisfy the valuation.
-/
theorem exists_macroTransition_of_eval_all {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (valuation : A.State -> Prop)
    (states : Finset A.State)
    (letter : Alphabet)
    (hstep :
      ∀ state, state ∈ states ->
        PosBool.Eval valuation (A.step state letter)) :
    ∃ nextStates : Finset A.State,
      A.MacroTransition states letter nextStates ∧
      nextStates ⊆ A.subsetStepAtoms states letter ∧
      ∀ nextState, nextState ∈ nextStates -> valuation nextState := by
  rcases
    A.macroStepSupport_exists_of_eval_all valuation states letter hstep with
    ⟨supportChoice, hvaluation⟩
  refine
    ⟨supportChoice.support,
      ⟨supportChoice, rfl⟩,
      ?_,
      hvaluation⟩
  exact supportChoice.support_subset_subsetStepAtoms

/--
Finite macro transitions exactly express the one-step APA obligations for a
continuation valuation.
-/
theorem exists_macroTransition_iff_eval_all {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (valuation : A.State -> Prop)
    (states : Finset A.State)
    (letter : Alphabet) :
    (∃ nextStates : Finset A.State,
      A.MacroTransition states letter nextStates ∧
      ∀ nextState, nextState ∈ nextStates -> valuation nextState) ↔
      ∀ state, state ∈ states ->
        PosBool.Eval valuation (A.step state letter) := by
  constructor
  · intro h state hstate
    rcases h with ⟨nextStates, htransition, hvaluation⟩
    exact
      A.eval_all_of_macroTransition htransition hvaluation state hstate
  · intro hstep
    rcases A.exists_macroTransition_of_eval_all valuation states letter hstep with
      ⟨nextStates, htransition, _hsubset, hvaluation⟩
    exact ⟨nextStates, htransition, hvaluation⟩

/-- All finite macro-successors of one macro-state on one input letter. -/
noncomputable def macroSuccessors {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (states : Finset A.State)
    (letter : Alphabet) :
    Finset (Finset A.State) := by
  classical
  exact Finset.univ.filter
    (fun nextStates => A.MacroTransition states letter nextStates)

@[simp]
theorem mem_macroSuccessors {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (states nextStates : Finset A.State)
    (letter : Alphabet) :
    nextStates ∈ A.macroSuccessors states letter ↔
      A.MacroTransition states letter nextStates := by
  classical
  simp [macroSuccessors]

/--
Deterministic powerset step for the macro-transition graph: from a finite set
of possible macro-states, collect all one-step macro-successors.
-/
noncomputable def macroConfigurationStep {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (configs : Finset (Finset A.State))
    (letter : Alphabet) :
    Finset (Finset A.State) := by
  classical
  exact configs.biUnion (fun states => A.macroSuccessors states letter)

@[simp]
theorem mem_macroConfigurationStep {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (configs : Finset (Finset A.State))
    (nextStates : Finset A.State)
    (letter : Alphabet) :
    nextStates ∈ A.macroConfigurationStep configs letter ↔
      ∃ states ∈ configs, A.MacroTransition states letter nextStates := by
  classical
  simp [macroConfigurationStep]

/--
All macro-transition edges generated from a deterministic configuration on one
input letter.

Keeping these edges, not only their targets, is the next deterministic memory
needed for Muller-style path extraction.
-/
noncomputable def macroConfigurationEdges {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (configs : Finset (Finset A.State))
    (letter : Alphabet) :
    Finset (Finset A.State × Finset A.State) := by
  classical
  exact configs.biUnion (fun states =>
    (A.macroSuccessors states letter).image (fun nextStates => (states, nextStates)))

@[simp]
theorem mem_macroConfigurationEdges {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (configs : Finset (Finset A.State))
    (edge : Finset A.State × Finset A.State)
    (letter : Alphabet) :
    edge ∈ A.macroConfigurationEdges configs letter ↔
      edge.1 ∈ configs ∧ A.MacroTransition edge.1 letter edge.2 := by
  classical
  constructor
  · intro hedge
    rcases Finset.mem_biUnion.mp hedge with ⟨states, hstates, hedgeStates⟩
    rcases Finset.mem_image.mp hedgeStates with ⟨nextStates, hnext, rfl⟩
    exact ⟨hstates, (A.mem_macroSuccessors states nextStates letter).mp hnext⟩
  · intro h
    exact Finset.mem_biUnion.mpr
      ⟨edge.1, h.1,
        Finset.mem_image.mpr
          ⟨edge.2,
            (A.mem_macroSuccessors edge.1 edge.2 letter).mpr h.2,
            rfl⟩⟩

theorem mem_macroConfigurationStep_iff_exists_edge {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (configs : Finset (Finset A.State))
    (nextStates : Finset A.State)
    (letter : Alphabet) :
    nextStates ∈ A.macroConfigurationStep configs letter ↔
      ∃ sourceStates,
        (sourceStates, nextStates) ∈ A.macroConfigurationEdges configs letter := by
  constructor
  · intro hnext
    rcases (A.mem_macroConfigurationStep configs nextStates letter).mp hnext with
      ⟨sourceStates, hsource, htransition⟩
    exact ⟨sourceStates,
      (A.mem_macroConfigurationEdges configs (sourceStates, nextStates) letter).mpr
        ⟨hsource, htransition⟩⟩
  · intro hnext
    rcases hnext with ⟨sourceStates, hedge⟩
    have h := (A.mem_macroConfigurationEdges configs (sourceStates, nextStates) letter).mp hedge
    exact (A.mem_macroConfigurationStep configs nextStates letter).mpr
      ⟨sourceStates, h.1, h.2⟩

theorem macroConfigurationEdges_source_mem {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {configs : Finset (Finset A.State)}
    {edge : Finset A.State × Finset A.State}
    {letter : Alphabet}
    (hedge : edge ∈ A.macroConfigurationEdges configs letter) :
    edge.1 ∈ configs :=
  ((A.mem_macroConfigurationEdges configs edge letter).mp hedge).1

theorem macroConfigurationEdges_transition {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {configs : Finset (Finset A.State)}
    {edge : Finset A.State × Finset A.State}
    {letter : Alphabet}
    (hedge : edge ∈ A.macroConfigurationEdges configs letter) :
    A.MacroTransition edge.1 letter edge.2 :=
  ((A.mem_macroConfigurationEdges configs edge letter).mp hedge).2

theorem macroConfigurationEdges_target_mem_step {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {configs : Finset (Finset A.State)}
    {edge : Finset A.State × Finset A.State}
    {letter : Alphabet}
    (hedge : edge ∈ A.macroConfigurationEdges configs letter) :
    edge.2 ∈ A.macroConfigurationStep configs letter := by
  have hsource := A.macroConfigurationEdges_source_mem hedge
  have htransition := A.macroConfigurationEdges_transition hedge
  exact (A.mem_macroConfigurationStep configs edge.2 letter).mpr
    ⟨edge.1, hsource, htransition⟩

/--
The deterministic prefix run of the macro-transition powerset construction.
At time `n`, this finite set contains exactly the macro-states reachable by
some finite sequence of support choices over the first `n` letters.
-/
noncomputable def macroConfigurationRun {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet) :
    Nat -> Finset (Finset A.State)
  | 0 => {initialStates}
  | n + 1 =>
      A.macroConfigurationStep
        (A.macroConfigurationRun initialStates word n)
        (word n)

@[simp]
theorem macroConfigurationRun_zero {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet) :
    A.macroConfigurationRun initialStates word 0 = {initialStates} :=
  rfl

theorem mem_macroConfigurationRun_succ {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates nextStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    nextStates ∈ A.macroConfigurationRun initialStates word (n + 1) ↔
      ∃ states ∈ A.macroConfigurationRun initialStates word n,
        A.MacroTransition states (word n) nextStates := by
  simp [macroConfigurationRun]

theorem macroConfigurationStep_mono {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {configs₁ configs₂ : Finset (Finset A.State)}
    {letter : Alphabet}
    (hsubset : configs₁ ⊆ configs₂) :
    A.macroConfigurationStep configs₁ letter ⊆
      A.macroConfigurationStep configs₂ letter := by
  intro nextStates hnextStates
  rcases
    (A.mem_macroConfigurationStep configs₁ nextStates letter).mp hnextStates with
    ⟨states, hstates, htransition⟩
  exact
    (A.mem_macroConfigurationStep configs₂ nextStates letter).mpr
      ⟨states, hsubset hstates, htransition⟩

/--
Monotonicity of the deterministic macro-configuration run in the initial
deterministic configuration set.

Starting from a larger set of possible APA macro-states preserves every finite
macro-state reachable from a smaller start set.
-/
theorem macroConfigurationRun_mono {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates₁ initialStates₂ : Finset A.State}
    {word : OmegaWord Alphabet}
    (hsubset : ({initialStates₁} : Finset (Finset A.State)) ⊆ {initialStates₂}) :
    ∀ n : Nat,
      A.macroConfigurationRun initialStates₁ word n ⊆
        A.macroConfigurationRun initialStates₂ word n := by
  intro n
  induction n with
  | zero =>
      simpa using hsubset
  | succ n ih =>
      intro states hstates
      exact A.macroConfigurationStep_mono ih hstates

/--
If one initial macro-state is literally a member of another deterministic
configuration set, its finite continuations remain reachable from the larger
initial configuration.
-/
theorem macroConfigurationRun_subset_of_initial_mem {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates startStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (hstart : startStates = initialStates) :
    ∀ n : Nat,
      A.macroConfigurationRun startStates word n ⊆
        A.macroConfigurationRun initialStates word n := by
  subst startStates
  intro n states hstates
  exact hstates

/--
Continue a reachable macro-state inside the original deterministic
macro-configuration run.

If `startStates` is reachable after `offset` letters, then every finite
continuation from `startStates` on the dropped word is reachable in the
original powerset run at the corresponding absolute time.
-/
theorem macroConfigurationRun_mem_of_mem_start {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates startStates states : Finset A.State}
    {word : OmegaWord Alphabet}
    {offset length : Nat}
    (hstart :
      startStates ∈ A.macroConfigurationRun initialStates word offset)
    (hstates :
      states ∈
        A.macroConfigurationRun startStates (OmegaWord.drop word offset)
          length) :
    states ∈ A.macroConfigurationRun initialStates word (offset + length) := by
  induction length generalizing states with
  | zero =>
      have hstatesEq : states = startStates := by
        simpa using hstates
      subst states
      simpa using hstart
  | succ length ih =>
      rw [A.mem_macroConfigurationRun_succ] at hstates
      rcases hstates with ⟨previousStates, hprevious, htransition⟩
      have hpreviousGlobal :
          previousStates ∈
            A.macroConfigurationRun initialStates word (offset + length) :=
        ih hprevious
      rw [show offset + (length + 1) = offset + length + 1 by omega]
      rw [A.mem_macroConfigurationRun_succ]
      refine ⟨previousStates, hpreviousGlobal, ?_⟩
      simpa [OmegaWord.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using htransition

/-- The deterministic edge stream generated by the configuration run. -/
noncomputable def macroConfigurationEdgeRun {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    Finset (Finset A.State × Finset A.State) :=
  A.macroConfigurationEdges
    (A.macroConfigurationRun initialStates word n)
    (word n)

@[simp]
theorem mem_macroConfigurationEdgeRun {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (n : Nat)
    (edge : Finset A.State × Finset A.State) :
    edge ∈ A.macroConfigurationEdgeRun initialStates word n ↔
      edge.1 ∈ A.macroConfigurationRun initialStates word n ∧
        A.MacroTransition edge.1 (word n) edge.2 := by
  simp [macroConfigurationEdgeRun]

theorem macroConfigurationEdges_mono {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {configs₁ configs₂ : Finset (Finset A.State)}
    {letter : Alphabet}
    (hsubset : configs₁ ⊆ configs₂) :
    A.macroConfigurationEdges configs₁ letter ⊆
      A.macroConfigurationEdges configs₂ letter := by
  intro edge hedge
  rcases (A.mem_macroConfigurationEdges configs₁ edge letter).mp hedge with
    ⟨hsource, htransition⟩
  exact
    (A.mem_macroConfigurationEdges configs₂ edge letter).mpr
      ⟨hsubset hsource, htransition⟩

theorem macroConfigurationEdgeRun_mem_of_mem_start {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates startStates : Finset A.State}
    {edge : Finset A.State × Finset A.State}
    {word : OmegaWord Alphabet}
    {offset length : Nat}
    (hstart :
      startStates ∈ A.macroConfigurationRun initialStates word offset)
    (hedge :
      edge ∈
        A.macroConfigurationEdgeRun startStates (OmegaWord.drop word offset)
          length) :
    edge ∈ A.macroConfigurationEdgeRun initialStates word (offset + length) := by
  rw [A.mem_macroConfigurationEdgeRun] at hedge ⊢
  exact
    ⟨A.macroConfigurationRun_mem_of_mem_start hstart hedge.1,
      by
        simpa [OmegaWord.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using hedge.2⟩

/--
Infinite paths through the finite APA macro-state transition relation.

This is the deterministic/subset-side object: at time `n`, `states n` is the
finite set of currently active APA states, and the next set is obtained by a
finite macro transition on the `n`-th input letter.
-/
structure MacroRun {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet) where
  states : Nat -> Finset A.State
  initial_states : states 0 = initialStates
  step_transition :
    ∀ n : Nat, A.MacroTransition (states n) (word n) (states (n + 1))

namespace MacroRun

@[simp]
theorem states_zero {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    run.states 0 = initialStates :=
  run.initial_states

/-- The suffix of a macro-run is again a macro-run on the dropped word. -/
def tail {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    A.MacroRun (run.states 1) (OmegaWord.drop word 1) where
  states n := run.states (n + 1)
  initial_states := rfl
  step_transition := by
    intro n
    simpa [OmegaWord.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using run.step_transition (n + 1)

@[simp]
theorem tail_states {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (n : Nat) :
    run.tail.states n = run.states (n + 1) :=
  rfl

/-- Drop the first `offset` macro-steps of a macro-run. -/
def drop {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (offset : Nat) :
    A.MacroRun (run.states offset) (OmegaWord.drop word offset) where
  states n := run.states (offset + n)
  initial_states := by simp
  step_transition := by
    intro n
    simpa [OmegaWord.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using run.step_transition (offset + n)

@[simp]
theorem drop_states {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (offset n : Nat) :
    (run.drop offset).states n = run.states (offset + n) :=
  rfl

@[simp]
theorem drop_zero {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (n : Nat) :
    (run.drop 0).states n = run.states n := by
  simp [drop]

theorem drop_one_states {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (n : Nat) :
    (run.drop 1).states n = run.tail.states n := by
  simp [drop, tail, Nat.add_comm]

end MacroRun

/-- A finite macro-state occurs infinitely often along a macro-run. -/
def MacroRun.StateSeenInfinitelyOften {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (states : Finset A.State) :
    Prop :=
  ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ run.states k = states

/-- The semantic set of finite macro-states seen infinitely often. -/
def MacroRun.InfStates {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    Set (Finset A.State) :=
  { states | run.StateSeenInfinitelyOften states }

/-- The concrete finite set of finite macro-states seen infinitely often. -/
noncomputable def MacroRun.infStateFinset {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    Finset (Finset A.State) := by
  classical
  exact Finset.univ.filter (fun states => run.StateSeenInfinitelyOften states)

@[simp]
theorem MacroRun.mem_infStateFinset {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (states : Finset A.State) :
    states ∈ run.infStateFinset ↔ run.StateSeenInfinitelyOften states := by
  classical
  simp [MacroRun.infStateFinset]

/-- The concrete finite infinity set represents the semantic recurring set. -/
theorem MacroRun.coe_infStateFinset {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    (run.infStateFinset : Set (Finset A.State)) = run.InfStates := by
  ext states
  exact run.mem_infStateFinset states

/-- Some macro-state occurs infinitely often along every macro-run. -/
theorem MacroRun.exists_stateSeenInfinitelyOften {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    ∃ states : Finset A.State, run.StateSeenInfinitelyOften states := by
  classical
  obtain ⟨states, hstates⟩ := Finite.exists_infinite_fiber run.states
  refine ⟨states, ?_⟩
  have hfreq : ∃ᶠ n in Filter.atTop, run.states n = states := by
    rw [Nat.frequently_atTop_iff_infinite]
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (Set.infinite_coe_iff.1 hstates)
  rw [Filter.frequently_atTop] at hfreq
  intro n
  rcases hfreq n with ⟨k, hk, hkstates⟩
  exact ⟨k, hk, hkstates⟩

/--
Every infinite macro-run is represented by the deterministic powerset
configuration run at every finite time.
-/
theorem MacroRun.states_mem_macroConfigurationRun {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (n : Nat) :
    run.states n ∈ A.macroConfigurationRun initialStates word n := by
  induction n with
  | zero =>
      simp [run.initial_states]
  | succ n ih =>
      rw [A.mem_macroConfigurationRun_succ]
      exact ⟨run.states n, ih, run.step_transition n⟩

/--
Every edge used by an infinite macro-run is present in the deterministic
configuration edge stream.
-/
theorem MacroRun.edge_mem_macroConfigurationEdgeRun {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (n : Nat) :
    (run.states n, run.states (n + 1)) ∈
      A.macroConfigurationEdgeRun initialStates word n := by
  exact (A.mem_macroConfigurationEdgeRun initialStates word n
    (run.states n, run.states (n + 1))).mpr
    ⟨run.states_mem_macroConfigurationRun n, run.step_transition n⟩

/--
The target of every edge used by a represented macro-run is represented in the
next deterministic configuration.
-/
theorem MacroRun.next_states_mem_macroConfigurationRun {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (n : Nat) :
    run.states (n + 1) ∈
      A.macroConfigurationRun initialStates word (n + 1) := by
  exact run.states_mem_macroConfigurationRun (n + 1)

/-- A deterministic edge-stream member has its source in the current configuration. -/
theorem macroConfigurationEdgeRun_source_mem {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {n : Nat}
    {edge : Finset A.State × Finset A.State}
    (hedge : edge ∈ A.macroConfigurationEdgeRun initialStates word n) :
    edge.1 ∈ A.macroConfigurationRun initialStates word n :=
  ((A.mem_macroConfigurationEdgeRun initialStates word n edge).mp hedge).1

/-- A deterministic edge-stream member has its target in the next configuration. -/
theorem macroConfigurationEdgeRun_target_mem_next {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {n : Nat}
    {edge : Finset A.State × Finset A.State}
    (hedge : edge ∈ A.macroConfigurationEdgeRun initialStates word n) :
    edge.2 ∈ A.macroConfigurationRun initialStates word (n + 1) := by
  rw [A.mem_macroConfigurationRun_succ]
  exact
    ⟨edge.1,
      A.macroConfigurationEdgeRun_source_mem hedge,
      ((A.mem_macroConfigurationEdgeRun initialStates word n edge).mp hedge).2⟩

/-- A finite prefix through the APA macro-transition relation. -/
structure MacroRunPrefix {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (length : Nat) where
  states : Nat -> Finset A.State
  initial_states : states 0 = initialStates
  step_transition :
    ∀ n : Nat, n < length ->
      A.MacroTransition (states n) (word n) (states (n + 1))

namespace MacroRunPrefix

@[simp]
theorem states_zero {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {length : Nat}
    (pref : A.MacroRunPrefix initialStates word length) :
    pref.states 0 = initialStates :=
  pref.initial_states

/-- Drop the first `offset` steps of a finite macro-run prefix. -/
def drop {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {offset length : Nat}
    (pref : A.MacroRunPrefix initialStates word (offset + length)) :
    A.MacroRunPrefix (pref.states offset) (OmegaWord.drop word offset) length where
  states n := pref.states (offset + n)
  initial_states := by simp
  step_transition := by
    intro n hn
    simpa [OmegaWord.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using pref.step_transition (offset + n) (by omega)

@[simp]
theorem drop_states {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {offset length : Nat}
    (pref : A.MacroRunPrefix initialStates word (offset + length))
    (n : Nat) :
    (pref.drop).states n = pref.states (offset + n) :=
  rfl

/--
Extend a finite macro-run prefix by one concrete macro transition from its
endpoint.
-/
def snoc {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {length : Nat}
    (pref : A.MacroRunPrefix initialStates word length)
    (nextStates : Finset A.State)
    (htransition :
      A.MacroTransition (pref.states length) (word length) nextStates) :
    A.MacroRunPrefix initialStates word (length + 1) where
  states n := if n ≤ length then pref.states n else nextStates
  initial_states := by
    have hzero : 0 ≤ length := Nat.zero_le length
    simp [hzero, pref.initial_states]
  step_transition := by
    intro n hn
    by_cases hlt : n < length
    · have hnle : n ≤ length := by omega
      have hsuccle : n + 1 ≤ length := by omega
      simpa [hnle, hsuccle] using pref.step_transition n hlt
    · have hn_eq : n = length := by omega
      subst n
      have hnle : length ≤ length := le_rfl
      have hsuccnle : ¬ length + 1 ≤ length := by omega
      simpa [hnle, hsuccnle] using htransition

@[simp]
theorem snoc_states_of_le {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {length : Nat}
    (pref : A.MacroRunPrefix initialStates word length)
    (nextStates : Finset A.State)
    (htransition :
      A.MacroTransition (pref.states length) (word length) nextStates)
    {n : Nat}
    (hn : n ≤ length) :
    (pref.snoc nextStates htransition).states n = pref.states n := by
  simp [snoc, hn]

@[simp]
theorem snoc_states_last {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {length : Nat}
    (pref : A.MacroRunPrefix initialStates word length)
    (nextStates : Finset A.State)
    (htransition :
      A.MacroTransition (pref.states length) (word length) nextStates) :
    (pref.snoc nextStates htransition).states (length + 1) = nextStates := by
  have hnot : ¬ length + 1 ≤ length := by omega
  simp [snoc, hnot]

/--
Every state reached by a finite macro-run prefix is reachable in the
deterministic macro-configuration run at the same time.
-/
theorem states_mem_macroConfigurationRun {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {length : Nat}
    (pref : A.MacroRunPrefix initialStates word length)
    {n : Nat}
    (hn : n ≤ length) :
    pref.states n ∈ A.macroConfigurationRun initialStates word n := by
  induction n with
  | zero =>
      simpa [pref.initial_states]
  | succ n ih =>
      rw [A.mem_macroConfigurationRun_succ]
      exact
        ⟨pref.states n,
          ih (by omega),
          pref.step_transition n (by omega)⟩

/--
Every concrete step of a finite macro-run prefix is present in the
deterministic macro-configuration edge stream.
-/
theorem edge_mem_macroConfigurationEdgeRun {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {length : Nat}
    (pref : A.MacroRunPrefix initialStates word length)
    {n : Nat}
    (hn : n < length) :
    (pref.states n, pref.states (n + 1)) ∈
      A.macroConfigurationEdgeRun initialStates word n := by
  rw [A.mem_macroConfigurationEdgeRun]
  exact
    ⟨pref.states_mem_macroConfigurationRun (by omega),
      pref.step_transition n hn⟩

end MacroRunPrefix

/--
Every deterministic powerset configuration member has a finite macro-run prefix
that reaches it.
-/
theorem exists_macroRunPrefix_of_mem_macroConfigurationRun {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates targetStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (length : Nat)
    (htarget :
      targetStates ∈ A.macroConfigurationRun initialStates word length) :
    ∃ pref : A.MacroRunPrefix initialStates word length,
      pref.states length = targetStates := by
  induction length generalizing targetStates with
  | zero =>
      refine ⟨
        { states := fun _ => initialStates
          initial_states := rfl
          step_transition := by
            intro n hn
            omega },
        ?_⟩
      have htargetEq : targetStates = initialStates := by
        simpa using htarget
      exact htargetEq.symm
  | succ length ih =>
      rw [A.mem_macroConfigurationRun_succ] at htarget
      rcases htarget with ⟨previousStates, hprevious, htransition⟩
      rcases ih previousStates hprevious with ⟨pref, hprefEnd⟩
      let extendedStates : Nat -> Finset A.State := fun k =>
        if k ≤ length then pref.states k else targetStates
      refine ⟨
        { states := extendedStates
          initial_states := by
            have hzero : 0 ≤ length := Nat.zero_le length
            simp [extendedStates, hzero, pref.initial_states]
          step_transition := by
            intro n hn
            by_cases hlt : n < length
            · have hnle : n ≤ length := by omega
              have hsuccle : n + 1 ≤ length := by omega
              simpa [extendedStates, hnle, hsuccle]
                using pref.step_transition n hlt
            · have hn_eq : n = length := by omega
              subst n
              have hle : length ≤ length := le_rfl
              have hnle : ¬ length + 1 ≤ length := by omega
              simpa [extendedStates, hle, hnle, hprefEnd]
                using htransition },
        ?_⟩
      have hnle : ¬ length + 1 ≤ length := by omega
      simp [extendedStates, hnle]

/--
Every deterministic edge-stream edge extends some finite macro-run prefix by
one transition.
-/
theorem exists_macroRunPrefix_of_mem_macroConfigurationEdgeRun {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (n : Nat)
    (edge : Finset A.State × Finset A.State)
    (hedge : edge ∈ A.macroConfigurationEdgeRun initialStates word n) :
    ∃ pref : A.MacroRunPrefix initialStates word (n + 1),
      pref.states n = edge.1 ∧ pref.states (n + 1) = edge.2 := by
  have hsource : edge.1 ∈ A.macroConfigurationRun initialStates word n :=
    A.macroConfigurationEdgeRun_source_mem hedge
  have htransition :
      A.MacroTransition edge.1 (word n) edge.2 :=
    ((A.mem_macroConfigurationEdgeRun initialStates word n edge).mp hedge).2
  rcases
    A.exists_macroRunPrefix_of_mem_macroConfigurationRun
      initialStates edge.1 word n hsource with
    ⟨pref, hprefEnd⟩
  let extendedStates : Nat -> Finset A.State := fun k =>
    if k ≤ n then pref.states k else edge.2
  refine ⟨
    { states := extendedStates
      initial_states := by
        have hzero : 0 ≤ n := Nat.zero_le n
        simp [extendedStates, hzero, pref.initial_states]
      step_transition := by
        intro k hk
        by_cases hlt : k < n
        · have hkle : k ≤ n := by omega
          have hsuccle : k + 1 ≤ n := by omega
          simpa [extendedStates, hkle, hsuccle]
            using pref.step_transition k hlt
        · have hk_eq : k = n := by omega
          subst k
          have hnle : n ≤ n := le_rfl
          have hsuccnle : ¬ n + 1 ≤ n := by omega
          simpa [extendedStates, hnle, hsuccnle, hprefEnd]
            using htransition },
    ?_, ?_⟩
  · have hnle : n ≤ n := le_rfl
    simp [extendedStates, hnle, hprefEnd]
  · have hsuccnle : ¬ n + 1 ≤ n := by omega
    simp [extendedStates, hsuccnle]

/-- The finite infinity set of a macro-run is nonempty. -/
theorem MacroRun.infStateFinset_nonempty {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    run.infStateFinset.Nonempty := by
  rcases run.exists_stateSeenInfinitelyOften with ⟨states, hstates⟩
  exact ⟨states, (run.mem_infStateFinset states).mpr hstates⟩

/--
If a macro-state is not seen infinitely often, then from some point on it is
never seen again.
-/
theorem MacroRun.eventually_ne_of_not_stateSeenInfinitelyOften {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (states : Finset A.State)
    (hnot : ¬ run.StateSeenInfinitelyOften states) :
    ∃ n : Nat, ∀ k : Nat, n ≤ k -> run.states k ≠ states := by
  rw [MacroRun.StateSeenInfinitelyOften] at hnot
  push Not at hnot
  exact hnot

/--
After some finite time, every visited macro-state belongs to the macro-run
infinity set.
-/
theorem MacroRun.eventually_mem_infStateFinset {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    ∃ n : Nat,
      ∀ k : Nat,
        n ≤ k ->
          run.states k ∈ run.infStateFinset := by
  classical
  let bad : Finset (Finset A.State) :=
    Finset.univ.filter (fun states => ¬ run.StateSeenInfinitelyOften states)
  have hbadBound :
      ∀ states ∈ bad,
        ∃ n : Nat, ∀ k : Nat, n ≤ k -> run.states k ≠ states := by
    intro states hstates
    rw [Finset.mem_filter] at hstates
    exact run.eventually_ne_of_not_stateSeenInfinitelyOften states hstates.2
  choose bound hbound using hbadBound
  let boundOf : Finset A.State -> Nat := fun states =>
    if hstates : states ∈ bad then bound states hstates else 0
  refine ⟨bad.sup boundOf, ?_⟩
  intro k hk
  rw [run.mem_infStateFinset]
  by_contra hnot
  have hbad : run.states k ∈ bad := by
    rw [Finset.mem_filter]
    exact ⟨by simp, hnot⟩
  have hle : boundOf (run.states k) ≤ bad.sup boundOf :=
    Finset.le_sup hbad
  have hboundOf :
      boundOf (run.states k) = bound (run.states k) hbad := by
    simp [boundOf, hbad]
  exact hbound (run.states k) hbad k
    (by
      rw [← hboundOf]
      exact le_trans hle hk)
    rfl

/-- A finite node in an alternating run tree. -/
abbrev Node := List Nat

/--
Decompose a non-root node into the first child below the root and the remaining
subnode below that child.

Nodes are stored in reverse path order: the newest child is at the head and the
root child is the final list element.  Thus a node of the form
`suffix ++ [rootChild]` decomposes as `(rootChild, suffix)`.
-/
def Node.rootDecomposition : Node -> Option (Nat × Node)
  | [] => none
  | child :: node =>
      match rootDecomposition node with
      | none => some (child, [])
      | some (rootChild, suffix) => some (rootChild, child :: suffix)

@[simp]
theorem Node.rootDecomposition_nil :
    (Node.rootDecomposition [] : Option (Nat × Node)) = none :=
  rfl

@[simp]
theorem Node.rootDecomposition_singleton (child : Nat) :
    Node.rootDecomposition [child] = some (child, []) :=
  rfl

@[simp]
theorem Node.rootDecomposition_append_singleton
    (suffix : Node)
    (rootChild : Nat) :
    Node.rootDecomposition (suffix ++ [rootChild]) =
      some (rootChild, suffix) := by
  induction suffix with
  | nil =>
      rfl
  | cons child suffix ih =>
      simp [Node.rootDecomposition, ih]

theorem Node.eq_append_singleton_of_rootDecomposition
    {node : Node}
    {rootChild : Nat}
    {suffix : Node}
    (hdecomp : Node.rootDecomposition node = some (rootChild, suffix)) :
    node = suffix ++ [rootChild] := by
  induction node generalizing suffix with
  | nil =>
      simp [Node.rootDecomposition] at hdecomp
  | cons child node ih =>
      cases hnode : Node.rootDecomposition node with
      | none =>
          cases node with
          | nil =>
              simp [Node.rootDecomposition, hnode] at hdecomp
              rcases hdecomp with ⟨rfl, rfl⟩
              rfl
          | cons next rest =>
              cases hrest : Node.rootDecomposition rest <;>
                simp [Node.rootDecomposition, hrest] at hnode
      | some data =>
          rcases data with ⟨innerRoot, innerSuffix⟩
          simp [Node.rootDecomposition, hnode] at hdecomp
          rcases hdecomp with ⟨rfl, rfl⟩
          have hnodeEq : node = innerSuffix ++ [innerRoot] :=
            ih hnode
          simp [hnodeEq, List.cons_append]

theorem Node.rootDecomposition_none_iff
    {node : Node} :
    Node.rootDecomposition node = none ↔ node = [] := by
  constructor
  · intro hnone
    cases node with
    | nil => rfl
    | cons child node =>
        cases hnode : Node.rootDecomposition node <;>
          simp [Node.rootDecomposition, hnode] at hnone
  · intro h
    subst node
    rfl

theorem Node.rootDecomposition_cons_of_some
    {node : Node}
    {rootChild : Nat}
    {suffix : Node}
    (hdecomp : Node.rootDecomposition node = some (rootChild, suffix))
    (child : Nat) :
    Node.rootDecomposition (child :: node) =
      some (rootChild, child :: suffix) := by
  simp [Node.rootDecomposition, hdecomp]

/--
One local expansion step of an alternating run tree.

The full run tree supplies such data at every active node.  This structure
isolates the local obligation: which natural-numbered children are active, what
state each child carries, and why those children satisfy the symbolic
transition formula.
-/
structure StepExpansion {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (letter : Alphabet) where
  childActive : Nat -> Prop
  childState : Nat -> A.State
  step_satisfied :
    PosBool.Eval
      (fun nextState =>
        ∃ child : Nat, childActive child ∧ childState child = nextState)
      (A.step state letter)

/--
An expansion whose active children are known to come from actual atoms of the
transition formula, not from irrelevant support-list padding.
-/
structure ExactStepExpansion {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (letter : Alphabet) extends A.StepExpansion state letter where
  child_atom :
    ∀ child, childActive child -> childState child ∈ (A.step state letter).atoms

/--
Every true symbolic transition has a finite support of successor states.

This is the APA-specific wrapper around `PosBool.eval_iff_exists_support` used
when turning the local step equation into actual run-tree children.
-/
theorem step_exists_support {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (valuation : A.State -> Prop)
    (state : A.State)
    (letter : Alphabet)
    (hstep : PosBool.Eval valuation (A.step state letter)) :
    ∃ support : List A.State,
      (∀ nextState, nextState ∈ support -> valuation nextState) ∧
        PosBool.Eval
          (fun nextState => nextState ∈ support)
          (A.step state letter) :=
  (PosBool.eval_iff_exists_support valuation (A.step state letter)).mp hstep

/--
Every true symbolic transition has a finite support containing only atoms of
the transition formula.
-/
theorem step_exists_exact_support {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (valuation : A.State -> Prop)
    (state : A.State)
    (letter : Alphabet)
    (hstep : PosBool.Eval valuation (A.step state letter)) :
    ∃ support : List A.State,
      (∀ nextState, nextState ∈ support -> valuation nextState) ∧
        (∀ nextState, nextState ∈ support -> nextState ∈ (A.step state letter).atoms) ∧
          PosBool.Eval
            (fun nextState => nextState ∈ support)
            (A.step state letter) :=
  (PosBool.eval_iff_exists_support_subset_atoms
    valuation (A.step state letter)).mp hstep

/--
Read a support-list transition as a transition to numbered children.

Inactive child numbers are assigned the automaton initial state as a harmless
default; only numbers occurring in the support are marked active.  This matches
the valuation shape required by `Run.step_satisfied`.
-/
theorem step_support_as_numbered_children {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (support : List A.State)
    (step : PosBool A.State)
    (hstep : PosBool.Eval (fun nextState => nextState ∈ support) step) :
    PosBool.Eval
      (fun nextState =>
        ∃ child : Nat,
          (∃ childState : A.State, support[child]? = some childState) ∧
            (support[child]?).getD A.initial = nextState)
      step := by
  refine
    PosBool.eval_mono
      (fun nextState hmem => ?_)
      step hstep
  rcases
    (PosBool.mem_iff_exists_getElem? support nextState).mp hmem with
    ⟨child, hchild⟩
  refine ⟨child, ?_, ?_⟩
  · exact ⟨nextState, hchild⟩
  · simp [hchild]

/-- A finite support list induces a local run-tree expansion. -/
def StepExpansion.ofSupport {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (letter : Alphabet)
    (support : List A.State)
    (hstep : PosBool.Eval (fun nextState => nextState ∈ support) (A.step state letter)) :
    A.StepExpansion state letter where
  childActive := fun child =>
    ∃ childState : A.State, support[child]? = some childState
  childState := fun child => (support[child]?).getD A.initial
  step_satisfied := by
    exact A.step_support_as_numbered_children support (A.step state letter) hstep

/-- A finite exact support list induces an exact local run-tree expansion. -/
def ExactStepExpansion.ofSupport {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (letter : Alphabet)
    (support : List A.State)
    (hatoms : ∀ nextState, nextState ∈ support -> nextState ∈ (A.step state letter).atoms)
    (hstep : PosBool.Eval (fun nextState => nextState ∈ support) (A.step state letter)) :
    A.ExactStepExpansion state letter where
  toStepExpansion := StepExpansion.ofSupport A state letter support hstep
  child_atom := by
    intro child hactive
    rcases hactive with ⟨childState, hchild⟩
    have hmem : childState ∈ support :=
      (PosBool.mem_iff_exists_getElem? support childState).mpr ⟨child, hchild⟩
    have hstate :
        (support[child]?).getD A.initial = childState := by
      simp [hchild]
    change (support[child]?).getD A.initial ∈ (A.step state letter).atoms
    rw [hstate]
    exact hatoms childState hmem

/-- A true symbolic transition admits a local run-tree expansion. -/
theorem step_exists_expansion {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (valuation : A.State -> Prop)
    (state : A.State)
    (letter : Alphabet)
    (hstep : PosBool.Eval valuation (A.step state letter)) :
    ∃ expansion : A.StepExpansion state letter,
      ∀ child, expansion.childActive child -> valuation (expansion.childState child) := by
  rcases A.step_exists_support valuation state letter hstep with
    ⟨support, hsupport, hsupportStep⟩
  refine ⟨StepExpansion.ofSupport A state letter support hsupportStep, ?_⟩
  intro child hactive
  rcases hactive with ⟨childState, hchild⟩
  have hmem : childState ∈ support :=
    (PosBool.mem_iff_exists_getElem? support childState).mpr ⟨child, hchild⟩
  have hstate :
      (support[child]?).getD A.initial = childState := by
    simp [hchild]
  change valuation ((support[child]?).getD A.initial)
  rw [hstate]
  exact hsupport childState hmem

/-- A true symbolic transition admits an exact local run-tree expansion. -/
theorem step_exists_exact_expansion {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (valuation : A.State -> Prop)
    (state : A.State)
    (letter : Alphabet)
    (hstep : PosBool.Eval valuation (A.step state letter)) :
    ∃ expansion : A.ExactStepExpansion state letter,
      ∀ child, expansion.childActive child -> valuation (expansion.childState child) := by
  rcases A.step_exists_exact_support valuation state letter hstep with
    ⟨support, hsupport, hatoms, hsupportStep⟩
  refine
    ⟨ExactStepExpansion.ofSupport A state letter support hatoms hsupportStep, ?_⟩
  intro child hactive
  rcases hactive with ⟨childState, hchild⟩
  have hmem : childState ∈ support :=
    (PosBool.mem_iff_exists_getElem? support childState).mpr ⟨child, hchild⟩
  have hstate :
      (support[child]?).getD A.initial = childState := by
    simp [hchild]
  change valuation ((support[child]?).getD A.initial)
  rw [hstate]
  exact hsupport childState hmem

/-- Prefix node of length `n` along an infinite branch. -/
def branchPrefix (branch : Nat -> Nat) : Nat -> Node
  | 0 => []
  | n + 1 => branch n :: branchPrefix branch n

@[simp]
theorem branchPrefix_zero (branch : Nat -> Nat) :
    branchPrefix branch 0 = [] :=
  rfl

@[simp]
theorem branchPrefix_succ (branch : Nat -> Nat) (n : Nat) :
    branchPrefix branch (n + 1) = branch n :: branchPrefix branch n :=
  rfl

theorem branchPrefix_shift
    (child : Nat)
    (branch : Nat -> Nat)
    (n : Nat) :
    branchPrefix (fun
      | 0 => child
      | k + 1 => branch k) (n + 1) =
      branchPrefix branch n ++ [child] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change branch n :: branchPrefix (fun
        | 0 => child
        | k + 1 => branch k) (n + 1) =
        branch n :: (branchPrefix branch n ++ [child])
      rw [ih]

-- Follow a finite node first, then continue along an infinite branch.  Nodes are
-- stored in reverse path order, so the recursion pushes children behind the
-- previously stored prefix.
def branchPrependNode : Node -> (Nat -> Nat) -> Nat -> Nat
  | [], branch => branch
  | child :: node, branch =>
      branchPrependNode node (fun
        | 0 => child
        | k + 1 => branch k)

theorem branchPrefix_prependNode
    (node : Node)
    (branch : Nat -> Nat)
    (n : Nat) :
    branchPrefix (branchPrependNode node branch) (node.length + n) =
      branchPrefix branch n ++ node := by
  induction node generalizing branch n with
  | nil =>
      simp [branchPrependNode]
  | cons child node ih =>
      change
        branchPrefix
            (branchPrependNode node (fun
              | 0 => child
              | k + 1 => branch k))
            ((child :: node).length + n) =
          branchPrefix branch n ++ child :: node
      rw [show (child :: node).length + n = node.length + (n + 1) by
        simp [Nat.add_comm, Nat.add_left_comm]]
      rw [ih]
      rw [branchPrefix_shift]
      simp [List.append_assoc]

@[simp]
theorem branchPrefix_length (branch : Nat -> Nat) (n : Nat) :
    (branchPrefix branch n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [branchPrefix, ih]

/-- A run tree of an alternating parity automaton on a word. -/
structure Run {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) where
  active : Node -> Prop
  stateAt : Node -> A.State
  root_active : active []
  root_state : stateAt [] = A.initial
  step_satisfied :
    ∀ node : Node,
      active node ->
        PosBool.Eval
          (fun nextState =>
            ∃ child : Nat, active (child :: node) ∧ stateAt (child :: node) = nextState)
          (A.step (stateAt node) (word node.length))

/-- A branch follows active nodes of a run tree. -/
def Run.ActiveBranch {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat) :
    Prop :=
  ∀ n : Nat, run.active (branchPrefix branch n)

/-- Priority `p` is seen infinitely often along an active branch. -/
def Run.PrioritySeenInfinitelyOften {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat)
    (p : Nat) :
    Prop :=
    ∀ n : Nat,
    ∃ k : Nat,
      n ≤ k ∧ A.priority (run.stateAt (branchPrefix branch k)) = p

/-- Some priority occurs infinitely often along every branch of a finite APA run tree. -/
theorem Run.exists_prioritySeenInfinitelyOften {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat) :
    ∃ p : Nat, run.PrioritySeenInfinitelyOften branch p := by
  classical
  let branchState : Nat -> A.State :=
    fun n => run.stateAt (branchPrefix branch n)
  obtain ⟨loopState, hloop⟩ := Finite.exists_infinite_fiber branchState
  refine ⟨A.priority loopState, ?_⟩
  have hfreq : ∃ᶠ n in Filter.atTop, branchState n = loopState := by
    rw [Nat.frequently_atTop_iff_infinite]
    simpa [branchState, Set.preimage, Set.mem_singleton_iff] using
      (Set.infinite_coe_iff.1 hloop)
  rw [Filter.frequently_atTop] at hfreq
  intro n
  rcases hfreq n with ⟨k, hk, hkloop⟩
  exact ⟨k, hk, by simp [branchState] at hkloop; simp [hkloop]⟩

/-- The infinitely often seen priorities on an APA branch have a least element. -/
theorem Run.exists_min_prioritySeenInfinitelyOften {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat) :
    ∃ p : Nat,
      run.PrioritySeenInfinitelyOften branch p ∧
        ∀ q : Nat, run.PrioritySeenInfinitelyOften branch q -> p ≤ q := by
  classical
  let seen : Set Nat := {p | run.PrioritySeenInfinitelyOften branch p}
  have hseenFinite : seen.Finite := by
    refine (Set.finite_range A.priority).subset ?_
    intro p hp
    rcases hp 0 with ⟨k, _hk, hkprio⟩
    exact ⟨run.stateAt (branchPrefix branch k), hkprio⟩
  have hseenNonempty : seen.Nonempty := by
    rcases run.exists_prioritySeenInfinitelyOften branch with ⟨p, hp⟩
    exact ⟨p, hp⟩
  rcases Set.exists_min_image seen id hseenFinite hseenNonempty with
    ⟨p, hpSeen, hpMin⟩
  exact ⟨p, hpSeen, fun q hq => hpMin q hq⟩

/-- Parity acceptance for one branch of a run tree. -/
def Run.BranchAccepts {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat) :
    Prop :=
  ∃ p : Nat,
    DetParityAutomaton.NatEven p ∧
      run.PrioritySeenInfinitelyOften branch p ∧
        ∀ q : Nat, run.PrioritySeenInfinitelyOften branch q -> p ≤ q

/-- A branch accepts exactly when its least recurring priority is even. -/
theorem Run.branchAccepts_iff_min_priority_even {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat) :
    run.BranchAccepts branch ↔
      ∃ p : Nat,
        run.PrioritySeenInfinitelyOften branch p ∧
          (∀ q : Nat, run.PrioritySeenInfinitelyOften branch q -> p ≤ q) ∧
            DetParityAutomaton.NatEven p := by
  constructor
  · intro h
    rcases h with ⟨p, hpEven, hpSeen, hpMin⟩
    exact ⟨p, hpSeen, hpMin, hpEven⟩
  · intro h
    rcases h with ⟨p, hpSeen, hpMin, hpEven⟩
    exact ⟨p, hpEven, hpSeen, hpMin⟩

/--
If the priorities on a branch are eventually constant and even, then the
branch satisfies the parity condition.
-/
theorem Run.branchAccepts_of_eventually_priority {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat)
    (p : Nat)
    (hpEven : DetParityAutomaton.NatEven p)
    (heventual :
      ∃ N : Nat,
        ∀ n : Nat, N ≤ n ->
          A.priority (run.stateAt (branchPrefix branch n)) = p) :
    run.BranchAccepts branch := by
  rcases heventual with ⟨N, hN⟩
  refine ⟨p, hpEven, ?_, ?_⟩
  · intro n
    refine ⟨max n N, ?_, ?_⟩
    · exact Nat.le_max_left n N
    · exact hN (max n N) (Nat.le_max_right n N)
  · intro q hqSeen
    rcases hqSeen N with ⟨k, hkN, hkq⟩
    have hpq : p = q := by
      rw [← hkq]
      exact (hN k hkN).symm
    rw [hpq]

/--
If the priorities on a branch are eventually constant and odd, then the branch
cannot satisfy the parity condition.
-/
theorem Run.not_branchAccepts_of_eventually_odd_priority {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat)
    (p : Nat)
    (hpOdd : ¬ DetParityAutomaton.NatEven p)
    (heventual :
      ∃ N : Nat,
        ∀ n : Nat, N ≤ n ->
          A.priority (run.stateAt (branchPrefix branch n)) = p) :
    ¬ run.BranchAccepts branch := by
  intro hBranch
  rcases hBranch with ⟨q, hqEven, hqSeen, _hqMin⟩
  rcases heventual with ⟨N, hN⟩
  rcases hqSeen N with ⟨k, hkN, hkq⟩
  have hpq : p = q := (hN k hkN).symm.trans hkq
  exact hpOdd (by
    rw [hpq]
    exact hqEven)

/-- A run tree is accepting if every active branch satisfies the parity condition. -/
def Run.Accepting {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word) :
    Prop :=
  ∀ branch : Nat -> Nat, run.ActiveBranch branch -> run.BranchAccepts branch

/--
An accepting run cannot contain an active branch whose priorities are
eventually constant and odd.
-/
theorem Run.not_accepting_of_eventually_odd_priority {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat)
    (hactive : run.ActiveBranch branch)
    (p : Nat)
    (hpOdd : ¬ DetParityAutomaton.NatEven p)
    (heventual :
      ∃ N : Nat,
        ∀ n : Nat, N ≤ n ->
          A.priority (run.stateAt (branchPrefix branch n)) = p) :
    ¬ run.Accepting := by
  intro hacc
  exact
    (run.not_branchAccepts_of_eventually_odd_priority branch p hpOdd heventual)
      (hacc branch hactive)

/-- Acceptance can be proved branchwise by showing that each least recurring priority is even. -/
theorem Run.accepting_of_all_min_priority_even {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (hminEven :
      ∀ branch : Nat -> Nat,
        run.ActiveBranch branch ->
          ∃ p : Nat,
            run.PrioritySeenInfinitelyOften branch p ∧
              (∀ q : Nat, run.PrioritySeenInfinitelyOften branch q -> p ≤ q) ∧
                DetParityAutomaton.NatEven p) :
    run.Accepting := by
  intro branch hbranch
  exact (run.branchAccepts_iff_min_priority_even branch).mpr
    (hminEven branch hbranch)

/-- The branch-minimum formulation is equivalent to APA run acceptance. -/
theorem Run.accepting_iff_all_min_priority_even {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word) :
    run.Accepting ↔
      ∀ branch : Nat -> Nat,
        run.ActiveBranch branch ->
          ∃ p : Nat,
            run.PrioritySeenInfinitelyOften branch p ∧
              (∀ q : Nat, run.PrioritySeenInfinitelyOften branch q -> p ≤ q) ∧
                DetParityAutomaton.NatEven p := by
  constructor
  · intro hacc branch hbranch
    exact (run.branchAccepts_iff_min_priority_even branch).mp
      (hacc branch hbranch)
  · exact run.accepting_of_all_min_priority_even

/-- Run-tree acceptance of an alternating parity automaton. -/
def Accepts {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    Prop :=
  ∃ run : A.Run word, run.Accepting

/-- The same alternating automaton with a different initial state. -/
def withInitial {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.State) :
    AlternatingParityAutomaton Alphabet where
  State := A.State
  stateFinite := A.stateFinite
  initial := state
  step := A.step
  priority := A.priority

/-- Acceptance from an arbitrary state. -/
def AcceptsFrom {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    Prop :=
  (A.withInitial state).Accepts word

/--
Active-node predicate for a run obtained by splicing one root expansion with
the accepting child subruns below its active children.
-/
def splicedActive {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {letter : Alphabet}
    (expansion : A.StepExpansion state letter)
    {wordTail : OmegaWord Alphabet}
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run wordTail)
    (node : Node) :
    Prop :=
  match Node.rootDecomposition node with
  | none => True
  | some (rootChild, suffix) =>
      ∃ hactive : expansion.childActive rootChild,
        (childRun rootChild hactive).active suffix

/--
State labeling for a run obtained by splicing one root expansion with child
subruns.  Inactive/default nodes are labeled by the root state; only active
nodes matter for run correctness.
-/
noncomputable def splicedStateAt {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {letter : Alphabet}
    (expansion : A.StepExpansion state letter)
    {wordTail : OmegaWord Alphabet}
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run wordTail)
    (node : Node) :
    A.State := by
  classical
  exact
    match Node.rootDecomposition node with
    | none => state
    | some (rootChild, suffix) =>
        if hactive : expansion.childActive rootChild then
          (childRun rootChild hactive).stateAt suffix
        else
          state

@[simp]
theorem splicedActive_nil {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {letter : Alphabet}
    (expansion : A.StepExpansion state letter)
    {wordTail : OmegaWord Alphabet}
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run wordTail) :
    splicedActive A expansion childRun [] := by
  simp [splicedActive]

@[simp]
theorem splicedStateAt_nil {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {letter : Alphabet}
    (expansion : A.StepExpansion state letter)
    {wordTail : OmegaWord Alphabet}
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run wordTail) :
    splicedStateAt A expansion childRun [] = state := by
  simp [splicedStateAt]

@[simp]
theorem splicedActive_append_singleton {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {letter : Alphabet}
    (expansion : A.StepExpansion state letter)
    {wordTail : OmegaWord Alphabet}
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run wordTail)
    (suffix : Node)
    (rootChild : Nat) :
    splicedActive A expansion childRun (suffix ++ [rootChild]) ↔
      ∃ hactive : expansion.childActive rootChild,
        (childRun rootChild hactive).active suffix := by
  simp [splicedActive]

theorem splicedStateAt_append_singleton_of_inactive {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {letter : Alphabet}
    (expansion : A.StepExpansion state letter)
    {wordTail : OmegaWord Alphabet}
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run wordTail)
    (suffix : Node)
    {rootChild : Nat}
    (hinactive : ¬ expansion.childActive rootChild) :
    splicedStateAt A expansion childRun (suffix ++ [rootChild]) = state := by
  simp [splicedStateAt, hinactive]

theorem splicedStateAt_append_singleton_of_active {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {letter : Alphabet}
    (expansion : A.StepExpansion state letter)
    {wordTail : OmegaWord Alphabet}
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run wordTail)
    (suffix : Node)
    {rootChild : Nat}
    (hactive : expansion.childActive rootChild) :
    splicedStateAt A expansion childRun (suffix ++ [rootChild]) =
      (childRun rootChild hactive).stateAt suffix := by
  classical
  simp [splicedStateAt, hactive]

theorem splicedActive_cons_of_decomposition {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {letter : Alphabet}
    (expansion : A.StepExpansion state letter)
    {wordTail : OmegaWord Alphabet}
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run wordTail)
    {node : Node}
    {rootChild : Nat}
    {suffix : Node}
    (hdecomp : Node.rootDecomposition node = some (rootChild, suffix))
    (child : Nat) :
    splicedActive A expansion childRun (child :: node) ↔
      ∃ hactive : expansion.childActive rootChild,
        (childRun rootChild hactive).active (child :: suffix) := by
  simp [splicedActive, Node.rootDecomposition_cons_of_some hdecomp child]

theorem splicedStateAt_cons_of_decomposition {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {letter : Alphabet}
    (expansion : A.StepExpansion state letter)
    {wordTail : OmegaWord Alphabet}
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run wordTail)
    {node : Node}
    {rootChild : Nat}
    {suffix : Node}
    (hdecomp : Node.rootDecomposition node = some (rootChild, suffix))
    (child : Nat)
    (hactive : expansion.childActive rootChild) :
    splicedStateAt A expansion childRun (child :: node) =
      (childRun rootChild hactive).stateAt (child :: suffix) := by
  classical
  simp [splicedStateAt, Node.rootDecomposition_cons_of_some hdecomp child,
    hactive]

theorem splicedActive_of_decomposition {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {letter : Alphabet}
    (expansion : A.StepExpansion state letter)
    {wordTail : OmegaWord Alphabet}
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run wordTail)
    {node : Node}
    {rootChild : Nat}
    {suffix : Node}
    (hdecomp : Node.rootDecomposition node = some (rootChild, suffix)) :
    splicedActive A expansion childRun node ↔
      ∃ hactive : expansion.childActive rootChild,
        (childRun rootChild hactive).active suffix := by
  simp [splicedActive, hdecomp]

theorem splicedStateAt_of_decomposition {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {letter : Alphabet}
    (expansion : A.StepExpansion state letter)
    {wordTail : OmegaWord Alphabet}
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run wordTail)
    {node : Node}
    {rootChild : Nat}
    {suffix : Node}
    (hdecomp : Node.rootDecomposition node = some (rootChild, suffix))
    (hactive : expansion.childActive rootChild) :
    splicedStateAt A expansion childRun node =
      (childRun rootChild hactive).stateAt suffix := by
  classical
  simp [splicedStateAt, hdecomp, hactive]

/--
Splice one local root expansion with run trees for all active root children.

This is the structural constructor behind the reverse direction of the APA
fixed-point equation.
-/
noncomputable def splicedRun {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (expansion : A.StepExpansion state (word 0))
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run (OmegaWord.drop word 1)) :
    (A.withInitial state).Run word where
  active := splicedActive A expansion childRun
  stateAt := splicedStateAt A expansion childRun
  root_active := by
    simp
  root_state := by
    simp [AlternatingParityAutomaton.withInitial]
  step_satisfied := by
    classical
    intro node hnode
    cases hdecomp : Node.rootDecomposition node with
    | none =>
        have hnodeEq : node = [] :=
          Node.rootDecomposition_none_iff.mp hdecomp
        subst node
        change
          PosBool.Eval
            (fun nextState =>
              ∃ child : Nat,
                splicedActive A expansion childRun [child] ∧
                  splicedStateAt A expansion childRun [child] = nextState)
            (A.step (splicedStateAt A expansion childRun []) (word 0))
        simp only [splicedStateAt_nil]
        refine
          PosBool.eval_mono
            (fun nextState hnext => ?_)
            (A.step state (word 0))
            expansion.step_satisfied
        rcases hnext with ⟨child, hchildActive, hchildState⟩
        refine ⟨child, ?_, ?_⟩
        · exact
            (splicedActive_append_singleton A expansion childRun [] child).mpr
              ⟨hchildActive,
                by
                  simpa using (childRun child hchildActive).root_active⟩
        · rw [← hchildState]
          have hsp :
              splicedStateAt A expansion childRun ([] ++ [child]) =
                (childRun child hchildActive).stateAt [] :=
            splicedStateAt_append_singleton_of_active
              A expansion childRun [] hchildActive
          have hroot :
              (childRun child hchildActive).stateAt [] =
                expansion.childState child := by
            simpa [AlternatingParityAutomaton.withInitial] using
              (childRun child hchildActive).root_state
          simpa using hsp.trans hroot
    | some data =>
        rcases data with ⟨rootChild, suffix⟩
        have hactiveSub :
            ∃ hactive : expansion.childActive rootChild,
              (childRun rootChild hactive).active suffix :=
          (splicedActive_of_decomposition A expansion childRun hdecomp).mp hnode
        rcases hactiveSub with ⟨hrootActive, hsuffixActive⟩
        have hstateAt :
            splicedStateAt A expansion childRun node =
              (childRun rootChild hrootActive).stateAt suffix :=
          splicedStateAt_of_decomposition A expansion childRun hdecomp hrootActive
        have hstep :=
          (childRun rootChild hrootActive).step_satisfied suffix hsuffixActive
        have hnodeEq : node = suffix ++ [rootChild] :=
          Node.eq_append_singleton_of_rootDecomposition hdecomp
        have hletter :
            word node.length =
              OmegaWord.drop word 1 suffix.length := by
          subst node
          simp [OmegaWord.drop, List.length_append, Nat.add_comm]
        change
          PosBool.Eval
            (fun nextState =>
              ∃ child : Nat,
                splicedActive A expansion childRun (child :: node) ∧
                  splicedStateAt A expansion childRun (child :: node) =
                    nextState)
            ((A.withInitial state).step
              (splicedStateAt A expansion childRun node)
              (word node.length))
        rw [hstateAt, hletter]
        change
          PosBool.Eval
            (fun nextState =>
              ∃ child : Nat,
                splicedActive A expansion childRun (child :: node) ∧
                  splicedStateAt A expansion childRun (child :: node) =
                    nextState)
            (A.step
              ((childRun rootChild hrootActive).stateAt suffix)
              (OmegaWord.drop word 1 suffix.length))
        refine
          PosBool.eval_mono
            (fun nextState hnext => ?_)
            (A.step
              ((childRun rootChild hrootActive).stateAt suffix)
              (OmegaWord.drop word 1 suffix.length))
            hstep
        rcases hnext with ⟨child, hchildActive, hchildState⟩
        refine ⟨child, ?_, ?_⟩
        · exact
            (splicedActive_cons_of_decomposition
              A expansion childRun hdecomp child).mpr
              ⟨hrootActive, hchildActive⟩
        · rw [← hchildState]
          exact
            splicedStateAt_cons_of_decomposition
              A expansion childRun hdecomp child hrootActive

theorem splicedRun_child_activeBranch {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {word : OmegaWord Alphabet}
    (expansion : A.StepExpansion state (word 0))
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run (OmegaWord.drop word 1))
    (rootChild : Nat)
    (tail : Nat -> Nat)
    (hbranch :
      (A.splicedRun state word expansion childRun).ActiveBranch
        (fun
          | 0 => rootChild
          | n + 1 => tail n)) :
    ∃ hactive : expansion.childActive rootChild,
      (childRun rootChild hactive).ActiveBranch tail := by
  classical
  have hroot :
      splicedActive A expansion childRun ([] ++ [rootChild]) :=
    by
      simpa using hbranch 1
  rcases
    (splicedActive_append_singleton A expansion childRun [] rootChild).mp hroot with
    ⟨hrootActive, _hchildRoot⟩
  refine ⟨hrootActive, ?_⟩
  intro n
  have hspliced :
      splicedActive A expansion childRun
        (branchPrefix tail n ++ [rootChild]) := by
    rw [← branchPrefix_shift rootChild tail n]
    exact hbranch (n + 1)
  exact
    ((splicedActive_append_singleton
      A expansion childRun (branchPrefix tail n) rootChild).mp hspliced).2

theorem splicedRun_stateAt_branchPrefix_shift {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {word : OmegaWord Alphabet}
    (expansion : A.StepExpansion state (word 0))
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run (OmegaWord.drop word 1))
    {rootChild : Nat}
    (hrootActive : expansion.childActive rootChild)
    (tail : Nat -> Nat)
    (n : Nat) :
    (A.splicedRun state word expansion childRun).stateAt
        (branchPrefix
          (fun
            | 0 => rootChild
            | k + 1 => tail k) (n + 1)) =
      (childRun rootChild hrootActive).stateAt (branchPrefix tail n) := by
  rw [branchPrefix_shift]
  exact
    splicedStateAt_append_singleton_of_active
      A expansion childRun (branchPrefix tail n) hrootActive

theorem splicedRun_prioritySeen_of_child {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {word : OmegaWord Alphabet}
    (expansion : A.StepExpansion state (word 0))
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run (OmegaWord.drop word 1))
    {rootChild : Nat}
    (hrootActive : expansion.childActive rootChild)
    (tail : Nat -> Nat)
    {p : Nat}
    (hseen :
      (childRun rootChild hrootActive).PrioritySeenInfinitelyOften tail p) :
    (A.splicedRun state word expansion childRun).PrioritySeenInfinitelyOften
      (fun
        | 0 => rootChild
        | n + 1 => tail n)
      p := by
  intro n
  rcases hseen n with ⟨k, hnk, hkprio⟩
  refine ⟨k + 1, Nat.le_trans hnk (Nat.le_succ k), ?_⟩
  rw [splicedRun_stateAt_branchPrefix_shift
    A expansion childRun hrootActive tail k]
  simpa [AlternatingParityAutomaton.withInitial] using hkprio

theorem child_prioritySeen_of_splicedRun {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {word : OmegaWord Alphabet}
    (expansion : A.StepExpansion state (word 0))
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run (OmegaWord.drop word 1))
    {rootChild : Nat}
    (hrootActive : expansion.childActive rootChild)
    (tail : Nat -> Nat)
    {p : Nat}
    (hseen :
      (A.splicedRun state word expansion childRun).PrioritySeenInfinitelyOften
        (fun
          | 0 => rootChild
          | n + 1 => tail n)
        p) :
    (childRun rootChild hrootActive).PrioritySeenInfinitelyOften tail p := by
  intro n
  rcases hseen (n + 1) with ⟨k, hnk, hkprio⟩
  cases k with
  | zero =>
      omega
  | succ k =>
      have hnk' : n ≤ k := Nat.succ_le_succ_iff.mp hnk
      refine ⟨k, hnk', ?_⟩
      rw [← splicedRun_stateAt_branchPrefix_shift
        A expansion childRun hrootActive tail k]
      simpa [AlternatingParityAutomaton.withInitial] using hkprio

theorem splicedRun_branchAccepts_of_child {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {state : A.State}
    {word : OmegaWord Alphabet}
    (expansion : A.StepExpansion state (word 0))
    (childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run (OmegaWord.drop word 1))
    {rootChild : Nat}
    (hrootActive : expansion.childActive rootChild)
    (tail : Nat -> Nat)
    (haccepts :
      (childRun rootChild hrootActive).BranchAccepts tail) :
    (A.splicedRun state word expansion childRun).BranchAccepts
      (fun
        | 0 => rootChild
        | n + 1 => tail n) := by
  rcases haccepts with ⟨p, hpEven, hpSeen, hpMin⟩
  refine
    ⟨p, hpEven,
      splicedRun_prioritySeen_of_child
        A expansion childRun hrootActive tail hpSeen,
      ?_⟩
  intro q hqSeen
  exact hpMin q
    (child_prioritySeen_of_splicedRun
      A expansion childRun hrootActive tail hqSeen)

/--
Reverse one-step fixed-point direction for APA acceptance: if the symbolic
transition can be satisfied by successor states that accept the tail word, then
the current state accepts the full word.
-/
theorem acceptsFrom_of_step {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (hstep :
      PosBool.Eval
        (fun nextState => A.AcceptsFrom nextState (OmegaWord.drop word 1))
        (A.step state (word 0))) :
    A.AcceptsFrom state word := by
  classical
  rcases A.step_exists_expansion
      (fun nextState => A.AcceptsFrom nextState (OmegaWord.drop word 1))
      state (word 0) hstep with
    ⟨expansion, hchildAccepts⟩
  let childRun :
      ∀ child, expansion.childActive child ->
        (A.withInitial (expansion.childState child)).Run (OmegaWord.drop word 1) :=
    fun child hactive =>
      Classical.choose (hchildAccepts child hactive)
  have hchildRunAccepting :
      ∀ child hactive, (childRun child hactive).Accepting := by
    intro child hactive
    exact Classical.choose_spec (hchildAccepts child hactive)
  refine ⟨A.splicedRun state word expansion childRun, ?_⟩
  intro branch hbranch
  let rootChild : Nat := branch 0
  let tail : Nat -> Nat := fun n => branch (n + 1)
  have hbranchEq :
      (fun
        | 0 => rootChild
        | n + 1 => tail n) = branch := by
    funext n
    cases n <;> rfl
  have hbranchCons :
      (A.splicedRun state word expansion childRun).ActiveBranch
        (fun
          | 0 => rootChild
          | n + 1 => tail n) := by
    simpa [hbranchEq] using hbranch
  rcases
    splicedRun_child_activeBranch
      A expansion childRun rootChild tail hbranchCons with
    ⟨hrootActive, htailActive⟩
  have htailAccepts :
      (childRun rootChild hrootActive).BranchAccepts tail :=
    hchildRunAccepting rootChild hrootActive tail htailActive
  have hsplicedAccepts :
      (A.splicedRun state word expansion childRun).BranchAccepts
        (fun
          | 0 => rootChild
          | n + 1 => tail n) :=
    splicedRun_branchAccepts_of_child
      A expansion childRun hrootActive tail htailAccepts
  simpa [hbranchEq] using hsplicedAccepts

namespace Run

variable {Alphabet : Type u}
variable {A : AlternatingParityAutomaton.{u, v} Alphabet}
variable {word : OmegaWord Alphabet}

/-- The finite set of APA states appearing at a fixed level of a run tree. -/
noncomputable def levelStates
    (run : A.Run word)
    (n : Nat) :
    Finset A.State := by
  classical
  exact
    Finset.univ.filter
      (fun state =>
        ∃ node : Node,
          node.length = n ∧
            (∀ pref : Node, ∀ suffix : Node,
              pref ++ suffix = node -> run.active suffix) ∧
              run.stateAt node = state)

@[simp]
theorem mem_levelStates
    (run : A.Run word)
    (n : Nat)
    (state : A.State) :
    state ∈ run.levelStates n ↔
      ∃ node : Node,
        node.length = n ∧
          (∀ pref : Node, ∀ suffix : Node,
            pref ++ suffix = node -> run.active suffix) ∧
            run.stateAt node = state := by
  classical
  simp [levelStates]

/-- The root level of a run tree contains exactly the automaton initial state. -/
theorem levelStates_zero
    (run : A.Run word) :
    run.levelStates 0 = {A.initial} := by
  classical
  ext state
  constructor
  · intro hstate
    rcases (run.mem_levelStates 0 state).mp hstate with
      ⟨node, hlength, _hpath, hnodeState⟩
    have hnodeNil : node = [] := by
      cases node with
      | nil => rfl
      | cons child tail => simp at hlength
    subst node
    have hstateInitial : state = A.initial := by
      simpa [run.root_state] using hnodeState.symm
    simp [hstateInitial]
  · intro hstate
    have hstateInitial : state = A.initial := by
      simpa using hstate
    subst state
    exact (run.mem_levelStates 0 A.initial).mpr
      ⟨[], rfl,
        (by
          intro pref suffix hsuffix
          have hsuffixNil : suffix = [] := by
            cases suffix with
            | nil => rfl
            | cons head tail =>
                cases pref <;> simp at hsuffix
          simpa [hsuffixNil] using run.root_active),
        run.root_state⟩

/-- Every path-active node contributes its state to the corresponding level set. -/
theorem stateAt_mem_levelStates_of_pathActive
    (run : A.Run word)
    {node : Node}
    (hpath :
      ∀ pref : Node, ∀ suffix : Node,
        pref ++ suffix = node -> run.active suffix) :
    run.stateAt node ∈ run.levelStates node.length :=
  (run.mem_levelStates node.length (run.stateAt node)).mpr
    ⟨node, rfl, hpath, rfl⟩

/--
The active children of a representative node show that every run-tree level set
satisfies the APA transition into the next level set.
-/
theorem step_eval_levelStates
    (run : A.Run word)
    {n : Nat}
    {state : A.State}
    (hstate : state ∈ run.levelStates n) :
    PosBool.Eval
      (fun nextState => nextState ∈ run.levelStates (n + 1))
      (A.step state (word n)) := by
  rcases (run.mem_levelStates n state).mp hstate with
    ⟨node, hlength, hpath, hnodeState⟩
  have hactive : run.active node := by
    exact hpath [] node (by simp)
  have hstep :
      PosBool.Eval
        (fun nextState =>
          ∃ child : Nat,
            run.active (child :: node) ∧ run.stateAt (child :: node) = nextState)
        (A.step state (word n)) := by
    simpa [hnodeState, hlength] using run.step_satisfied node hactive
  refine
    PosBool.eval_mono
      (fun nextState hnext => ?_)
      (A.step state (word n))
      hstep
  rcases hnext with ⟨child, hchildActive, hchildState⟩
  rw [← hchildState]
  have hchildPath :
      ∀ pref : Node, ∀ suffix : Node,
        pref ++ suffix = child :: node -> run.active suffix := by
    intro pref suffix hsuffix
    cases pref with
    | nil =>
        have hsuffixEq : suffix = child :: node := by
          simpa using hsuffix
        simpa [hsuffixEq] using hchildActive
    | cons head tail =>
        have htail : tail ++ suffix = node := by
          simpa using congrArg List.tail hsuffix
        exact hpath tail suffix htail
  have hmem :
      run.stateAt (child :: node) ∈
        run.levelStates (child :: node).length :=
    run.stateAt_mem_levelStates_of_pathActive hchildPath
  simpa [hlength, Nat.add_comm] using hmem

/--
Every run-tree level has some finite macro successor contained in the next
run-tree level.  This is the sound local extraction used by the APA-to-Muller
construction; it is weaker than choosing a whole accepting macro-run, but it is
derived from one concrete run tree.
-/
theorem exists_macroTransition_to_levelStates_subset
    (run : A.Run word)
    (n : Nat) :
    ∃ nextStates : Finset A.State,
      A.MacroTransition (run.levelStates n) (word n) nextStates ∧
      nextStates ⊆ A.subsetStepAtoms (run.levelStates n) (word n) ∧
      nextStates ⊆ run.levelStates (n + 1) := by
  rcases
    A.exists_macroTransition_of_eval_all
      (fun nextState => nextState ∈ run.levelStates (n + 1))
      (run.levelStates n)
      (word n)
      (by
        intro state hstate
        exact run.step_eval_levelStates hstate) with
    ⟨nextStates, htransition, hsubsetAtoms, hsubsetLevel⟩
  exact ⟨nextStates, htransition, hsubsetAtoms, by
    intro nextState hnext
    exact hsubsetLevel nextState hnext⟩

/--
Any finite set of states already known to occur at level `n` has a macro
successor contained in the next actual run-tree level.
-/
theorem exists_macroTransition_of_subset_levelStates
    (run : A.Run word)
    {n : Nat}
    {states : Finset A.State}
    (hstates : states ⊆ run.levelStates n) :
    ∃ nextStates : Finset A.State,
      A.MacroTransition states (word n) nextStates ∧
      nextStates ⊆ A.subsetStepAtoms states (word n) ∧
      nextStates ⊆ run.levelStates (n + 1) := by
  rcases
    A.exists_macroTransition_of_eval_all
      (fun nextState => nextState ∈ run.levelStates (n + 1))
      states
      (word n)
      (by
        intro state hstate
        exact run.step_eval_levelStates (hstates hstate)) with
    ⟨nextStates, htransition, hsubsetAtoms, hsubsetLevel⟩
  exact ⟨nextStates, htransition, hsubsetAtoms, by
    intro nextState hnext
    exact hsubsetLevel nextState hnext⟩

/--
A recursively chosen macro-state sequence extracted from one concrete run tree.
Every chosen macro-state is contained in the actual level set at the same time.
-/
noncomputable def levelMacroState
    (run : A.Run word) :
    ∀ n : Nat, { states : Finset A.State // states ⊆ run.levelStates n }
  | 0 =>
      ⟨{A.initial}, by
        rw [run.levelStates_zero]⟩
  | n + 1 =>
      let current := levelMacroState run n
      let witness :=
        Classical.choose
          (run.exists_macroTransition_of_subset_levelStates current.property)
      ⟨witness,
        (Classical.choose_spec
          (run.exists_macroTransition_of_subset_levelStates
            current.property)).2.2⟩

@[simp]
theorem levelMacroState_zero
    (run : A.Run word) :
    (run.levelMacroState 0).1 = {A.initial} :=
  rfl

theorem levelMacroState_subset_levelStates
    (run : A.Run word)
    (n : Nat) :
    (run.levelMacroState n).1 ⊆ run.levelStates n :=
  (run.levelMacroState n).2

theorem levelMacroState_transition
    (run : A.Run word)
    (n : Nat) :
    A.MacroTransition
      (run.levelMacroState n).1
      (word n)
      (run.levelMacroState (n + 1)).1 := by
  simp [levelMacroState]
  exact
    (Classical.choose_spec
      (run.exists_macroTransition_of_subset_levelStates
        (run.levelMacroState n).property)).1

/--
The macro-run extracted from one concrete APA run tree.  Its states may be a
proper subset of the full run-tree level, but every chosen state appears in the
run tree at the matching level.
-/
noncomputable def levelMacroRun
    (run : A.Run word) :
    A.MacroRun {A.initial} word where
  states n := (run.levelMacroState n).1
  initial_states := run.levelMacroState_zero
  step_transition := run.levelMacroState_transition

@[simp]
theorem levelMacroRun_states
    (run : A.Run word)
    (n : Nat) :
    run.levelMacroRun.states n = (run.levelMacroState n).1 :=
  rfl

theorem levelMacroRun_states_subset_levelStates
    (run : A.Run word)
    (n : Nat) :
    run.levelMacroRun.states n ⊆ run.levelStates n :=
  run.levelMacroState_subset_levelStates n

/-- A finite node lies on an active root-to-node path. -/
def PathActive
    (run : A.Run word)
    (node : Node) :
    Prop :=
  ∀ pref : Node, ∀ suffix : Node, pref ++ suffix = node -> run.active suffix

theorem pathActive_nil
    (run : A.Run word) :
    run.PathActive [] := by
  intro pref suffix hsuffix
  have hsuffixNil : suffix = [] := by
    cases suffix with
    | nil => rfl
    | cons head tail =>
        cases pref <;> simp at hsuffix
  simpa [hsuffixNil] using run.root_active

theorem pathActive_self
    (run : A.Run word)
    (node : Node)
    (hpath : run.PathActive node) :
    run.active node := by
  exact hpath [] node (by simp)

theorem pathActive_cons
    (run : A.Run word)
    (child : Nat)
    (node : Node)
    (hpath : run.PathActive (child :: node)) :
    run.PathActive node := by
  intro pref suffix hsuffix
  exact hpath (child :: pref) suffix (by simp [hsuffix])

theorem PathActive.extend
    (run : A.Run word)
    (node : Node)
    (hpath : run.PathActive node)
    (child : Nat)
    (hchild : run.active (child :: node)) :
    run.PathActive (child :: node) := by
  intro pref suffix hsuffix
  cases pref with
  | nil =>
      have hsuffixEq : suffix = child :: node := by
        simpa using hsuffix
      simpa [hsuffixEq] using hchild
  | cons head tail =>
      have htail : tail ++ suffix = node := by
        simpa using congrArg List.tail hsuffix
      exact hpath tail suffix htail

/--
An individual state edge is realized by an actual active parent/child edge of
the run tree between levels `n` and `n + 1`.
-/
def StateEdgeRealizedAtLevel
    (run : A.Run word)
    (n : Nat)
    (edge : A.State × A.State) :
    Prop :=
  ∃ node : Node,
    ∃ child : Nat,
      node.length = n ∧
        run.PathActive node ∧
          run.stateAt node = edge.1 ∧
            run.active (child :: node) ∧
              run.stateAt (child :: node) = edge.2

/--
Every finite set of states drawn from a run-tree level has a macro transition
whose individual support edges are all witnessed by actual active child edges
of the run tree.

This strengthens `exists_macroTransition_of_subset_levelStates`: besides
staying inside the next level, it records enough local provenance to later
reason about branches through support edges.
-/
theorem exists_macroTransitionWithStateEdges_of_subset_levelStates
    (run : A.Run word)
    {n : Nat}
    {states : Finset A.State}
    (hstates : states ⊆ run.levelStates n) :
    ∃ nextStates : Finset A.State,
      ∃ stateEdges : Finset (A.State × A.State),
        A.MacroTransitionWithStateEdges states (word n) nextStates stateEdges ∧
          nextStates ⊆ run.levelStates (n + 1) ∧
            ∀ edge, edge ∈ stateEdges ->
              run.StateEdgeRealizedAtLevel n edge := by
  classical
  let sourceNode : (state : { state // state ∈ states }) -> Node :=
    fun state =>
      Classical.choose ((run.mem_levelStates n state.1).mp (hstates state.2))
  have sourceNode_spec :
      ∀ state : { state // state ∈ states },
        (sourceNode state).length = n ∧
          run.PathActive (sourceNode state) ∧
            run.stateAt (sourceNode state) = state.1 := by
    intro state
    exact Classical.choose_spec
      ((run.mem_levelStates n state.1).mp (hstates state.2))
  have sourceNode_active :
      ∀ state : { state // state ∈ states },
        run.active (sourceNode state) := by
    intro state
    exact (sourceNode_spec state).2.1 [] (sourceNode state) (by simp)
  let valuation :
      (state : { state // state ∈ states }) -> A.State -> Prop :=
    fun state nextState =>
      ∃ child : Nat,
        run.active (child :: sourceNode state) ∧
          run.stateAt (child :: sourceNode state) = nextState
  have hstep :
      ∀ state : { state // state ∈ states },
        PosBool.Eval (valuation state) (A.step state.1 (word n)) := by
    intro state
    have hraw := run.step_satisfied
      (sourceNode state) (sourceNode_active state)
    have hstateEq := (sourceNode_spec state).2.2
    have hlength := (sourceNode_spec state).1
    simpa [valuation, hstateEq, hlength] using hraw
  let stepSupport :
      ∀ state : { state // state ∈ states },
        A.StepSupport state.1 (word n) :=
    fun state =>
      Classical.choose
        (A.stepSupport_exists_of_eval
          (valuation state) state.1 (word n) (hstep state))
  have stepSupport_spec :
      ∀ state : { state // state ∈ states },
        ∀ nextState,
          nextState ∈ (stepSupport state).support ->
            valuation state nextState := by
    intro state nextState hnext
    exact Classical.choose_spec
      (A.stepSupport_exists_of_eval
        (valuation state) state.1 (word n) (hstep state))
      nextState hnext
  let macroSupport : A.MacroStepSupport states (word n) :=
    { choice := stepSupport }
  refine ⟨macroSupport.support, macroSupport.stateEdges, ?_, ?_, ?_⟩
  · exact ⟨macroSupport, rfl, rfl⟩
  · intro nextState hnext
    rcases
      (MacroStepSupport.mem_support
        (supportChoice := macroSupport)
        (nextState := nextState)).mp hnext with
      ⟨state, hstateNext⟩
    rcases stepSupport_spec state nextState hstateNext with
      ⟨child, hchildActive, hchildState⟩
    rw [← hchildState]
    have hchildPath :
        run.PathActive (child :: sourceNode state) :=
      (sourceNode_spec state).2.1.extend run (sourceNode state) child hchildActive
    have hmem :
        run.stateAt (child :: sourceNode state) ∈
          run.levelStates (child :: sourceNode state).length :=
      run.stateAt_mem_levelStates_of_pathActive hchildPath
    simpa [(sourceNode_spec state).1, Nat.add_comm] using hmem
  · intro edge hedge
    rcases
      (MacroStepSupport.mem_stateEdges
        (supportChoice := macroSupport)).mp hedge with
      ⟨state, hsource, htarget⟩
    rcases stepSupport_spec state edge.2 htarget with
      ⟨child, hchildActive, hchildState⟩
    exact
      ⟨sourceNode state, child,
        (sourceNode_spec state).1,
        (sourceNode_spec state).2.1,
        by simpa [hsource] using (sourceNode_spec state).2.2,
        hchildActive,
        hchildState⟩

/--
A recursively chosen macro-state sequence whose step witnesses are realized by
actual active parent/child edges of the run tree.
-/
noncomputable def realizedLevelMacroState
    (run : A.Run word) :
    ∀ n : Nat, { states : Finset A.State // states ⊆ run.levelStates n }
  | 0 =>
      ⟨{A.initial}, by
        rw [run.levelStates_zero]⟩
  | n + 1 =>
      let current := realizedLevelMacroState run n
      let witness :=
        Classical.choose
          (run.exists_macroTransitionWithStateEdges_of_subset_levelStates
            current.property)
      ⟨witness,
        (Classical.choose_spec
          (Classical.choose_spec
            (run.exists_macroTransitionWithStateEdges_of_subset_levelStates
              current.property))).2.1⟩

@[simp]
theorem realizedLevelMacroState_zero
    (run : A.Run word) :
    (run.realizedLevelMacroState 0).1 = {A.initial} :=
  rfl

theorem realizedLevelMacroState_subset_levelStates
    (run : A.Run word)
    (n : Nat) :
    (run.realizedLevelMacroState n).1 ⊆ run.levelStates n :=
  (run.realizedLevelMacroState n).2

/--
The realized macro-state sequence has a macro transition whose individual
state edges are actual active run-tree child edges.
-/
theorem realizedLevelMacroState_transitionWithStateEdges
    (run : A.Run word)
    (n : Nat) :
    ∃ stateEdges : Finset (A.State × A.State),
      A.MacroTransitionWithStateEdges
        (run.realizedLevelMacroState n).1
        (word n)
        (run.realizedLevelMacroState (n + 1)).1
        stateEdges ∧
        ∀ edge, edge ∈ stateEdges ->
          run.StateEdgeRealizedAtLevel n edge := by
  let h :=
    run.exists_macroTransitionWithStateEdges_of_subset_levelStates
      (run.realizedLevelMacroState n).property
  let hnext := Classical.choose_spec h
  let stateEdges := Classical.choose hnext
  have hspec := Classical.choose_spec hnext
  change
    ∃ stateEdges : Finset (A.State × A.State),
      A.MacroTransitionWithStateEdges
        (run.realizedLevelMacroState n).1
        (word n)
        (Classical.choose h)
        stateEdges ∧
        ∀ edge, edge ∈ stateEdges ->
          run.StateEdgeRealizedAtLevel n edge
  exact ⟨stateEdges, hspec.1, hspec.2.2⟩

theorem realizedLevelMacroState_transition
    (run : A.Run word)
    (n : Nat) :
    A.MacroTransition
      (run.realizedLevelMacroState n).1
      (word n)
      (run.realizedLevelMacroState (n + 1)).1 := by
  rcases run.realizedLevelMacroState_transitionWithStateEdges n with
    ⟨stateEdges, htransition, _hrealized⟩
  exact htransition.to_macroTransition

/--
The macro-run extracted from one concrete APA run tree using only support
choices realized by active run-tree child edges.
-/
noncomputable def realizedLevelMacroRun
    (run : A.Run word) :
    A.MacroRun {A.initial} word where
  states n := (run.realizedLevelMacroState n).1
  initial_states := run.realizedLevelMacroState_zero
  step_transition := run.realizedLevelMacroState_transition

@[simp]
theorem realizedLevelMacroRun_states
    (run : A.Run word)
    (n : Nat) :
    run.realizedLevelMacroRun.states n = (run.realizedLevelMacroState n).1 :=
  rfl

theorem realizedLevelMacroRun_states_subset_levelStates
    (run : A.Run word)
    (n : Nat) :
    run.realizedLevelMacroRun.states n ⊆ run.levelStates n :=
  run.realizedLevelMacroState_subset_levelStates n

/--
The subtree below any active node is a run from the state stored at that node on
the corresponding suffix of the input word.
-/
def subRun
    (run : A.Run word)
    (node : Node)
    (hnode : run.active node) :
    (A.withInitial (run.stateAt node)).Run (OmegaWord.drop word node.length) where
  active suffix := run.active (suffix ++ node)
  stateAt suffix := run.stateAt (suffix ++ node)
  root_active := by
    simpa using hnode
  root_state := rfl
  step_satisfied := by
    intro suffix hactive
    have hstep := run.step_satisfied (suffix ++ node) hactive
    simpa [AlternatingParityAutomaton.withInitial, List.length_append,
      OmegaWord.drop, Nat.add_comm, Nat.add_assoc] using hstep

@[simp] theorem subRun_active
    (run : A.Run word)
    (node : Node)
    (hnode : run.active node)
    (suffix : Node) :
    (run.subRun node hnode).active suffix = run.active (suffix ++ node) :=
  rfl

@[simp] theorem subRun_stateAt
    (run : A.Run word)
    (node : Node)
    (hnode : run.active node)
    (suffix : Node) :
    (run.subRun node hnode).stateAt suffix = run.stateAt (suffix ++ node) :=
  rfl

theorem PathActive.extend_of_subRun_child
    (run : A.Run word)
    (node : Node)
    (hpath : run.PathActive node)
    (hnode : run.active node)
    (child : Nat)
    (hchild : (run.subRun node hnode).active [child]) :
    run.PathActive (child :: node) := by
  exact hpath.extend run node child (by simpa using hchild)

theorem active_branchPrependNode_prefix
    (run : A.Run word)
    (node : Node)
    (branch : Nat -> Nat)
    (hpath : run.PathActive node) :
    ∀ k : Nat, k ≤ node.length ->
      run.active (branchPrefix (branchPrependNode node branch) k) := by
  induction node generalizing branch with
  | nil =>
      intro k hk
      have hkzero : k = 0 := Nat.eq_zero_of_le_zero hk
      simpa [hkzero, branchPrependNode] using run.root_active
  | cons child node ih =>
      intro k hk
      by_cases hkle : k ≤ node.length
      · exact ih
          (fun
            | 0 => child
            | n + 1 => branch n)
          (run.pathActive_cons child node hpath) k hkle
      · have hklen : k = node.length + 1 := by
          apply Nat.le_antisymm
          · simpa using hk
          · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hkle)
        have hself : run.active (child :: node) :=
          run.pathActive_self (child :: node) hpath
        change run.active
          (branchPrefix
            (branchPrependNode node (fun
              | 0 => child
              | n + 1 => branch n)) k)
        rw [hklen]
        rw [branchPrefix_prependNode]
        simpa [branchPrefix_shift] using hself

/--
Acceptance is inherited by the subtree below any node that is reached through
active prefixes of the original run.
-/
theorem subRun_accepting
    (run : A.Run word)
    (node : Node)
    (hpath : run.PathActive node)
    (hnode : run.active node)
    (hacc : run.Accepting) :
    (run.subRun node hnode).Accepting := by
  intro branch hbranch
  let lifted : Nat -> Nat := branchPrependNode node branch
  have hliftedActive : run.ActiveBranch lifted := by
    intro k
    by_cases hk : k ≤ node.length
    · exact run.active_branchPrependNode_prefix node branch hpath k hk
    · have hlen : node.length ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hk)
      let j := k - node.length
      have hkEq : k = node.length + j := by
        exact (Nat.add_sub_of_le hlen).symm
      have hbranchj : (run.subRun node hnode).active (branchPrefix branch j) :=
        hbranch j
      change run.active (branchPrefix lifted k)
      rw [hkEq]
      rw [branchPrefix_prependNode]
      simpa [lifted, j] using hbranchj
  rcases hacc lifted hliftedActive with ⟨p, hpEven, hpSeen, hpMin⟩
  refine ⟨p, hpEven, ?_, ?_⟩
  · intro n
    rcases hpSeen (node.length + n) with ⟨k, hk, hkprio⟩
    have hlen : node.length ≤ k :=
      Nat.le_trans (Nat.le_add_right node.length n) hk
    let j := k - node.length
    have hkEq : k = node.length + j := by
      exact (Nat.add_sub_of_le hlen).symm
    refine ⟨j, ?_, ?_⟩
    · have hnk : node.length + n ≤ node.length + j := by
        simpa [← hkEq] using hk
      exact Nat.add_le_add_iff_left.mp hnk
    · change A.priority
        (run.stateAt (branchPrefix branch j ++ node)) = p
      rw [← branchPrefix_prependNode node branch j]
      simpa [lifted, hkEq] using hkprio
  · intro q hqSeen
    apply hpMin q
    intro n
    rcases hqSeen n with ⟨j, hj, hjprio⟩
    refine ⟨node.length + j, ?_, ?_⟩
    · exact Nat.le_trans hj (Nat.le_add_left j node.length)
    · change A.priority (run.stateAt (branchPrefix lifted (node.length + j))) = q
      rw [branchPrefix_prependNode]
      simpa [lifted] using hjprio

/--
The accepting subtree below a path-active node witnesses acceptance from that
node's state on the corresponding suffix word.
-/
theorem subRun_acceptsFrom
    (run : A.Run word)
    (node : Node)
    (hpath : run.PathActive node)
    (hnode : run.active node)
    (hacc : run.Accepting) :
    A.AcceptsFrom (run.stateAt node) (OmegaWord.drop word node.length) := by
  exact ⟨run.subRun node hnode, run.subRun_accepting node hpath hnode hacc⟩

/--
Every state appearing at a reachable level of an accepting run tree accepts the
corresponding suffix word.
-/
theorem acceptsFrom_of_mem_levelStates
    (run : A.Run word)
    (hacc : run.Accepting)
    {n : Nat}
    {state : A.State}
    (hstate : state ∈ run.levelStates n) :
    A.AcceptsFrom state (OmegaWord.drop word n) := by
  rcases (run.mem_levelStates n state).mp hstate with
    ⟨node, hlength, hpath, hnodeState⟩
  have hnode : run.active node := by
    exact hpath [] node (by simp)
  have hacceptsNode :
      A.AcceptsFrom
        (run.stateAt node)
        (OmegaWord.drop word node.length) :=
    run.subRun_acceptsFrom node hpath hnode hacc
  simpa [hnodeState, hlength] using hacceptsNode

/--
The macro-run extracted from an accepting run tree carries only states that
accept the matching input suffix.
-/
theorem levelMacroRun_acceptsFrom_all_at
    (run : A.Run word)
    (hacc : run.Accepting)
    (n : Nat) :
    ∀ state, state ∈ run.levelMacroRun.states n ->
      A.AcceptsFrom state (OmegaWord.drop word n) := by
  intro state hstate
  exact run.acceptsFrom_of_mem_levelStates hacc
    (run.levelMacroRun_states_subset_levelStates n hstate)

/--
The realized-edge macro-run extracted from an accepting run tree also carries
only states that accept the matching input suffix.
-/
theorem realizedLevelMacroRun_acceptsFrom_all_at
    (run : A.Run word)
    (hacc : run.Accepting)
    (n : Nat) :
    ∀ state, state ∈ run.realizedLevelMacroRun.states n ->
      A.AcceptsFrom state (OmegaWord.drop word n) := by
  intro state hstate
  exact run.acceptsFrom_of_mem_levelStates hacc
    (run.realizedLevelMacroRun_states_subset_levelStates n hstate)

/--
Finite prefixes generated by repeatedly applying an active-child extension
rule.  This is the finite skeleton used to turn local continuation choices into
an infinite active branch.
-/
noncomputable def choicePathData
    (run : A.Run word)
    (P : Node -> Prop)
    (hroot : P [])
    (step :
      ∀ node : Node,
        run.PathActive node ->
          P node ->
            ∃ child : Nat, run.active (child :: node) ∧ P (child :: node)) :
    (n : Nat) -> { node : Node // run.PathActive node ∧ P node ∧ node.length = n }
  | 0 => ⟨[], run.pathActive_nil, hroot, rfl⟩
  | n + 1 =>
      let prev := run.choicePathData P hroot step n
      let child := Classical.choose (step prev.1 prev.2.1 prev.2.2.1)
      have hchild :
          run.active (child :: prev.1) :=
        (Classical.choose_spec (step prev.1 prev.2.1 prev.2.2.1)).1
      have hP :
          P (child :: prev.1) :=
        (Classical.choose_spec (step prev.1 prev.2.1 prev.2.2.1)).2
      ⟨child :: prev.1,
        prev.2.1.extend run prev.1 child hchild,
        hP,
        by
          have hlen := prev.2.2.2
          simp [hlen]⟩

/-- The branch induced by `choicePathData`. -/
noncomputable def choicePathBranch
    (run : A.Run word)
    (P : Node -> Prop)
    (hroot : P [])
    (step :
      ∀ node : Node,
        run.PathActive node ->
          P node ->
            ∃ child : Nat, run.active (child :: node) ∧ P (child :: node)) :
    Nat -> Nat :=
  fun n =>
    Classical.choose
      (step
        (run.choicePathData P hroot step n).1
        (run.choicePathData P hroot step n).2.1
        (run.choicePathData P hroot step n).2.2.1)

theorem branchPrefix_choicePathBranch
    (run : A.Run word)
    (P : Node -> Prop)
    (hroot : P [])
    (step :
      ∀ node : Node,
        run.PathActive node ->
          P node ->
            ∃ child : Nat, run.active (child :: node) ∧ P (child :: node))
    (n : Nat) :
    branchPrefix (run.choicePathBranch P hroot step) n =
      (run.choicePathData P hroot step n).1 := by
  induction n with
  | zero =>
      simp [choicePathData]
  | succ n ih =>
      rw [branchPrefix_succ, ih]
      rfl

theorem choicePathBranch_active
    (run : A.Run word)
    (P : Node -> Prop)
    (hroot : P [])
    (step :
      ∀ node : Node,
        run.PathActive node ->
          P node ->
            ∃ child : Nat, run.active (child :: node) ∧ P (child :: node)) :
    run.ActiveBranch (run.choicePathBranch P hroot step) := by
  intro n
  rw [run.branchPrefix_choicePathBranch P hroot step n]
  exact run.pathActive_self
    (run.choicePathData P hroot step n).1
    (run.choicePathData P hroot step n).2.1

theorem choicePathBranch_property
    (run : A.Run word)
    (P : Node -> Prop)
    (hroot : P [])
    (step :
      ∀ node : Node,
        run.PathActive node ->
          P node ->
            ∃ child : Nat, run.active (child :: node) ∧ P (child :: node))
    (n : Nat) :
    P (branchPrefix (run.choicePathBranch P hroot step) n) := by
  rw [run.branchPrefix_choicePathBranch P hroot step n]
  exact (run.choicePathData P hroot step n).2.2.1

/--
The subtree below an active root child is a run from that child state on the
one-letter suffix of the input word.
-/
def childRun
    (run : A.Run word)
    (child : Nat)
    (hchild : run.active [child]) :
    (A.withInitial (run.stateAt [child])).Run (OmegaWord.drop word 1) where
  active node := run.active (node ++ [child])
  stateAt node := run.stateAt (node ++ [child])
  root_active := by
    simpa using hchild
  root_state := rfl
  step_satisfied := by
    intro node hactive
    have hstep := run.step_satisfied (node ++ [child]) hactive
    simpa [AlternatingParityAutomaton.withInitial, List.length_append,
      OmegaWord.drop, Nat.add_comm, Nat.add_assoc] using hstep

@[simp] theorem childRun_active
    (run : A.Run word)
    (child : Nat)
    (hchild : run.active [child])
    (suffix : Node) :
    (run.childRun child hchild).active suffix =
      run.active (suffix ++ [child]) :=
  rfl

@[simp] theorem childRun_stateAt
    (run : A.Run word)
    (child : Nat)
    (hchild : run.active [child])
    (suffix : Node) :
    (run.childRun child hchild).stateAt suffix =
      run.stateAt (suffix ++ [child]) :=
  rfl

theorem childRun_eq_subRun
    (run : A.Run word)
    (child : Nat)
    (hchild : run.active [child]) :
    run.childRun child hchild = run.subRun [child] hchild :=
  rfl

/--
Acceptance is inherited by the subtree below an active root child.
-/
theorem childRun_accepting
    (run : A.Run word)
    (child : Nat)
    (hchild : run.active [child])
    (hacc : run.Accepting) :
    (run.childRun child hchild).Accepting := by
  intro branch hbranch
  let shifted : Nat -> Nat := fun
    | 0 => child
    | n + 1 => branch n
  have hshiftActive : run.ActiveBranch shifted := by
    intro n
    cases n with
    | zero =>
        simpa [shifted] using run.root_active
    | succ n =>
        have hb := hbranch n
        change run.active (branchPrefix shifted (n + 1))
        rw [show branchPrefix shifted (n + 1) =
          branchPrefix branch n ++ [child] by
          exact branchPrefix_shift child branch n]
        exact hb
  rcases hacc shifted hshiftActive with ⟨p, hpEven, hpSeen, hpMin⟩
  refine ⟨p, hpEven, ?_, ?_⟩
  · intro n
    rcases hpSeen (n + 1) with ⟨k, hk, hkprio⟩
    cases k with
    | zero =>
        exact False.elim (Nat.not_succ_le_zero n hk)
    | succ k =>
        refine ⟨k, Nat.succ_le_succ_iff.mp hk, ?_⟩
        change A.priority (run.stateAt (branchPrefix branch k ++ [child])) = p
        rw [← show branchPrefix shifted (k + 1) =
          branchPrefix branch k ++ [child] by
          exact branchPrefix_shift child branch k]
        exact hkprio
  · intro q hqSeen
    apply hpMin q
    intro n
    rcases hqSeen n with ⟨k, hk, hkprio⟩
    refine ⟨k + 1, Nat.le_trans hk (Nat.le_succ k), ?_⟩
    change A.priority (run.stateAt (branchPrefix shifted (k + 1))) = q
    rw [show branchPrefix shifted (k + 1) =
      branchPrefix branch k ++ [child] by
      exact branchPrefix_shift child branch k]
    exact hkprio

/--
An accepting subtree below an active root child witnesses acceptance from the
child state on the one-letter suffix.
-/
theorem childRun_acceptsFrom
    (run : A.Run word)
    (child : Nat)
    (hchild : run.active [child])
    (hacc : run.Accepting) :
    A.AcceptsFrom (run.stateAt [child]) (OmegaWord.drop word 1) := by
  exact ⟨run.childRun child hchild, run.childRun_accepting child hchild hacc⟩

end Run

/--
Acceptance from a state satisfies the one-step transition when successor atoms
are interpreted as acceptance from that successor state on the one-letter
suffix.
-/
theorem acceptsFrom_step {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (haccepts : A.AcceptsFrom state word) :
    PosBool.Eval
      (fun nextState => A.AcceptsFrom nextState (OmegaWord.drop word 1))
      (A.step state (word 0)) := by
  rcases haccepts with ⟨run, hacc⟩
  have hrootState : run.stateAt [] = state := by
    simpa [AlternatingParityAutomaton.withInitial] using run.root_state
  have hstep := run.step_satisfied [] run.root_active
  change
    PosBool.Eval
      (fun nextState =>
        ∃ child : Nat,
          run.active [child] ∧ run.stateAt [child] = nextState)
      (A.step (run.stateAt []) (word 0)) at hstep
  rw [hrootState] at hstep
  refine
    PosBool.eval_mono
      (fun nextState hnext => ?_)
      (A.step state (word 0))
      hstep
  rcases hnext with ⟨child, hchildActive, hchildState⟩
  subst nextState
  let childRun :
      (A.withInitial (run.stateAt [child])).Run (OmegaWord.drop word 1) := {
    active := fun node => run.active (node ++ [child])
    stateAt := fun node => run.stateAt (node ++ [child])
    root_active := by
      simpa using hchildActive
    root_state := rfl
    step_satisfied := by
      intro node hactive
      have hstepNode := run.step_satisfied (node ++ [child]) hactive
      simpa [AlternatingParityAutomaton.withInitial, List.length_append,
        OmegaWord.drop, Nat.add_comm, Nat.add_assoc] using hstepNode }
  refine ⟨childRun, ?_⟩
  intro branch hbranch
  let shifted : Nat -> Nat := fun
    | 0 => child
    | n + 1 => branch n
  have hshiftActive : run.ActiveBranch shifted := by
    intro n
    cases n with
    | zero =>
        simpa [shifted] using run.root_active
    | succ n =>
        have hb := hbranch n
        change run.active (AlternatingParityAutomaton.branchPrefix shifted (n + 1))
        rw [show AlternatingParityAutomaton.branchPrefix shifted (n + 1) =
          AlternatingParityAutomaton.branchPrefix branch n ++ [child] by
          exact AlternatingParityAutomaton.branchPrefix_shift child branch n]
        exact hb
  rcases hacc shifted hshiftActive with ⟨p, hpEven, hpSeen, hpMin⟩
  refine ⟨p, hpEven, ?_, ?_⟩
  · intro n
    rcases hpSeen (n + 1) with ⟨k, hk, hkprio⟩
    cases k with
    | zero =>
        exact False.elim (Nat.not_succ_le_zero n hk)
    | succ k =>
        refine ⟨k, Nat.succ_le_succ_iff.mp hk, ?_⟩
        change A.priority
          (run.stateAt
            (AlternatingParityAutomaton.branchPrefix branch k ++ [child])) = p
        rw [← show AlternatingParityAutomaton.branchPrefix shifted (k + 1) =
          AlternatingParityAutomaton.branchPrefix branch k ++ [child] by
          exact AlternatingParityAutomaton.branchPrefix_shift child branch k]
        exact hkprio
  · intro q hqSeen
    apply hpMin q
    intro n
    rcases hqSeen n with ⟨k, hk, hkprio⟩
    refine ⟨k + 1, Nat.le_trans hk (Nat.le_succ k), ?_⟩
    change A.priority
      (run.stateAt (AlternatingParityAutomaton.branchPrefix shifted (k + 1))) = q
    rw [show AlternatingParityAutomaton.branchPrefix shifted (k + 1) =
      AlternatingParityAutomaton.branchPrefix branch k ++ [child] by
      exact AlternatingParityAutomaton.branchPrefix_shift child branch k]
    exact hkprio

/-- Run-tree APA acceptance is exactly the one-step positive-Boolean equation. -/
theorem acceptsFrom_step_iff {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    PosBool.Eval
        (fun nextState => A.AcceptsFrom nextState (OmegaWord.drop word 1))
        (A.step state (word 0)) ↔
      A.AcceptsFrom state word := by
  constructor
  · exact A.acceptsFrom_of_step state word
  · exact A.acceptsFrom_step state word

/--
A one-step finite macro successor satisfying APA acceptance of the suffix exists
exactly when every active state accepts the current word.
-/
theorem exists_macroTransition_iff_acceptsFrom_all {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (states : Finset A.State)
    (word : OmegaWord Alphabet) :
    (∃ nextStates : Finset A.State,
      A.MacroTransition states (word 0) nextStates ∧
      ∀ nextState, nextState ∈ nextStates ->
        A.AcceptsFrom nextState (OmegaWord.drop word 1)) ↔
      ∀ state, state ∈ states -> A.AcceptsFrom state word := by
  rw [A.exists_macroTransition_iff_eval_all
    (fun nextState => A.AcceptsFrom nextState (OmegaWord.drop word 1))
    states (word 0)]
  constructor
  · intro hstep state hstate
    exact (A.acceptsFrom_step_iff state word).mp (hstep state hstate)
  · intro haccepts state hstate
    exact (A.acceptsFrom_step_iff state word).mpr (haccepts state hstate)

/--
Completeness, in bounded form: accepting all active states produces a finite
macro successor of accepting suffix states.
-/
theorem exists_macroTransition_of_acceptsFrom_all {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (states : Finset A.State)
    (word : OmegaWord Alphabet)
    (haccepts : ∀ state, state ∈ states -> A.AcceptsFrom state word) :
    ∃ nextStates : Finset A.State,
      A.MacroTransition states (word 0) nextStates ∧
      nextStates ⊆ A.subsetStepAtoms states (word 0) ∧
      ∀ nextState, nextState ∈ nextStates ->
        A.AcceptsFrom nextState (OmegaWord.drop word 1) := by
  exact
    A.exists_macroTransition_of_eval_all
      (fun nextState => A.AcceptsFrom nextState (OmegaWord.drop word 1))
      states
      (word 0)
      (by
        intro state hstate
        exact (A.acceptsFrom_step_iff state word).mpr
          (haccepts state hstate))

/--
Soundness, in bounded form: a macro transition to accepting suffix states makes
all current active states accepting.
-/
theorem acceptsFrom_all_of_macroTransition {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {states nextStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (htransition : A.MacroTransition states (word 0) nextStates)
    (hnextAccepts :
      ∀ nextState, nextState ∈ nextStates ->
        A.AcceptsFrom nextState (OmegaWord.drop word 1)) :
    ∀ state, state ∈ states -> A.AcceptsFrom state word := by
  intro state hstate
  exact
    (A.acceptsFrom_step_iff state word).mp
      (A.eval_all_of_macroTransition htransition hnextAccepts state hstate)

/--
The first step of a macro-run is sound with respect to APA acceptance: if every
state in the first successor macro-state accepts the suffix, then every initial
macro-state accepts the original word.
-/
theorem MacroRun.acceptsFrom_all_initial_of_tail {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (hnextAccepts :
      ∀ nextState, nextState ∈ run.states 1 ->
        A.AcceptsFrom nextState (OmegaWord.drop word 1)) :
    ∀ state, state ∈ initialStates -> A.AcceptsFrom state word := by
  have hcurrent :
      ∀ state, state ∈ run.states 0 -> A.AcceptsFrom state word :=
    A.acceptsFrom_all_of_macroTransition
      (run.step_transition 0)
      hnextAccepts
  intro state hstate
  exact hcurrent state (by simpa [run.initial_states] using hstate)

/--
At any position of a macro-run, accepting all states in the next macro-state on
the next suffix implies accepting all current macro-states on the current suffix.
-/
theorem MacroRun.acceptsFrom_all_at_of_next {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (offset : Nat)
    (hnextAccepts :
      ∀ nextState, nextState ∈ run.states (offset + 1) ->
        A.AcceptsFrom nextState (OmegaWord.drop word (offset + 1))) :
    ∀ state, state ∈ run.states offset ->
      A.AcceptsFrom state (OmegaWord.drop word offset) := by
  have hdropNext :
      ∀ nextState, nextState ∈ (run.drop offset).states 1 ->
        A.AcceptsFrom nextState
          (OmegaWord.drop (OmegaWord.drop word offset) 1) := by
    intro nextState hnext
    rw [OmegaWord.drop_drop]
    exact hnextAccepts nextState (by simpa [Nat.add_comm] using hnext)
  have hcurrent :=
    (run.drop offset).acceptsFrom_all_initial_of_tail hdropNext
  intro state hstate
  exact hcurrent state (by simpa using hstate)

/--
At any position, accepting all current macro-states produces a finite successor
macro-state of accepting next-suffix states.
-/
theorem MacroRun.exists_macroTransition_at_of_acceptsFrom_all {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (offset : Nat)
    (haccepts :
      ∀ state, state ∈ run.states offset ->
        A.AcceptsFrom state (OmegaWord.drop word offset)) :
    ∃ nextStates : Finset A.State,
      A.MacroTransition (run.states offset) (word offset) nextStates ∧
      nextStates ⊆ A.subsetStepAtoms (run.states offset) (word offset) ∧
      ∀ nextState, nextState ∈ nextStates ->
        A.AcceptsFrom nextState (OmegaWord.drop word (offset + 1)) := by
  rcases
    A.exists_macroTransition_of_acceptsFrom_all
      (run.states offset)
      (OmegaWord.drop word offset)
      haccepts with
    ⟨nextStates, htransition, hsubset, hnextAccepts⟩
  refine ⟨nextStates, ?_, ?_, ?_⟩
  · simpa [OmegaWord.drop] using htransition
  · simpa [OmegaWord.drop] using hsubset
  · intro nextState hnext
    rw [← OmegaWord.drop_drop]
    exact hnextAccepts nextState hnext

/--
At any position of a macro-run, the actual next macro-state is a sound successor
for acceptance.
-/
theorem MacroRun.acceptsFrom_all_at_of_next_state {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (offset : Nat)
    (hnextAccepts :
      ∀ nextState, nextState ∈ run.states (offset + 1) ->
        A.AcceptsFrom nextState (OmegaWord.drop word (offset + 1))) :
    ∀ state, state ∈ run.states offset ->
      A.AcceptsFrom state (OmegaWord.drop word offset) :=
  run.acceptsFrom_all_at_of_next offset hnextAccepts

/--
Acceptance of all macro-states propagates backwards along any finite interval of
a macro-run.
-/
theorem MacroRun.acceptsFrom_all_at_of_later {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (offset distance : Nat)
    (hlater :
      ∀ state, state ∈ run.states (offset + distance) ->
        A.AcceptsFrom state (OmegaWord.drop word (offset + distance))) :
    ∀ state, state ∈ run.states offset ->
      A.AcceptsFrom state (OmegaWord.drop word offset) := by
  induction distance generalizing offset with
  | zero =>
      intro state hstate
      simpa using hlater state hstate
  | succ distance ih =>
      apply run.acceptsFrom_all_at_of_next offset
      intro nextState hnext
      have htail :
          ∀ state, state ∈ run.states ((offset + 1) + distance) ->
            A.AcceptsFrom state
              (OmegaWord.drop word ((offset + 1) + distance)) := by
        intro state hstate
        have hstates :
            state ∈ run.states (offset + (distance + 1)) := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstate
        have haccepts := hlater state hstates
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using haccepts
      exact ih (offset + 1) htail nextState hnext

/--
If all states in a later macro-state accept their later suffix, then all initial
macro-states accept the original word.
-/
theorem MacroRun.acceptsFrom_all_initial_of_later {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (distance : Nat)
    (hlater :
      ∀ state, state ∈ run.states distance ->
        A.AcceptsFrom state (OmegaWord.drop word distance)) :
    ∀ state, state ∈ initialStates -> A.AcceptsFrom state word := by
  have hzero :
      ∀ state, state ∈ run.states 0 ->
        A.AcceptsFrom state (OmegaWord.drop word 0) := by
    simpa using
      (run.acceptsFrom_all_at_of_later 0 distance
        (by
          intro state hstate
          have hstate' : state ∈ run.states distance := by
            simpa using hstate
          simpa using hlater state hstate'))
  intro state hstate
  simpa [run.initial_states] using hzero state (by simpa [run.initial_states] using hstate)

/--
Semantic Muller-style acceptance for a macro-run.

This is still a semantic bridge predicate, not yet the final automaton
accepting family: it says that some recurring macro-state appears at a concrete
offset where all its APA states accept the corresponding suffix.
-/
def MacroRun.SemanticAccepting {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    Prop :=
  ∃ offset : Nat,
    run.states offset ∈ run.infStateFinset ∧
      ∀ state, state ∈ run.states offset ->
        A.AcceptsFrom state (OmegaWord.drop word offset)

/--
The macro-run extracted from an accepting APA run tree is semantically
accepting in the recurrence-based macro-run sense.
-/
theorem levelMacroRun_semanticAccepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (hacc : run.Accepting) :
    run.levelMacroRun.SemanticAccepting := by
  let macroRun := run.levelMacroRun
  rcases macroRun.infStateFinset_nonempty with ⟨recurringStates, hrecurring⟩
  have hseen :
      macroRun.StateSeenInfinitelyOften recurringStates :=
    (macroRun.mem_infStateFinset recurringStates).mp hrecurring
  rcases hseen 0 with ⟨offset, _hoffset, hstates⟩
  refine ⟨offset, ?_, ?_⟩
  · rw [hstates]
    exact hrecurring
  · intro state hstate
    exact run.levelMacroRun_acceptsFrom_all_at hacc offset state hstate

/--
The realized-edge macro-run extracted from an accepting APA run tree is also
semantically accepting.  Unlike `levelMacroRun`, each of its transitions has an
available witness whose state edges are actual active run-tree child edges.
-/
theorem realizedLevelMacroRun_semanticAccepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (hacc : run.Accepting) :
    run.realizedLevelMacroRun.SemanticAccepting := by
  let macroRun := run.realizedLevelMacroRun
  rcases macroRun.infStateFinset_nonempty with ⟨recurringStates, hrecurring⟩
  have hseen :
      macroRun.StateSeenInfinitelyOften recurringStates :=
    (macroRun.mem_infStateFinset recurringStates).mp hrecurring
  rcases hseen 0 with ⟨offset, _hoffset, hstates⟩
  refine ⟨offset, ?_, ?_⟩
  · rw [hstates]
    exact hrecurring
  · intro state hstate
    exact run.realizedLevelMacroRun_acceptsFrom_all_at hacc offset state hstate

/--
An accepting APA run tree therefore directly supplies a semantically accepting
macro-run started from the singleton initial macro-state.
-/
theorem exists_levelMacroRun_semanticAccepting_of_accepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (hacc : run.Accepting) :
    ∃ macroRun : A.MacroRun {A.initial} word,
      macroRun.SemanticAccepting := by
  exact ⟨run.levelMacroRun, levelMacroRun_semanticAccepting run hacc⟩

/--
An accepting APA run tree also supplies a semantically accepting macro-run
whose local transition witnesses can be chosen from actual active child edges.
-/
theorem exists_realizedLevelMacroRun_semanticAccepting_of_accepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (hacc : run.Accepting) :
    ∃ macroRun : A.MacroRun {A.initial} word,
      macroRun.SemanticAccepting := by
  exact
    ⟨run.realizedLevelMacroRun,
      realizedLevelMacroRun_semanticAccepting run hacc⟩

/--
Soundness of semantic macro-run acceptance: a semantically accepting macro-run
from `initialStates` proves APA acceptance for every initial macro-state.
-/
theorem MacroRun.acceptsFrom_all_initial_of_semanticAccepting {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (haccepting : run.SemanticAccepting) :
    ∀ state, state ∈ initialStates -> A.AcceptsFrom state word := by
  rcases haccepting with ⟨offset, _hrecurs, haccepts⟩
  exact run.acceptsFrom_all_initial_of_later offset haccepts

/--
Semantic macro-run acceptance also yields APA acceptance from a singleton
initial macro-state.
-/
theorem MacroRun.acceptsFrom_of_mem_initial_of_semanticAccepting {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (haccepting : run.SemanticAccepting)
    {state : A.State}
    (hstate : state ∈ initialStates) :
    A.AcceptsFrom state word :=
  run.acceptsFrom_all_initial_of_semanticAccepting haccepting state hstate

/--
The accepting macro-run data obtained by repeatedly choosing finite
macro-successors whose states accept the corresponding suffix.
-/
noncomputable def acceptingMacroRunData {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (haccepts :
      ∀ state, state ∈ initialStates -> A.AcceptsFrom state word) :
    (n : Nat) ->
      { states : Finset A.State //
        ∀ state, state ∈ states ->
          A.AcceptsFrom state (OmegaWord.drop word n) }
  | 0 => ⟨initialStates, by simpa using haccepts⟩
  | n + 1 =>
      let current := acceptingMacroRunData A initialStates word haccepts n
      let existsNext :=
        A.exists_macroTransition_of_acceptsFrom_all
          current.1
          (OmegaWord.drop word n)
          current.2
      let nextStates := Classical.choose existsNext
      ⟨nextStates,
        by
          intro state hstate
          have hnext :=
            (Classical.choose_spec existsNext).2.2 state hstate
          simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using hnext⟩

/-- The recursively chosen accepting macro-run data keeps every state accepting. -/
theorem acceptingMacroRunData_accepts {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (haccepts :
      ∀ state, state ∈ initialStates -> A.AcceptsFrom state word)
    (n : Nat) :
    ∀ state,
      state ∈ (A.acceptingMacroRunData initialStates word haccepts n).1 ->
        A.AcceptsFrom state (OmegaWord.drop word n) :=
  (A.acceptingMacroRunData initialStates word haccepts n).2

/-- Consecutive accepting macro-run data states satisfy the macro transition relation. -/
theorem acceptingMacroRunData_step {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (haccepts :
      ∀ state, state ∈ initialStates -> A.AcceptsFrom state word)
    (n : Nat) :
    A.MacroTransition
      (A.acceptingMacroRunData initialStates word haccepts n).1
      (word n)
      (A.acceptingMacroRunData initialStates word haccepts (n + 1)).1 := by
  let current := A.acceptingMacroRunData initialStates word haccepts n
  let existsNext :=
    A.exists_macroTransition_of_acceptsFrom_all
      current.1
      (OmegaWord.drop word n)
      current.2
  change
    A.MacroTransition
      current.1
      (word n)
      (Classical.choose existsNext)
  simpa [OmegaWord.drop] using
    (Classical.choose_spec existsNext).1

/-- APA acceptance of all initial macro-states generates a macro-run. -/
noncomputable def acceptingMacroRunFromAccepts {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (haccepts :
      ∀ state, state ∈ initialStates -> A.AcceptsFrom state word) :
    A.MacroRun initialStates word where
  states n := (A.acceptingMacroRunData initialStates word haccepts n).1
  initial_states := by
    simp [acceptingMacroRunData]
  step_transition := by
    intro n
    exact A.acceptingMacroRunData_step initialStates word haccepts n

/-- Every state of the constructed accepting macro-run accepts its suffix. -/
theorem acceptingMacroRunFromAccepts_accepts_all_at {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (haccepts :
      ∀ state, state ∈ initialStates -> A.AcceptsFrom state word)
    (n : Nat) :
    ∀ state,
      state ∈
        (A.acceptingMacroRunFromAccepts initialStates word haccepts).states n ->
        A.AcceptsFrom state (OmegaWord.drop word n) :=
  A.acceptingMacroRunData_accepts initialStates word haccepts n

/--
Completeness of semantic macro-run acceptance: if every initial macro-state
accepts the word, then there is a semantically accepting macro-run from it.
-/
theorem exists_semanticAccepting_macroRun_of_accepts_all {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (haccepts :
      ∀ state, state ∈ initialStates -> A.AcceptsFrom state word) :
    ∃ run : A.MacroRun initialStates word, run.SemanticAccepting := by
  let run := A.acceptingMacroRunFromAccepts initialStates word haccepts
  rcases run.infStateFinset_nonempty with ⟨recurringStates, hrecurring⟩
  have hseen : run.StateSeenInfinitelyOften recurringStates := by
    exact (run.mem_infStateFinset recurringStates).mp hrecurring
  rcases hseen 0 with ⟨offset, _hoffset, hstates⟩
  refine ⟨run, offset, ?_, ?_⟩
  · rw [hstates]
    exact hrecurring
  · intro state hstate
    exact
      A.acceptingMacroRunFromAccepts_accepts_all_at
        initialStates word haccepts offset state hstate

/--
Semantic macro-runs characterize APA acceptance of all states in the initial
macro-state.
-/
theorem exists_semanticAccepting_macroRun_iff_accepts_all {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet) :
    (∃ run : A.MacroRun initialStates word, run.SemanticAccepting) ↔
      ∀ state, state ∈ initialStates -> A.AcceptsFrom state word := by
  constructor
  · intro hrun
    rcases hrun with ⟨run, haccepting⟩
    exact run.acceptsFrom_all_initial_of_semanticAccepting haccepting
  · intro haccepts
    exact A.exists_semanticAccepting_macroRun_of_accepts_all
      initialStates word haccepts

@[simp]
theorem acceptsFrom_initial {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    A.AcceptsFrom A.initial word = A.Accepts word :=
  rfl

/--
For the singleton initial macro-state, semantic macro-run acceptance is
equivalent to ordinary APA acceptance.
-/
theorem exists_semanticAccepting_macroRun_singleton_iff_accepts {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    (∃ run : A.MacroRun {A.initial} word, run.SemanticAccepting) ↔
      A.Accepts word := by
  rw [A.exists_semanticAccepting_macroRun_iff_accepts_all]
  constructor
  · intro haccepts
    simpa [A.acceptsFrom_initial word] using
      haccepts A.initial (by simp)
  · intro haccepts state hstate
    have hstateInitial : state = A.initial := by
      simpa using hstate
    subst state
    simpa [A.acceptsFrom_initial word] using haccepts

/--
One-step symbolic acceptance equation for an alternating automaton.

This is not yet a full run-tree acceptance definition; it is the local
coalgebraic equation that the LTL front end proves for its transition map.
-/
def StepEquation {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (language : A.State -> Set (OmegaWord Alphabet)) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    PosBool.Eval
        (fun nextState => language nextState (OmegaWord.drop word 1))
        (A.step state (word 0)) ↔
      language state word

/--
A language certificate for an alternating parity automaton.

The actual run-tree semantics/determinization theorem can instantiate this
record.  Downstream compiler steps use only the accepted language and the
local step equation.
-/
structure LanguageCertificate {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) where
  language : A.State -> Set (OmegaWord Alphabet)
  stepEquation : A.StepEquation language

/-- The semantic run-tree language is a certified solution of the APA step equation. -/
def runLanguageCertificate {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    A.LanguageCertificate where
  language := fun state word => A.AcceptsFrom state word
  stepEquation := by
    intro state word
    exact A.acceptsFrom_step_iff state word

/-- A certificate relating the run-tree semantics to a state-indexed language. -/
structure RunLanguageCertificate {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) extends
      A.LanguageCertificate where
  acceptsFrom_iff :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      A.AcceptsFrom state word ↔ word ∈ toLanguageCertificate.language state

/--
The concrete run-tree semantics, viewed as a state-indexed language, is a
certified APA run language.
-/
def semanticRunLanguageCertificate {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    A.RunLanguageCertificate where
  toLanguageCertificate := A.runLanguageCertificate
  acceptsFrom_iff := by
    intro state word
    rfl

/-- The initial accepted language is the state-wise run language at `A.initial`. -/
theorem RunLanguageCertificate.initial_accepts_iff {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (cert : A.RunLanguageCertificate)
    (word : OmegaWord Alphabet) :
    A.Accepts word ↔ word ∈ cert.toLanguageCertificate.language A.initial := by
  simpa using cert.acceptsFrom_iff A.initial word

/-- The omega-language accepted from the initial state, according to a certificate. -/
def LanguageCertificate.initialLanguage {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (cert : A.LanguageCertificate) :
    Set (OmegaWord Alphabet) :=
  cert.language A.initial

end AlternatingParityAutomaton

end DistributedSynthesis
