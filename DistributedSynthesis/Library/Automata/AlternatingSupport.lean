/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Library.Automata.Compilers
import DistributedSynthesis.Formalizations.Theorem.ThmMullerToDPA
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi

/-! # Alternating-automaton support constructions
Macro configurations, support runs, Muller interfaces, and their correctness
adapters, extracted unchanged from the mixed backend. Conditional
normal-form and realization premises remain explicit. This module contains no
distributed-synthesis construction and imports no synthesis backend. -/

namespace DistributedSynthesis

universe u v w a b x y z

namespace AlternatingParityAutomaton

/--
Deterministic Muller skeleton induced by the finite APA macro-configuration
transition graph.

The accepting family is a parameter here.  This isolates the deterministic
powerset dynamics from the later acceptance proof: the remaining APA
determinization work is to instantiate `accepting` with the correct Muller
condition and prove language equivalence.
-/
noncomputable def macroConfigurationMuller
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (Finset (Finset A.State)))) :
    DetMullerAutomaton.{u, v} Alphabet where
  State := Finset (Finset A.State)
  stateFinite := inferInstance
  initial := {initialStates}
  step := fun configs letter => A.macroConfigurationStep configs letter
  accepting := accepting

@[simp]
theorem macroConfigurationMuller_run
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (Finset (Finset A.State))))
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (A.macroConfigurationMuller initialStates accepting).run word n =
      A.macroConfigurationRun initialStates word n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        A.macroConfigurationStep
            ((A.macroConfigurationMuller initialStates accepting).run word n)
            (word n) =
          A.macroConfigurationRun initialStates word (n + 1)
      rw [ih]
      rfl

@[simp]
theorem macroConfigurationMuller_runFrom_initial
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (Finset (Finset A.State))))
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (A.macroConfigurationMuller initialStates accepting).runFrom
        ({initialStates} : Finset (Finset A.State)) word n =
      A.macroConfigurationRun initialStates word n := by
  simpa [DetMullerAutomaton.run]
    using A.macroConfigurationMuller_run initialStates accepting word n

@[simp]
theorem macroConfigurationMuller_mem_infStateFinset
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (Finset (Finset A.State))))
    (word : OmegaWord Alphabet)
    (configs : Finset (Finset A.State)) :
    configs ∈
        (A.macroConfigurationMuller initialStates accepting).infStateFinset word ↔
      ∀ n : Nat,
        ∃ k : Nat,
          n ≤ k ∧ A.macroConfigurationRun initialStates word k = configs := by
  classical
  trans
    (A.macroConfigurationMuller initialStates accepting).StateSeenInfinitelyOften
      word configs
  · exact
      DetMullerAutomaton.mem_infStateFinset
        (A.macroConfigurationMuller initialStates accepting) word configs
  change
    (∀ n : Nat,
      ∃ k : Nat,
        n ≤ k ∧
          (A.macroConfigurationMuller initialStates accepting).runFrom
            (A.macroConfigurationMuller initialStates accepting).initial word k =
              configs) ↔
      ∀ n : Nat,
        ∃ k : Nat,
          n ≤ k ∧ A.macroConfigurationRun initialStates word k = configs
  constructor
  · intro h n
    rcases h n with ⟨k, hk, hrun⟩
    refine ⟨k, hk, ?_⟩
    have hcfg :
        (A.macroConfigurationMuller initialStates accepting).runFrom
            (A.macroConfigurationMuller initialStates accepting).initial word k =
          A.macroConfigurationRun initialStates word k := by
      simpa [DetMullerAutomaton.run] using
        A.macroConfigurationMuller_run initialStates accepting word k
    simpa [hcfg] using hrun
  · intro h n
    rcases h n with ⟨k, hk, hrun⟩
    refine ⟨k, hk, ?_⟩
    have hcfg :
        (A.macroConfigurationMuller initialStates accepting).runFrom
            (A.macroConfigurationMuller initialStates accepting).initial word k =
          A.macroConfigurationRun initialStates word k := by
      simpa [DetMullerAutomaton.run] using
        A.macroConfigurationMuller_run initialStates accepting word k
    simpa [hcfg] using hrun

/--
The Muller skeleton accepts exactly when the recurring deterministic
macro-configurations generated by `macroConfigurationRun` belong to the chosen
Muller family.
-/
theorem macroConfigurationMuller_accepts_iff
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (Finset (Finset A.State))))
    (word : OmegaWord Alphabet) :
    (A.macroConfigurationMuller initialStates accepting).Accepts word ↔
      ({ configs : Finset (Finset A.State) |
          ∀ n : Nat,
            ∃ k : Nat,
              n ≤ k ∧ A.macroConfigurationRun initialStates word k = configs } :
        Set (Finset (Finset A.State))) ∈ accepting := by
  change
    ({ configs : Finset (Finset A.State) |
        (A.macroConfigurationMuller initialStates accepting).StateSeenInfinitelyOften
          word configs } : Set (Finset (Finset A.State))) ∈ accepting ↔
      ({ configs : Finset (Finset A.State) |
          ∀ n : Nat,
            ∃ k : Nat,
              n ≤ k ∧ A.macroConfigurationRun initialStates word k = configs } :
        Set (Finset (Finset A.State))) ∈ accepting
  have hset :
      ({ configs : Finset (Finset A.State) |
          (A.macroConfigurationMuller initialStates accepting).StateSeenInfinitelyOften
            word configs } : Set (Finset (Finset A.State))) =
        ({ configs : Finset (Finset A.State) |
            ∀ n : Nat,
              ∃ k : Nat,
                n ≤ k ∧ A.macroConfigurationRun initialStates word k = configs } :
          Set (Finset (Finset A.State))) := by
    ext configs
    exact
      (DetMullerAutomaton.mem_infStateFinset
        (A.macroConfigurationMuller initialStates accepting) word configs).symm.trans
        (A.macroConfigurationMuller_mem_infStateFinset
          initialStates accepting word configs)
  rw [hset]

end AlternatingParityAutomaton

/-- A certified conversion from a language-certified APA to a deterministic Muller automaton. -/
structure APAToMullerCompilation
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (apaCert : A.LanguageCertificate) where
  muller : DetMullerAutomaton.{u, w} Alphabet
  correct :
    ∀ word : OmegaWord Alphabet,
      muller.Accepts word ↔ word ∈ apaCert.initialLanguage

/-- Package a Muller automaton recognizing the APA initial language. -/
def APAToMullerCompilation.ofRecognizes
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {apaCert : A.LanguageCertificate}
    (muller : DetMullerAutomaton.{u, w} Alphabet)
    (h : muller.Recognizes apaCert.initialLanguage) :
    APAToMullerCompilation.{u, v, w} A apaCert where
  muller := muller
  correct := h

/--
An APA-to-Muller compilation automatically yields an APA-to-DPA compilation via
the proved LAR Muller-to-DPA construction.
-/
noncomputable def APAToMullerCompilation.toDPACompilation
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {apaCert : A.LanguageCertificate}
    (det : APAToMullerCompilation.{u, v, w} A apaCert) :
    APAToDPACompilation.{u, v, w} A apaCert where
  dpa :=
    (DetMullerAutomaton.LAR.eventAutomaton_toDPACompilation
      (A := det.muller)).dpa
  correct := by
    intro word
    trans det.muller.Accepts word
    · exact
        (DetMullerAutomaton.LAR.eventAutomaton_toDPACompilation
          (A := det.muller)).correct word
    · exact det.correct word

/-- A certified run-semantics conversion from an APA to a deterministic Muller automaton. -/
structure APARunToMullerCompilation
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) where
  muller : DetMullerAutomaton.{u, w} Alphabet
  correct :
    ∀ word : OmegaWord Alphabet,
      muller.Accepts word ↔ A.Accepts word

/--
A run-semantics APA-to-Muller compilation yields a run-semantics APA-to-DPA
compilation by the already-proved LAR Muller-to-DPA construction.
-/
noncomputable def APARunToMullerCompilation.toDPACompilation
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (det : APARunToMullerCompilation.{u, v, w} A) :
    APARunToDPACompilation.{u, v, w} A where
  dpa :=
    (DetMullerAutomaton.LAR.eventAutomaton_toDPACompilation
      (A := det.muller)).dpa
  correct := by
    intro word
    trans det.muller.Accepts word
    · exact
        (DetMullerAutomaton.LAR.eventAutomaton_toDPACompilation
          (A := det.muller)).correct word
    · exact det.correct word

/--
Turn a run-semantics APA-to-Muller compilation plus a run-language certificate
into the language-certificate Muller form.

This is the Muller analogue of `APARunToDPACompilation.toLanguageCompilation`;
it lets later constructions stay at the deterministic-Muller level and apply
LAR only after the APA language bridge has been discharged.
-/
def APARunToMullerCompilation.toLanguageCompilation
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {cert : A.RunLanguageCertificate}
    (det : APARunToMullerCompilation.{u, v, w} A) :
    APAToMullerCompilation.{u, v, w} A cert.toLanguageCertificate where
  muller := det.muller
  correct := by
    intro word
    trans A.Accepts word
    · exact det.correct word
    trans word ∈ cert.toLanguageCertificate.language A.initial
    · exact cert.initial_accepts_iff word
    · rfl

/--
A uniform run-semantics APA-to-Muller compiler.  This is the precise reusable
target for an APA subset/Muller construction; LAR then supplies parity.
-/
structure APARunToMullerCompiler
    (Alphabet : Type u) where
  compile :
    ∀ A : AlternatingParityAutomaton.{u, v} Alphabet,
      APARunToMullerCompilation.{u, v, w} A

namespace APARunToMullerCompiler

/-- Compose a uniform APA-to-Muller compiler with LAR to obtain a uniform APA-to-DPA compiler. -/
noncomputable def toDPACompiler
    {Alphabet : Type u}
    (compiler : APARunToMullerCompiler.{u, v, w} Alphabet) :
    APARunToDPACompiler.{u, v, w} Alphabet where
  compile := fun A => (compiler.compile A).toDPACompilation

/--
Apply a uniform run-semantics APA-to-Muller compiler to an APA equipped with a
run-language certificate.
-/
def toLanguageCompilation
    {Alphabet : Type u}
    (compiler : APARunToMullerCompiler.{u, v, w} Alphabet)
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate) :
    APAToMullerCompilation.{u, v, w} A cert.toLanguageCertificate :=
  (compiler.compile A).toLanguageCompilation

end APARunToMullerCompiler

/-- A state-wise certified conversion from APA state languages to Muller state languages. -/
structure APAToMullerStateCompilation
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (apaCert : A.LanguageCertificate) where
  muller : DetMullerAutomaton.{u, w} Alphabet
  stateOf : A.State -> muller.State
  initial_state : stateOf A.initial = muller.initial
  correctFrom :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      muller.AcceptsFrom (stateOf state) word ↔ word ∈ apaCert.language state

/-- State-wise APA-to-Muller compilation yields the initial-language form. -/
def APAToMullerStateCompilation.toInitialCompilation
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {apaCert : A.LanguageCertificate}
    (det : APAToMullerStateCompilation.{u, v, w} A apaCert) :
    APAToMullerCompilation.{u, v, w} A apaCert where
  muller := det.muller
  correct := by
    intro word
    change det.muller.AcceptsFrom det.muller.initial word ↔ word ∈ apaCert.initialLanguage
    rw [← det.initial_state]
    exact det.correctFrom A.initial word

/--
A state-wise APA-to-Muller compilation plus a run-language certificate yields
the run-semantics Muller determinization target.
-/
def APAToMullerStateCompilation.toRunCompilation
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {cert : A.RunLanguageCertificate}
    (det : APAToMullerStateCompilation.{u, v, w} A cert.toLanguageCertificate) :
    APARunToMullerCompilation.{u, v, w} A where
  muller := det.muller
  correct := by
    intro word
    change det.muller.AcceptsFrom det.muller.initial word ↔ A.Accepts word
    rw [← det.initial_state]
    trans word ∈ cert.toLanguageCertificate.language A.initial
    · exact det.correctFrom A.initial word
    · exact (cert.initial_accepts_iff word).symm

/--
State-wise APA-to-Muller compilation also composes directly with LAR to give a
state-wise APA-to-DPA compilation.
-/
noncomputable def APAToMullerStateCompilation.toDPAStateCompilation
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {apaCert : A.LanguageCertificate}
    (det : APAToMullerStateCompilation.{u, v, w} A apaCert) :
    APAToDPAStateCompilation.{u, v, w} A apaCert where
  dpa :=
    (DetMullerAutomaton.LAR.eventAutomaton_toDPACompilation
      (A := det.muller)).dpa
  stateOf := fun state =>
    (det.stateOf state,
      DetMullerAutomaton.LAR.initialRecord det.muller,
      ∅)
  initial_state := by
    change
      (det.stateOf A.initial,
        DetMullerAutomaton.LAR.initialRecord det.muller,
        ∅) =
        (det.muller.initial,
          DetMullerAutomaton.LAR.initialRecord det.muller,
          ∅)
    simp [det.initial_state]
  correctFrom := by
    intro state word
    trans det.muller.AcceptsFrom (det.stateOf state) word
    · exact
        DetMullerAutomaton.LAR.eventAutomaton_correctFrom
          (A := det.muller)
          (state :=
            (det.stateOf state,
              DetMullerAutomaton.LAR.initialRecord det.muller,
              ∅))
          word
    · exact det.correctFrom state word

/-- A macro-transition edge between finite APA macro-states. -/
abbrev APAMacroEdge {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :=
  Finset A.State × Finset A.State

/-- A support edge between individual APA states. -/
abbrev APAStateEdge {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :=
  A.State × A.State

/--
The deterministic state tracked by the APA macro-configuration construction.

`configs` is the current reachable set of APA macro-states.  `edges` records
the macro-transition edges generated in the previous deterministic step.  The
edge component is the finite memory needed for later Muller acceptance over
recurring transition structure.
-/
structure APAMacroConfigurationState {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) where
  configs : Finset (Finset A.State)
  edges : Finset (APAMacroEdge A)

namespace APAMacroConfigurationState

def toProd {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (state : APAMacroConfigurationState A) :
    Finset (Finset A.State) × Finset (APAMacroEdge A) :=
  (state.configs, state.edges)

def ofProd {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (state : Finset (Finset A.State) × Finset (APAMacroEdge A)) :
    APAMacroConfigurationState A where
  configs := state.1
  edges := state.2

def equivProd {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    APAMacroConfigurationState A ≃
      Finset (Finset A.State) × Finset (APAMacroEdge A) where
  toFun := toProd
  invFun := ofProd
  left_inv := by
    intro state
    cases state
    rfl
  right_inv := by
    intro state
    rcases state with ⟨configs, edges⟩
    rfl

noncomputable instance finsetStateFintype {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Fintype (Finset A.State) := by
  classical
  exact inferInstance

noncomputable instance edgeFintype {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Fintype (APAMacroEdge A) := by
  classical
  exact inferInstance

noncomputable instance edgeFinsetFintype {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Fintype (Finset (APAMacroEdge A)) := by
  classical
  exact inferInstance

noncomputable instance {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Fintype (APAMacroConfigurationState A) := by
  classical
  exact
    Fintype.ofEquiv
      (Finset (Finset A.State) × Finset (APAMacroEdge A))
      (equivProd A).symm

/-- Initial deterministic macro-configuration state for a chosen APA macro-state. -/
def initial {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (initialStates : Finset A.State) :
    APAMacroConfigurationState A where
  configs := {initialStates}
  edges := ∅

/-- One deterministic macro-configuration step. -/
noncomputable def step {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (state : APAMacroConfigurationState A)
    (letter : Alphabet) :
    APAMacroConfigurationState A :=
  let edges := A.macroConfigurationEdges state.configs letter
  { configs := A.macroConfigurationStep state.configs letter
    edges := edges }

@[simp]
theorem initial_configs {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (initialStates : Finset A.State) :
    (initial (A := A) initialStates).configs = {initialStates} :=
  rfl

@[simp]
theorem initial_edges {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (initialStates : Finset A.State) :
    (initial (A := A) initialStates).edges = ∅ :=
  rfl

@[simp]
theorem step_configs {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (state : APAMacroConfigurationState A)
    (letter : Alphabet) :
    (step state letter).configs =
      A.macroConfigurationStep state.configs letter :=
  rfl

@[simp]
theorem step_edges {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (state : APAMacroConfigurationState A)
    (letter : Alphabet) :
    (step state letter).edges =
      A.macroConfigurationEdges state.configs letter :=
  rfl

end APAMacroConfigurationState

/--
The deterministic Muller skeleton carried by the APA macro-configuration state
machine.  The accepting family is supplied separately; subsequent lemmas build
the correct Muller family on this concrete deterministic carrier.
-/
noncomputable def AlternatingParityAutomaton.macroConfigurationMullerSkeleton
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (APAMacroConfigurationState A))) :
    DetMullerAutomaton.{u, v} Alphabet where
  State := APAMacroConfigurationState A
  stateFinite := by
    classical
    exact inferInstance
  initial := APAMacroConfigurationState.initial initialStates
  step := APAMacroConfigurationState.step
  accepting := accepting

@[simp]
theorem AlternatingParityAutomaton.macroConfigurationMullerSkeleton_runFrom_configs
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (APAMacroConfigurationState A)))
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((A.macroConfigurationMullerSkeleton initialStates accepting).runFrom
      (APAMacroConfigurationState.initial initialStates) word n).configs =
        A.macroConfigurationRun initialStates word n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        A.macroConfigurationStep
            (((A.macroConfigurationMullerSkeleton initialStates accepting).runFrom
              (APAMacroConfigurationState.initial initialStates) word n).configs)
            (word n) =
          A.macroConfigurationRun initialStates word (n + 1)
      rw [ih]
      rfl

theorem AlternatingParityAutomaton.macroConfigurationMullerSkeleton_run_configs
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (APAMacroConfigurationState A)))
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((A.macroConfigurationMullerSkeleton initialStates accepting).run word n).configs =
      A.macroConfigurationRun initialStates word n := by
  exact A.macroConfigurationMullerSkeleton_runFrom_configs
    initialStates accepting word n

theorem AlternatingParityAutomaton.macroConfigurationMullerSkeleton_runFrom_edges_succ
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (APAMacroConfigurationState A)))
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((A.macroConfigurationMullerSkeleton initialStates accepting).runFrom
      (APAMacroConfigurationState.initial initialStates) word (n + 1)).edges =
        A.macroConfigurationEdgeRun initialStates word n := by
  change
    A.macroConfigurationEdges
        (((A.macroConfigurationMullerSkeleton initialStates accepting).runFrom
          (APAMacroConfigurationState.initial initialStates) word n).configs)
        (word n) =
      A.macroConfigurationEdgeRun initialStates word n
  rw [A.macroConfigurationMullerSkeleton_runFrom_configs
    initialStates accepting word n]
  rfl

theorem AlternatingParityAutomaton.macroConfigurationMullerSkeleton_run_edges_succ
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (APAMacroConfigurationState A)))
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((A.macroConfigurationMullerSkeleton initialStates accepting).run word
      (n + 1)).edges =
        A.macroConfigurationEdgeRun initialStates word n := by
  exact A.macroConfigurationMullerSkeleton_runFrom_edges_succ
    initialStates accepting word n

/--
All individual support edges generated from a deterministic configuration on
one input letter, ranging over all macro transitions and their support choices.
-/
noncomputable def AlternatingParityAutomaton.macroConfigurationStateEdges
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (configs : Finset (Finset A.State))
    (letter : Alphabet) :
    Finset (APAStateEdge A) := by
  classical
  exact Finset.univ.filter (fun edge =>
    ∃ states ∈ configs,
      ∃ nextStates : Finset A.State,
        ∃ stateEdges : Finset (APAStateEdge A),
          A.MacroTransitionWithStateEdges states letter nextStates stateEdges ∧
            edge ∈ stateEdges)

@[simp]
theorem AlternatingParityAutomaton.mem_macroConfigurationStateEdges
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (configs : Finset (Finset A.State))
    (edge : APAStateEdge A)
    (letter : Alphabet) :
    edge ∈ A.macroConfigurationStateEdges configs letter ↔
      ∃ states ∈ configs,
        ∃ nextStates : Finset A.State,
          ∃ stateEdges : Finset (APAStateEdge A),
            A.MacroTransitionWithStateEdges states letter nextStates stateEdges ∧
              edge ∈ stateEdges := by
  classical
  simp [macroConfigurationStateEdges]

/-- The deterministic support-edge stream generated by the configuration run. -/
noncomputable def AlternatingParityAutomaton.macroConfigurationStateEdgeRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    Finset (APAStateEdge A) :=
  A.macroConfigurationStateEdges
    (A.macroConfigurationRun initialStates word n)
    (word n)

@[simp]
theorem AlternatingParityAutomaton.mem_macroConfigurationStateEdgeRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (n : Nat)
    (edge : APAStateEdge A) :
    edge ∈ A.macroConfigurationStateEdgeRun initialStates word n ↔
      ∃ states ∈ A.macroConfigurationRun initialStates word n,
        ∃ nextStates : Finset A.State,
          ∃ stateEdges : Finset (APAStateEdge A),
            A.MacroTransitionWithStateEdges states (word n) nextStates stateEdges ∧
              edge ∈ stateEdges := by
  simp [macroConfigurationStateEdgeRun]

theorem AlternatingParityAutomaton.macroConfigurationStateEdges_mono
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {configs₁ configs₂ : Finset (Finset A.State)}
    {letter : Alphabet}
    (hsubset : configs₁ ⊆ configs₂) :
    A.macroConfigurationStateEdges configs₁ letter ⊆
      A.macroConfigurationStateEdges configs₂ letter := by
  intro edge hedge
  rcases (A.mem_macroConfigurationStateEdges configs₁ edge letter).mp hedge with
    ⟨states, hstates, nextStates, stateEdges, htransition, hedgeState⟩
  exact
    (A.mem_macroConfigurationStateEdges configs₂ edge letter).mpr
      ⟨states, hsubset hstates, nextStates, stateEdges,
        htransition, hedgeState⟩

theorem AlternatingParityAutomaton.macroConfigurationStateEdgeRun_mem_of_mem_start
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates startStates : Finset A.State}
    {edge : APAStateEdge A}
    {word : OmegaWord Alphabet}
    {offset length : Nat}
    (hstart :
      startStates ∈ A.macroConfigurationRun initialStates word offset)
    (hedge :
      edge ∈
        A.macroConfigurationStateEdgeRun startStates
          (OmegaWord.drop word offset) length) :
    edge ∈
      A.macroConfigurationStateEdgeRun initialStates word (offset + length) := by
  rw [A.mem_macroConfigurationStateEdgeRun] at hedge ⊢
  rcases hedge with
    ⟨states, hstates, nextStates, stateEdges, htransition, hedgeState⟩
  refine
    ⟨states, A.macroConfigurationRun_mem_of_mem_start hstart hstates,
      nextStates, stateEdges, ?_, hedgeState⟩
  simpa [OmegaWord.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using htransition

/--
The deterministic state tracked by the support-edge-enriched APA
macro-configuration construction.
-/
structure APASupportConfigurationState {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) where
  configs : Finset (Finset A.State)
  macroEdges : Finset (APAMacroEdge A)
  stateEdges : Finset (APAStateEdge A)

namespace APASupportConfigurationState

def toProd {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (state : APASupportConfigurationState A) :
    (Finset (Finset A.State) × Finset (APAMacroEdge A)) ×
      Finset (APAStateEdge A) :=
  ((state.configs, state.macroEdges), state.stateEdges)

def ofProd {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (state :
      (Finset (Finset A.State) × Finset (APAMacroEdge A)) ×
        Finset (APAStateEdge A)) :
    APASupportConfigurationState A where
  configs := state.1.1
  macroEdges := state.1.2
  stateEdges := state.2

def equivProd {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    APASupportConfigurationState A ≃
      (Finset (Finset A.State) × Finset (APAMacroEdge A)) ×
        Finset (APAStateEdge A) where
  toFun := toProd
  invFun := ofProd
  left_inv := by
    intro state
    cases state
    rfl
  right_inv := by
    intro state
    rcases state with ⟨⟨configs, macroEdges⟩, stateEdges⟩
    rfl

noncomputable instance {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Fintype (APASupportConfigurationState A) := by
  classical
  exact
    Fintype.ofEquiv
      ((Finset (Finset A.State) × Finset (APAMacroEdge A)) ×
        Finset (APAStateEdge A))
      (equivProd A).symm

def initial {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (initialStates : Finset A.State) :
    APASupportConfigurationState A where
  configs := {initialStates}
  macroEdges := ∅
  stateEdges := ∅

noncomputable def step {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (state : APASupportConfigurationState A)
    (letter : Alphabet) :
    APASupportConfigurationState A :=
  { configs := A.macroConfigurationStep state.configs letter
    macroEdges := A.macroConfigurationEdges state.configs letter
    stateEdges := A.macroConfigurationStateEdges state.configs letter }

@[simp]
theorem initial_configs {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (initialStates : Finset A.State) :
    (initial (A := A) initialStates).configs = {initialStates} :=
  rfl

@[simp]
theorem initial_macroEdges {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (initialStates : Finset A.State) :
    (initial (A := A) initialStates).macroEdges = ∅ :=
  rfl

@[simp]
theorem initial_stateEdges {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (initialStates : Finset A.State) :
    (initial (A := A) initialStates).stateEdges = ∅ :=
  rfl

@[simp]
theorem step_configs {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (state : APASupportConfigurationState A)
    (letter : Alphabet) :
    (step state letter).configs =
      A.macroConfigurationStep state.configs letter :=
  rfl

@[simp]
theorem step_macroEdges {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (state : APASupportConfigurationState A)
    (letter : Alphabet) :
    (step state letter).macroEdges =
      A.macroConfigurationEdges state.configs letter :=
  rfl

@[simp]
theorem step_stateEdges {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (state : APASupportConfigurationState A)
    (letter : Alphabet) :
    (step state letter).stateEdges =
      A.macroConfigurationStateEdges state.configs letter :=
  rfl

end APASupportConfigurationState

def AlternatingParityAutomaton.stepSupportWithInitialTo
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root state : A.State)
    (letter : Alphabet)
    (support : (A.withInitial root).StepSupport state letter) :
    A.StepSupport state letter where
  support := support.support
  support_satisfies := by
    simpa [AlternatingParityAutomaton.withInitial] using support.support_satisfies
  support_atoms := by
    intro next hnext
    simpa [AlternatingParityAutomaton.withInitial] using
      support.support_atoms next hnext

def AlternatingParityAutomaton.stepSupportWithInitialFrom
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root state : A.State)
    (letter : Alphabet)
    (support : A.StepSupport state letter) :
    (A.withInitial root).StepSupport state letter where
  support := support.support
  support_satisfies := by
    simpa [AlternatingParityAutomaton.withInitial] using support.support_satisfies
  support_atoms := by
    intro next hnext
    simpa [AlternatingParityAutomaton.withInitial] using
      support.support_atoms next hnext

noncomputable def AlternatingParityAutomaton.macroStepSupportWithInitialTo
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (states : Finset A.State)
    (letter : Alphabet)
    (support : (A.withInitial root).MacroStepSupport states letter) :
    A.MacroStepSupport states letter where
  choice := fun state =>
    A.stepSupportWithInitialTo root state.1 letter (support.choice state)

noncomputable def AlternatingParityAutomaton.macroStepSupportWithInitialFrom
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (states : Finset A.State)
    (letter : Alphabet)
    (support : A.MacroStepSupport states letter) :
    (A.withInitial root).MacroStepSupport states letter where
  choice := fun state =>
    A.stepSupportWithInitialFrom root state.1 letter (support.choice state)

theorem AlternatingParityAutomaton.macroTransition_withInitial_iff
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (states nextStates : Finset A.State)
    (letter : Alphabet) :
    (A.withInitial root).MacroTransition states letter nextStates ↔
      A.MacroTransition states letter nextStates := by
  constructor
  · intro htransition
    rcases htransition with ⟨support, hsupport⟩
    refine ⟨A.macroStepSupportWithInitialTo root states letter support, ?_⟩
    simpa [AlternatingParityAutomaton.macroStepSupportWithInitialTo,
      AlternatingParityAutomaton.stepSupportWithInitialTo,
      MacroStepSupport.support, AlternatingParityAutomaton.withInitial] using
      hsupport
  · intro htransition
    rcases htransition with ⟨support, hsupport⟩
    refine ⟨A.macroStepSupportWithInitialFrom root states letter support, ?_⟩
    simpa [AlternatingParityAutomaton.macroStepSupportWithInitialFrom,
      AlternatingParityAutomaton.stepSupportWithInitialFrom,
      MacroStepSupport.support, AlternatingParityAutomaton.withInitial] using
      hsupport

theorem AlternatingParityAutomaton.macroTransitionWithStateEdges_withInitial_iff
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (states nextStates : Finset A.State)
    (letter : Alphabet)
    (stateEdges : Finset (APAStateEdge A)) :
    (A.withInitial root).MacroTransitionWithStateEdges
        states letter nextStates stateEdges ↔
      A.MacroTransitionWithStateEdges states letter nextStates stateEdges := by
  constructor
  · intro htransition
    rcases htransition with ⟨support, hsupport, hstateEdges⟩
    refine
      ⟨A.macroStepSupportWithInitialTo root states letter support, ?_, ?_⟩
    · simpa [AlternatingParityAutomaton.macroStepSupportWithInitialTo,
        AlternatingParityAutomaton.stepSupportWithInitialTo,
        MacroStepSupport.support, AlternatingParityAutomaton.withInitial] using
        hsupport
    · simpa [AlternatingParityAutomaton.macroStepSupportWithInitialTo,
        AlternatingParityAutomaton.stepSupportWithInitialTo,
        MacroStepSupport.stateEdges, AlternatingParityAutomaton.withInitial] using
        hstateEdges
  · intro htransition
    rcases htransition with ⟨support, hsupport, hstateEdges⟩
    refine
      ⟨A.macroStepSupportWithInitialFrom root states letter support, ?_, ?_⟩
    · simpa [AlternatingParityAutomaton.macroStepSupportWithInitialFrom,
        AlternatingParityAutomaton.stepSupportWithInitialFrom,
        MacroStepSupport.support, AlternatingParityAutomaton.withInitial] using
        hsupport
    · simpa [AlternatingParityAutomaton.macroStepSupportWithInitialFrom,
        AlternatingParityAutomaton.stepSupportWithInitialFrom,
        MacroStepSupport.stateEdges, AlternatingParityAutomaton.withInitial] using
        hstateEdges

theorem AlternatingParityAutomaton.macroConfigurationStep_withInitial_eq
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (configs : Finset (Finset A.State))
    (letter : Alphabet) :
    (A.withInitial root).macroConfigurationStep configs letter =
      A.macroConfigurationStep configs letter := by
  ext nextStates
  constructor
  · intro hmem
    rcases
      ((A.withInitial root).mem_macroConfigurationStep
        configs nextStates letter).mp hmem with
      ⟨states, hstates, htransition⟩
    exact
      (A.mem_macroConfigurationStep configs nextStates letter).mpr
        ⟨states, hstates,
          (A.macroTransition_withInitial_iff
            root states nextStates letter).mp htransition⟩
  · intro hmem
    rcases (A.mem_macroConfigurationStep configs nextStates letter).mp
      hmem with
      ⟨states, hstates, htransition⟩
    exact
      ((A.withInitial root).mem_macroConfigurationStep
        configs nextStates letter).mpr
        ⟨states, hstates,
          (A.macroTransition_withInitial_iff
            root states nextStates letter).mpr htransition⟩

theorem AlternatingParityAutomaton.macroConfigurationEdges_withInitial_eq
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (configs : Finset (Finset A.State))
    (letter : Alphabet) :
    (A.withInitial root).macroConfigurationEdges configs letter =
      A.macroConfigurationEdges configs letter := by
  ext edge
  constructor
  · intro hmem
    rcases
      ((A.withInitial root).mem_macroConfigurationEdges
        configs edge letter).mp hmem with
      ⟨hsource, htransition⟩
    exact
      (A.mem_macroConfigurationEdges configs edge letter).mpr
        ⟨hsource,
          (A.macroTransition_withInitial_iff
            root edge.1 edge.2 letter).mp htransition⟩
  · intro hmem
    rcases (A.mem_macroConfigurationEdges configs edge letter).mp
      hmem with
      ⟨hsource, htransition⟩
    exact
      ((A.withInitial root).mem_macroConfigurationEdges
        configs edge letter).mpr
        ⟨hsource,
          (A.macroTransition_withInitial_iff
            root edge.1 edge.2 letter).mpr htransition⟩

theorem AlternatingParityAutomaton.macroConfigurationStateEdges_withInitial_eq
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (configs : Finset (Finset A.State))
    (letter : Alphabet) :
    (A.withInitial root).macroConfigurationStateEdges configs letter =
      A.macroConfigurationStateEdges configs letter := by
  ext edge
  constructor
  · intro hmem
    rcases
      ((A.withInitial root).mem_macroConfigurationStateEdges
        configs edge letter).mp hmem with
      ⟨states, hstates, nextStates, stateEdges, htransition, hedge⟩
    exact
      (A.mem_macroConfigurationStateEdges configs edge letter).mpr
        ⟨states, hstates, nextStates, stateEdges,
          (A.macroTransitionWithStateEdges_withInitial_iff
            root states nextStates letter stateEdges).mp htransition,
          hedge⟩
  · intro hmem
    rcases (A.mem_macroConfigurationStateEdges configs edge letter).mp
      hmem with
      ⟨states, hstates, nextStates, stateEdges, htransition, hedge⟩
    exact
      ((A.withInitial root).mem_macroConfigurationStateEdges
        configs edge letter).mpr
        ⟨states, hstates, nextStates, stateEdges,
          (A.macroTransitionWithStateEdges_withInitial_iff
            root states nextStates letter stateEdges).mpr htransition,
          hedge⟩

noncomputable def APASupportConfigurationState.withInitialTo
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (state : APASupportConfigurationState (A.withInitial root)) :
    APASupportConfigurationState A where
  configs := state.configs
  macroEdges := state.macroEdges
  stateEdges := state.stateEdges

@[simp]
theorem APASupportConfigurationState.withInitialTo_initial
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (initialStates : Finset A.State) :
    APASupportConfigurationState.withInitialTo A root
        (APASupportConfigurationState.initial
          (A := A.withInitial root) initialStates) =
      APASupportConfigurationState.initial (A := A) initialStates := by
  rfl

theorem APASupportConfigurationState.withInitialTo_step
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (state : APASupportConfigurationState (A.withInitial root))
    (letter : Alphabet) :
    APASupportConfigurationState.withInitialTo A root
        (APASupportConfigurationState.step state letter) =
      APASupportConfigurationState.step
        (APASupportConfigurationState.withInitialTo A root state) letter := by
  cases state with
  | mk configs macroEdges stateEdges =>
      apply (APASupportConfigurationState.equivProd A).injective
      simp [APASupportConfigurationState.withInitialTo,
        APASupportConfigurationState.step,
        APASupportConfigurationState.equivProd,
        APASupportConfigurationState.toProd,
        AlternatingParityAutomaton.macroConfigurationStep_withInitial_eq,
        AlternatingParityAutomaton.macroConfigurationEdges_withInitial_eq,
        AlternatingParityAutomaton.macroConfigurationStateEdges_withInitial_eq]

/--
The deterministic Muller skeleton with individual support-edge memory.  This is
the carrier needed for the final APA-to-Muller accepting family.
-/
noncomputable def AlternatingParityAutomaton.supportConfigurationMullerSkeleton
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (APASupportConfigurationState A))) :
    DetMullerAutomaton.{u, v} Alphabet where
  State := APASupportConfigurationState A
  stateFinite := by
    classical
    exact inferInstance
  initial := APASupportConfigurationState.initial initialStates
  step := APASupportConfigurationState.step
  accepting := accepting

@[simp]
theorem AlternatingParityAutomaton.supportConfigurationMullerSkeleton_runFrom_configs
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (APASupportConfigurationState A)))
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((A.supportConfigurationMullerSkeleton initialStates accepting).runFrom
      (APASupportConfigurationState.initial initialStates) word n).configs =
        A.macroConfigurationRun initialStates word n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        A.macroConfigurationStep
            (((A.supportConfigurationMullerSkeleton initialStates accepting).runFrom
              (APASupportConfigurationState.initial initialStates) word n).configs)
            (word n) =
          A.macroConfigurationRun initialStates word (n + 1)
      rw [ih]
      rfl

theorem AlternatingParityAutomaton.supportConfigurationMullerSkeleton_run_configs
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (APASupportConfigurationState A)))
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((A.supportConfigurationMullerSkeleton initialStates accepting).run word n).configs =
      A.macroConfigurationRun initialStates word n := by
  exact A.supportConfigurationMullerSkeleton_runFrom_configs
    initialStates accepting word n

/--
The deterministic support-carrier run does not depend on the Muller accepting
family installed on the same carrier.
-/
theorem AlternatingParityAutomaton.supportConfigurationMullerSkeleton_run_eq
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting₁ accepting₂ : Set (Set (APASupportConfigurationState A)))
    (word : OmegaWord Alphabet) :
    (A.supportConfigurationMullerSkeleton initialStates accepting₁).run word =
      (A.supportConfigurationMullerSkeleton initialStates accepting₂).run word := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        APASupportConfigurationState.step
            ((A.supportConfigurationMullerSkeleton initialStates accepting₁).run word n)
            (word n) =
          APASupportConfigurationState.step
            ((A.supportConfigurationMullerSkeleton initialStates accepting₂).run word n)
            (word n)
      rw [ih]

/--
Consequently, the infinity set of the support-carrier run is independent of the
chosen Muller accepting family.
-/
theorem AlternatingParityAutomaton.supportConfigurationMullerSkeleton_InfStates_eq
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting₁ accepting₂ : Set (Set (APASupportConfigurationState A)))
    (word : OmegaWord Alphabet) :
    (A.supportConfigurationMullerSkeleton initialStates accepting₁).InfStates word =
      (A.supportConfigurationMullerSkeleton initialStates accepting₂).InfStates word := by
  ext state
  constructor
  · intro hseen n
    rcases hseen n with ⟨k, hk, hkstate⟩
    refine ⟨k, hk, ?_⟩
    have hrun :=
      congrFun
        (A.supportConfigurationMullerSkeleton_run_eq
          initialStates accepting₁ accepting₂ word) k
    change
      (A.supportConfigurationMullerSkeleton initialStates accepting₁).run word k =
        state at hkstate
    change
      (A.supportConfigurationMullerSkeleton initialStates accepting₂).run word k =
        state
    exact hrun.symm.trans hkstate
  · intro hseen n
    rcases hseen n with ⟨k, hk, hkstate⟩
    refine ⟨k, hk, ?_⟩
    have hrun :=
      congrFun
        (A.supportConfigurationMullerSkeleton_run_eq
          initialStates accepting₁ accepting₂ word) k
    change
      (A.supportConfigurationMullerSkeleton initialStates accepting₂).run word k =
        state at hkstate
    change
      (A.supportConfigurationMullerSkeleton initialStates accepting₁).run word k =
        state
    exact hrun.trans hkstate

theorem AlternatingParityAutomaton.supportConfigurationMullerSkeleton_runFrom_macroEdges_succ
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (APASupportConfigurationState A)))
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((A.supportConfigurationMullerSkeleton initialStates accepting).runFrom
      (APASupportConfigurationState.initial initialStates) word (n + 1)).macroEdges =
        A.macroConfigurationEdgeRun initialStates word n := by
  change
    A.macroConfigurationEdges
        (((A.supportConfigurationMullerSkeleton initialStates accepting).runFrom
          (APASupportConfigurationState.initial initialStates) word n).configs)
        (word n) =
      A.macroConfigurationEdgeRun initialStates word n
  rw [A.supportConfigurationMullerSkeleton_runFrom_configs
    initialStates accepting word n]
  rfl

theorem AlternatingParityAutomaton.supportConfigurationMullerSkeleton_run_macroEdges_succ
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (APASupportConfigurationState A)))
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((A.supportConfigurationMullerSkeleton initialStates accepting).run word
      (n + 1)).macroEdges =
        A.macroConfigurationEdgeRun initialStates word n := by
  exact A.supportConfigurationMullerSkeleton_runFrom_macroEdges_succ
    initialStates accepting word n

theorem AlternatingParityAutomaton.supportConfigurationMullerSkeleton_runFrom_stateEdges_succ
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (APASupportConfigurationState A)))
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((A.supportConfigurationMullerSkeleton initialStates accepting).runFrom
      (APASupportConfigurationState.initial initialStates) word (n + 1)).stateEdges =
        A.macroConfigurationStateEdgeRun initialStates word n := by
  change
    A.macroConfigurationStateEdges
        (((A.supportConfigurationMullerSkeleton initialStates accepting).runFrom
          (APASupportConfigurationState.initial initialStates) word n).configs)
        (word n) =
      A.macroConfigurationStateEdgeRun initialStates word n
  rw [A.supportConfigurationMullerSkeleton_runFrom_configs
    initialStates accepting word n]
  rfl

theorem AlternatingParityAutomaton.supportConfigurationMullerSkeleton_run_stateEdges_succ
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (APASupportConfigurationState A)))
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((A.supportConfigurationMullerSkeleton initialStates accepting).run word
      (n + 1)).stateEdges =
        A.macroConfigurationStateEdgeRun initialStates word n := by
  exact A.supportConfigurationMullerSkeleton_runFrom_stateEdges_succ
    initialStates accepting word n

/--
Early local copy of the finite-stream recurrence lemma, used by the enriched
support-edge skeleton before the generic named version below.
-/
theorem exists_seenInfinitelyOften_of_frequently_mem_finset_early
    {α : Type u}
    [Fintype α]
    (stream : Nat -> α)
    (targets : Finset α)
    (hfreq : ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ stream k ∈ targets) :
    ∃ target : α,
      target ∈ targets ∧
        ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ stream k = target := by
  classical
  by_contra hnone
  push Not at hnone
  have htargetBound :
      ∀ target ∈ targets,
        ∃ n : Nat, ∀ k : Nat, n ≤ k -> stream k ≠ target := by
    intro target htarget
    exact hnone target htarget
  choose bound hbound using htargetBound
  let boundOf : α -> Nat := fun target =>
    if htarget : target ∈ targets then bound target htarget else 0
  rcases hfreq (targets.sup boundOf) with ⟨k, hk, hkTarget⟩
  have hle : boundOf (stream k) ≤ targets.sup boundOf :=
    Finset.le_sup hkTarget
  have hboundOf :
      boundOf (stream k) = bound (stream k) hkTarget := by
    simp [boundOf, hkTarget]
  exact hbound (stream k) hkTarget k
    (by
      rw [← hboundOf]
      exact le_trans hle hk)
    rfl

/-- Chosen individual support edges for one step of a macro-run. -/
noncomputable def AlternatingParityAutomaton.MacroRun.stepStateEdges
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (n : Nat) :
    Finset (APAStateEdge A) :=
  Classical.choose
    (A.exists_stateEdges_of_macroTransition (run.step_transition n))

theorem AlternatingParityAutomaton.MacroRun.stepStateEdges_transition
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (n : Nat) :
    A.MacroTransitionWithStateEdges
      (run.states n)
      (word n)
      (run.states (n + 1))
      (run.stepStateEdges n) :=
  Classical.choose_spec
    (A.exists_stateEdges_of_macroTransition (run.step_transition n))

/--
Every individual support edge chosen by a macro-run step is present in the
deterministic support-edge stream at that step.
-/
theorem AlternatingParityAutomaton.MacroRun.stateEdge_mem_macroConfigurationStateEdgeRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (n : Nat)
    {edge : APAStateEdge A}
    (hedge : edge ∈ run.stepStateEdges n) :
    edge ∈ A.macroConfigurationStateEdgeRun initialStates word n := by
  exact
    (A.mem_macroConfigurationStateEdgeRun initialStates word n edge).mpr
      ⟨run.states n,
        run.states_mem_macroConfigurationRun n,
        run.states (n + 1),
        run.stepStateEdges n,
        run.stepStateEdges_transition n,
        hedge⟩

theorem AlternatingParityAutomaton.MacroRun.stepStateEdges_source_mem
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (n : Nat)
    {edge : APAStateEdge A}
    (hedge : edge ∈ run.stepStateEdges n) :
    edge.1 ∈ run.states n := by
  exact (run.stepStateEdges_transition n).edge_source_mem hedge

theorem AlternatingParityAutomaton.MacroRun.stepStateEdges_target_mem
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (n : Nat)
    {edge : APAStateEdge A}
    (hedge : edge ∈ run.stepStateEdges n) :
    edge.2 ∈ run.states (n + 1) := by
  exact (run.stepStateEdges_transition n).edge_target_mem hedge

/--
A macro-run with explicit per-step individual state-edge witnesses.

`MacroRun.stepStateEdges` is intentionally a classical selector from the
existence proof for each macro-transition.  For the APA run-tree-to-support
argument we need to carry the edge choices that came from the concrete run tree,
so this structure records them explicitly.
-/
structure AlternatingParityAutomaton.EdgeWitnessedMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet) where
  toMacroRun : A.MacroRun initialStates word
  stateEdges : Nat -> Finset (APAStateEdge A)
  step_stateEdges_transition :
    ∀ n : Nat,
      A.MacroTransitionWithStateEdges
        (toMacroRun.states n)
        (word n)
        (toMacroRun.states (n + 1))
        (stateEdges n)

namespace AlternatingParityAutomaton.EdgeWitnessedMacroRun

theorem stateEdges_source_mem
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (n : Nat)
    {edge : APAStateEdge A}
    (hedge : edge ∈ run.stateEdges n) :
    edge.1 ∈ run.toMacroRun.states n := by
  exact (run.step_stateEdges_transition n).edge_source_mem hedge

theorem stateEdges_target_mem
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (n : Nat)
    {edge : APAStateEdge A}
    (hedge : edge ∈ run.stateEdges n) :
    edge.2 ∈ run.toMacroRun.states (n + 1) := by
  exact (run.step_stateEdges_transition n).edge_target_mem hedge

/-- An explicitly chosen individual state edge occurs infinitely often. -/
def StateEdgeSeenInfinitelyOften
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (edge : APAStateEdge A) :
    Prop :=
  ∀ n : Nat,
    ∃ k : Nat,
      n ≤ k ∧ edge ∈ run.stateEdges k

/-- The finite set of explicitly chosen individual state edges seen infinitely often. -/
noncomputable def infStateEdgeFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word) :
    Finset (APAStateEdge A) := by
  classical
  exact Finset.univ.filter (fun edge => run.StateEdgeSeenInfinitelyOften edge)

@[simp]
theorem mem_infStateEdgeFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (edge : APAStateEdge A) :
    edge ∈ run.infStateEdgeFinset ↔ run.StateEdgeSeenInfinitelyOften edge := by
  classical
  simp [infStateEdgeFinset]

/-- A coherent infinite path through the explicitly recorded support choices. -/
def SupportPath
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (path : Nat -> A.State) :
    Prop :=
  path 0 ∈ initialStates ∧
    ∀ n : Nat, (path n, path (n + 1)) ∈ run.stateEdges n

theorem SupportPath.state_mem
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {run : A.EdgeWitnessedMacroRun initialStates word}
    {path : Nat -> A.State}
    (hpath : run.SupportPath path)
    (n : Nat) :
    path n ∈ run.toMacroRun.states n := by
  induction n with
  | zero =>
      simpa [run.toMacroRun.initial_states] using hpath.1
  | succ n _ih =>
      exact run.stateEdges_target_mem n (hpath.2 n)

/--
Every state in an edge-witnessed macro-run frontier has a finite support-edge
prefix from the initial macro-state.
-/
theorem exists_supportPathPrefix_of_state_mem
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    {length : Nat}
    {target : A.State}
    (htarget : target ∈ run.toMacroRun.states length) :
    ∃ pref : Nat -> A.State,
      pref 0 ∈ initialStates ∧
        pref length = target ∧
          ∀ i : Nat, i < length ->
            (pref i, pref (i + 1)) ∈ run.stateEdges i := by
  induction length generalizing target with
  | zero =>
      refine ⟨fun _ => target, ?_, rfl, ?_⟩
      · simpa [run.toMacroRun.initial_states] using htarget
      · intro i hi
        omega
  | succ length ih =>
      rcases
        (run.step_stateEdges_transition length).exists_edge_of_target_mem
          htarget with
        ⟨source, hsource, hedge⟩
      rcases ih hsource with ⟨pref, hprefixInit, hprefixEnd, hprefixEdges⟩
      let extended : Nat -> A.State := fun i =>
        if i ≤ length then pref i else target
      refine ⟨extended, ?_, ?_, ?_⟩
      · have hzero : 0 ≤ length := Nat.zero_le length
        simpa [extended, hzero] using hprefixInit
      · have hnot : ¬ length + 1 ≤ length := by omega
        simp [extended, hnot]
      · intro i hi
        by_cases hlt : i < length
        · have hi_le : i ≤ length := by omega
          have hsucc_le : i + 1 ≤ length := by omega
          simpa [extended, hi_le, hsucc_le] using hprefixEdges i hlt
        · have hi_eq : i = length := by omega
          subst i
          have hle : length ≤ length := le_rfl
          have hnot : ¬ length + 1 ≤ length := by omega
          simpa [extended, hle, hnot, hprefixEnd] using hedge

/--
An edge-witnessed macro-run is support-accepting if every infinite path through
its explicitly recorded state edges satisfies the APA parity condition.
-/
def SupportAccepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word) :
    Prop :=
  ∀ path : Nat -> A.State,
    run.SupportPath path ->
      ∃ p : Nat,
        DetParityAutomaton.NatEven p ∧
          (∀ n : Nat, ∃ k : Nat, n ≤ k ∧ A.priority (path k) = p) ∧
            ∀ q : Nat,
              (∀ n : Nat, ∃ k : Nat, n ≤ k ∧ A.priority (path k) = q) ->
                p ≤ q

/--
An edge-witnessed macro-run is realized by APA run trees when every initial
state has a run tree whose active branches follow the explicitly recorded
state edges.
-/
def HasRunTreeRealization
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word) :
    Prop :=
  ∀ state, state ∈ initialStates ->
    ∃ runTree : (A.withInitial state).Run word,
      ∀ branch : Nat -> Nat,
        runTree.ActiveBranch branch ->
          run.SupportPath
            (fun n => runTree.stateAt (branchPrefix branch n))

/--
If an edge-witnessed macro-run is support-accepting and realized by actual APA
run trees, then every initial macro-state accepts the word.
-/
theorem acceptsFrom_all_initial_of_supportAccepting_realized
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (hsupport : run.SupportAccepting)
    (hrealized : run.HasRunTreeRealization) :
    ∀ state, state ∈ initialStates -> A.AcceptsFrom state word := by
  intro state hstate
  rcases hrealized state hstate with ⟨runTree, hbranches⟩
  refine ⟨runTree, ?_⟩
  intro branch hbranch
  have hpath :
      run.SupportPath
        (fun n => runTree.stateAt (branchPrefix branch n)) :=
    hbranches branch hbranch
  rcases hsupport
    (fun n => runTree.stateAt (branchPrefix branch n)) hpath with
    ⟨p, hpEven, hpSeen, hpMin⟩
  refine ⟨p, hpEven, ?_, ?_⟩
  · intro n
    rcases hpSeen n with ⟨k, hk, hkprio⟩
    exact ⟨k, hk, by simpa [AlternatingParityAutomaton.withInitial] using hkprio⟩
  · intro q hqSeen
    apply hpMin q
    intro n
    rcases hqSeen n with ⟨k, hk, hkprio⟩
    exact ⟨k, hk, by simpa [AlternatingParityAutomaton.withInitial] using hkprio⟩

noncomputable def stepSupportChoice
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (n : Nat) :
    A.MacroStepSupport (run.toMacroRun.states n) (word n) :=
  Classical.choose (run.step_stateEdges_transition n)

theorem stepSupportChoice_support
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (n : Nat) :
    (run.stepSupportChoice n).support = run.toMacroRun.states (n + 1) :=
  (Classical.choose_spec (run.step_stateEdges_transition n)).1

theorem stepSupportChoice_stateEdges
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (n : Nat) :
    (run.stepSupportChoice n).stateEdges = run.stateEdges n :=
  (Classical.choose_spec (run.step_stateEdges_transition n)).2

noncomputable def realizedRunStateAt
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (root : A.State) :
    Node -> A.State := by
  classical
  exact
    fun
    | [] => root
    | child :: node =>
        let parent := realizedRunStateAt run root node
        if hmem : parent ∈ run.toMacroRun.states node.length then
          (((run.stepSupportChoice node.length).choice ⟨parent, hmem⟩).support.toList[child]?).getD
            A.initial
        else
          A.initial

def realizedRunActive
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (root : A.State) :
    Node -> Prop
  | [] => True
  | child :: node =>
      run.realizedRunActive root node ∧
        ∃ hmem :
          run.realizedRunStateAt root node ∈ run.toMacroRun.states node.length,
          ∃ childState : A.State,
            (((run.stepSupportChoice node.length).choice
              ⟨run.realizedRunStateAt root node, hmem⟩).support.toList[child]?) =
                some childState

@[simp]
theorem realizedRunStateAt_nil
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (root : A.State) :
    run.realizedRunStateAt root [] = root :=
  rfl

@[simp]
theorem realizedRunActive_nil
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (root : A.State) :
    run.realizedRunActive root [] :=
  trivial

theorem realizedRunStateAt_mem_states
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    {root : A.State}
    (hroot : root ∈ initialStates)
    {node : Node}
    (hactive : run.realizedRunActive root node) :
    run.realizedRunStateAt root node ∈ run.toMacroRun.states node.length := by
  induction node with
  | nil =>
      simpa [realizedRunStateAt, run.toMacroRun.initial_states] using hroot
  | cons child node ih =>
      rcases hactive with ⟨hparentActive, hchild⟩
      rcases hchild with ⟨hmem, childState, hchildSome⟩
      have hstate :
          run.realizedRunStateAt root (child :: node) = childState := by
        simp [realizedRunStateAt, hmem, hchildSome]
      have hchildMemList :
          childState ∈ ((run.stepSupportChoice node.length).choice
            ⟨run.realizedRunStateAt root node, hmem⟩).support.toList :=
        (PosBool.mem_iff_exists_getElem?
          ((run.stepSupportChoice node.length).choice
            ⟨run.realizedRunStateAt root node, hmem⟩).support.toList
          childState).mpr ⟨child, hchildSome⟩
      have hchildMemSupport :
          childState ∈ ((run.stepSupportChoice node.length).choice
            ⟨run.realizedRunStateAt root node, hmem⟩).support := by
        simpa using hchildMemList
      have hchildMemMacro :
          childState ∈ (run.stepSupportChoice node.length).support :=
        (MacroStepSupport.mem_support
          (supportChoice := run.stepSupportChoice node.length)
          (nextState := childState)).mpr
          ⟨⟨run.realizedRunStateAt root node, hmem⟩, hchildMemSupport⟩
      have hnext :
          childState ∈ run.toMacroRun.states (node.length + 1) := by
        simpa [run.stepSupportChoice_support node.length] using hchildMemMacro
      simpa [hstate] using hnext

theorem realizedRun_edge_mem_stateEdges
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    {root : A.State}
    {node : Node}
    {child : Nat}
    (hactive : run.realizedRunActive root (child :: node)) :
    (run.realizedRunStateAt root node,
      run.realizedRunStateAt root (child :: node)) ∈
        run.stateEdges node.length := by
  rcases hactive with ⟨_hparentActive, hchild⟩
  rcases hchild with ⟨hmem, childState, hchildSome⟩
  have hstate :
      run.realizedRunStateAt root (child :: node) = childState := by
    simp [realizedRunStateAt, hmem, hchildSome]
  have hchildMemList :
      childState ∈ ((run.stepSupportChoice node.length).choice
        ⟨run.realizedRunStateAt root node, hmem⟩).support.toList :=
    (PosBool.mem_iff_exists_getElem?
      ((run.stepSupportChoice node.length).choice
        ⟨run.realizedRunStateAt root node, hmem⟩).support.toList
      childState).mpr ⟨child, hchildSome⟩
  have hchildMemSupport :
      childState ∈ ((run.stepSupportChoice node.length).choice
        ⟨run.realizedRunStateAt root node, hmem⟩).support := by
    simpa using hchildMemList
  have hedge :
      (run.realizedRunStateAt root node, childState) ∈
        (run.stepSupportChoice node.length).stateEdges :=
    (MacroStepSupport.mem_stateEdges
      (supportChoice := run.stepSupportChoice node.length)
      (edge := (run.realizedRunStateAt root node, childState))).mpr
      ⟨⟨run.realizedRunStateAt root node, hmem⟩, rfl, hchildMemSupport⟩
  simpa [run.stepSupportChoice_stateEdges node.length, hstate] using hedge

noncomputable def realizedRunTree
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (root : A.State)
    (hroot : root ∈ initialStates) :
    (A.withInitial root).Run word where
  active := run.realizedRunActive root
  stateAt := run.realizedRunStateAt root
  root_active := by simp
  root_state := by simp [AlternatingParityAutomaton.withInitial]
  step_satisfied := by
    classical
    intro node hnode
    have hmem :
        run.realizedRunStateAt root node ∈ run.toMacroRun.states node.length :=
      run.realizedRunStateAt_mem_states hroot hnode
    have hstep :
        PosBool.Eval
          (fun nextState =>
            nextState ∈ ((run.stepSupportChoice node.length).choice
              ⟨run.realizedRunStateAt root node, hmem⟩).support)
          (A.step (run.realizedRunStateAt root node) (word node.length)) :=
      ((run.stepSupportChoice node.length).choice
        ⟨run.realizedRunStateAt root node, hmem⟩).support_satisfies
    change
      PosBool.Eval
        (fun nextState =>
          ∃ child : Nat,
            run.realizedRunActive root (child :: node) ∧
              run.realizedRunStateAt root (child :: node) = nextState)
        (A.step (run.realizedRunStateAt root node) (word node.length))
    refine
      PosBool.eval_mono
        ?_
        (A.step (run.realizedRunStateAt root node) (word node.length))
        hstep
    intro nextState hnext
    have hnextList :
        nextState ∈ ((run.stepSupportChoice node.length).choice
          ⟨run.realizedRunStateAt root node, hmem⟩).support.toList := by
      simpa using hnext
    rcases
      (PosBool.mem_iff_exists_getElem?
        ((run.stepSupportChoice node.length).choice
          ⟨run.realizedRunStateAt root node, hmem⟩).support.toList
        nextState).mp hnextList with
      ⟨child, hchildSome⟩
    refine ⟨child, ?_, ?_⟩
    · exact ⟨hnode, hmem, nextState, hchildSome⟩
    · simp [realizedRunStateAt, hmem, hchildSome]

theorem realizedRunTree_branch_supportPath
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    {root : A.State}
    (hroot : root ∈ initialStates)
    (branch : Nat -> Nat)
    (hbranch : (run.realizedRunTree root hroot).ActiveBranch branch) :
    run.SupportPath
      (fun n => (run.realizedRunTree root hroot).stateAt (branchPrefix branch n)) := by
  constructor
  · simpa [realizedRunTree, realizedRunStateAt] using hroot
  · intro n
    have hactive :
        run.realizedRunActive root
          (branch n :: branchPrefix branch n) := by
      simpa [realizedRunTree, branchPrefix] using hbranch (n + 1)
    have hedge :=
      run.realizedRun_edge_mem_stateEdges hactive
    simpa [realizedRunTree, branchPrefix] using hedge

theorem hasRunTreeRealization
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word) :
    run.HasRunTreeRealization := by
  intro root hroot
  exact
    ⟨run.realizedRunTree root hroot,
      fun branch hbranch =>
        run.realizedRunTree_branch_supportPath hroot branch hbranch⟩

/--
After some finite point, every explicitly chosen state edge belongs to the
edge-witnessed macro-run's recurring explicit edge set.
-/
theorem eventually_stateEdges_subset_infStateEdgeFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word) :
    ∃ base : Nat,
      ∀ n : Nat, base ≤ n ->
        run.stateEdges n ⊆ run.infStateEdgeFinset := by
  classical
  let nonrecurring : Finset (APAStateEdge A) :=
    Finset.univ.filter (fun edge => ¬ run.StateEdgeSeenInfinitelyOften edge)
  have hnotSeenBound :
      ∀ edge ∈ nonrecurring,
        ∃ bound : Nat,
          ∀ k : Nat, bound ≤ k -> edge ∉ run.stateEdges k := by
    intro edge hedge
    have hnot : ¬ run.StateEdgeSeenInfinitelyOften edge :=
      (Finset.mem_filter.mp hedge).2
    rw [StateEdgeSeenInfinitelyOften] at hnot
    push Not at hnot
    exact hnot
  choose bound hbound using hnotSeenBound
  let boundOf : APAStateEdge A -> Nat := fun edge =>
    if hedge : edge ∈ nonrecurring then bound edge hedge else 0
  refine ⟨nonrecurring.sup boundOf, ?_⟩
  intro n hn edge hedge
  by_contra hedgeInf
  have hedgeNonrecurring : edge ∈ nonrecurring := by
    rw [Finset.mem_filter]
    constructor
    · simp
    · intro hseen
      exact hedgeInf ((run.mem_infStateEdgeFinset edge).mpr hseen)
  have hle : boundOf edge ≤ nonrecurring.sup boundOf :=
    Finset.le_sup hedgeNonrecurring
  have hboundOf : boundOf edge = bound edge hedgeNonrecurring := by
    simp [boundOf, hedgeNonrecurring]
  exact hbound edge hedgeNonrecurring n
    (by
      rw [← hboundOf]
      exact le_trans hle hn)
    hedge

theorem SupportPath.eventually_edge_recurring
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {run : A.EdgeWitnessedMacroRun initialStates word}
    {path : Nat -> A.State}
    (hpath : run.SupportPath path) :
    ∃ base : Nat,
      ∀ n : Nat, base ≤ n ->
        (path n, path (n + 1)) ∈ run.infStateEdgeFinset := by
  rcases run.eventually_stateEdges_subset_infStateEdgeFinset with ⟨base, hbase⟩
  exact ⟨base, fun n hn => hbase n hn (hpath.2 n)⟩

end AlternatingParityAutomaton.EdgeWitnessedMacroRun

/--
The realized-level macro-run of a concrete APA run tree, equipped with the
actual per-step state-edge witnesses extracted from active parent/child edges.
-/
noncomputable def AlternatingParityAutomaton.Run.realizedEdgeWitnessedMacroRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word) :
    A.EdgeWitnessedMacroRun {A.initial} word where
  toMacroRun := run.realizedLevelMacroRun
  stateEdges n :=
    Classical.choose (run.realizedLevelMacroState_transitionWithStateEdges n)
  step_stateEdges_transition := by
    intro n
    exact
      (Classical.choose_spec
        (run.realizedLevelMacroState_transitionWithStateEdges n)).1

theorem AlternatingParityAutomaton.Run.realizedEdgeWitnessedMacroRun_stateEdges_realized
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (n : Nat)
    {edge : APAStateEdge A}
    (hedge : edge ∈ run.realizedEdgeWitnessedMacroRun.stateEdges n) :
    run.StateEdgeRealizedAtLevel n edge :=
  (Classical.choose_spec
    (run.realizedLevelMacroState_transitionWithStateEdges n)).2 edge hedge

/-- A coherent infinite path through the support choices of a macro-run. -/
def AlternatingParityAutomaton.MacroRun.SupportPath
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (path : Nat -> A.State) :
    Prop :=
  path 0 ∈ initialStates ∧
    ∀ n : Nat, (path n, path (n + 1)) ∈ run.stepStateEdges n

theorem AlternatingParityAutomaton.MacroRun.SupportPath.state_mem
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {run : A.MacroRun initialStates word}
    {path : Nat -> A.State}
    (hpath : run.SupportPath path)
    (n : Nat) :
    path n ∈ run.states n := by
  induction n with
  | zero =>
      simpa [run.initial_states] using hpath.1
  | succ n ih =>
      exact run.stepStateEdges_target_mem n (hpath.2 n)

/--
If every macro-state of a macro-run consists of APA states accepting the
corresponding suffix, then every concrete support path through that macro-run
also consists of accepting suffix states.
-/
theorem AlternatingParityAutomaton.MacroRun.SupportPath.acceptsFrom_at
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {run : A.MacroRun initialStates word}
    {path : Nat -> A.State}
    (hpath : run.SupportPath path)
    (haccepts :
      ∀ n : Nat,
        ∀ state, state ∈ run.states n ->
          A.AcceptsFrom state (OmegaWord.drop word n)) :
    ∀ n : Nat,
      A.AcceptsFrom (path n) (OmegaWord.drop word n) := by
  intro n
  exact haccepts n (path n) (hpath.state_mem n)

/--
The canonical macro-run generated from APA acceptance carries accepting suffix
states along every concrete support path.  This is the local invariant needed
for the remaining branch-splicing proof from APA acceptance to the
support-witness Muller condition.
-/
theorem AlternatingParityAutomaton.acceptingMacroRunFromAccepts_supportPath_acceptsFrom
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (haccepts :
      ∀ state, state ∈ initialStates -> A.AcceptsFrom state word)
    {path : Nat -> A.State}
    (hpath :
      (A.acceptingMacroRunFromAccepts initialStates word haccepts).SupportPath
        path) :
    ∀ n : Nat,
      A.AcceptsFrom (path n) (OmegaWord.drop word n) := by
  exact hpath.acceptsFrom_at
    (fun n state hstate =>
      A.acceptingMacroRunFromAccepts_accepts_all_at
        initialStates word haccepts n state hstate)

theorem AlternatingParityAutomaton.MacroRun.SupportPath.edge_source_mem
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {run : A.MacroRun initialStates word}
    {path : Nat -> A.State}
    (hpath : run.SupportPath path)
    (n : Nat) :
    path n ∈ run.states n :=
  hpath.state_mem n

/-- The finite prefix of an infinite macro-run. -/
def AlternatingParityAutomaton.MacroRun.prefix
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (length : Nat) :
    A.MacroRunPrefix initialStates word length where
  states := run.states
  initial_states := run.initial_states
  step_transition := by
    intro n _hn
    exact run.step_transition n

@[simp]
theorem AlternatingParityAutomaton.MacroRun.prefix_states
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (length n : Nat) :
    (run.prefix length).states n = run.states n :=
  rfl

/-- An individual APA support edge occurs infinitely often along a macro-run. -/
def AlternatingParityAutomaton.MacroRun.StateEdgeSeenInfinitelyOften
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (edge : APAStateEdge A) :
    Prop :=
  ∀ n : Nat,
    ∃ k : Nat,
      n ≤ k ∧ edge ∈ run.stepStateEdges k

/-- The finite set of individual support edges seen infinitely often on a macro-run. -/
noncomputable def AlternatingParityAutomaton.MacroRun.infStateEdgeFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    Finset (APAStateEdge A) := by
  classical
  exact Finset.univ.filter (fun edge => run.StateEdgeSeenInfinitelyOften edge)

@[simp]
theorem AlternatingParityAutomaton.MacroRun.mem_infStateEdgeFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (edge : APAStateEdge A) :
    edge ∈ run.infStateEdgeFinset ↔ run.StateEdgeSeenInfinitelyOften edge := by
  classical
  simp [MacroRun.infStateEdgeFinset]

theorem AlternatingParityAutomaton.MacroRun.eventually_stepStateEdges_subset_infStateEdgeFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    ∃ base : Nat,
      ∀ n : Nat, base ≤ n ->
        run.stepStateEdges n ⊆ run.infStateEdgeFinset := by
  classical
  let nonrecurring : Finset (APAStateEdge A) :=
    Finset.univ.filter (fun edge => ¬ run.StateEdgeSeenInfinitelyOften edge)
  have hnotSeenBound :
      ∀ edge ∈ nonrecurring,
        ∃ bound : Nat,
          ∀ k : Nat, bound ≤ k -> edge ∉ run.stepStateEdges k := by
    intro edge hedge
    have hnot : ¬ run.StateEdgeSeenInfinitelyOften edge :=
      (Finset.mem_filter.mp hedge).2
    rw [MacroRun.StateEdgeSeenInfinitelyOften] at hnot
    push Not at hnot
    exact hnot
  choose bound hbound using hnotSeenBound
  let boundOf : APAStateEdge A -> Nat := fun edge =>
    if hedge : edge ∈ nonrecurring then bound edge hedge else 0
  refine ⟨nonrecurring.sup boundOf, ?_⟩
  intro n hn edge hedge
  by_contra hedgeInf
  have hedgeNonrecurring : edge ∈ nonrecurring := by
    rw [Finset.mem_filter]
    constructor
    · simp
    · exact (by
        intro hseen
        exact hedgeInf ((run.mem_infStateEdgeFinset edge).mpr hseen))
  have hle : boundOf edge ≤ nonrecurring.sup boundOf :=
    Finset.le_sup hedgeNonrecurring
  have hboundOf : boundOf edge = bound edge hedgeNonrecurring := by
    simp [boundOf, hedgeNonrecurring]
  exact hbound edge hedgeNonrecurring n
    (by
      rw [← hboundOf]
      exact le_trans hle hn)
    hedge

theorem AlternatingParityAutomaton.MacroRun.SupportPath.eventually_edge_recurring
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {run : A.MacroRun initialStates word}
    {path : Nat -> A.State}
    (hpath : run.SupportPath path) :
    ∃ base : Nat,
      ∀ n : Nat, base ≤ n ->
        (path n, path (n + 1)) ∈ run.infStateEdgeFinset := by
  rcases run.eventually_stepStateEdges_subset_infStateEdgeFinset with ⟨base, hbase⟩
  exact ⟨base, fun n hn => hbase n hn (hpath.2 n)⟩

/--
A macro-run is support-accepting if every infinite path through its concrete
chosen support edges satisfies the parity condition.
-/
def AlternatingParityAutomaton.MacroRun.SupportAccepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    Prop :=
  ∀ path : Nat -> A.State,
    run.SupportPath path ->
      ∃ p : Nat,
        DetParityAutomaton.NatEven p ∧
          (∀ n : Nat, ∃ k : Nat, n ≤ k ∧ A.priority (path k) = p) ∧
            ∀ q : Nat,
              (∀ n : Nat, ∃ k : Nat, n ≤ k ∧ A.priority (path k) = q) ->
                p ≤ q

/--
A macro-run is realized by APA run trees when every initial macro-state has a
run tree whose active branches follow the macro-run's selected support edges.
-/
def AlternatingParityAutomaton.MacroRun.HasRunTreeRealization
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    Prop :=
  ∀ state, state ∈ initialStates ->
    ∃ runTree : (A.withInitial state).Run word,
      ∀ branch : Nat -> Nat,
        runTree.ActiveBranch branch ->
          run.SupportPath
            (fun n => runTree.stateAt (branchPrefix branch n))

/--
If a macro-run's selected support edges are parity accepting and realized by
actual APA run trees, then every initial macro-state accepts the word.
-/
theorem AlternatingParityAutomaton.MacroRun.acceptsFrom_all_initial_of_supportAccepting_realized
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (hsupport : run.SupportAccepting)
    (hrealized : run.HasRunTreeRealization) :
    ∀ state, state ∈ initialStates -> A.AcceptsFrom state word := by
  intro state hstate
  rcases hrealized state hstate with ⟨runTree, hbranches⟩
  refine ⟨runTree, ?_⟩
  intro branch hbranch
  have hpath :
      run.SupportPath
        (fun n => runTree.stateAt (branchPrefix branch n)) :=
    hbranches branch hbranch
  rcases hsupport
    (fun n => runTree.stateAt (branchPrefix branch n)) hpath with
    ⟨p, hpEven, hpSeen, hpMin⟩
  refine ⟨p, hpEven, ?_, ?_⟩
  · intro n
    rcases hpSeen n with ⟨k, hk, hkprio⟩
    exact ⟨k, hk, by simpa [AlternatingParityAutomaton.withInitial] using hkprio⟩
  · intro q hqSeen
    apply hpMin q
    intro n
    rcases hqSeen n with ⟨k, hk, hkprio⟩
    exact ⟨k, hk, by simpa [AlternatingParityAutomaton.withInitial] using hkprio⟩

/--
If an individual support edge recurs infinitely often on a macro-run, then some
recurring state of the support-edge deterministic skeleton contains it.
-/
theorem AlternatingParityAutomaton.exists_recurringSupportConfigurationState_of_macroRun_stateEdgeSeen
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    (run : A.MacroRun initialStates word)
    {edge : APAStateEdge A}
    (hseen : run.StateEdgeSeenInfinitelyOften edge) :
    ∃ configState :
        (A.supportConfigurationMullerSkeleton initialStates accepting).State,
      configState ∈
        (A.supportConfigurationMullerSkeleton initialStates accepting).infStateFinset word ∧
        edge ∈ configState.stateEdges := by
  classical
  let muller := A.supportConfigurationMullerSkeleton initialStates accepting
  let targets : Finset muller.State :=
    Finset.univ.filter (fun configState => edge ∈ configState.stateEdges)
  have hfreq :
      ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ muller.run word k ∈ targets := by
    intro n
    rcases hseen n with ⟨k, hk, hedge⟩
    refine ⟨k + 1, Nat.le_trans hk (Nat.le_succ k), ?_⟩
    rw [Finset.mem_filter]
    constructor
    · simp
    · have hedgeRun :
          edge ∈ A.macroConfigurationStateEdgeRun initialStates word k :=
        run.stateEdge_mem_macroConfigurationStateEdgeRun k hedge
      have hedges :
          (muller.run word (k + 1)).stateEdges =
            A.macroConfigurationStateEdgeRun initialStates word k := by
        exact A.supportConfigurationMullerSkeleton_run_stateEdges_succ
          initialStates accepting word k
      rw [hedges]
      exact hedgeRun
  rcases
    exists_seenInfinitelyOften_of_frequently_mem_finset_early
      (fun n => muller.run word n) targets hfreq with
    ⟨configState, htarget, hconfigSeen⟩
  refine ⟨configState, ?_, ?_⟩
  · exact
      (muller.mem_infStateFinset word configState).mpr
        (by
          intro n
          exact hconfigSeen n)
  · exact (Finset.mem_filter.mp htarget).2

/--
The individual APA support edges that occur in some recurring deterministic
support-configuration state.
-/
def AlternatingParityAutomaton.supportRecurringStateEdges
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (infStates : Set (APASupportConfigurationState A)) :
    Set (APAStateEdge A) :=
  { edge |
    ∃ configState : APASupportConfigurationState A,
      configState ∈ infStates ∧ edge ∈ configState.stateEdges }

/--
The APA macro-states that occur inside some recurring deterministic
support-configuration state.
-/
def AlternatingParityAutomaton.supportRecurringMacroStates
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (infStates : Set (APASupportConfigurationState A)) :
    Set (Finset A.State) :=
  { states |
    ∃ configState : APASupportConfigurationState A,
      configState ∈ infStates ∧ states ∈ configState.configs }

/--
The APA macro-transition edges that occur inside some recurring deterministic
support-configuration state.
-/
def AlternatingParityAutomaton.supportRecurringMacroEdges
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (infStates : Set (APASupportConfigurationState A)) :
    Set (APAMacroEdge A) :=
  { edge |
    ∃ configState : APASupportConfigurationState A,
      configState ∈ infStates ∧ edge ∈ configState.macroEdges }

/--
A macro-state recorded in a recurring support-configuration state is reachable
arbitrarily far along the deterministic macro-configuration run.
-/
theorem AlternatingParityAutomaton.supportRecurringMacroState_frequently_mem_macroConfigurationRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    {states : Finset A.State}
    (hstates :
      states ∈
        A.supportRecurringMacroStates
          ((A.supportConfigurationMullerSkeleton initialStates accepting).InfStates word)) :
    ∀ n : Nat,
      ∃ k : Nat,
        n ≤ k ∧ states ∈ A.macroConfigurationRun initialStates word k := by
  rcases hstates with ⟨configState, hconfigRecurring, hcontains⟩
  intro n
  let muller := A.supportConfigurationMullerSkeleton initialStates accepting
  have hseen : muller.StateSeenInfinitelyOften word configState := hconfigRecurring
  rcases hseen n with ⟨k, hk, hkconfig⟩
  refine ⟨k, hk, ?_⟩
  have hkconfigRun : muller.run word k = configState := hkconfig
  have hcontainsAtRun :
      states ∈ (muller.run word k).configs := by
    rw [hkconfigRun]
    exact hcontains
  have hconfigs :
      (muller.run word k).configs =
        A.macroConfigurationRun initialStates word k :=
    A.supportConfigurationMullerSkeleton_run_configs
      initialStates accepting word k
  simpa [hconfigs] using hcontainsAtRun

/--
A recurring support-carrier macro-state has arbitrarily late concrete
macro-run prefixes reaching it.
-/
theorem AlternatingParityAutomaton.supportRecurringMacroState_exists_macroRunPrefix_after
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    {states : Finset A.State}
    (hstates :
      states ∈
        A.supportRecurringMacroStates
          ((A.supportConfigurationMullerSkeleton initialStates accepting).InfStates word)) :
    ∀ n : Nat,
      ∃ k : Nat,
        ∃ pref : A.MacroRunPrefix initialStates word k,
          n ≤ k ∧ pref.states k = states := by
  intro n
  rcases
    A.supportRecurringMacroState_frequently_mem_macroConfigurationRun
      accepting hstates n with
    ⟨k, hk, hmem⟩
  rcases
    A.exists_macroRunPrefix_of_mem_macroConfigurationRun
      initialStates states word k hmem with
    ⟨pref, hpref⟩
  exact ⟨k, pref, hk, hpref⟩

/--
A macro-transition edge recorded in a recurring support-configuration state
appears arbitrarily far along the deterministic macro-edge run.
-/
theorem AlternatingParityAutomaton.supportRecurringMacroEdge_frequently_mem_macroConfigurationEdgeRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    {edge : APAMacroEdge A}
    (hedge :
      edge ∈
        A.supportRecurringMacroEdges
          ((A.supportConfigurationMullerSkeleton initialStates accepting).InfStates word)) :
    ∀ n : Nat,
      ∃ k : Nat,
        n ≤ k ∧ edge ∈ A.macroConfigurationEdgeRun initialStates word k := by
  rcases hedge with ⟨configState, hconfigRecurring, hedgeConfig⟩
  intro n
  let muller := A.supportConfigurationMullerSkeleton initialStates accepting
  have hseen : muller.StateSeenInfinitelyOften word configState := hconfigRecurring
  rcases hseen (n + 1) with ⟨k, hk, hkconfig⟩
  have hkpos : k ≠ 0 := by omega
  rcases Nat.exists_eq_succ_of_ne_zero hkpos with ⟨j, rfl⟩
  have hkconfigRun : muller.run word (j + 1) = configState := by
    simpa [Nat.succ_eq_add_one] using hkconfig
  refine ⟨j, ?_, ?_⟩
  · omega
  · have hedgeAtRun :
        edge ∈ (muller.run word (j + 1)).macroEdges := by
      rw [hkconfigRun]
      exact hedgeConfig
    have hedges :
        (muller.run word (j + 1)).macroEdges =
          A.macroConfigurationEdgeRun initialStates word j :=
      A.supportConfigurationMullerSkeleton_run_macroEdges_succ
        initialStates accepting word j
    rw [hedges] at hedgeAtRun
    exact hedgeAtRun

/--
A recurring support-carrier macro-edge has arbitrarily late concrete macro-run
prefixes whose last transition is that edge.
-/
theorem AlternatingParityAutomaton.supportRecurringMacroEdge_exists_macroRunPrefix_after
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    {edge : APAMacroEdge A}
    (hedge :
      edge ∈
        A.supportRecurringMacroEdges
          ((A.supportConfigurationMullerSkeleton initialStates accepting).InfStates word)) :
    ∀ n : Nat,
      ∃ k : Nat,
        ∃ pref : A.MacroRunPrefix initialStates word (k + 1),
          n ≤ k ∧ pref.states k = edge.1 ∧ pref.states (k + 1) = edge.2 := by
  intro n
  rcases
    A.supportRecurringMacroEdge_frequently_mem_macroConfigurationEdgeRun
      accepting hedge n with
    ⟨k, hk, hedgeRun⟩
  rcases
    A.exists_macroRunPrefix_of_mem_macroConfigurationEdgeRun
      initialStates word k edge hedgeRun with
    ⟨pref, hsource, htarget⟩
  exact ⟨k, pref, hk, hsource, htarget⟩

/--
An individual APA support edge recorded in a recurring support-configuration
state appears arbitrarily far along the deterministic support-edge run.
-/
theorem AlternatingParityAutomaton.supportRecurringStateEdge_frequently_mem_macroConfigurationStateEdgeRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    {edge : APAStateEdge A}
    (hedge :
      edge ∈
        A.supportRecurringStateEdges
          ((A.supportConfigurationMullerSkeleton initialStates accepting).InfStates word)) :
    ∀ n : Nat,
      ∃ k : Nat,
        n ≤ k ∧ edge ∈ A.macroConfigurationStateEdgeRun initialStates word k := by
  rcases hedge with ⟨configState, hconfigRecurring, hedgeConfig⟩
  intro n
  let muller := A.supportConfigurationMullerSkeleton initialStates accepting
  have hseen : muller.StateSeenInfinitelyOften word configState := hconfigRecurring
  rcases hseen (n + 1) with ⟨k, hk, hkconfig⟩
  have hkpos : k ≠ 0 := by omega
  rcases Nat.exists_eq_succ_of_ne_zero hkpos with ⟨j, rfl⟩
  have hkconfigRun : muller.run word (j + 1) = configState := by
    simpa [Nat.succ_eq_add_one] using hkconfig
  refine ⟨j, ?_, ?_⟩
  · omega
  · have hedgeAtRun :
        edge ∈ (muller.run word (j + 1)).stateEdges := by
      rw [hkconfigRun]
      exact hedgeConfig
    have hedges :
        (muller.run word (j + 1)).stateEdges =
          A.macroConfigurationStateEdgeRun initialStates word j :=
      A.supportConfigurationMullerSkeleton_run_stateEdges_succ
        initialStates accepting word j
    rw [hedges] at hedgeAtRun
    exact hedgeAtRun

/--
A recurring individual support edge has arbitrarily late concrete macro-run
prefixes whose last transition admits a support choice containing the edge.
-/
theorem AlternatingParityAutomaton.supportRecurringStateEdge_exists_macroRunPrefix_after
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    {edge : APAStateEdge A}
    (hedge :
      edge ∈
        A.supportRecurringStateEdges
          ((A.supportConfigurationMullerSkeleton initialStates accepting).InfStates word)) :
    ∀ n : Nat,
      ∃ k : Nat,
        ∃ sourceStates : Finset A.State,
          ∃ targetStates : Finset A.State,
            ∃ stateEdges : Finset (APAStateEdge A),
              ∃ pref : A.MacroRunPrefix initialStates word k,
                n ≤ k ∧
                  pref.states k = sourceStates ∧
                  A.MacroTransitionWithStateEdges
                    sourceStates (word k) targetStates stateEdges ∧
                  edge ∈ stateEdges := by
  intro n
  rcases
    A.supportRecurringStateEdge_frequently_mem_macroConfigurationStateEdgeRun
      accepting hedge n with
    ⟨k, hk, hedgeRun⟩
  rcases
    (A.mem_macroConfigurationStateEdgeRun
      initialStates word k edge).mp hedgeRun with
    ⟨sourceStates, hsource, targetStates, stateEdges, htransition, hedgeStateEdges⟩
  rcases
    A.exists_macroRunPrefix_of_mem_macroConfigurationRun
      initialStates sourceStates word k hsource with
    ⟨pref, hpref⟩
  exact
    ⟨k, sourceStates, targetStates, stateEdges, pref,
      hk, hpref, htransition, hedgeStateEdges⟩

/-- An infinite path follows the recurring support-edge graph. -/
def AlternatingParityAutomaton.SupportEdgePath
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (infStates : Set (APASupportConfigurationState A))
    (path : Nat -> A.State) :
    Prop :=
  ∀ n : Nat,
    (path n, path (n + 1)) ∈ A.supportRecurringStateEdges infStates

/-- Priority `p` is seen infinitely often along a support-edge path. -/
def AlternatingParityAutomaton.SupportEdgePathPrioritySeenInfinitelyOften
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (path : Nat -> A.State)
    (p : Nat) :
    Prop :=
  ∀ n : Nat,
    ∃ k : Nat,
      n ≤ k ∧ A.priority (path k) = p

theorem AlternatingParityAutomaton.supportEdgePathPrioritySeenInfinitelyOften_iff
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (path : Nat -> A.State)
    (p : Nat) :
    A.SupportEdgePathPrioritySeenInfinitelyOften path p ↔
      ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ A.priority (path k) = p := by
  rfl

theorem AlternatingParityAutomaton.supportEdgePathPrioritySeenInfinitelyOften_tail
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (path : Nat -> A.State)
    (base p : Nat) :
    A.SupportEdgePathPrioritySeenInfinitelyOften
        (fun n => path (base + n)) p ↔
      A.SupportEdgePathPrioritySeenInfinitelyOften path p := by
  constructor
  · intro htail n
    rcases htail n with ⟨k, hnk, hkprio⟩
    refine ⟨base + k, ?_, hkprio⟩
    omega
  · intro hfull n
    rcases hfull (base + n) with ⟨k, hk, hkprio⟩
    refine ⟨k - base, ?_, ?_⟩
    · omega
    · have hk_eq : base + (k - base) = k := by
        omega
      simpa [hk_eq] using hkprio

theorem AlternatingParityAutomaton.Run.prioritySeenInfinitelyOften_iff_supportPath
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat)
    (p : Nat) :
    run.PrioritySeenInfinitelyOften branch p ↔
      A.SupportEdgePathPrioritySeenInfinitelyOften
        (fun n => run.stateAt (branchPrefix branch n)) p := by
  rfl

theorem AlternatingParityAutomaton.Run.branchAccepts_of_supportPath_min_even
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat)
    (hmin :
      ∃ p : Nat,
        DetParityAutomaton.NatEven p ∧
          A.SupportEdgePathPrioritySeenInfinitelyOften
            (fun n => run.stateAt (branchPrefix branch n)) p ∧
            ∀ q : Nat,
              A.SupportEdgePathPrioritySeenInfinitelyOften
                (fun n => run.stateAt (branchPrefix branch n)) q -> p ≤ q) :
    run.BranchAccepts branch := by
  rcases hmin with ⟨p, hpEven, hpSeen, hpMin⟩
  refine ⟨p, hpEven, ?_, ?_⟩
  · exact
      (run.prioritySeenInfinitelyOften_iff_supportPath branch p).mpr hpSeen
  · intro q hq
    exact hpMin q
      ((run.prioritySeenInfinitelyOften_iff_supportPath branch q).mp hq)

/--
A run-tree branch realizes an abstract state path when it is active and has the
same APA state at every depth.
-/
def AlternatingParityAutomaton.Run.RealizesStatePath
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (path : Nat -> A.State)
    (branch : Nat -> Nat) :
    Prop :=
  run.ActiveBranch branch ∧
    ∀ n : Nat, run.stateAt (branchPrefix branch n) = path n

/--
Local child-extension form of branch coherence for an abstract state path.

This is weaker than asking for a branch explicitly: it only says that whenever
an active node already realizes the current path state, it has an active child
realizing the next path state.  The generic choice construction below turns this
local invariant into an actual infinite branch.
-/
def AlternatingParityAutomaton.Run.StatePathCoherentChildren
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (path : Nat -> A.State) :
    Prop :=
  run.stateAt [] = path 0 ∧
    ∀ node : Node,
      run.PathActive node ->
        run.stateAt node = path node.length ->
          ∃ child : Nat,
              run.active (child :: node) ∧
                run.stateAt (child :: node) = path (node.length + 1)

/--
Tail-local child-extension form for an abstract state path.

This is the recurrence-level analogue of `StatePathCoherentChildren`: the path
need only start at some active node of the run tree.  From every descendant of
that node that realizes the current path state, one active child realizes the
next path state.
-/
def AlternatingParityAutomaton.Run.StatePathTailCoherentChildren
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (path : Nat -> A.State) :
    Prop :=
  ∃ node : Node,
    run.PathActive node ∧
      ∃ hnode : run.active node,
        (run.subRun node hnode).StatePathCoherentChildren path

/--
The local child-coherence predicate depends only on the pointwise abstract
state path, not on the particular function used to name it.
-/
theorem AlternatingParityAutomaton.Run.StatePathCoherentChildren.congr_path
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {run : A.Run word}
    {path path' : Nat -> A.State}
    (hcoherent : run.StatePathCoherentChildren path)
    (heq : ∀ n : Nat, path n = path' n) :
    run.StatePathCoherentChildren path' := by
  constructor
  · exact hcoherent.1.trans (heq 0)
  · intro node hpathNode hnodeState
    have hnodeStateOld :
        run.stateAt node = path node.length :=
      hnodeState.trans (heq node.length).symm
    rcases hcoherent.2 node hpathNode hnodeStateOld with
      ⟨child, hchildActive, hchildState⟩
    exact ⟨child, hchildActive, hchildState.trans (heq (node.length + 1))⟩

/--
Tail-local child coherence is also extensional in the abstract state path.
This is useful after fixed-point arguments replace a path by an eventually
equal stabilized tail.
-/
theorem AlternatingParityAutomaton.Run.StatePathTailCoherentChildren.congr_path
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {run : A.Run word}
    {path path' : Nat -> A.State}
    (hcoherent : run.StatePathTailCoherentChildren path)
    (heq : ∀ n : Nat, path n = path' n) :
    run.StatePathTailCoherentChildren path' := by
  rcases hcoherent with ⟨node, hpathNode, hnode, hcoherentSub⟩
  exact
    ⟨node, hpathNode, hnode,
      hcoherentSub.congr_path heq⟩

/--
Concrete nested realization criterion for a tail state path.

The data gives an active base node, together with one active child extension
for every descendant suffix that has already followed the abstract path.  This
is often easier to prove from run-tree recurrence than the `subRun` formulation
directly.
-/
def AlternatingParityAutomaton.Run.StatePathThreadedTailRealization
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (path : Nat -> A.State) :
    Prop :=
  ∃ node : Node,
    run.PathActive node ∧
      ∃ hnode : run.active node,
        run.stateAt node = path 0 ∧
          ∀ suffix : Node,
            (run.subRun node hnode).PathActive suffix ->
              run.stateAt (suffix ++ node) = path suffix.length ->
                ∃ child : Nat,
                  run.active (child :: suffix ++ node) ∧
                    run.stateAt (child :: suffix ++ node) =
                      path (suffix.length + 1)

/--
Threaded tail realization is invariant under pointwise equality of the
abstract path.
-/
theorem AlternatingParityAutomaton.Run.StatePathThreadedTailRealization.congr_path
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {run : A.Run word}
    {path path' : Nat -> A.State}
    (hthreaded : run.StatePathThreadedTailRealization path)
    (heq : ∀ n : Nat, path n = path' n) :
    run.StatePathThreadedTailRealization path' := by
  rcases hthreaded with
    ⟨node, hpathNode, hnode, hnodeState, hstep⟩
  refine ⟨node, hpathNode, hnode, hnodeState.trans (heq 0), ?_⟩
  intro suffix hsuffixActive hsuffixState
  have hsuffixStateOld :
      run.stateAt (suffix ++ node) = path suffix.length :=
    hsuffixState.trans (heq suffix.length).symm
  rcases hstep suffix hsuffixActive hsuffixStateOld with
    ⟨child, hchildActive, hchildState⟩
  exact ⟨child, hchildActive, hchildState.trans (heq (suffix.length + 1))⟩

/--
Node-local realization of one state edge.

This is stronger than `StateEdgeRealizedAtLevel`: the realizing parent node is
fixed, which is exactly what is needed to thread a path through one branch.
-/
def AlternatingParityAutomaton.Run.StateEdgeRealizedFromNode
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (node : Node)
    (edge : APAStateEdge A) :
    Prop :=
  run.PathActive node ∧
    run.stateAt node = edge.1 ∧
      ∃ child : Nat,
        run.active (child :: node) ∧
          run.stateAt (child :: node) = edge.2

/--
The node-local edge realization immediately gives the level-local realization
predicate already used by the support-edge extraction.
-/
theorem AlternatingParityAutomaton.Run.stateEdgeRealizedAtLevel_of_fromNode
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    {node : Node}
    {edge : APAStateEdge A}
    (hrealized : run.StateEdgeRealizedFromNode node edge) :
    run.StateEdgeRealizedAtLevel node.length edge := by
  rcases hrealized with ⟨hpath, hsource, child, hchild, htarget⟩
  exact ⟨node, child, rfl, hpath, hsource, hchild, htarget⟩

/--
If every path-following suffix node realizes the next path edge locally, then
the whole path has a threaded tail realization.
-/
theorem AlternatingParityAutomaton.Run.statePathThreadedTailRealization_of_nodeLocalEdges
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    {path : Nat -> A.State}
    {node : Node}
    (hpathNode : run.PathActive node)
    (hnodeState : run.stateAt node = path 0)
    (hstep :
      ∀ suffix : Node,
        let hnode : run.active node := run.pathActive_self node hpathNode
        (run.subRun node hnode).PathActive suffix ->
          run.stateAt (suffix ++ node) = path suffix.length ->
            run.StateEdgeRealizedFromNode
              (suffix ++ node)
              (path suffix.length, path (suffix.length + 1))) :
    run.StatePathThreadedTailRealization path := by
  let hnode : run.active node := run.pathActive_self node hpathNode
  refine ⟨node, hpathNode, hnode, hnodeState, ?_⟩
  intro suffix hsuffixActive hsuffixState
  have hrealized :=
    hstep suffix hsuffixActive hsuffixState
  rcases hrealized with ⟨_hpath, _hsource, child, hchildActive, hchildState⟩
  exact ⟨child, hchildActive, hchildState⟩

/--
Path activity in a subtree lifts back to path activity of the corresponding
original run-tree node.
-/
theorem AlternatingParityAutomaton.Run.pathActive_append_of_subRun_pathActive
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    {node suffix : Node}
    (hpathNode : run.PathActive node)
    (hnode : run.active node)
    (hsuffix : (run.subRun node hnode).PathActive suffix) :
    run.PathActive (suffix ++ node) := by
  induction suffix with
  | nil =>
      simpa using hpathNode
  | cons child suffix ih =>
      have hsuffixTail :
          (run.subRun node hnode).PathActive suffix :=
        (run.subRun node hnode).pathActive_cons child suffix hsuffix
      have htail :
          run.PathActive (suffix ++ node) :=
        ih hsuffixTail
      have hchild :
          run.active (child :: (suffix ++ node)) := by
        have hself :
            (run.subRun node hnode).active (child :: suffix) :=
          (run.subRun node hnode).pathActive_self (child :: suffix) hsuffix
        simpa [List.cons_append] using hself
      exact htail.extend run (suffix ++ node) child hchild

/--
Path activity below a subtree root can also be read back from path activity of
the appended original node.
-/
theorem AlternatingParityAutomaton.Run.subRun_pathActive_of_pathActive_append
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    {node suffix : Node}
    (hnode : run.active node)
    (hpath : run.PathActive (suffix ++ node)) :
    (run.subRun node hnode).PathActive suffix := by
  intro pref tail htail
  change run.active (tail ++ node)
  exact hpath pref (tail ++ node) (by simpa [List.append_assoc] using congrArg (fun xs => xs ++ node) htail)

/--
Threaded tail realization is exactly the same as choosing a base active node
and proving node-local realization of each one-step edge along every
path-following suffix below that node.

This equivalence is the branch-sensitive replacement for reasoning only from
level-wise recurring edges.
-/
theorem AlternatingParityAutomaton.Run.statePathThreadedTailRealization_iff_nodeLocalEdges
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    {path : Nat -> A.State} :
    run.StatePathThreadedTailRealization path ↔
      ∃ node : Node,
        ∃ hpathNode : run.PathActive node,
          run.stateAt node = path 0 ∧
            ∀ (hnode' : run.active node) (suffix : Node),
              (run.subRun node hnode').PathActive suffix ->
                run.stateAt (suffix ++ node) = path suffix.length ->
                  run.StateEdgeRealizedFromNode
                    (suffix ++ node)
                    (path suffix.length, path (suffix.length + 1)) := by
  constructor
  · intro hthreaded
    rcases hthreaded with ⟨node, hpathNode, hnode, hnodeState, hstep⟩
    refine ⟨node, hpathNode, hnodeState, ?_⟩
    intro hnode' suffix hsuffixActive hsuffixState
    have hsuffixActiveMain :
        (run.subRun node hnode).PathActive suffix := by
      simpa [AlternatingParityAutomaton.Run.subRun_active] using hsuffixActive
    rcases hstep suffix hsuffixActiveMain hsuffixState with
      ⟨child, hchildActive, hchildState⟩
    refine ⟨?_, hsuffixState, child, hchildActive, hchildState⟩
    exact
      run.pathActive_append_of_subRun_pathActive hpathNode hnode
        hsuffixActive
  · intro hlocal
    rcases hlocal with ⟨node, hpathNode, hnodeState, hstep⟩
    exact
      run.statePathThreadedTailRealization_of_nodeLocalEdges
        hpathNode hnodeState
        (fun suffix hsuffixActive hsuffixState =>
          hstep (run.pathActive_self node hpathNode)
            suffix hsuffixActive hsuffixState)

/--
The threaded original-run formulation implies the subtree-local tail coherence
criterion used by the generic branch extraction theorem.
-/
theorem AlternatingParityAutomaton.Run.statePathTailCoherentChildren_of_threadedTailRealization
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    {path : Nat -> A.State}
  (hthreaded : run.StatePathThreadedTailRealization path) :
    run.StatePathTailCoherentChildren path := by
  classical
  rcases hthreaded with ⟨node, hpathNode, hnodeActive, hnodeState, hstep⟩
  refine ⟨node, hpathNode, hnodeActive, ?_⟩
  constructor
  · simpa [AlternatingParityAutomaton.Run.subRun_stateAt] using hnodeState
  · intro suffix hsuffixActive hsuffixState
    have hsuffixStateOriginal :
        run.stateAt (suffix ++ node) = path suffix.length := by
      simpa [AlternatingParityAutomaton.Run.subRun_stateAt] using hsuffixState
    rcases hstep suffix hsuffixActive hsuffixStateOriginal with
      ⟨child, hchildActive, hchildState⟩
    refine ⟨child, ?_, ?_⟩
    · simpa [AlternatingParityAutomaton.Run.subRun_active] using hchildActive
    · simpa [AlternatingParityAutomaton.Run.subRun_stateAt] using hchildState

/--
The subtree-local tail child-extension criterion also gives the threaded
original-run formulation.

This is the converse bridge to
`statePathTailCoherentChildren_of_threadedTailRealization`: once the coherent
children are stated in a subtree, each subtree child can be re-read as a
node-local original-run edge below the same base node.
-/
theorem AlternatingParityAutomaton.Run.statePathThreadedTailRealization_of_tailCoherentChildren
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    {path : Nat -> A.State}
    (hcoherent : run.StatePathTailCoherentChildren path) :
    run.StatePathThreadedTailRealization path := by
  rcases hcoherent with ⟨node, hpathNode, hnodeActive, hcoherentSub⟩
  refine ⟨node, hpathNode, hnodeActive, ?_, ?_⟩
  · simpa [AlternatingParityAutomaton.Run.subRun_stateAt] using hcoherentSub.1
  · intro suffix hsuffixActive hsuffixState
    have hsuffixStateSub :
        (run.subRun node hnodeActive).stateAt suffix = path suffix.length := by
      simpa [AlternatingParityAutomaton.Run.subRun_stateAt] using hsuffixState
    rcases hcoherentSub.2 suffix hsuffixActive hsuffixStateSub with
      ⟨child, hchildActiveSub, hchildStateSub⟩
    refine ⟨child, ?_, ?_⟩
    · simpa [AlternatingParityAutomaton.Run.subRun_active] using hchildActiveSub
    · simpa [AlternatingParityAutomaton.Run.subRun_stateAt] using hchildStateSub

/--
Node-local completeness of the recurring edge graph for one concrete run tree.

This is the exact strengthening missing from a purely level-wise recurrence
argument: every recurring APA state edge must be realizable below every active
occurrence of its source state, not only at some unrelated node on the same
level.
-/
def AlternatingParityAutomaton.Run.RecurringStateEdgesNodeLocalComplete
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word) :
    Prop :=
  ∀ edge : APAStateEdge A,
    edge ∈ run.realizedEdgeWitnessedMacroRun.infStateEdgeFinset ->
      ∀ node : Node,
        run.PathActive node ->
          run.stateAt node = edge.1 ->
            ∃ child : Nat,
              run.active (child :: node) ∧
                run.stateAt (child :: node) = edge.2

/--
An active run tree is atom-complete when every syntactic successor atom of an
active node is represented by some active child.

This is stronger than ordinary APA run-tree validity but is the natural shape
for saturated tableau runs: positive-Boolean monotonicity allows additional
children, and this property then turns timed atom membership into concrete
one-step child extension.
-/
def AlternatingParityAutomaton.Run.AtomComplete
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word) :
    Prop :=
  ∀ node : Node,
    run.PathActive node ->
      ∀ nextState : A.State,
        nextState ∈ (A.step (run.stateAt node) (word node.length)).atoms ->
          ∃ child : Nat,
            run.active (child :: node) ∧
              run.stateAt (child :: node) = nextState

/--
Atom-completeness proves node-local completeness once each recurring edge
target is known to be a timed successor atom at every active occurrence of its
source.
-/
theorem AlternatingParityAutomaton.Run.recurringStateEdgesNodeLocalComplete_of_atomComplete_and_recurringTargetAtoms
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (hatomComplete : run.AtomComplete)
    (hrecurringTargetAtoms :
      ∀ edge : APAStateEdge A,
        edge ∈ run.realizedEdgeWitnessedMacroRun.infStateEdgeFinset ->
          ∀ node : Node,
            run.PathActive node ->
              run.stateAt node = edge.1 ->
                edge.2 ∈
                  (A.step (run.stateAt node) (word node.length)).atoms) :
    run.RecurringStateEdgesNodeLocalComplete := by
  intro edge hedge node hpath hstate
  exact
    hatomComplete node hpath edge.2
      (hrecurringTargetAtoms edge hedge node hpath hstate)

/--
Atom-completeness plus timed atom membership gives subtree-local
child-extension for a path.

The timed atom hypothesis is deliberately level-aware: an untimed recurring
edge graph alone does not determine that a successor is available at the word
position of an arbitrary same-state occurrence.
-/
theorem AlternatingParityAutomaton.Run.statePathTailCoherentChildren_of_atomComplete_and_timedAtoms
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (hatomComplete : run.AtomComplete)
    {path : Nat -> A.State}
    {node : Node}
    (hpathNode : run.PathActive node)
    (hnodeState : run.stateAt node = path 0)
    (htimedAtoms :
      ∀ suffix : Node,
        (run.subRun node (run.pathActive_self node hpathNode)).PathActive suffix ->
          run.stateAt (suffix ++ node) = path suffix.length ->
            path (suffix.length + 1) ∈
              (A.step (path suffix.length) (word (suffix ++ node).length)).atoms) :
    run.StatePathTailCoherentChildren path := by
  let hnode : run.active node := run.pathActive_self node hpathNode
  refine ⟨node, hpathNode, hnode, ?_⟩
  constructor
  · simpa [AlternatingParityAutomaton.Run.subRun_stateAt] using hnodeState
  · intro suffix hsuffixActive hsuffixState
    have hsuffixPath :
        run.PathActive (suffix ++ node) :=
      run.pathActive_append_of_subRun_pathActive hpathNode hnode hsuffixActive
    have hsuffixStateOriginal :
        run.stateAt (suffix ++ node) = path suffix.length := by
      simpa [AlternatingParityAutomaton.Run.subRun_stateAt] using hsuffixState
    have hatomOriginal :
        path (suffix.length + 1) ∈
          (A.step (run.stateAt (suffix ++ node)) (word (suffix ++ node).length)).atoms := by
      simpa [hsuffixStateOriginal] using
        htimedAtoms suffix hsuffixActive hsuffixStateOriginal
    rcases
      hatomComplete (suffix ++ node) hsuffixPath
        (path (suffix.length + 1)) hatomOriginal with
      ⟨child, hchildActive, hchildState⟩
    refine ⟨child, ?_, ?_⟩
    · simpa [AlternatingParityAutomaton.Run.subRun_active] using hchildActive
    · simpa [AlternatingParityAutomaton.Run.subRun_stateAt] using hchildState

/--
Timed atom-extension support for one abstract state path.

It chooses an active occurrence of the path head and then requires that, below
that occurrence, the next abstract path state is an atom of the transition
formula at the actual word position of every matching subtree node.
-/
def AlternatingParityAutomaton.Run.StatePathTimedAtomTailSupport
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (path : Nat -> A.State) :
    Prop :=
  ∃ node : Node,
    run.PathActive node ∧
      run.stateAt node = path 0 ∧
        ∀ suffix : Node,
          run.PathActive (suffix ++ node) ->
            run.stateAt (suffix ++ node) = path suffix.length ->
              path (suffix.length + 1) ∈
                (A.step (path suffix.length) (word (suffix ++ node).length)).atoms

/--
Timed atom tail support is invariant under pointwise equality of the abstract
path.
-/
theorem AlternatingParityAutomaton.Run.StatePathTimedAtomTailSupport.congr_path
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {run : A.Run word}
    {path path' : Nat -> A.State}
    (htimed : run.StatePathTimedAtomTailSupport path)
    (heq : ∀ n : Nat, path n = path' n) :
    run.StatePathTimedAtomTailSupport path' := by
  rcases htimed with ⟨node, hpathNode, hnodeState, htimedAtoms⟩
  refine ⟨node, hpathNode, hnodeState.trans (heq 0), ?_⟩
  intro suffix hsuffixPath hsuffixState
  have hsuffixStateOld :
      run.stateAt (suffix ++ node) = path suffix.length :=
    hsuffixState.trans (heq suffix.length).symm
  have hatom := htimedAtoms suffix hsuffixPath hsuffixStateOld
  simpa [heq suffix.length, heq (suffix.length + 1)] using hatom

/--
A threaded tail realization whose concrete child steps are transition atoms
also gives the timed-atom tail-support criterion.
-/
theorem AlternatingParityAutomaton.Run.statePathTimedAtomTailSupport_of_threadedTailRealization
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    {path : Nat -> A.State}
    (hthreaded : run.StatePathThreadedTailRealization path)
    (hchildAtom :
      ∀ node : Node,
        ∀ child : Nat,
          run.PathActive node ->
            run.active (child :: node) ->
              run.stateAt (child :: node) ∈
                (A.step (run.stateAt node) (word node.length)).atoms) :
    run.StatePathTimedAtomTailSupport path := by
  rcases hthreaded with ⟨node, hpathNode, hnodeActive, hnodeState, hstep⟩
  refine ⟨node, hpathNode, hnodeState, ?_⟩
  intro suffix hsuffixPath hsuffixState
  have hsuffixSub :
      (run.subRun node hnodeActive).PathActive suffix :=
    run.subRun_pathActive_of_pathActive_append hnodeActive hsuffixPath
  rcases hstep suffix hsuffixSub hsuffixState with
    ⟨child, hchildActive, hchildState⟩
  have htarget :
      run.stateAt (child :: (suffix ++ node)) = path (suffix.length + 1) := by
    simpa [List.cons_append] using hchildState
  have hatom :=
    hchildAtom (suffix ++ node) child hsuffixPath hchildActive
  simpa [hsuffixState, htarget] using hatom

/--
The subtree-local tail-child-extension criterion gives timed-atom tail support
whenever the concrete run records every active child as a transition atom.
-/
theorem AlternatingParityAutomaton.Run.statePathTimedAtomTailSupport_of_tailCoherentChildren
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    {path : Nat -> A.State}
    (hcoherent : run.StatePathTailCoherentChildren path)
    (hchildAtom :
      ∀ node : Node,
        ∀ child : Nat,
          run.PathActive node ->
            run.active (child :: node) ->
              run.stateAt (child :: node) ∈
                (A.step (run.stateAt node) (word node.length)).atoms) :
    run.StatePathTimedAtomTailSupport path :=
  run.statePathTimedAtomTailSupport_of_threadedTailRealization
    (run.statePathThreadedTailRealization_of_tailCoherentChildren hcoherent)
    hchildAtom

/--
Atom-completeness turns timed atom-extension support into subtree-local
child-extension.
-/
theorem AlternatingParityAutomaton.Run.statePathTailCoherentChildren_of_atomComplete_and_timedAtomTailSupport
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (hatomComplete : run.AtomComplete)
    {path : Nat -> A.State}
    (htimed : run.StatePathTimedAtomTailSupport path) :
    run.StatePathTailCoherentChildren path := by
  rcases htimed with ⟨node, hpathNode, hnodeState, htimedAtoms⟩
  have hnode : run.active node := run.pathActive_self node hpathNode
  exact
    run.statePathTailCoherentChildren_of_atomComplete_and_timedAtoms
      hatomComplete hpathNode hnodeState
      (fun suffix hsuffixActive hsuffixState =>
        htimedAtoms suffix
          (run.pathActive_append_of_subRun_pathActive hpathNode hnode hsuffixActive)
          hsuffixState)

/--
If the recurring edge graph is node-locally complete, then every infinite path
through that graph satisfies the subtree-local child-extension criterion.
-/
theorem AlternatingParityAutomaton.Run.statePathTailCoherentChildren_of_recurringStateEdgesNodeLocalComplete
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (hlocal : run.RecurringStateEdgesNodeLocalComplete)
    {path : Nat -> A.State}
    (hpath :
      ∀ n : Nat,
        (path n, path (n + 1)) ∈
          run.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) :
    run.StatePathTailCoherentChildren path := by
  classical
  have hfirstSeen :
      run.realizedEdgeWitnessedMacroRun.StateEdgeSeenInfinitelyOften
        (path 0, path 1) := by
    exact
      (run.realizedEdgeWitnessedMacroRun.mem_infStateEdgeFinset
        (path 0, path 1)).mp (hpath 0)
  rcases hfirstSeen 0 with ⟨level, _hlevel, hedgeLevel⟩
  rcases
    run.realizedEdgeWitnessedMacroRun_stateEdges_realized
      level hedgeLevel with
    ⟨node, child, hnodeLength, hpathNode, hnodeState, hchildActive, hchildState⟩
  have hnodeActive : run.active node :=
    run.pathActive_self node hpathNode
  refine ⟨node, hpathNode, hnodeActive, ?_⟩
  constructor
  · simpa [AlternatingParityAutomaton.Run.subRun_stateAt] using hnodeState
  · intro suffix hsuffixActive hsuffixState
    have hsuffixPath :
        run.PathActive (suffix ++ node) :=
      run.pathActive_append_of_subRun_pathActive hpathNode hnodeActive
        hsuffixActive
    have hsuffixStateOriginal :
        run.stateAt (suffix ++ node) = path suffix.length := by
      simpa [AlternatingParityAutomaton.Run.subRun_stateAt] using hsuffixState
    rcases
      hlocal
        (path suffix.length, path (suffix.length + 1))
        (hpath suffix.length)
        (suffix ++ node)
        hsuffixPath
        hsuffixStateOriginal with
      ⟨nextChild, hnextActive, hnextState⟩
    refine ⟨nextChild, ?_, ?_⟩
    · simpa [AlternatingParityAutomaton.Run.subRun_active] using hnextActive
    · simpa [AlternatingParityAutomaton.Run.subRun_stateAt] using hnextState

/--
The generic branch-extraction step for branch-realizability.

After this lemma, the remaining APA completeness work can focus on the local
child-extension invariant rather than carrying an explicit infinite branch.
-/
theorem AlternatingParityAutomaton.Run.exists_realizingBranch_of_coherentChildren
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (path : Nat -> A.State)
    (hcoherent : run.StatePathCoherentChildren path) :
    ∃ branch : Nat -> Nat, run.RealizesStatePath path branch := by
  classical
  let P : Node -> Prop := fun node => run.stateAt node = path node.length
  have hroot : P [] := by
    simpa [P] using hcoherent.1
  have hstep :
      ∀ node : Node,
        run.PathActive node ->
          P node ->
            ∃ child : Nat, run.active (child :: node) ∧ P (child :: node) := by
    intro node hactive hP
    rcases hcoherent.2 node hactive hP with ⟨child, hchildActive, hchildState⟩
    refine ⟨child, hchildActive, ?_⟩
    simpa [P] using hchildState
  let branch := run.choicePathBranch P hroot hstep
  refine ⟨branch, ?_, ?_⟩
  · exact run.choicePathBranch_active P hroot hstep
  · intro n
    have hP : P (branchPrefix branch n) :=
      run.choicePathBranch_property P hroot hstep n
    simpa [P, branchPrefix_length] using hP

/--
The generic branch-extraction step for tail-realizability.

It turns a local child-extension invariant below some active node into an
actual branch whose suffix realizes the abstract path.
-/
theorem AlternatingParityAutomaton.Run.exists_tailRealizingBranch_of_tailCoherentChildren
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (path : Nat -> A.State)
    (hcoherent : run.StatePathTailCoherentChildren path) :
    ∃ branch : Nat -> Nat,
      ∃ offset : Nat,
        run.ActiveBranch branch ∧
          ∀ n : Nat,
            run.stateAt (branchPrefix branch (offset + n)) = path n := by
  classical
  rcases hcoherent with ⟨node, hpathNode, hnodeActive, hcoherentSub⟩
  let sub := run.subRun node hnodeActive
  rcases sub.exists_realizingBranch_of_coherentChildren path hcoherentSub with
    ⟨tailBranch, htailActive, htailState⟩
  let branch := branchPrependNode node tailBranch
  refine ⟨branch, node.length, ?_, ?_⟩
  · intro k
    by_cases hk : k ≤ node.length
    · exact run.active_branchPrependNode_prefix node tailBranch hpathNode k hk
    · have hlen : node.length ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hk)
      let j := k - node.length
      have hkEq : k = node.length + j := by
        exact (Nat.add_sub_of_le hlen).symm
      have htailActiveAt : sub.active (branchPrefix tailBranch j) :=
        htailActive j
      change run.active (branchPrefix branch k)
      rw [hkEq]
      rw [branchPrefix_prependNode]
      simpa [branch, sub, j] using htailActiveAt
  · intro n
    rw [branchPrefix_prependNode]
    simpa [branch, sub] using htailState n

/--
All infinite paths through the recurring support-edge graph satisfy the parity
condition.
-/
def AlternatingParityAutomaton.SupportRecurringStateEdgesAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (infStates : Set (APASupportConfigurationState A)) :
    Prop :=
  ∀ path : Nat -> A.State,
    A.SupportEdgePath infStates path ->
      ∃ p : Nat,
        DetParityAutomaton.NatEven p ∧
          A.SupportEdgePathPrioritySeenInfinitelyOften path p ∧
            ∀ q : Nat,
              A.SupportEdgePathPrioritySeenInfinitelyOften path q -> p ≤ q

/--
A finite state-edge graph satisfies the APA parity condition on all of its
infinite paths.
-/
def AlternatingParityAutomaton.SupportWitnessStateEdgesAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (stateEdges : Finset (APAStateEdge A)) :
    Prop :=
  ∀ path : Nat -> A.State,
    (∀ n : Nat, (path n, path (n + 1)) ∈ stateEdges) ->
      ∃ p : Nat,
        DetParityAutomaton.NatEven p ∧
          A.SupportEdgePathPrioritySeenInfinitelyOften path p ∧
            ∀ q : Nat,
              A.SupportEdgePathPrioritySeenInfinitelyOften path q -> p ≤ q

/--
The support-witness parity condition is monotone under taking subgraphs.

This is useful for pruned tableau witnesses: it is often easier to prove that
some finite support graph is accepting, then show that the recurring edges of
the concrete edge-witnessed macro-run are contained in that graph.
-/
theorem AlternatingParityAutomaton.SupportWitnessStateEdgesAccepting.mono
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {stateEdges acceptedEdges : Finset (APAStateEdge A)}
    (haccepting : A.SupportWitnessStateEdgesAccepting acceptedEdges)
    (hsubset : stateEdges ⊆ acceptedEdges) :
    A.SupportWitnessStateEdgesAccepting stateEdges := by
  intro path hpath
  exact haccepting path (fun n => hsubset (hpath n))

theorem AlternatingParityAutomaton.supportWitnessStateEdgesAccepting_of_subset
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {stateEdges acceptedEdges : Finset (APAStateEdge A)}
    (haccepting : A.SupportWitnessStateEdgesAccepting acceptedEdges)
    (hsubset : stateEdges ⊆ acceptedEdges) :
    A.SupportWitnessStateEdgesAccepting stateEdges :=
  haccepting.mono hsubset

/--
The APA state edges mentioned by a finite set of nondeterministic Muller states.

The concrete Muller automaton below stores a macro-state together with the
support edges used by the transition that reached it.  Its Muller condition
therefore evaluates the union of the recurring stored edge sets.
-/
noncomputable def AlternatingParityAutomaton.edgeWitnessedNondetMullerStateEdgeUnion
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (states : Finset (Finset A.State × Finset (APAStateEdge A))) :
    Finset (APAStateEdge A) := by
  classical
  exact states.biUnion (fun state => state.2)

/--
Nondeterministic Muller automaton whose runs are explicit APA macro-runs with
per-step support-edge witnesses.

The second component of a state records the support edges used by the previous
transition.  The initial dummy edge set is ignored by the Muller condition
because it appears only at time zero on runs built from edge-witnessed
macro-runs.
-/
noncomputable def AlternatingParityAutomaton.edgeWitnessedMacroRunMuller
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State) :
    NondetMullerAutomaton.{u, v} Alphabet where
  State := Finset A.State × Finset (APAStateEdge A)
  stateFinite := by
    classical
    infer_instance
  initial := (initialStates, ∅)
  step := fun source letter target =>
    A.MacroTransitionWithStateEdges source.1 letter target.1 target.2
  accepting :=
    { states |
      A.SupportWitnessStateEdgesAccepting
        (A.edgeWitnessedNondetMullerStateEdgeUnion states) }

theorem AlternatingParityAutomaton.edgeWitnessedMacroRunMuller_accepting_iff
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (states : Finset ((A.edgeWitnessedMacroRunMuller initialStates).State)) :
    states ∈ (A.edgeWitnessedMacroRunMuller initialStates).accepting ↔
      A.SupportWitnessStateEdgesAccepting
        (A.edgeWitnessedNondetMullerStateEdgeUnion states) := by
  rfl

/--
Every accepting edge-witnessed macro-run is accepted by the concrete
nondeterministic Muller macro-run automaton.
-/
theorem AlternatingParityAutomaton.edgeWitnessedMacroRunMuller_accepts_of_acceptingEdgeWitnessedMacroRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (haccepting : A.SupportWitnessStateEdgesAccepting run.infStateEdgeFinset) :
    (A.edgeWitnessedMacroRunMuller initialStates).Accepts word := by
  classical
  let muller := A.edgeWitnessedMacroRunMuller initialStates
  let path : Nat -> muller.State :=
    fun n =>
      match n with
      | 0 => (initialStates, ∅)
      | Nat.succ n => (run.toMacroRun.states (n + 1), run.stateEdges n)
  let ndRun : muller.RunFrom muller.initial word :=
    { path := path
      initial_state := rfl
      step_valid := by
        intro n
        cases n with
        | zero =>
            simpa [muller, path, AlternatingParityAutomaton.edgeWitnessedMacroRunMuller,
              run.toMacroRun.initial_states]
              using run.step_stateEdges_transition 0
        | succ n =>
            simpa [muller, path, AlternatingParityAutomaton.edgeWitnessedMacroRunMuller,
              Nat.add_assoc]
              using run.step_stateEdges_transition (n + 1) }
  refine ⟨ndRun, ?_⟩
  rw [NondetMullerAutomaton.RunFrom.Accepts]
  rw [A.edgeWitnessedMacroRunMuller_accepting_iff initialStates]
  refine haccepting.mono ?_
  intro edge hedge
  rw [AlternatingParityAutomaton.EdgeWitnessedMacroRun.mem_infStateEdgeFinset]
  intro n
  have hedgeUnion := hedge
  simp [AlternatingParityAutomaton.edgeWitnessedNondetMullerStateEdgeUnion]
    at hedgeUnion
  rcases hedgeUnion with ⟨macroState, edgeSet, hstateInf, hedgeState⟩
  let state : muller.State := (macroState, edgeSet)
  have hstateSeen :
      ndRun.StateSeenInfinitelyOften state :=
    (NondetMullerAutomaton.RunFrom.mem_infStateFinset ndRun).mp hstateInf
  rcases hstateSeen (n + 1) with ⟨k, hk, hpathk⟩
  cases k with
  | zero =>
      omega
  | succ k =>
      refine ⟨k, Nat.succ_le_succ_iff.mp hk, ?_⟩
      have hsecond : run.stateEdges k = edgeSet := by
        simpa [state, ndRun, path] using congrArg Prod.snd hpathk
      simpa [hsecond] using hedgeState

/--
Conversely, every accepting run of the concrete nondeterministic Muller
macro-run automaton extracts an accepting edge-witnessed APA macro-run.
-/
theorem AlternatingParityAutomaton.exists_acceptingEdgeWitnessedMacroRun_of_edgeWitnessedMacroRunMuller_accepts
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.edgeWitnessedMacroRunMuller initialStates).Accepts word) :
    ∃ run : A.EdgeWitnessedMacroRun initialStates word,
      A.SupportWitnessStateEdgesAccepting run.infStateEdgeFinset := by
  classical
  let muller := A.edgeWitnessedMacroRunMuller initialStates
  rcases haccepts with ⟨ndRun, hndAccepts⟩
  let run : A.EdgeWitnessedMacroRun initialStates word :=
    { toMacroRun :=
        { states := fun n => (ndRun.path n).1
          initial_states := by
            simpa [muller, AlternatingParityAutomaton.edgeWitnessedMacroRunMuller]
              using congrArg Prod.fst ndRun.initial_state
          step_transition := fun n =>
            (ndRun.step_valid n).to_macroTransition }
      stateEdges := fun n => (ndRun.path (n + 1)).2
      step_stateEdges_transition := fun n => ndRun.step_valid n }
  refine ⟨run, ?_⟩
  rw [NondetMullerAutomaton.RunFrom.Accepts] at hndAccepts
  rw [A.edgeWitnessedMacroRunMuller_accepting_iff initialStates] at hndAccepts
  refine hndAccepts.mono ?_
  intro edge hedge
  rw [AlternatingParityAutomaton.EdgeWitnessedMacroRun.mem_infStateEdgeFinset]
    at hedge
  let targets : Finset muller.State :=
    Finset.univ.filter (fun state => edge ∈ state.2)
  have hfreq :
      ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ ndRun.path k ∈ targets := by
    intro n
    rcases hedge n with ⟨k, hk, hedgek⟩
    refine ⟨k + 1, Nat.le_trans hk (Nat.le_succ k), ?_⟩
    simp [targets, run] at hedgek ⊢
    exact hedgek
  rcases
    exists_seenInfinitelyOften_of_frequently_mem_finset_early
      ndRun.path targets hfreq with
    ⟨state, hstateTarget, hstateSeen⟩
  have hstateInf : state ∈ ndRun.infStateFinset :=
    (NondetMullerAutomaton.RunFrom.mem_infStateFinset ndRun).mpr hstateSeen
  have hedgeState : edge ∈ state.2 := by
    simpa [targets] using (Finset.mem_filter.mp hstateTarget).2
  simp [AlternatingParityAutomaton.edgeWitnessedNondetMullerStateEdgeUnion]
  exact ⟨state.1, state.2, hstateInf, hedgeState⟩

/--
The concrete nondeterministic Muller macro-run automaton recognizes exactly
the existence of an accepting edge-witnessed APA macro-run.
-/
theorem AlternatingParityAutomaton.edgeWitnessedMacroRunMuller_accepts_iff_exists_acceptingEdgeWitnessedMacroRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet} :
    (A.edgeWitnessedMacroRunMuller initialStates).Accepts word ↔
      ∃ run : A.EdgeWitnessedMacroRun initialStates word,
        A.SupportWitnessStateEdgesAccepting run.infStateEdgeFinset := by
  constructor
  · exact
      A.exists_acceptingEdgeWitnessedMacroRun_of_edgeWitnessedMacroRunMuller_accepts
  · intro h
    rcases h with ⟨run, haccepting⟩
    exact
      A.edgeWitnessedMacroRunMuller_accepts_of_acceptingEdgeWitnessedMacroRun
        run haccepting

/--
Realizability of explicit macro-run support choices by actual APA run trees.

This is the remaining structural soundness obligation for the concrete
nondeterministic Muller macro-run automaton.  The Muller automaton guesses
finite support choices; this property says those choices can always be unfolded
into run trees for the initial macro-states.
-/
def AlternatingParityAutomaton.EdgeWitnessedMacroRunRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (initialStates : Finset A.State) (word : OmegaWord Alphabet)
    (run : A.EdgeWitnessedMacroRun initialStates word),
      run.HasRunTreeRealization

theorem AlternatingParityAutomaton.edgeWitnessedMacroRunRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    A.EdgeWitnessedMacroRunRealizable := by
  intro _initialStates _word run
  exact run.hasRunTreeRealization

/--
Upgrade a macro-run to an edge-witnessed macro-run using its canonical per-step
support-edge selector `MacroRun.stepStateEdges`.

Every macro-run already carries a classical choice of individual state edges for
each macro transition, so this is the trivial repackaging that exposes a plain
`MacroRun` at the `EdgeWitnessedMacroRun` interface.
-/
noncomputable def AlternatingParityAutomaton.MacroRun.toEdgeWitnessedMacroRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    A.EdgeWitnessedMacroRun initialStates word where
  toMacroRun := run
  stateEdges := run.stepStateEdges
  step_stateEdges_transition := run.stepStateEdges_transition

@[simp]
theorem AlternatingParityAutomaton.MacroRun.toEdgeWitnessedMacroRun_stateEdges
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (n : Nat) :
    run.toEdgeWitnessedMacroRun.stateEdges n = run.stepStateEdges n :=
  rfl

/--
If a macro-run is eventually confined to an accepting support graph, then it
witnesses an accepting edge-witnessed macro-run.

Once every per-step state-edge selection lands inside a finite `acceptedEdges`
that satisfies the support parity condition, the recurring state-edge finset of
the upgraded edge-witnessed macro-run is contained in `acceptedEdges`, and
monotonicity of `SupportWitnessStateEdgesAccepting` transfers acceptance.

This isolates the remaining APA-determinization-soundness obligation as a clean
automata statement: it suffices to realize the accepting recurrent support
witness as one coherent macro-run that is eventually confined to its accepting
state-edge graph.
-/
theorem AlternatingParityAutomaton.exists_accepting_edgeWitnessedMacroRun_of_eventually_confined_macroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    {acceptedEdges : Finset (APAStateEdge A)}
    (hAccepting : A.SupportWitnessStateEdgesAccepting acceptedEdges)
    {N : Nat}
    (hconfined : ∀ n, N ≤ n -> run.stepStateEdges n ⊆ acceptedEdges) :
    ∃ ewr : A.EdgeWitnessedMacroRun initialStates word,
      A.SupportWitnessStateEdgesAccepting ewr.infStateEdgeFinset := by
  classical
  refine ⟨run.toEdgeWitnessedMacroRun, hAccepting.mono ?_⟩
  intro edge hedge
  rw [AlternatingParityAutomaton.EdgeWitnessedMacroRun.mem_infStateEdgeFinset]
    at hedge
  rcases hedge N with ⟨k, hk, hedgek⟩
  exact hconfined k hk (by simpa using hedgek)

/--
Steering core for the determinization-soundness construction.

Given a step invariant `Good` together with the guarantee that every `Good`
macro-state can take a concrete macro transition under the current letter whose
individual support edges stay inside a fixed `acceptedEdges` graph and whose
target is again `Good`, dependent choice assembles one coherent edge-witnessed
macro-run all of whose recorded state edges lie in `acceptedEdges`.

This is the reusable engine for the recurrent-lasso argument: the caller only
has to exhibit a confined one-step extension property, not an entire run.
-/
theorem AlternatingParityAutomaton.exists_confined_edgeWitnessedMacroRun_of_steering
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {acceptedEdges : Finset (APAStateEdge A)}
    (Good : Nat -> Finset A.State -> Prop)
    (hinit : Good 0 initialStates)
    (hstep :
      ∀ n S, Good n S ->
        ∃ S' E,
          A.MacroTransitionWithStateEdges S (word n) S' E ∧
            E ⊆ acceptedEdges ∧ Good (n + 1) S') :
    ∃ ewr : A.EdgeWitnessedMacroRun initialStates word,
      ∀ n, ewr.stateEdges n ⊆ acceptedEdges := by
  classical
  -- For each `Good` macro-state, choose a confined one-step continuation.
  let pick : ∀ n (S : Finset A.State), Good n S ->
      { p : Finset A.State × Finset (APAStateEdge A) //
        A.MacroTransitionWithStateEdges S (word n) p.1 p.2 ∧
          p.2 ⊆ acceptedEdges ∧ Good (n + 1) p.1 } :=
    fun n S h =>
      ⟨(Classical.choose (hstep n S h),
          Classical.choose (Classical.choose_spec (hstep n S h))),
        Classical.choose_spec (Classical.choose_spec (hstep n S h))⟩
  -- The state/proof sequence built by dependent recursion.
  let seq : ∀ n, { S : Finset A.State // Good n S } :=
    fun n =>
      Nat.rec (motive := fun n => { S : Finset A.State // Good n S })
        ⟨initialStates, hinit⟩
        (fun n prev => ⟨(pick n prev.1 prev.2).1.1, (pick n prev.1 prev.2).2.2.2⟩)
        n
  refine
    ⟨{ toMacroRun :=
        { states := fun n => (seq n).1
          initial_states := rfl
          step_transition := fun n =>
            ((pick n (seq n).1 (seq n).2).2.1).to_macroTransition }
       stateEdges := fun n => (pick n (seq n).1 (seq n).2).1.2
       step_stateEdges_transition := fun n =>
         (pick n (seq n).1 (seq n).2).2.1 },
      ?_⟩
  intro n
  exact (pick n (seq n).1 (seq n).2).2.2.1

/--
The steering core combined with an accepting target graph: any confined steering
invariant yields an accepting edge-witnessed macro-run.
-/
theorem AlternatingParityAutomaton.exists_accepting_edgeWitnessedMacroRun_of_steering
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {acceptedEdges : Finset (APAStateEdge A)}
    (hAccepting : A.SupportWitnessStateEdgesAccepting acceptedEdges)
    (Good : Nat -> Finset A.State -> Prop)
    (hinit : Good 0 initialStates)
    (hstep :
      ∀ n S, Good n S ->
        ∃ S' E,
          A.MacroTransitionWithStateEdges S (word n) S' E ∧
            E ⊆ acceptedEdges ∧ Good (n + 1) S') :
    ∃ ewr : A.EdgeWitnessedMacroRun initialStates word,
      A.SupportWitnessStateEdgesAccepting ewr.infStateEdgeFinset := by
  classical
  obtain ⟨ewr, hconf⟩ :=
    A.exists_confined_edgeWitnessedMacroRun_of_steering Good hinit hstep
  refine ⟨ewr, hAccepting.mono ?_⟩
  intro edge hedge
  rw [AlternatingParityAutomaton.EdgeWitnessedMacroRun.mem_infStateEdgeFinset]
    at hedge
  rcases hedge 0 with ⟨k, _, hk⟩
  exact hconf k hk

/--
An accepting support graph cannot contain a path whose priority is eventually
constant at an odd value.

This is the generic parity fact used by LTL tableau pruning: once a support
path has stabilized in formula, the stable priority must be even.
-/
theorem AlternatingParityAutomaton.SupportWitnessStateEdgesAccepting.eventually_constant_priority_even
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {stateEdges : Finset (APAStateEdge A)}
    (haccepting : A.SupportWitnessStateEdgesAccepting stateEdges)
    {path : Nat -> A.State}
    (hpath : ∀ n : Nat, (path n, path (n + 1)) ∈ stateEdges)
    {N p : Nat}
    (hstable : ∀ n : Nat, N ≤ n -> A.priority (path n) = p) :
    DetParityAutomaton.NatEven p := by
  rcases haccepting path hpath with ⟨q, hqEven, hqSeen, _hqMin⟩
  rcases hqSeen N with ⟨k, hk, hkprio⟩
  have hq : q = p := by
    rw [← hkprio]
    exact hstable k hk
  rwa [← hq]

/--
A singleton self-loop whose state has even priority is an accepting support
graph.

This is the local endpoint needed by pruned fixed-point tableau witnesses after
an accepting temporal obligation has stabilized to one recurrent self-loop.
-/
theorem AlternatingParityAutomaton.supportWitnessStateEdgesAccepting_singleton_self
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (heven : DetParityAutomaton.NatEven (A.priority state)) :
    A.SupportWitnessStateEdgesAccepting ({(state, state)} : Finset (APAStateEdge A)) := by
  intro path hpath
  have hpath_zero : path 0 = state := by
    have hedge := hpath 0
    simpa using congrArg Prod.fst (Finset.mem_singleton.mp hedge)
  have hpath_const : ∀ n : Nat, path n = state := by
    intro n
    induction n with
    | zero => exact hpath_zero
    | succ n ih =>
        have hedge := hpath n
        have htarget : path (n + 1) = state := by
          simpa using congrArg Prod.snd (Finset.mem_singleton.mp hedge)
        exact htarget
  refine ⟨A.priority state, heven, ?_, ?_⟩
  · intro n
    exact ⟨n, Nat.le_refl n, by simp [hpath_const n]⟩
  · intro q hqSeen
    rcases hqSeen 0 with ⟨k, _hk, hkprio⟩
    have hq : q = A.priority state := by
      simpa [hpath_const k] using hkprio.symm
    rw [hq]

/--
If every infinite path through an explicit recurring edge graph is realized by
an active branch of an accepting run tree, then that finite edge graph satisfies
the support-witness parity condition.
-/
theorem AlternatingParityAutomaton.supportWitnessStateEdgesAccepting_of_branchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {word : OmegaWord Alphabet}
    (runTree : A.Run word)
    {stateEdges : Finset (APAStateEdge A)}
    (haccepting : runTree.Accepting)
    (hrealizable :
      ∀ path : Nat -> A.State,
        (∀ n : Nat, (path n, path (n + 1)) ∈ stateEdges) ->
          ∃ branch : Nat -> Nat, runTree.RealizesStatePath path branch) :
    A.SupportWitnessStateEdgesAccepting stateEdges := by
  intro path hpath
  rcases hrealizable path hpath with ⟨branch, hbranchActive, hstate⟩
  rcases haccepting branch hbranchActive with
    ⟨p, hpEven, hpSeen, hpMin⟩
  refine ⟨p, hpEven, ?_, ?_⟩
  · intro n
    rcases hpSeen n with ⟨k, hk, hkprio⟩
    refine ⟨k, hk, ?_⟩
    simpa [hstate k] using hkprio
  · intro q hqSeen
    apply hpMin q
    intro n
    rcases hqSeen n with ⟨k, hk, hkprio⟩
    refine ⟨k, hk, ?_⟩
    simpa [hstate k] using hkprio

/--
Tail-realization is enough for the support-witness parity condition.

This is the form usually needed for recurring edge graphs: an infinite path
through the recurring graph may correspond to a suffix of an accepting tree
branch rather than to the branch from depth zero.  Since parity acceptance only
depends on priorities seen infinitely often, dropping a finite prefix preserves
the minimum recurring priority.
-/
theorem AlternatingParityAutomaton.supportWitnessStateEdgesAccepting_of_tailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {word : OmegaWord Alphabet}
    (runTree : A.Run word)
    {stateEdges : Finset (APAStateEdge A)}
    (haccepting : runTree.Accepting)
    (hrealizable :
      ∀ path : Nat -> A.State,
        (∀ n : Nat, (path n, path (n + 1)) ∈ stateEdges) ->
          ∃ branch : Nat -> Nat,
            ∃ offset : Nat,
              runTree.ActiveBranch branch ∧
                ∀ n : Nat,
                  runTree.stateAt (branchPrefix branch (offset + n)) = path n) :
    A.SupportWitnessStateEdgesAccepting stateEdges := by
  intro path hpath
  rcases hrealizable path hpath with
    ⟨branch, offset, hbranchActive, hstate⟩
  rcases haccepting branch hbranchActive with
    ⟨p, hpEven, hpSeen, hpMin⟩
  refine ⟨p, hpEven, ?_, ?_⟩
  · intro n
    rcases hpSeen (offset + n) with ⟨k, hk, hkprio⟩
    have hoffset_le_k : offset ≤ k :=
      Nat.le_trans (Nat.le_add_right offset n) hk
    have hn_le_sub : n ≤ k - offset :=
      Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hk)
    refine ⟨k - offset, hn_le_sub, ?_⟩
    have hkdecomp : offset + (k - offset) = k :=
      Nat.add_sub_of_le hoffset_le_k
    have hstateAt :
        runTree.stateAt (branchPrefix branch k) = path (k - offset) := by
      simpa [hkdecomp] using hstate (k - offset)
    simpa [← hstateAt] using hkprio
  · intro q hqSeen
    apply hpMin q
    intro n
    rcases hqSeen n with ⟨k, hk, hkprio⟩
    refine ⟨offset + k, ?_, ?_⟩
    · exact Nat.le_trans hk (Nat.le_add_left k offset)
    · have hstateAt :
          runTree.stateAt (branchPrefix branch (offset + k)) = path k :=
        hstate k
      simpa [hstateAt] using hkprio

/--
Specialized sufficiency theorem for the realized edge-witnessed macro-run
extracted from a concrete APA run tree.
-/
theorem AlternatingParityAutomaton.Run.realizedEdgeWitnessedMacroRun_supportWitnessStateEdgesAccepting_of_branchRealizable
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (runTree : A.Run word)
    (haccepting : runTree.Accepting)
    (hrealizable :
      ∀ path : Nat -> A.State,
        (∀ n : Nat,
          (path n, path (n + 1)) ∈
            runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
          ∃ branch : Nat -> Nat, runTree.RealizesStatePath path branch) :
    A.SupportWitnessStateEdgesAccepting
      runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset :=
  A.supportWitnessStateEdgesAccepting_of_branchRealizable
    runTree haccepting hrealizable

/--
Tail-realization variant for the realized edge-witnessed macro-run extracted
from a concrete APA run tree.
-/
theorem AlternatingParityAutomaton.Run.realizedEdgeWitnessedMacroRun_supportWitnessStateEdgesAccepting_of_tailBranchRealizable
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (runTree : A.Run word)
    (haccepting : runTree.Accepting)
    (hrealizable :
      ∀ path : Nat -> A.State,
        (∀ n : Nat,
          (path n, path (n + 1)) ∈
            runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
          ∃ branch : Nat -> Nat,
            ∃ offset : Nat,
              runTree.ActiveBranch branch ∧
                ∀ n : Nat,
                  runTree.stateAt (branchPrefix branch (offset + n)) = path n) :
    A.SupportWitnessStateEdgesAccepting
      runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset :=
  A.supportWitnessStateEdgesAccepting_of_tailBranchRealizable
    runTree haccepting hrealizable


/--
The finite state-edge graph consisting exactly of all individual APA edges that
occur in recurring deterministic support configurations.
-/
noncomputable def AlternatingParityAutomaton.supportRecurringStateEdgeFinset
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (infStates : Set (APASupportConfigurationState A)) :
    Finset (APAStateEdge A) :=
  by
    classical
    exact
      (Finset.univ : Finset (APAStateEdge A)).filter
        (fun edge => edge ∈ A.supportRecurringStateEdges infStates)

theorem AlternatingParityAutomaton.mem_supportRecurringStateEdgeFinset
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (infStates : Set (APASupportConfigurationState A))
    (edge : APAStateEdge A) :
    edge ∈ A.supportRecurringStateEdgeFinset infStates ↔
      edge ∈ A.supportRecurringStateEdges infStates := by
  classical
  simp [supportRecurringStateEdgeFinset]

theorem AlternatingParityAutomaton.supportWitnessStateEdgesAccepting_of_supportRecurringStateEdgesAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {infStates : Set (APASupportConfigurationState A)}
    (haccepting : A.SupportRecurringStateEdgesAccepting infStates) :
    A.SupportWitnessStateEdgesAccepting
      (A.supportRecurringStateEdgeFinset infStates) := by
  intro path hpath
  exact haccepting path (fun n =>
      (A.mem_supportRecurringStateEdgeFinset
        infStates (path n, path (n + 1))).mp (hpath n))

/--
If the recurring explicit edge graph of an edge-witnessed macro-run is parity
accepting, then the edge-witnessed macro-run is support-accepting.
-/
theorem AlternatingParityAutomaton.EdgeWitnessedMacroRun.supportAccepting_of_infStateEdgeFinset_accepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (haccepting : A.SupportWitnessStateEdgesAccepting run.infStateEdgeFinset) :
    run.SupportAccepting := by
  intro path hpath
  rcases hpath.eventually_edge_recurring with ⟨base, hbase⟩
  let tailPath : Nat -> A.State := fun n => path (base + n)
  have htailEdges :
      ∀ n : Nat, (tailPath n, tailPath (n + 1)) ∈ run.infStateEdgeFinset := by
    intro n
    have hedge :
        (path (base + n), path (base + n + 1)) ∈ run.infStateEdgeFinset :=
      hbase (base + n) (Nat.le_add_right base n)
    simpa [tailPath, Nat.add_assoc] using hedge
  rcases haccepting tailPath htailEdges with
    ⟨p, hpEven, hpSeenTail, hpMinTail⟩
  refine ⟨p, hpEven, ?_, ?_⟩
  · exact
      (A.supportEdgePathPrioritySeenInfinitelyOften_tail path base p).mp
        hpSeenTail
  · intro q hqSeen
    exact hpMinTail q
      ((A.supportEdgePathPrioritySeenInfinitelyOften_tail path base q).mpr
        hqSeen)

/--
Subgraph form of `supportAccepting_of_infStateEdgeFinset_accepting`.

For pruned tableau witnesses it is often easier to prove that the recurring
edges of the selected macro-run are contained in a finite accepting support
graph.  Monotonicity then recovers acceptance of the exact recurring-edge
graph and hence support-acceptance of the edge-witnessed macro-run.
-/
theorem AlternatingParityAutomaton.EdgeWitnessedMacroRun.supportAccepting_of_subgraph_accepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    {acceptedEdges : Finset (APAStateEdge A)}
    (hsubset : run.infStateEdgeFinset ⊆ acceptedEdges)
    (haccepting : A.SupportWitnessStateEdgesAccepting acceptedEdges) :
    run.SupportAccepting :=
  run.supportAccepting_of_infStateEdgeFinset_accepting
    (A.supportWitnessStateEdgesAccepting_of_subset haccepting hsubset)

/--
If a selected edge-witnessed macro-run is realized by run trees and its
recurring edges are contained in an accepting finite support graph, then all
initial macro-states accept the word.

This is the generic correctness step that a pruned LTL tableau construction
needs after producing its finite accepting support graph.
-/
theorem AlternatingParityAutomaton.EdgeWitnessedMacroRun.acceptsFrom_all_initial_of_subgraph_accepting_realized
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    {acceptedEdges : Finset (APAStateEdge A)}
    (hsubset : run.infStateEdgeFinset ⊆ acceptedEdges)
    (haccepting : A.SupportWitnessStateEdgesAccepting acceptedEdges)
    (hrealized : run.HasRunTreeRealization) :
    ∀ state, state ∈ initialStates -> A.AcceptsFrom state word :=
  run.acceptsFrom_all_initial_of_supportAccepting_realized
    (run.supportAccepting_of_subgraph_accepting hsubset haccepting)
    hrealized

theorem AlternatingParityAutomaton.MacroRun.supportAccepting_of_infStateEdgeFinset_accepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (haccepting : A.SupportWitnessStateEdgesAccepting run.infStateEdgeFinset) :
    run.SupportAccepting := by
  intro path hpath
  rcases hpath.eventually_edge_recurring with ⟨base, hbase⟩
  let tailPath : Nat -> A.State := fun n => path (base + n)
  have htailEdges :
      ∀ n : Nat, (tailPath n, tailPath (n + 1)) ∈ run.infStateEdgeFinset := by
    intro n
    have hedge :
        (path (base + n), path (base + n + 1)) ∈ run.infStateEdgeFinset :=
      hbase (base + n) (Nat.le_add_right base n)
    simpa [tailPath, Nat.add_assoc] using hedge
  rcases haccepting tailPath htailEdges with
    ⟨p, hpEven, hpSeenTail, hpMinTail⟩
  refine ⟨p, hpEven, ?_, ?_⟩
  · exact
      (A.supportEdgePathPrioritySeenInfinitelyOften_tail path base p).mp
        hpSeenTail
  · intro q hqSeen
    exact hpMinTail q
      ((A.supportEdgePathPrioritySeenInfinitelyOften_tail path base q).mpr
        hqSeen)

/--
The intended existential recurrent witness over the deterministic support
carrier.  This is the finite accepting object needed for the APA existential
run-DAG semantics: choose recurring macro-states, recurring macro-edges, and
recurring individual state-edges, require the chosen macro graph to be closed,
and require the chosen state-edge graph to satisfy parity on all paths.
-/
def AlternatingParityAutomaton.SupportRecurrentWitness
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (infStates : Set (APASupportConfigurationState A)) :
    Prop :=
  ∃ macroStates : Finset (Finset A.State),
    ∃ macroEdges : Finset (APAMacroEdge A),
      ∃ stateEdges : Finset (APAStateEdge A),
        macroStates.Nonempty ∧
          (∀ states, states ∈ macroStates ->
            states ∈ A.supportRecurringMacroStates infStates) ∧
          (∀ edge, edge ∈ macroEdges ->
            edge ∈ A.supportRecurringMacroEdges infStates) ∧
          (∀ edge, edge ∈ stateEdges ->
            edge ∈ A.supportRecurringStateEdges infStates) ∧
          (∀ edge, edge ∈ macroEdges ->
            edge.1 ∈ macroStates ∧ edge.2 ∈ macroStates) ∧
          (∀ states, states ∈ macroStates ->
            ∃ edge, edge ∈ macroEdges ∧ edge.1 = states ∧ edge.2 ∈ macroStates) ∧
          (∀ edge, edge ∈ stateEdges ->
            (∃ sourceStates ∈ macroStates, edge.1 ∈ sourceStates) ∧
              ∃ targetStates ∈ macroStates, edge.2 ∈ targetStates) ∧
          A.SupportWitnessStateEdgesAccepting stateEdges

/-- The witness-based Muller accepting family intended to replace the provisional one. -/
def AlternatingParityAutomaton.supportWitnessAcceptingFamily
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Set (Set (APASupportConfigurationState A)) :=
  { infStates | A.SupportRecurrentWitness infStates }

/--
The deterministic Muller automaton using the existential recurrent-witness
accepting family.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMuller
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State) :
    DetMullerAutomaton.{u, v} Alphabet :=
  A.supportConfigurationMullerSkeleton
    initialStates
    A.supportWitnessAcceptingFamily

theorem AlternatingParityAutomaton.supportWitnessMuller_accepts_iff
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet) :
    (A.supportWitnessMuller initialStates).Accepts word ↔
      A.SupportRecurrentWitness
        ((A.supportWitnessMuller initialStates).InfStates word) := by
  rfl

/--
The remaining APA-determinization-soundness kernel, stated as a clean
automata-only property.

Every accepted support-witness Muller singleton must be realizable as one
coherent macro-run that is eventually confined to some accepting state-edge
graph.  This is the single open obligation isolated by
`exists_accepting_edgeWitnessedMacroRun_of_eventually_confined_macroRun`: it
hides no LTL content and no parity reasoning beyond
`SupportWitnessStateEdgesAccepting`.
-/
def AlternatingParityAutomaton.SupportWitnessConfinedMacroRunRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (initialStates : Finset A.State) (word : OmegaWord Alphabet),
    (A.supportWitnessMuller initialStates).Accepts word ->
      ∃ run : A.MacroRun initialStates word,
        ∃ acceptedEdges : Finset (APAStateEdge A),
          ∃ N : Nat,
            A.SupportWitnessStateEdgesAccepting acceptedEdges ∧
              ∀ n, N ≤ n -> run.stepStateEdges n ⊆ acceptedEdges

/--
The confined-macro-run kernel yields the accepting edge-witnessed macro-run for
every accepted support-witness Muller singleton.

This discharges the exact existential demanded by the canonical LTL soundness
handoff `subformulaClosure_supportWitnessMuller_prefixSatisfies_of_acceptingEdgeWitnessed`.
-/
theorem AlternatingParityAutomaton.exists_accepting_edgeWitnessedMacroRun_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hkernel : A.SupportWitnessConfinedMacroRunRealizable)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ ewr : A.EdgeWitnessedMacroRun initialStates word,
      A.SupportWitnessStateEdgesAccepting ewr.infStateEdgeFinset := by
  obtain ⟨run, acceptedEdges, N, hAccepting, hconfined⟩ :=
    hkernel initialStates word haccepts
  exact
    A.exists_accepting_edgeWitnessedMacroRun_of_eventually_confined_macroRun
      run hAccepting hconfined

theorem AlternatingParityAutomaton.supportWitnessMuller_acceptsFrom_runFrom_drop_iff
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (config : (A.supportWitnessMuller initialStates).State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (A.supportWitnessMuller initialStates).AcceptsFrom
        ((A.supportWitnessMuller initialStates).runFrom config word n)
        (OmegaWord.drop word n) ↔
      (A.supportWitnessMuller initialStates).AcceptsFrom config word := by
  exact
    DetMullerAutomaton.acceptsFrom_runFrom_drop_iff
      (A.supportWitnessMuller initialStates) config word n

theorem AlternatingParityAutomaton.supportWitnessMuller_acceptsFrom_run_drop_iff
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (A.supportWitnessMuller initialStates).AcceptsFrom
        ((A.supportWitnessMuller initialStates).run word n)
        (OmegaWord.drop word n) ↔
      (A.supportWitnessMuller initialStates).Accepts word := by
  exact
    DetMullerAutomaton.acceptsFrom_run_drop_iff
      (A.supportWitnessMuller initialStates) word n

theorem AlternatingParityAutomaton.supportWitnessMuller_run_configs
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((A.supportWitnessMuller initialStates).run word n).configs =
      A.macroConfigurationRun initialStates word n := by
  simpa [AlternatingParityAutomaton.supportWitnessMuller] using
    A.supportConfigurationMullerSkeleton_run_configs
      initialStates A.supportWitnessAcceptingFamily word n

theorem AlternatingParityAutomaton.supportWitnessMuller_acceptsFrom_run_drop_of_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word)
    (n : Nat) :
    (A.supportWitnessMuller initialStates).AcceptsFrom
        ((A.supportWitnessMuller initialStates).run word n)
        (OmegaWord.drop word n) := by
  exact
    (A.supportWitnessMuller_acceptsFrom_run_drop_iff
      initialStates word n).mpr haccepts

/--
Any concrete macro-configuration occurrence at time `n` is contained in the
current deterministic support-witness carrier state, and that carrier state
accepts the suffix whenever the original support-witness Muller run accepts.

This is a deterministic-side transport lemma: it does not claim that every
state in `states` is already semantically accepting.  The LTL soundness anchor
still has to prove that formula-level fact from the accepting recurrent
support data.
-/
theorem AlternatingParityAutomaton.exists_supportWitnessMuller_accepting_suffix_config_of_macroConfigurationRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates states : Finset A.State}
    {word : OmegaWord Alphabet}
    {n : Nat}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word)
    (hstates : states ∈ A.macroConfigurationRun initialStates word n) :
    ∃ config : (A.supportWitnessMuller initialStates).State,
      (A.supportWitnessMuller initialStates).AcceptsFrom
        config (OmegaWord.drop word n) ∧
        states ∈ config.configs := by
  refine
    ⟨(A.supportWitnessMuller initialStates).run word n, ?_, ?_⟩
  · exact
      A.supportWitnessMuller_acceptsFrom_run_drop_of_accepts haccepts n
  · simpa [A.supportWitnessMuller_run_configs initialStates word n] using hstates

/--
Accepting family for the state-wise support-witness Muller carrier.

The carrier below tags every support-configuration state with the APA state
whose singleton language it is tracking.  Acceptance says that, for every tag
that actually occurs in the recurrent set, the projected recurrent
support-configurations carry the usual support witness.
-/
def AlternatingParityAutomaton.stateSupportWitnessAcceptingFamily
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Set (Set (A.State × APASupportConfigurationState A)) :=
  { infStates |
    ∀ root config,
      (root, config) ∈ infStates ->
        A.SupportRecurrentWitness
          { config' | (root, config') ∈ infStates } }

/--
One deterministic Muller carrier for all APA singleton state languages.

The first component records which APA state is being tracked; the second
component is the support-configuration subset construction started from that
singleton.  This is the concrete state-wise carrier needed by
`APAToMullerStateCompilation`.
-/
noncomputable def AlternatingParityAutomaton.stateSupportWitnessMuller
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    DetMullerAutomaton.{u, v} Alphabet where
  State := A.State × APASupportConfigurationState A
  stateFinite := by
    classical
    exact inferInstance
  initial := (A.initial, APASupportConfigurationState.initial {A.initial})
  step := fun state letter =>
    (state.1, APASupportConfigurationState.step state.2 letter)
  accepting := A.stateSupportWitnessAcceptingFamily

theorem AlternatingParityAutomaton.stateSupportWitnessMuller_runFrom_fst
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (config : APASupportConfigurationState A)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((A.stateSupportWitnessMuller).runFrom (root, config) word n).1 = root := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (((A.stateSupportWitnessMuller).runFrom (root, config) word n).1,
          APASupportConfigurationState.step
            ((A.stateSupportWitnessMuller).runFrom (root, config) word n).2
            (word n)).1 = root
      exact ih

theorem AlternatingParityAutomaton.stateSupportWitnessMuller_runFrom_snd
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((A.stateSupportWitnessMuller).runFrom
        (root, APASupportConfigurationState.initial initialStates) word n).2 =
      ((A.supportWitnessMuller initialStates).run word n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (APASupportConfigurationState.step
          ((A.stateSupportWitnessMuller).runFrom
            (root, APASupportConfigurationState.initial initialStates) word n).2
          (word n)) =
          (A.supportWitnessMuller initialStates).step
            ((A.supportWitnessMuller initialStates).run word n)
            (word n)
      rw [ih]
      rfl

theorem AlternatingParityAutomaton.stateSupportWitnessMuller_runFrom_initial_singleton_snd
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((A.stateSupportWitnessMuller).runFrom
        (root, APASupportConfigurationState.initial {root}) word n).2 =
      ((A.supportWitnessMuller {root}).run word n) :=
  A.stateSupportWitnessMuller_runFrom_snd root {root} word n

theorem AlternatingParityAutomaton.stateSupportWitnessMuller_infStatesFrom_fst
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (config : APASupportConfigurationState A)
    (word : OmegaWord Alphabet)
    {q : A.State × APASupportConfigurationState A}
    (hq :
      q ∈
        (A.stateSupportWitnessMuller).InfStatesFrom
          (root, config) word) :
    q.1 = root := by
  rcases hq 0 with ⟨k, _hk, hkq⟩
  have hfst :=
    A.stateSupportWitnessMuller_runFrom_fst root config word k
  rw [hkq] at hfst
  exact hfst

theorem AlternatingParityAutomaton.stateSupportWitnessMuller_infStatesFrom_singleton_snd_iff
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (config : APASupportConfigurationState A) :
    config ∈ (A.supportWitnessMuller {root}).InfStates word ↔
      (root, config) ∈
        (A.stateSupportWitnessMuller).InfStatesFrom
          (root, APASupportConfigurationState.initial {root}) word := by
  constructor
  · intro hconfig n
    rcases hconfig n with ⟨k, hk, hrun⟩
    refine ⟨k, hk, ?_⟩
    apply Prod.ext
    · exact
        A.stateSupportWitnessMuller_runFrom_fst
          root (APASupportConfigurationState.initial {root}) word k
    · rw [A.stateSupportWitnessMuller_runFrom_initial_singleton_snd root word k]
      exact hrun
  · intro hconfig n
    rcases hconfig n with ⟨k, hk, hrun⟩
    refine ⟨k, hk, ?_⟩
    have hsnd := congrArg Prod.snd hrun
    rwa [A.stateSupportWitnessMuller_runFrom_initial_singleton_snd root word k] at hsnd

theorem AlternatingParityAutomaton.stateSupportWitnessMuller_acceptsFrom_singleton_iff
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet) :
    (A.stateSupportWitnessMuller).AcceptsFrom
        (root, APASupportConfigurationState.initial {root}) word ↔
      (A.supportWitnessMuller {root}).Accepts word := by
  constructor
  · intro haccepts
    have hfamily :
        (A.stateSupportWitnessMuller).InfStatesFrom
            (root, APASupportConfigurationState.initial {root}) word ∈
          A.stateSupportWitnessAcceptingFamily := haccepts
    have hsome :
        ∃ config : APASupportConfigurationState A,
          config ∈ (A.supportWitnessMuller {root}).InfStates word :=
      DetMullerAutomaton.exists_stateSeenInfinitelyOften
        (A.supportWitnessMuller {root}) word
    rcases hsome with ⟨config, hconfig⟩
    have hpair :
        (root, config) ∈
          (A.stateSupportWitnessMuller).InfStatesFrom
            (root, APASupportConfigurationState.initial {root}) word :=
      (A.stateSupportWitnessMuller_infStatesFrom_singleton_snd_iff
        root word config).mp hconfig
    have hset :
        { config' |
            (root, config') ∈
              (A.stateSupportWitnessMuller).InfStatesFrom
                (root, APASupportConfigurationState.initial {root}) word } =
          (A.supportWitnessMuller {root}).InfStates word := by
      ext config'
      exact
        (A.stateSupportWitnessMuller_infStatesFrom_singleton_snd_iff
          root word config').symm
    exact
      (A.supportWitnessMuller_accepts_iff {root} word).mpr
        (hset ▸ hfamily root config hpair)
  · intro haccepts
    have hwitness :
        A.SupportRecurrentWitness
          ((A.supportWitnessMuller {root}).InfStates word) :=
      (A.supportWitnessMuller_accepts_iff {root} word).mp haccepts
    intro otherRoot config hmem
    have hroot :
        otherRoot = root :=
      A.stateSupportWitnessMuller_infStatesFrom_fst
        root (APASupportConfigurationState.initial {root}) word hmem
    subst otherRoot
    have hset :
        { config' |
            (root, config') ∈
              (A.stateSupportWitnessMuller).InfStatesFrom
                (root, APASupportConfigurationState.initial {root}) word } =
          (A.supportWitnessMuller {root}).InfStates word := by
      ext config'
      exact
        (A.stateSupportWitnessMuller_infStatesFrom_singleton_snd_iff
          root word config').symm
    exact hset.symm ▸ hwitness

/--
Package the concrete support-witness Muller carrier as a state-wise
APA-to-Muller compilation once its singleton support-witness languages have
been identified with the supplied APA certificate language.

This isolates the remaining determinization theorem to the semantic equivalence
for `supportWitnessMuller {state}`; the state-tagged carrier and the state-wise
compiler interface are already handled here.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerStateCompilationOfCorrect
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (apaCert : A.LanguageCertificate)
    (hcorrect :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        (A.supportWitnessMuller {state}).Accepts word ↔
          word ∈ apaCert.language state) :
    APAToMullerStateCompilation.{u, v, v} A apaCert where
  muller := A.stateSupportWitnessMuller
  stateOf := fun state => (state, APASupportConfigurationState.initial {state})
  initial_state := rfl
  correctFrom := by
    intro state word
    trans (A.supportWitnessMuller {state}).Accepts word
    · exact A.stateSupportWitnessMuller_acceptsFrom_singleton_iff state word
    · exact hcorrect state word

/--
Run-semantics specialization of
`supportWitnessMullerStateCompilationOfCorrect`: it is enough to prove the
singleton support-witness Muller automaton recognizes `AcceptsFrom` for every
APA state.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfCorrect
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hcorrect :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        (A.supportWitnessMuller {state}).Accepts word ↔
          A.AcceptsFrom state word) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerStateCompilationOfCorrect
    cert.toLanguageCertificate
    (by
      intro state word
      trans A.AcceptsFrom state word
      · exact hcorrect state word
      · exact cert.acceptsFrom_iff state word)

/--
The same support-witness backend, composed with the proved LAR
Muller-to-DPA construction.  After the singleton support-witness semantic
equivalence is proved, this is the concrete `APAToDPAStateCompilation` needed
by the full LTL backend.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfCorrect
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hcorrect :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        (A.supportWitnessMuller {state}).Accepts word ↔
          A.AcceptsFrom state word) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  (A.supportWitnessMullerRunStateCompilationOfCorrect cert hcorrect).toDPAStateCompilation

/--
Run-semantics packaging of the support-witness Muller backend.  Once the
singleton support-witness Muller automata are identified with `AcceptsFrom`,
no additional language certificate is needed to obtain an
`APARunToMullerCompilation`.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessRunToMullerCompilationOfCorrect
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hcorrect :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        (A.supportWitnessMuller {state}).Accepts word ↔
          A.AcceptsFrom state word) :
    APARunToMullerCompilation.{u, v, v} A :=
  (A.supportWitnessMullerRunStateCompilationOfCorrect
    A.semanticRunLanguageCertificate hcorrect).toRunCompilation

/--
The same packaging composed with the existing LAR Muller-to-DPA construction.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessRunToDPACompilationOfCorrect
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hcorrect :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        (A.supportWitnessMuller {state}).Accepts word ↔
          A.AcceptsFrom state word) :
    APARunToDPACompilation.{u, v, v} A :=
  (A.supportWitnessRunToMullerCompilationOfCorrect hcorrect).toDPACompilation

/--
Operational form of an accepted recurrent support witness.  Besides the finite
carrier used by `SupportRecurrentWitness`, this record stores the concrete
prefix-realization facts needed to turn recurrence in the deterministic support
configuration stream back into APA macro-run evidence.
-/
structure AlternatingParityAutomaton.SupportOperationalWitness
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet)
    (infStates : Set (APASupportConfigurationState A)) where
  macroStates : Finset (Finset A.State)
  macroEdges : Finset (APAMacroEdge A)
  stateEdges : Finset (APAStateEdge A)
  macroStates_nonempty : macroStates.Nonempty
  macroStates_recurring :
    ∀ states, states ∈ macroStates ->
      states ∈ A.supportRecurringMacroStates infStates
  macroEdges_recurring :
    ∀ edge, edge ∈ macroEdges ->
      edge ∈ A.supportRecurringMacroEdges infStates
  stateEdges_recurring :
    ∀ edge, edge ∈ stateEdges ->
      edge ∈ A.supportRecurringStateEdges infStates
  macroEdges_closed :
    ∀ edge, edge ∈ macroEdges ->
      edge.1 ∈ macroStates ∧ edge.2 ∈ macroStates
  macroStates_progress :
    ∀ states, states ∈ macroStates ->
      ∃ edge, edge ∈ macroEdges ∧ edge.1 = states ∧ edge.2 ∈ macroStates
  stateEdges_covered :
    ∀ edge, edge ∈ stateEdges ->
      (∃ sourceStates ∈ macroStates, edge.1 ∈ sourceStates) ∧
        ∃ targetStates ∈ macroStates, edge.2 ∈ targetStates
  stateEdges_accepting :
    A.SupportWitnessStateEdgesAccepting stateEdges
  macroState_prefixes :
    ∀ states, states ∈ macroStates ->
      ∀ n : Nat,
        ∃ k : Nat,
          ∃ pref : A.MacroRunPrefix initialStates word k,
            n ≤ k ∧ pref.states k = states
  macroEdge_prefixes :
    ∀ edge, edge ∈ macroEdges ->
      ∀ n : Nat,
        ∃ k : Nat,
          ∃ pref : A.MacroRunPrefix initialStates word (k + 1),
            n ≤ k ∧ pref.states k = edge.1 ∧
              pref.states (k + 1) = edge.2
  stateEdge_prefixes :
    ∀ edge, edge ∈ stateEdges ->
      ∀ n : Nat,
        ∃ k : Nat,
          ∃ sourceStates : Finset A.State,
            ∃ targetStates : Finset A.State,
              ∃ stepStateEdges : Finset (APAStateEdge A),
                ∃ pref : A.MacroRunPrefix initialStates word k,
                  n ≤ k ∧
                    pref.states k = sourceStates ∧
                    A.MacroTransitionWithStateEdges
                      sourceStates (word k) targetStates stepStateEdges ∧
                    edge ∈ stepStateEdges

/--
Acceptance by the witness-based support Muller automaton exposes the finite
recurring state-edge graph that carries the parity condition.
-/
theorem AlternatingParityAutomaton.exists_recurrent_stateEdges_accepting_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ stateEdges : Finset (APAStateEdge A),
      (∀ edge, edge ∈ stateEdges ->
        edge ∈ A.supportRecurringStateEdges
          ((A.supportWitnessMuller initialStates).InfStates word)) ∧
        A.SupportWitnessStateEdgesAccepting stateEdges := by
  have hwitness :
      A.SupportRecurrentWitness
        ((A.supportWitnessMuller initialStates).InfStates word) :=
    (A.supportWitnessMuller_accepts_iff initialStates word).mp haccepts
  rcases hwitness with
    ⟨macroStates, macroEdges, stateEdges,
      _hmacroStatesNonempty,
      _hmacroStatesRecurring,
      _hmacroEdgesRecurring,
      hstateEdgesRecurring,
      _hmacroEdgesClosed,
      _hmacroStatesProgress,
      _hstateEdgesCovered,
      hstateEdgesAccepting⟩
  exact ⟨stateEdges, hstateEdgesRecurring, hstateEdgesAccepting⟩

/--
Acceptance by the witness-based support Muller automaton exposes the whole
finite recurrent macro/state-edge witness: a nonempty recurring macro carrier,
recurring closed macro edges with progress, covered recurring state edges, and
the finite parity condition on those state edges.
-/
theorem AlternatingParityAutomaton.exists_recurrent_macroGraph_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ macroStates : Finset (Finset A.State),
      ∃ macroEdges : Finset (APAMacroEdge A),
        ∃ stateEdges : Finset (APAStateEdge A),
          macroStates.Nonempty ∧
            (∀ states, states ∈ macroStates ->
              states ∈ A.supportRecurringMacroStates
                ((A.supportWitnessMuller initialStates).InfStates word)) ∧
            (∀ edge, edge ∈ macroEdges ->
              edge ∈ A.supportRecurringMacroEdges
                ((A.supportWitnessMuller initialStates).InfStates word)) ∧
            (∀ edge, edge ∈ stateEdges ->
              edge ∈ A.supportRecurringStateEdges
                ((A.supportWitnessMuller initialStates).InfStates word)) ∧
            (∀ edge, edge ∈ macroEdges ->
              edge.1 ∈ macroStates ∧ edge.2 ∈ macroStates) ∧
            (∀ states, states ∈ macroStates ->
              ∃ edge, edge ∈ macroEdges ∧ edge.1 = states ∧
                edge.2 ∈ macroStates) ∧
            (∀ edge, edge ∈ stateEdges ->
              (∃ sourceStates ∈ macroStates, edge.1 ∈ sourceStates) ∧
                ∃ targetStates ∈ macroStates, edge.2 ∈ targetStates) ∧
            A.SupportWitnessStateEdgesAccepting stateEdges := by
  exact (A.supportWitnessMuller_accepts_iff initialStates word).mp haccepts

/--
In particular, witness-Muller acceptance gives at least one recurring
macro-state in the support carrier.
-/
theorem AlternatingParityAutomaton.exists_recurring_macroState_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ states : Finset A.State,
      states ∈ A.supportRecurringMacroStates
        ((A.supportWitnessMuller initialStates).InfStates word) := by
  rcases
    A.exists_recurrent_macroGraph_of_supportWitnessMuller_accepts
      haccepts with
    ⟨macroStates, _macroEdges, _stateEdges,
      hmacroStatesNonempty,
      hmacroStatesRecurring,
      _hmacroEdgesRecurring,
      _hstateEdgesRecurring,
      _hmacroEdgesClosed,
      _hmacroStatesProgress,
      _hstateEdgesCovered,
      _hstateEdgesAccepting⟩
  rcases hmacroStatesNonempty with ⟨states, hstates⟩
  exact ⟨states, hmacroStatesRecurring states hstates⟩

/--
Witness-Muller acceptance gives a recurring macro-state that is reached by
concrete macro-run prefixes arbitrarily far along the word.
-/
theorem AlternatingParityAutomaton.exists_recurring_macroState_prefixes_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ states : Finset A.State,
      states ∈ A.supportRecurringMacroStates
        ((A.supportWitnessMuller initialStates).InfStates word) ∧
        ∀ n : Nat,
          ∃ k : Nat,
            ∃ pref : A.MacroRunPrefix initialStates word k,
              n ≤ k ∧ pref.states k = states := by
  rcases A.exists_recurring_macroState_of_supportWitnessMuller_accepts
      haccepts with
    ⟨states, hstates⟩
  refine ⟨states, hstates, ?_⟩
  have hstatesSkeleton :
      states ∈
        A.supportRecurringMacroStates
          ((A.supportConfigurationMullerSkeleton
            initialStates A.supportWitnessAcceptingFamily).InfStates word) := by
    simpa [AlternatingParityAutomaton.supportWitnessMuller] using hstates
  intro n
  exact
    A.supportRecurringMacroState_exists_macroRunPrefix_after
      A.supportWitnessAcceptingFamily hstatesSkeleton n

/--
Witness-Muller acceptance also exposes one recurring macro-state with a
recurring outgoing macro-edge whose target macro-state is recurring.  This is
the finite progress hook needed to turn the accepted recurrent carrier into
infinite macro paths.
-/
theorem AlternatingParityAutomaton.exists_recurring_macroEdge_progress_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ states : Finset A.State,
      ∃ edge : APAMacroEdge A,
        states ∈ A.supportRecurringMacroStates
          ((A.supportWitnessMuller initialStates).InfStates word) ∧
          edge ∈ A.supportRecurringMacroEdges
            ((A.supportWitnessMuller initialStates).InfStates word) ∧
          edge.1 = states ∧
          edge.2 ∈ A.supportRecurringMacroStates
            ((A.supportWitnessMuller initialStates).InfStates word) := by
  rcases
    A.exists_recurrent_macroGraph_of_supportWitnessMuller_accepts
      haccepts with
    ⟨macroStates, macroEdges, _stateEdges,
      hmacroStatesNonempty,
      hmacroStatesRecurring,
      hmacroEdgesRecurring,
      _hstateEdgesRecurring,
      _hmacroEdgesClosed,
      hmacroStatesProgress,
      _hstateEdgesCovered,
      _hstateEdgesAccepting⟩
  rcases hmacroStatesNonempty with ⟨states, hstates⟩
  rcases hmacroStatesProgress states hstates with
    ⟨edge, hedge, hsource, htarget⟩
  exact
    ⟨states, edge,
      hmacroStatesRecurring states hstates,
      hmacroEdgesRecurring edge hedge,
      hsource,
      hmacroStatesRecurring edge.2 htarget⟩

/--
The recurring progress edge exposed by witness-Muller acceptance is also
realized by concrete macro-run prefixes arbitrarily far along the word.
-/
theorem AlternatingParityAutomaton.exists_recurring_macroEdge_progress_prefixes_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ states : Finset A.State,
      ∃ edge : APAMacroEdge A,
        states ∈ A.supportRecurringMacroStates
          ((A.supportWitnessMuller initialStates).InfStates word) ∧
          edge ∈ A.supportRecurringMacroEdges
            ((A.supportWitnessMuller initialStates).InfStates word) ∧
          edge.1 = states ∧
          edge.2 ∈ A.supportRecurringMacroStates
            ((A.supportWitnessMuller initialStates).InfStates word) ∧
          ∀ n : Nat,
            ∃ k : Nat,
              ∃ pref : A.MacroRunPrefix initialStates word (k + 1),
                n ≤ k ∧ pref.states k = edge.1 ∧
                  pref.states (k + 1) = edge.2 := by
  rcases
    A.exists_recurring_macroEdge_progress_of_supportWitnessMuller_accepts
      haccepts with
    ⟨states, edge, hstates, hedge, hsource, htarget⟩
  refine ⟨states, edge, hstates, hedge, hsource, htarget, ?_⟩
  have hedgeSkeleton :
      edge ∈
        A.supportRecurringMacroEdges
          ((A.supportConfigurationMullerSkeleton
            initialStates A.supportWitnessAcceptingFamily).InfStates word) := by
    simpa [AlternatingParityAutomaton.supportWitnessMuller] using hedge
  intro n
  exact
    A.supportRecurringMacroEdge_exists_macroRunPrefix_after
      A.supportWitnessAcceptingFamily hedgeSkeleton n

/--
Witness-Muller acceptance exposes a finite accepting set of recurrent
individual support edges, and every such edge is realized by concrete
macro-run prefixes arbitrarily far along the word.
-/
theorem AlternatingParityAutomaton.exists_recurrent_stateEdges_prefixes_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ stateEdges : Finset (APAStateEdge A),
      A.SupportWitnessStateEdgesAccepting stateEdges ∧
        ∀ edge, edge ∈ stateEdges ->
          ∀ n : Nat,
            ∃ k : Nat,
              ∃ sourceStates : Finset A.State,
                ∃ targetStates : Finset A.State,
                  ∃ stepStateEdges : Finset (APAStateEdge A),
                    ∃ pref : A.MacroRunPrefix initialStates word k,
                      n ≤ k ∧
                        pref.states k = sourceStates ∧
                        A.MacroTransitionWithStateEdges
                          sourceStates (word k) targetStates stepStateEdges ∧
                        edge ∈ stepStateEdges := by
  rcases
    A.exists_recurrent_stateEdges_accepting_of_supportWitnessMuller_accepts
      haccepts with
    ⟨stateEdges, hstateEdgesRecurring, hstateEdgesAccepting⟩
  refine ⟨stateEdges, hstateEdgesAccepting, ?_⟩
  intro edge hedge n
  have hedgeSkeleton :
      edge ∈
        A.supportRecurringStateEdges
          ((A.supportConfigurationMullerSkeleton
            initialStates A.supportWitnessAcceptingFamily).InfStates word) := by
    simpa [AlternatingParityAutomaton.supportWitnessMuller] using
      hstateEdgesRecurring edge hedge
  exact
    A.supportRecurringStateEdge_exists_macroRunPrefix_after
      A.supportWitnessAcceptingFamily hedgeSkeleton n

/--
Witness-Muller acceptance can be unpacked as one finite recurrent witness
graph together with operational prefix realizations for every selected
macro-state, macro-edge, and individual state-edge.
-/
theorem AlternatingParityAutomaton.exists_recurrent_macroGraph_prefixes_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ macroStates : Finset (Finset A.State),
      ∃ macroEdges : Finset (APAMacroEdge A),
        ∃ stateEdges : Finset (APAStateEdge A),
          macroStates.Nonempty ∧
            (∀ states, states ∈ macroStates ->
              states ∈ A.supportRecurringMacroStates
                ((A.supportWitnessMuller initialStates).InfStates word)) ∧
            (∀ edge, edge ∈ macroEdges ->
              edge ∈ A.supportRecurringMacroEdges
                ((A.supportWitnessMuller initialStates).InfStates word)) ∧
            (∀ edge, edge ∈ stateEdges ->
              edge ∈ A.supportRecurringStateEdges
                ((A.supportWitnessMuller initialStates).InfStates word)) ∧
            (∀ edge, edge ∈ macroEdges ->
              edge.1 ∈ macroStates ∧ edge.2 ∈ macroStates) ∧
            (∀ states, states ∈ macroStates ->
              ∃ edge, edge ∈ macroEdges ∧ edge.1 = states ∧
                edge.2 ∈ macroStates) ∧
            (∀ edge, edge ∈ stateEdges ->
              (∃ sourceStates ∈ macroStates, edge.1 ∈ sourceStates) ∧
                ∃ targetStates ∈ macroStates, edge.2 ∈ targetStates) ∧
            A.SupportWitnessStateEdgesAccepting stateEdges ∧
            (∀ states, states ∈ macroStates ->
              ∀ n : Nat,
                ∃ k : Nat,
                  ∃ pref : A.MacroRunPrefix initialStates word k,
                    n ≤ k ∧ pref.states k = states) ∧
            (∀ edge, edge ∈ macroEdges ->
              ∀ n : Nat,
                ∃ k : Nat,
                  ∃ pref : A.MacroRunPrefix initialStates word (k + 1),
                    n ≤ k ∧ pref.states k = edge.1 ∧
                      pref.states (k + 1) = edge.2) ∧
            (∀ edge, edge ∈ stateEdges ->
              ∀ n : Nat,
                ∃ k : Nat,
                  ∃ sourceStates : Finset A.State,
                    ∃ targetStates : Finset A.State,
                      ∃ stepStateEdges : Finset (APAStateEdge A),
                        ∃ pref : A.MacroRunPrefix initialStates word k,
                          n ≤ k ∧
                            pref.states k = sourceStates ∧
                            A.MacroTransitionWithStateEdges
                              sourceStates (word k) targetStates stepStateEdges ∧
                            edge ∈ stepStateEdges) := by
  rcases
    A.exists_recurrent_macroGraph_of_supportWitnessMuller_accepts
      haccepts with
    ⟨macroStates, macroEdges, stateEdges,
      hmacroStatesNonempty,
      hmacroStatesRecurring,
      hmacroEdgesRecurring,
      hstateEdgesRecurring,
      hmacroEdgesClosed,
      hmacroStatesProgress,
      hstateEdgesCovered,
      hstateEdgesAccepting⟩
  refine
    ⟨macroStates, macroEdges, stateEdges,
      hmacroStatesNonempty,
      hmacroStatesRecurring,
      hmacroEdgesRecurring,
      hstateEdgesRecurring,
      hmacroEdgesClosed,
      hmacroStatesProgress,
      hstateEdgesCovered,
      hstateEdgesAccepting,
      ?_,
      ?_,
      ?_⟩
  · intro states hstates n
    have hstatesSkeleton :
        states ∈
          A.supportRecurringMacroStates
            ((A.supportConfigurationMullerSkeleton
              initialStates A.supportWitnessAcceptingFamily).InfStates word) := by
      simpa [AlternatingParityAutomaton.supportWitnessMuller] using
        hmacroStatesRecurring states hstates
    exact
      A.supportRecurringMacroState_exists_macroRunPrefix_after
        A.supportWitnessAcceptingFamily hstatesSkeleton n
  · intro edge hedge n
    have hedgeSkeleton :
        edge ∈
          A.supportRecurringMacroEdges
            ((A.supportConfigurationMullerSkeleton
              initialStates A.supportWitnessAcceptingFamily).InfStates word) := by
      simpa [AlternatingParityAutomaton.supportWitnessMuller] using
        hmacroEdgesRecurring edge hedge
    exact
      A.supportRecurringMacroEdge_exists_macroRunPrefix_after
        A.supportWitnessAcceptingFamily hedgeSkeleton n
  · intro edge hedge n
    have hedgeSkeleton :
        edge ∈
          A.supportRecurringStateEdges
            ((A.supportConfigurationMullerSkeleton
              initialStates A.supportWitnessAcceptingFamily).InfStates word) := by
      simpa [AlternatingParityAutomaton.supportWitnessMuller] using
        hstateEdgesRecurring edge hedge
    exact
      A.supportRecurringStateEdge_exists_macroRunPrefix_after
        A.supportWitnessAcceptingFamily hedgeSkeleton n

/--
Accepted witness-Muller runs yield an operational witness object consumed by
the remaining APA-to-Muller soundness construction.
-/
theorem AlternatingParityAutomaton.exists_supportOperationalWitness_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ _witness :
      A.SupportOperationalWitness
        initialStates word
        ((A.supportWitnessMuller initialStates).InfStates word),
      True := by
  rcases
    A.exists_recurrent_macroGraph_prefixes_of_supportWitnessMuller_accepts
      haccepts with
    ⟨macroStates, macroEdges, stateEdges,
      hmacroStatesNonempty,
      hmacroStatesRecurring,
      hmacroEdgesRecurring,
      hstateEdgesRecurring,
      hmacroEdgesClosed,
      hmacroStatesProgress,
      hstateEdgesCovered,
      hstateEdgesAccepting,
      hmacroStatePrefixes,
      hmacroEdgePrefixes,
      hstateEdgePrefixes⟩
  refine ⟨?_, trivial⟩
  exact
    { macroStates := macroStates
      macroEdges := macroEdges
      stateEdges := stateEdges
      macroStates_nonempty := hmacroStatesNonempty
      macroStates_recurring := hmacroStatesRecurring
      macroEdges_recurring := hmacroEdgesRecurring
      stateEdges_recurring := hstateEdgesRecurring
      macroEdges_closed := hmacroEdgesClosed
      macroStates_progress := hmacroStatesProgress
      stateEdges_covered := hstateEdgesCovered
      stateEdges_accepting := hstateEdgesAccepting
      macroState_prefixes := hmacroStatePrefixes
      macroEdge_prefixes := hmacroEdgePrefixes
      stateEdge_prefixes := hstateEdgePrefixes }

/--
Noncomputably select the operational witness certified by witness-Muller
acceptance.
-/
noncomputable def AlternatingParityAutomaton.supportOperationalWitness_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    A.SupportOperationalWitness
      initialStates word
      ((A.supportWitnessMuller initialStates).InfStates word) :=
  Classical.choose
    (A.exists_supportOperationalWitness_of_supportWitnessMuller_accepts
      haccepts)

/--
Splice a finite macro-run prefix with an infinite continuation started at the
prefix endpoint.
-/
noncomputable def AlternatingParityAutomaton.MacroRunPrefix.splice
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {offset : Nat}
    (pref : A.MacroRunPrefix initialStates word offset)
    (tailRun : A.MacroRun (pref.states offset) (OmegaWord.drop word offset)) :
    A.MacroRun initialStates word where
  states n := if n ≤ offset then pref.states n else tailRun.states (n - offset)
  initial_states := by
    have hzero : 0 ≤ offset := Nat.zero_le offset
    simp [hzero, pref.initial_states]
  step_transition := by
    intro n
    by_cases hlt : n < offset
    · have hnle : n ≤ offset := by omega
      have hsuccle : n + 1 ≤ offset := by omega
      simpa [hnle, hsuccle] using pref.step_transition n hlt
    · have hoffset_le : offset ≤ n := by omega
      by_cases hn_eq : n = offset
      · subst n
        have hle : offset ≤ offset := le_rfl
        have hsuccnle : ¬ offset + 1 ≤ offset := by omega
        have hsub : offset + 1 - offset = 1 := by omega
        simpa [hle, hsuccnle, hsub, OmegaWord.drop] using
          tailRun.step_transition 0
      · have hnle : ¬ n ≤ offset := by omega
        have hsuccnle : ¬ n + 1 ≤ offset := by omega
        have hidx : offset + (n - offset) = n := by omega
        have hsuccsub : n + 1 - offset = (n - offset) + 1 := by omega
        simpa [hnle, hsuccnle, OmegaWord.drop, hidx, hsuccsub] using
          tailRun.step_transition (n - offset)

@[simp]
theorem AlternatingParityAutomaton.MacroRunPrefix.splice_states_le
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {offset : Nat}
    (pref : A.MacroRunPrefix initialStates word offset)
    (tailRun : A.MacroRun (pref.states offset) (OmegaWord.drop word offset))
    {n : Nat}
    (hn : n ≤ offset) :
    (pref.splice tailRun).states n = pref.states n := by
  simp [AlternatingParityAutomaton.MacroRunPrefix.splice, hn]

@[simp]
theorem AlternatingParityAutomaton.MacroRunPrefix.splice_states_ge
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {offset : Nat}
    (pref : A.MacroRunPrefix initialStates word offset)
    (tailRun : A.MacroRun (pref.states offset) (OmegaWord.drop word offset))
    {n : Nat}
    (hn : offset ≤ n) :
    (pref.splice tailRun).states n = tailRun.states (n - offset) := by
  by_cases hle : n ≤ offset
  · have hn_eq : n = offset := by omega
    subst n
    simp [AlternatingParityAutomaton.MacroRunPrefix.splice]
  · simp [AlternatingParityAutomaton.MacroRunPrefix.splice, hle]

/--
Semantic acceptance survives prefix splicing: if the continuation is
semantically accepting, then the whole run is semantically accepting.
-/
theorem AlternatingParityAutomaton.MacroRunPrefix.splice_semanticAccepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {offset : Nat}
    (pref : A.MacroRunPrefix initialStates word offset)
    (tailRun : A.MacroRun (pref.states offset) (OmegaWord.drop word offset))
    (htail : tailRun.SemanticAccepting) :
    (pref.splice tailRun).SemanticAccepting := by
  rcases htail with ⟨tailOffset, htailRecurring, htailAccepts⟩
  refine ⟨offset + tailOffset, ?_, ?_⟩
  · rw [(pref.splice tailRun).mem_infStateFinset]
    intro bound
    have htailSeen :
        tailRun.StateSeenInfinitelyOften (tailRun.states tailOffset) := by
      exact (tailRun.mem_infStateFinset (tailRun.states tailOffset)).mp
        htailRecurring
    rcases htailSeen (bound - offset) with ⟨k, hk, hkstates⟩
    refine ⟨offset + k, ?_, ?_⟩
    · omega
    · have hoff : offset ≤ offset + k := by omega
      calc
        (pref.splice tailRun).states (offset + k)
            = tailRun.states (offset + k - offset) :=
              pref.splice_states_ge tailRun hoff
        _ = tailRun.states k := by
              congr 1
              omega
        _ = tailRun.states tailOffset := hkstates
        _ = (pref.splice tailRun).states (offset + tailOffset) := by
              symm
              have hoffTail : offset ≤ offset + tailOffset := by omega
              calc
                (pref.splice tailRun).states (offset + tailOffset)
                    = tailRun.states (offset + tailOffset - offset) :=
                      pref.splice_states_ge tailRun hoffTail
                _ = tailRun.states tailOffset := by
                      congr 1
                      omega
  · intro state hstate
    have hoff : offset ≤ offset + tailOffset := by omega
    have hstateTail : state ∈ tailRun.states tailOffset := by
      simpa [Nat.add_sub_cancel_left] using hstate
    have haccept := htailAccepts state hstateTail
    simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using haccept

/--
The operational support witness is semantically realizable once it can be
spliced into a genuine macro-run whose recurring macro-state is accepting in
the APA semantics.
-/
def AlternatingParityAutomaton.SupportOperationalWitness.HasSemanticMacroRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (_witness : A.SupportOperationalWitness initialStates word infStates) :
    Prop :=
  ∃ run : A.MacroRun initialStates word, run.SemanticAccepting

/--
The operational witness data is only a carrier for recurrence evidence: its
semantic macro-run obligation is exactly APA acceptance of every initial
macro-state.

This theorem is useful when proving support-witness soundness, because it keeps
the semantic hypothesis at the APA boundary instead of hiding it inside
the selected recurrent support graph.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.hasSemanticMacroRun_iff_accepts_all
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates) :
    witness.HasSemanticMacroRun ↔
      ∀ state, state ∈ initialStates -> A.AcceptsFrom state word := by
  exact A.exists_semanticAccepting_macroRun_iff_accepts_all initialStates word

theorem AlternatingParityAutomaton.SupportOperationalWitness.acceptsFrom_of_hasSemanticMacroRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    (hsemantic : witness.HasSemanticMacroRun)
    {state : A.State}
    (hstate : state ∈ initialStates) :
    A.AcceptsFrom state word := by
  rcases hsemantic with ⟨run, haccepting⟩
  exact run.acceptsFrom_of_mem_initial_of_semanticAccepting haccepting hstate

/--
If some finite prefix endpoint carried by an operational witness has accepting
continuations for all of its APA states, then the witness has a semantically
accepting macro-run.  The proof splices the finite prefix with the canonical
accepting macro-run from that endpoint.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.hasSemanticMacroRun_of_prefix_accepts
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {offset : Nat}
    (pref : A.MacroRunPrefix initialStates word offset)
    (haccepts :
      ∀ state, state ∈ pref.states offset ->
        A.AcceptsFrom state (OmegaWord.drop word offset)) :
    witness.HasSemanticMacroRun := by
  rcases
    A.exists_semanticAccepting_macroRun_of_accepts_all
      (pref.states offset) (OmegaWord.drop word offset) haccepts with
    ⟨tailRun, htailSemantic⟩
  exact ⟨pref.splice tailRun, pref.splice_semanticAccepting tailRun htailSemantic⟩

/--
Conversely, a semantic macro-run witness exposes the finite accepting frontier
required by the prefix-continuation formulation of support-witness soundness.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.exists_prefix_accepts_of_hasSemanticMacroRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    (hsemantic : witness.HasSemanticMacroRun) :
    ∃ offset : Nat,
      ∃ pref : A.MacroRunPrefix initialStates word offset,
        ∀ state, state ∈ pref.states offset ->
          A.AcceptsFrom state (OmegaWord.drop word offset) := by
  rcases hsemantic with ⟨run, offset, _hrecurring, haccepts⟩
  exact ⟨offset, run.prefix offset, by simpa using haccepts⟩

theorem AlternatingParityAutomaton.SupportOperationalWitness.exists_progress_edge
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {states : Finset A.State}
    (hstates : states ∈ witness.macroStates) :
    ∃ edge : APAMacroEdge A,
      edge ∈ witness.macroEdges ∧ edge.1 = states ∧
        edge.2 ∈ witness.macroStates :=
  witness.macroStates_progress states hstates

/--
In an operational witness, every selected macro-state has a selected outgoing
macro-edge whose concrete realization appears arbitrarily far along the word.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.exists_progress_edge_prefixes
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {states : Finset A.State}
    (hstates : states ∈ witness.macroStates) :
    ∃ edge : APAMacroEdge A,
      edge ∈ witness.macroEdges ∧
        edge.1 = states ∧
        edge.2 ∈ witness.macroStates ∧
        ∀ n : Nat,
          ∃ k : Nat,
            ∃ pref : A.MacroRunPrefix initialStates word (k + 1),
              n ≤ k ∧ pref.states k = edge.1 ∧
                pref.states (k + 1) = edge.2 := by
  rcases witness.exists_progress_edge hstates with
    ⟨edge, hedge, hsource, htarget⟩
  exact
    ⟨edge, hedge, hsource, htarget,
      witness.macroEdge_prefixes edge hedge⟩

/--
An operational witness contains an infinite path through its selected finite
macro-state carrier.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.exists_macroPath
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates) :
    ∃ path : Nat -> Finset A.State,
      (∀ n, path n ∈ witness.macroStates) ∧
        ∀ n,
          ∃ edge : APAMacroEdge A,
            edge ∈ witness.macroEdges ∧
              edge.1 = path n ∧ edge.2 = path (n + 1) := by
  classical
  rcases witness.macroStates_nonempty with ⟨start, hstart⟩
  let next : { states : Finset A.State // states ∈ witness.macroStates } ->
      { states : Finset A.State // states ∈ witness.macroStates } :=
    fun states =>
      let edge := Classical.choose (witness.macroStates_progress states.1 states.2)
      ⟨edge.2,
        (Classical.choose_spec
          (witness.macroStates_progress states.1 states.2)).2.2⟩
  let pathSub : Nat -> { states : Finset A.State // states ∈ witness.macroStates } :=
    Nat.rec ⟨start, hstart⟩ (fun _ previous => next previous)
  let path : Nat -> Finset A.State := fun n => (pathSub n).1
  refine ⟨path, ?_, ?_⟩
  · intro n
    exact (pathSub n).2
  · intro n
    let edge := Classical.choose
      (witness.macroStates_progress (pathSub n).1 (pathSub n).2)
    have hedgeSpec :
        edge ∈ witness.macroEdges ∧ edge.1 = (pathSub n).1 ∧
          edge.2 ∈ witness.macroStates :=
      Classical.choose_spec
        (witness.macroStates_progress (pathSub n).1 (pathSub n).2)
    refine ⟨edge, hedgeSpec.1, hedgeSpec.2.1, ?_⟩
    change edge.2 = (pathSub (n + 1)).1
    simp [pathSub, next, edge]

/--
The macro path selected from an operational witness can be chosen so every step
has arbitrarily late concrete macro-run prefix realizations.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.exists_macroPath_with_prefixes
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates) :
    ∃ path : Nat -> Finset A.State,
      (∀ n, path n ∈ witness.macroStates) ∧
        ∀ n,
          ∃ edge : APAMacroEdge A,
            edge ∈ witness.macroEdges ∧
              edge.1 = path n ∧
              edge.2 = path (n + 1) ∧
              ∀ bound : Nat,
                ∃ k : Nat,
                  ∃ pref : A.MacroRunPrefix initialStates word (k + 1),
                    bound ≤ k ∧ pref.states k = edge.1 ∧
                      pref.states (k + 1) = edge.2 := by
  rcases witness.exists_macroPath with ⟨path, hpathStates, hpathEdges⟩
  refine ⟨path, hpathStates, ?_⟩
  intro n
  rcases hpathEdges n with ⟨edge, hedge, hsource, htarget⟩
  exact
    ⟨edge, hedge, hsource, htarget,
      witness.macroEdge_prefixes edge hedge⟩

/--
Sampled concrete realizations of an operational macro path can be chosen
strictly farther and farther along the word.

This does not yet splice the samples into one consecutive macro-run; it is the
coherent sampled schedule needed before that final extraction can be stated.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.exists_macroPath_with_increasing_prefixes
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates) :
    ∃ path : Nat -> Finset A.State,
      ∃ time : Nat -> Nat,
        (∀ n, path n ∈ witness.macroStates) ∧
          (∀ n, time n < time (n + 1)) ∧
            ∀ n,
              ∃ edge : APAMacroEdge A,
                ∃ pref : A.MacroRunPrefix initialStates word (time n + 1),
                  edge ∈ witness.macroEdges ∧
                    edge.1 = path n ∧
                      edge.2 = path (n + 1) ∧
                        pref.states (time n) = edge.1 ∧
                          pref.states (time n + 1) = edge.2 := by
  classical
  rcases witness.exists_macroPath_with_prefixes with
    ⟨path, hpathStates, hpathEdges⟩
  let edgeOf : Nat -> APAMacroEdge A := fun n =>
    Classical.choose (hpathEdges n)
  have hedgeOf :
      ∀ n,
        edgeOf n ∈ witness.macroEdges ∧
          (edgeOf n).1 = path n ∧
            (edgeOf n).2 = path (n + 1) ∧
              ∀ bound : Nat,
                ∃ k : Nat,
                  ∃ pref : A.MacroRunPrefix initialStates word (k + 1),
                    bound ≤ k ∧ pref.states k = (edgeOf n).1 ∧
                      pref.states (k + 1) = (edgeOf n).2 := by
    intro n
    exact Classical.choose_spec (hpathEdges n)
  let step : Nat -> Nat -> Nat := fun n previous =>
    Classical.choose ((hedgeOf n).2.2.2 (previous + 1))
  have hstep :
      ∀ n previous,
        previous + 1 ≤ step n previous ∧
          ∃ pref : A.MacroRunPrefix initialStates word (step n previous + 1),
            pref.states (step n previous) = (edgeOf n).1 ∧
              pref.states (step n previous + 1) = (edgeOf n).2 := by
    intro n previous
    have hspec :=
      Classical.choose_spec ((hedgeOf n).2.2.2 (previous + 1))
    rcases hspec with ⟨pref, hle, hsource, htarget⟩
    exact ⟨hle, pref, hsource, htarget⟩
  let time : Nat -> Nat :=
    Nat.rec (step 0 0) (fun n previous => step (n + 1) previous)
  have htimeStep :
      time 0 = step 0 0 ∧
        ∀ n, time (n + 1) = step (n + 1) (time n) := by
    constructor
    · rfl
    · intro n
      rfl
  refine ⟨path, time, hpathStates, ?_, ?_⟩
  · intro n
    rw [htimeStep.2 n]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (time n))
      (hstep (n + 1) (time n)).1
  · intro n
    refine ⟨edgeOf n, ?_⟩
    by_cases hn : n = 0
    · subst n
      rw [htimeStep.1]
      rcases (hstep 0 0).2 with ⟨pref, hsource, htarget⟩
      exact
        ⟨pref,
          (hedgeOf 0).1,
          (hedgeOf 0).2.1,
          (hedgeOf 0).2.2.1,
          hsource,
          htarget⟩
    · have hpos : ∃ m, n = m + 1 := by
        cases n with
        | zero => exact False.elim (hn rfl)
        | succ m => exact ⟨m, rfl⟩
      rcases hpos with ⟨m, rfl⟩
      rw [htimeStep.2 m]
      rcases (hstep (m + 1) (time m)).2 with
        ⟨pref, hsource, htarget⟩
      exact
        ⟨pref,
          (hedgeOf (m + 1)).1,
          (hedgeOf (m + 1)).2.1,
          (hedgeOf (m + 1)).2.2.1,
          hsource,
          htarget⟩

theorem AlternatingParityAutomaton.SupportOperationalWitness.stateEdge_source_covered
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {edge : APAStateEdge A}
    (hedge : edge ∈ witness.stateEdges) :
    ∃ sourceStates ∈ witness.macroStates, edge.1 ∈ sourceStates :=
  (witness.stateEdges_covered edge hedge).1

theorem AlternatingParityAutomaton.SupportOperationalWitness.stateEdge_target_covered
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {edge : APAStateEdge A}
    (hedge : edge ∈ witness.stateEdges) :
    ∃ targetStates ∈ witness.macroStates, edge.2 ∈ targetStates :=
  (witness.stateEdges_covered edge hedge).2

/--
Every infinite path through the selected state-edge graph is also a path
through the recurring support-edge graph represented by the operational
witness.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.stateEdgePath_supportEdgePath
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {path : Nat -> A.State}
    (hpath : ∀ n : Nat, (path n, path (n + 1)) ∈ witness.stateEdges) :
    A.SupportEdgePath infStates path := by
  intro n
  exact witness.stateEdges_recurring (path n, path (n + 1)) (hpath n)

/--
Every infinite path through the selected state-edge graph of an operational
witness satisfies the APA parity condition.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.stateEdgePath_min_even
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {path : Nat -> A.State}
    (hpath : ∀ n : Nat, (path n, path (n + 1)) ∈ witness.stateEdges) :
    ∃ p : Nat,
      DetParityAutomaton.NatEven p ∧
        A.SupportEdgePathPrioritySeenInfinitelyOften path p ∧
          ∀ q : Nat,
            A.SupportEdgePathPrioritySeenInfinitelyOften path q -> p ≤ q :=
  witness.stateEdges_accepting path hpath

/--
Concrete prefix realizations of selected state edges include the source and
target membership facts induced by the support transition containing that edge.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.stateEdge_prefixes_with_membership
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {edge : APAStateEdge A}
    (hedge : edge ∈ witness.stateEdges) :
    ∀ n : Nat,
      ∃ k : Nat,
        ∃ sourceStates : Finset A.State,
          ∃ targetStates : Finset A.State,
            ∃ stepStateEdges : Finset (APAStateEdge A),
              ∃ pref : A.MacroRunPrefix initialStates word k,
                n ≤ k ∧
                  pref.states k = sourceStates ∧
                  A.MacroTransitionWithStateEdges
                    sourceStates (word k) targetStates stepStateEdges ∧
                  edge ∈ stepStateEdges ∧
                  edge.1 ∈ sourceStates ∧
                  edge.2 ∈ targetStates := by
  intro n
  rcases witness.stateEdge_prefixes edge hedge n with
    ⟨k, sourceStates, targetStates, stepStateEdges, pref,
      hle, hpref, htransition, hedgeStep⟩
  exact
    ⟨k, sourceStates, targetStates, stepStateEdges, pref,
      hle, hpref, htransition, hedgeStep,
      htransition.edge_source_mem hedgeStep,
      htransition.edge_target_mem hedgeStep⟩

/--
Concrete prefix realizations of selected state edges can be extended through
the transition that realizes the edge.

This is the timed form needed by the LTL frontier proof: the returned prefix
ends at the target macro-state at time `k + 1`, not only at the source
macro-state at time `k`.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.stateEdge_prefixes_with_extended_prefix
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {edge : APAStateEdge A}
    (hedge : edge ∈ witness.stateEdges) :
    ∀ n : Nat,
      ∃ k : Nat,
        ∃ sourceStates : Finset A.State,
          ∃ targetStates : Finset A.State,
            ∃ stepStateEdges : Finset (APAStateEdge A),
              ∃ pref : A.MacroRunPrefix initialStates word (k + 1),
                n ≤ k ∧
                  pref.states k = sourceStates ∧
                  pref.states (k + 1) = targetStates ∧
                  A.MacroTransitionWithStateEdges
                    sourceStates (word k) targetStates stepStateEdges ∧
                  edge ∈ stepStateEdges ∧
                  edge.1 ∈ sourceStates ∧
                  edge.2 ∈ targetStates := by
  intro n
  rcases witness.stateEdge_prefixes edge hedge n with
    ⟨k, sourceStates, targetStates, stepStateEdges, pref,
      hle, hpref, htransition, hedgeStep⟩
  have hmacro :
      A.MacroTransition (pref.states k) (word k) targetStates := by
    simpa [hpref] using htransition.to_macroTransition
  let prefExtended := pref.snoc targetStates hmacro
  refine
    ⟨k, sourceStates, targetStates, stepStateEdges, prefExtended,
      hle, ?_, ?_, htransition, hedgeStep,
      htransition.edge_source_mem hedgeStep,
      htransition.edge_target_mem hedgeStep⟩
  · have hk : k ≤ k := le_rfl
    simpa [prefExtended, hpref] using
      (AlternatingParityAutomaton.MacroRunPrefix.snoc_states_of_le
        pref targetStates hmacro hk)
  · simpa [prefExtended] using
      (AlternatingParityAutomaton.MacroRunPrefix.snoc_states_last
        pref targetStates hmacro)

/--
Prefix recurrence for an operational macro-state witness also gives membership
in the deterministic macro-configuration run.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.macroState_prefixes_mem_macroConfigurationRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {states : Finset A.State}
    (hstates : states ∈ witness.macroStates) :
    ∀ n : Nat,
      ∃ k : Nat,
        n ≤ k ∧ states ∈ A.macroConfigurationRun initialStates word k := by
  intro n
  rcases witness.macroState_prefixes states hstates n with
    ⟨k, pref, hle, hprefStates⟩
  refine ⟨k, hle, ?_⟩
  simpa [hprefStates] using
    pref.states_mem_macroConfigurationRun (n := k) le_rfl

/--
Selected operational macro-states of an accepted support-witness Muller run can
be sampled arbitrarily far out inside accepting deterministic suffix carrier
states.

This is the operational-witness form needed by the LTL recurrent-frontier
anchor: it combines recurrence of a selected macro-state with deterministic
Muller suffix invariance, but still leaves the semantic formula argument
explicit.
-/
theorem AlternatingParityAutomaton.exists_supportWitnessMuller_accepting_suffix_config_of_operational_macroState
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates states : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word)
    (hstates :
      states ∈
        (A.supportOperationalWitness_of_supportWitnessMuller_accepts
          (initialStates := initialStates) haccepts).macroStates) :
    ∀ n : Nat,
      ∃ k : Nat,
        ∃ config : (A.supportWitnessMuller initialStates).State,
          n ≤ k ∧
            (A.supportWitnessMuller initialStates).AcceptsFrom
              config (OmegaWord.drop word k) ∧
              states ∈ config.configs := by
  intro n
  let witness :=
    A.supportOperationalWitness_of_supportWitnessMuller_accepts
      (initialStates := initialStates) haccepts
  rcases
    witness.macroState_prefixes_mem_macroConfigurationRun
      (states := states) hstates n with
    ⟨k, hle, hconfig⟩
  rcases
    A.exists_supportWitnessMuller_accepting_suffix_config_of_macroConfigurationRun
      haccepts hconfig with
    ⟨config, hconfigAccepts, hstatesConfig⟩
  exact ⟨k, config, hle, hconfigAccepts, hstatesConfig⟩

/--
Prefix recurrence for an operational macro-edge witness also gives membership
in the deterministic macro-configuration edge stream.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.macroEdge_prefixes_mem_macroConfigurationEdgeRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {edge : APAMacroEdge A}
    (hedge : edge ∈ witness.macroEdges) :
    ∀ n : Nat,
      ∃ k : Nat,
        n ≤ k ∧
          edge ∈ A.macroConfigurationEdgeRun initialStates word k := by
  intro n
  rcases witness.macroEdge_prefixes edge hedge n with
    ⟨k, pref, hle, hprefSource, hprefTarget⟩
  refine ⟨k, hle, ?_⟩
  simpa [hprefSource, hprefTarget] using
    pref.edge_mem_macroConfigurationEdgeRun (n := k) (Nat.lt_succ_self k)

/--
Prefix recurrence for a selected macro-edge exposes the whole deterministic
macro-configuration step at the realizing time.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.macroEdge_prefixes_mem_macroConfigurationStep
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {edge : APAMacroEdge A}
    (hedge : edge ∈ witness.macroEdges) :
    ∀ n : Nat,
      ∃ k : Nat,
        n ≤ k ∧
          edge.1 ∈ A.macroConfigurationRun initialStates word k ∧
            edge.2 ∈ A.macroConfigurationRun initialStates word (k + 1) ∧
              edge ∈ A.macroConfigurationEdgeRun initialStates word k := by
  intro n
  rcases witness.macroEdge_prefixes edge hedge n with
    ⟨k, pref, hle, hprefSource, hprefTarget⟩
  have hsource :
      edge.1 ∈ A.macroConfigurationRun initialStates word k := by
    simpa [hprefSource] using
      pref.states_mem_macroConfigurationRun (n := k) (by omega)
  have htarget :
      edge.2 ∈ A.macroConfigurationRun initialStates word (k + 1) := by
    simpa [hprefTarget] using
      pref.states_mem_macroConfigurationRun (n := k + 1) le_rfl
  have hedgeRun :
      edge ∈ A.macroConfigurationEdgeRun initialStates word k := by
    simpa [hprefSource, hprefTarget] using
      pref.edge_mem_macroConfigurationEdgeRun (n := k) (Nat.lt_succ_self k)
  exact ⟨k, hle, hsource, htarget, hedgeRun⟩

/--
Every selected recurring macro-state has a selected progress edge whose
concrete realizations are deterministic macro-configuration steps arbitrarily
far along the word.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.exists_progress_edge_macroConfigurationStep
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {states : Finset A.State}
    (hstates : states ∈ witness.macroStates) :
    ∃ edge : APAMacroEdge A,
      edge ∈ witness.macroEdges ∧
        edge.1 = states ∧
          edge.2 ∈ witness.macroStates ∧
            ∀ n : Nat,
              ∃ k : Nat,
                n ≤ k ∧
                  edge.1 ∈ A.macroConfigurationRun initialStates word k ∧
                    edge.2 ∈ A.macroConfigurationRun initialStates word (k + 1) ∧
                      edge ∈ A.macroConfigurationEdgeRun initialStates word k := by
  rcases witness.exists_progress_edge hstates with
    ⟨edge, hedge, hsource, htarget⟩
  exact
    ⟨edge, hedge, hsource, htarget,
      witness.macroEdge_prefixes_mem_macroConfigurationStep hedge⟩

/--
Concrete operational state-edge prefixes can be viewed from the deterministic
macro-configuration run at the same time.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.stateEdge_prefixes_mem_macroConfigurationRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {edge : APAStateEdge A}
    (hedge : edge ∈ witness.stateEdges) :
    ∀ n : Nat,
      ∃ k : Nat,
        ∃ sourceStates : Finset A.State,
          ∃ targetStates : Finset A.State,
            ∃ stepStateEdges : Finset (APAStateEdge A),
              n ≤ k ∧
                sourceStates ∈ A.macroConfigurationRun initialStates word k ∧
                  A.MacroTransitionWithStateEdges
                    sourceStates (word k) targetStates stepStateEdges ∧
                    edge ∈ stepStateEdges ∧
                      edge.1 ∈ sourceStates ∧
                        edge.2 ∈ targetStates := by
  intro n
  rcases witness.stateEdge_prefixes_with_membership hedge n with
    ⟨k, sourceStates, targetStates, stepStateEdges, pref,
      hle, hpref, htransition, hedgeStep, hedgeSource, hedgeTarget⟩
  refine
    ⟨k, sourceStates, targetStates, stepStateEdges,
      hle, ?_, htransition, hedgeStep, hedgeSource, hedgeTarget⟩
  simpa [hpref] using
    pref.states_mem_macroConfigurationRun (n := k) le_rfl

/--
Concrete operational state-edge prefixes determine a full deterministic
macro-configuration step: the source is reachable at time `k`, the target is
reachable at time `k + 1`, and the macro-edge is present in the deterministic
edge stream.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.stateEdge_prefixes_mem_macroConfigurationStep
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates)
    {edge : APAStateEdge A}
    (hedge : edge ∈ witness.stateEdges) :
    ∀ n : Nat,
      ∃ k : Nat,
        ∃ sourceStates : Finset A.State,
          ∃ targetStates : Finset A.State,
            ∃ stepStateEdges : Finset (APAStateEdge A),
              n ≤ k ∧
                sourceStates ∈ A.macroConfigurationRun initialStates word k ∧
                  targetStates ∈ A.macroConfigurationRun initialStates word (k + 1) ∧
                    (sourceStates, targetStates) ∈
                      A.macroConfigurationEdgeRun initialStates word k ∧
                      A.MacroTransitionWithStateEdges
                        sourceStates (word k) targetStates stepStateEdges ∧
                        edge ∈ stepStateEdges ∧
                          edge.1 ∈ sourceStates ∧
                            edge.2 ∈ targetStates := by
  intro n
  rcases witness.stateEdge_prefixes_with_extended_prefix hedge n with
    ⟨k, sourceStates, targetStates, stepStateEdges, pref,
      hle, hprefSource, hprefTarget, htransition, hedgeStep,
      hedgeSource, hedgeTarget⟩
  have hsourceMem :
      sourceStates ∈ A.macroConfigurationRun initialStates word k := by
    simpa [hprefSource] using
      pref.states_mem_macroConfigurationRun (n := k) (by omega)
  have htargetMem :
      targetStates ∈ A.macroConfigurationRun initialStates word (k + 1) := by
    simpa [hprefTarget] using
      pref.states_mem_macroConfigurationRun (n := k + 1) le_rfl
  have hedgeRun :
      (sourceStates, targetStates) ∈
        A.macroConfigurationEdgeRun initialStates word k := by
    simpa [hprefSource, hprefTarget] using
      pref.edge_mem_macroConfigurationEdgeRun (n := k) (Nat.lt_succ_self k)
  exact
    ⟨k, sourceStates, targetStates, stepStateEdges,
      hle, hsourceMem, htargetMem, hedgeRun, htransition, hedgeStep,
      hedgeSource, hedgeTarget⟩

/--
Forgetting the operational prefix data of an operational witness recovers the
finite recurrent witness used as the witness-Muller accepting family.
-/
theorem AlternatingParityAutomaton.SupportOperationalWitness.to_supportRecurrentWitness
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {infStates : Set (APASupportConfigurationState A)}
    (witness : A.SupportOperationalWitness initialStates word infStates) :
    A.SupportRecurrentWitness infStates := by
  exact
    ⟨witness.macroStates,
      witness.macroEdges,
      witness.stateEdges,
      witness.macroStates_nonempty,
      witness.macroStates_recurring,
      witness.macroEdges_recurring,
      witness.stateEdges_recurring,
      witness.macroEdges_closed,
      witness.macroStates_progress,
      witness.stateEdges_covered,
      witness.stateEdges_accepting⟩

/--
Witness-Muller acceptance is equivalent to existence of the operational witness
object for its run's infinity set.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_accepts_iff_exists_operationalWitness
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet) :
    (A.supportWitnessMuller initialStates).Accepts word ↔
      ∃ _witness :
        A.SupportOperationalWitness
          initialStates word
          ((A.supportWitnessMuller initialStates).InfStates word),
        True := by
  constructor
  · intro haccepts
    exact A.exists_supportOperationalWitness_of_supportWitnessMuller_accepts haccepts
  · intro hoperational
    rcases hoperational with ⟨witness, _⟩
    exact
      (A.supportWitnessMuller_accepts_iff initialStates word).mpr
        witness.to_supportRecurrentWitness

/--
Witness-Muller acceptance directly yields an operational macro-path whose
selected macro-edges have arbitrarily late concrete prefix realizations.
-/
theorem AlternatingParityAutomaton.exists_operational_macroPath_with_prefixes_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ witness :
        A.SupportOperationalWitness
          initialStates word
          ((A.supportWitnessMuller initialStates).InfStates word),
      ∃ path : Nat -> Finset A.State,
        (∀ n, path n ∈ witness.macroStates) ∧
          ∀ n,
            ∃ edge : APAMacroEdge A,
              edge ∈ witness.macroEdges ∧
                edge.1 = path n ∧
                edge.2 = path (n + 1) ∧
                ∀ bound : Nat,
                  ∃ k : Nat,
                    ∃ pref : A.MacroRunPrefix initialStates word (k + 1),
                      bound ≤ k ∧ pref.states k = edge.1 ∧
                        pref.states (k + 1) = edge.2 := by
  let witness :=
    A.supportOperationalWitness_of_supportWitnessMuller_accepts haccepts
  exact ⟨witness, witness.exists_macroPath_with_prefixes⟩

/--
Witness-Muller acceptance directly yields a sampled operational macro path
whose concrete prefix realizations occur at strictly increasing times.
-/
theorem AlternatingParityAutomaton.exists_operational_macroPath_with_increasing_prefixes_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ witness :
        A.SupportOperationalWitness
          initialStates word
          ((A.supportWitnessMuller initialStates).InfStates word),
      ∃ path : Nat -> Finset A.State,
        ∃ time : Nat -> Nat,
          (∀ n, path n ∈ witness.macroStates) ∧
            (∀ n, time n < time (n + 1)) ∧
              ∀ n,
                ∃ edge : APAMacroEdge A,
                  ∃ pref : A.MacroRunPrefix initialStates word (time n + 1),
                    edge ∈ witness.macroEdges ∧
                      edge.1 = path n ∧
                        edge.2 = path (n + 1) ∧
                          pref.states (time n) = edge.1 ∧
                            pref.states (time n + 1) = edge.2 := by
  let witness :=
    A.supportOperationalWitness_of_supportWitnessMuller_accepts haccepts
  exact ⟨witness, witness.exists_macroPath_with_increasing_prefixes⟩

/--
Witness-Muller acceptance directly yields the parity condition for every path
through the selected accepting state-edge graph of its operational witness.
-/
theorem AlternatingParityAutomaton.exists_operational_stateEdgeParity_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ witness :
        A.SupportOperationalWitness
          initialStates word
          ((A.supportWitnessMuller initialStates).InfStates word),
      ∀ path : Nat -> A.State,
        (∀ n : Nat, (path n, path (n + 1)) ∈ witness.stateEdges) ->
          ∃ p : Nat,
            DetParityAutomaton.NatEven p ∧
              A.SupportEdgePathPrioritySeenInfinitelyOften path p ∧
                ∀ q : Nat,
                  A.SupportEdgePathPrioritySeenInfinitelyOften path q -> p ≤ q := by
  let witness :=
    A.supportOperationalWitness_of_supportWitnessMuller_accepts haccepts
  exact ⟨witness, fun path hpath => witness.stateEdgePath_min_even hpath⟩

/--
For an accepted witness-Muller word, every path through the selected state-edge
graph of the operational witness is both a recurring support-edge path and
parity accepting.
-/
theorem AlternatingParityAutomaton.exists_operational_stateEdgePath_support_and_parity_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ witness :
        A.SupportOperationalWitness
          initialStates word
          ((A.supportWitnessMuller initialStates).InfStates word),
      ∀ path : Nat -> A.State,
        (∀ n : Nat, (path n, path (n + 1)) ∈ witness.stateEdges) ->
          A.SupportEdgePath
              ((A.supportWitnessMuller initialStates).InfStates word) path ∧
            ∃ p : Nat,
              DetParityAutomaton.NatEven p ∧
                A.SupportEdgePathPrioritySeenInfinitelyOften path p ∧
                  ∀ q : Nat,
                    A.SupportEdgePathPrioritySeenInfinitelyOften path q -> p ≤ q := by
  let witness :=
    A.supportOperationalWitness_of_supportWitnessMuller_accepts haccepts
  refine ⟨witness, ?_⟩
  intro path hpath
  exact
    ⟨witness.stateEdgePath_supportEdgePath hpath,
      witness.stateEdgePath_min_even hpath⟩

/--
Witness-Muller acceptance yields an infinite path through the accepted
recurrent macro graph.  The path stays inside recurring macro-states, and every
step is justified by a recurring macro-edge of the support carrier.
-/
theorem AlternatingParityAutomaton.exists_recurring_macroPath_of_supportWitnessMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportWitnessMuller initialStates).Accepts word) :
    ∃ path : Nat -> Finset A.State,
      (∀ n,
        path n ∈ A.supportRecurringMacroStates
          ((A.supportWitnessMuller initialStates).InfStates word)) ∧
        ∀ n,
          ∃ edge : APAMacroEdge A,
            edge ∈ A.supportRecurringMacroEdges
              ((A.supportWitnessMuller initialStates).InfStates word) ∧
              edge.1 = path n ∧ edge.2 = path (n + 1) := by
  classical
  rcases
    A.exists_recurrent_macroGraph_of_supportWitnessMuller_accepts
      haccepts with
    ⟨macroStates, macroEdges, _stateEdges,
      hmacroStatesNonempty,
      hmacroStatesRecurring,
      hmacroEdgesRecurring,
      _hstateEdgesRecurring,
      _hmacroEdgesClosed,
      hmacroStatesProgress,
      _hstateEdgesCovered,
      _hstateEdgesAccepting⟩
  rcases hmacroStatesNonempty with ⟨start, hstart⟩
  let next : { states : Finset A.State // states ∈ macroStates } ->
      { states : Finset A.State // states ∈ macroStates } :=
    fun states =>
      let edge := Classical.choose (hmacroStatesProgress states.1 states.2)
      ⟨edge.2,
        (Classical.choose_spec
          (hmacroStatesProgress states.1 states.2)).2.2⟩
  let pathSub : Nat -> { states : Finset A.State // states ∈ macroStates } :=
    Nat.rec ⟨start, hstart⟩ (fun _ previous => next previous)
  let path : Nat -> Finset A.State := fun n => (pathSub n).1
  refine ⟨path, ?_, ?_⟩
  · intro n
    exact hmacroStatesRecurring (pathSub n).1 (pathSub n).2
  · intro n
    let edge := Classical.choose
      (hmacroStatesProgress (pathSub n).1 (pathSub n).2)
    have hedgeSpec :
        edge ∈ macroEdges ∧ edge.1 = (pathSub n).1 ∧
          edge.2 ∈ macroStates :=
      Classical.choose_spec
        (hmacroStatesProgress (pathSub n).1 (pathSub n).2)
    refine ⟨edge, hmacroEdgesRecurring edge hedgeSpec.1, hedgeSpec.2.1, ?_⟩
    change edge.2 = (pathSub (n + 1)).1
    simp [pathSub, next, edge]

/-- The Muller accepting family for the support-edge deterministic carrier. -/
def AlternatingParityAutomaton.supportConfigurationAcceptingFamily
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Set (Set (APASupportConfigurationState A)) :=
  { infStates | A.SupportRecurringStateEdgesAccepting infStates }

/--
The deterministic Muller automaton obtained from the APA support-configuration
carrier with the branch-parity accepting family.
-/
noncomputable def AlternatingParityAutomaton.supportConfigurationMuller
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State) :
    DetMullerAutomaton.{u, v} Alphabet :=
  A.supportConfigurationMullerSkeleton
    initialStates
    A.supportConfigurationAcceptingFamily

theorem AlternatingParityAutomaton.supportConfigurationMuller_accepts_iff
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (word : OmegaWord Alphabet) :
    (A.supportConfigurationMuller initialStates).Accepts word ↔
      A.SupportRecurringStateEdgesAccepting
        ((A.supportConfigurationMuller initialStates).InfStates word) := by
  rfl

/--
Acceptance by the support-edge Muller condition yields an explicit finite
recurring edge graph whose every infinite path satisfies the APA parity
condition.
-/
theorem AlternatingParityAutomaton.exists_recurrent_stateEdges_accepting_of_supportConfigurationMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.supportConfigurationMuller initialStates).Accepts word) :
    ∃ stateEdges : Finset (APAStateEdge A),
      (∀ edge, edge ∈ stateEdges ->
        edge ∈ A.supportRecurringStateEdges
          ((A.supportConfigurationMuller initialStates).InfStates word)) ∧
        A.SupportWitnessStateEdgesAccepting stateEdges := by
  let infStates :=
    (A.supportConfigurationMuller initialStates).InfStates word
  let stateEdges := A.supportRecurringStateEdgeFinset infStates
  refine ⟨stateEdges, ?_, ?_⟩
  · intro edge hedge
    exact
      (A.mem_supportRecurringStateEdgeFinset infStates edge).mp hedge
  · exact
      A.supportWitnessStateEdgesAccepting_of_supportRecurringStateEdgesAccepting
        ((A.supportConfigurationMuller_accepts_iff initialStates word).mp haccepts)

theorem AlternatingParityAutomaton.MacroRun.infStateEdge_mem_supportRecurringStateEdges
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    (run : A.MacroRun initialStates word)
    {edge : APAStateEdge A}
    (hedge : edge ∈ run.infStateEdgeFinset) :
    edge ∈
      A.supportRecurringStateEdges
        ((A.supportConfigurationMullerSkeleton initialStates accepting).InfStates word) := by
  classical
  have hseen : run.StateEdgeSeenInfinitelyOften edge :=
    (run.mem_infStateEdgeFinset edge).mp hedge
  rcases
    A.exists_recurringSupportConfigurationState_of_macroRun_stateEdgeSeen
      accepting run hseen with
    ⟨configState, hconfigRecurring, hedgeConfig⟩
  refine ⟨configState, ?_, hedgeConfig⟩
  exact
    ((A.supportConfigurationMullerSkeleton initialStates accepting).mem_infStateFinset
      word configState).mp hconfigRecurring

/--
If the support-configuration Muller condition accepts a word, then the
recurring individual support-edge graph of any concrete macro-run over that
word satisfies the finite parity witness condition.
-/
theorem AlternatingParityAutomaton.MacroRun.supportWitnessStateEdgesAccepting_of_supportConfigurationMuller_accepts
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (haccepts : (A.supportConfigurationMuller initialStates).Accepts word) :
    A.SupportWitnessStateEdgesAccepting run.infStateEdgeFinset := by
  have haccepting :
      A.SupportRecurringStateEdgesAccepting
        ((A.supportConfigurationMuller initialStates).InfStates word) :=
    (A.supportConfigurationMuller_accepts_iff initialStates word).mp haccepts
  intro path hpath
  exact haccepting path (fun n =>
    by
      have hedgeRecurring :
          (path n, path (n + 1)) ∈
            A.supportRecurringStateEdges
              ((A.supportConfigurationMullerSkeleton
                initialStates
                A.supportConfigurationAcceptingFamily).InfStates word) :=
        run.infStateEdge_mem_supportRecurringStateEdges
          A.supportConfigurationAcceptingFamily (hpath n)
      simpa [AlternatingParityAutomaton.supportConfigurationMuller] using
        hedgeRecurring)

/--
Consequently, the provisional support-configuration Muller acceptance condition
makes every concrete macro-run over the word support-accepting.
-/
theorem AlternatingParityAutomaton.MacroRun.supportAccepting_of_supportConfigurationMuller_accepts
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (haccepts : (A.supportConfigurationMuller initialStates).Accepts word) :
    run.SupportAccepting :=
  run.supportAccepting_of_infStateEdgeFinset_accepting
    (run.supportWitnessStateEdgesAccepting_of_supportConfigurationMuller_accepts
      haccepts)

theorem AlternatingParityAutomaton.MacroRun.SupportPath.exists_tail_supportEdgePath
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    {run : A.MacroRun initialStates word}
    {path : Nat -> A.State}
    (hpath : run.SupportPath path) :
    ∃ base : Nat,
      A.SupportEdgePath
        ((A.supportConfigurationMullerSkeleton initialStates accepting).InfStates word)
        (fun n => path (base + n)) := by
  rcases hpath.eventually_edge_recurring with ⟨base, hbase⟩
  refine ⟨base, ?_⟩
  intro n
  have hedgeInf :
      (path (base + n), path (base + n + 1)) ∈ run.infStateEdgeFinset :=
    hbase (base + n) (Nat.le_add_right base n)
  have hedgeRecurring :
      (path (base + n), path (base + n + 1)) ∈
        A.supportRecurringStateEdges
          ((A.supportConfigurationMullerSkeleton initialStates accepting).InfStates word) :=
    run.infStateEdge_mem_supportRecurringStateEdges accepting hedgeInf
  simpa [Nat.add_assoc] using hedgeRecurring

theorem AlternatingParityAutomaton.MacroRun.SupportPath.exists_tail_min_priority_even_of_mullerAccepts
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    {run : A.MacroRun initialStates word}
    {path : Nat -> A.State}
    (hpath : run.SupportPath path)
    (haccepts : (A.supportConfigurationMuller initialStates).Accepts word) :
    ∃ base : Nat,
      ∃ p : Nat,
        DetParityAutomaton.NatEven p ∧
          A.SupportEdgePathPrioritySeenInfinitelyOften
            (fun n => path (base + n)) p ∧
            ∀ q : Nat,
              A.SupportEdgePathPrioritySeenInfinitelyOften
                (fun n => path (base + n)) q -> p ≤ q := by
  have haccepting :
      A.SupportRecurringStateEdgesAccepting
        ((A.supportConfigurationMuller initialStates).InfStates word) :=
    (A.supportConfigurationMuller_accepts_iff initialStates word).mp haccepts
  rcases
    hpath.exists_tail_supportEdgePath
      A.supportConfigurationAcceptingFamily with
    ⟨base, htail⟩
  have htail' :
      A.SupportEdgePath
        ((A.supportConfigurationMuller initialStates).InfStates word)
        (fun n => path (base + n)) := by
    simpa [AlternatingParityAutomaton.supportConfigurationMuller] using htail
  rcases haccepting (fun n => path (base + n)) htail' with
    ⟨p, hpEven, hpSeen, hpMin⟩
  exact ⟨base, p, hpEven, hpSeen, hpMin⟩

/--
If a macro-state recurs infinitely often on a macro-run, then some recurring
state of the support-edge deterministic skeleton contains that macro-state in
its reachable configuration component.
-/
theorem AlternatingParityAutomaton.exists_recurringSupportConfigurationState_of_macroRun_stateSeen
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    (run : A.MacroRun initialStates word)
    {states : Finset A.State}
    (hseen : run.StateSeenInfinitelyOften states) :
    ∃ configState :
        (A.supportConfigurationMullerSkeleton initialStates accepting).State,
      configState ∈
        (A.supportConfigurationMullerSkeleton initialStates accepting).infStateFinset word ∧
        states ∈ configState.configs := by
  classical
  let muller := A.supportConfigurationMullerSkeleton initialStates accepting
  let targets : Finset muller.State :=
    Finset.univ.filter (fun configState => states ∈ configState.configs)
  have hfreq :
      ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ muller.run word k ∈ targets := by
    intro n
    rcases hseen n with ⟨k, hk, hkstates⟩
    refine ⟨k, hk, ?_⟩
    rw [Finset.mem_filter]
    constructor
    · simp
    · have hmem :
          run.states k ∈ A.macroConfigurationRun initialStates word k :=
        run.states_mem_macroConfigurationRun k
      have hconfigs :
          (muller.run word k).configs =
            A.macroConfigurationRun initialStates word k := by
        exact A.supportConfigurationMullerSkeleton_run_configs
          initialStates accepting word k
      rw [hkstates] at hmem
      rw [hconfigs]
      exact hmem
  rcases
    exists_seenInfinitelyOften_of_frequently_mem_finset_early
      (fun n => muller.run word n) targets hfreq with
    ⟨configState, htarget, hconfigSeen⟩
  refine ⟨configState, ?_, ?_⟩
  · exact
      (muller.mem_infStateFinset word configState).mpr
        (by
          intro n
          exact hconfigSeen n)
  · exact (Finset.mem_filter.mp htarget).2

theorem AlternatingParityAutomaton.MacroRun.infState_mem_supportRecurringMacroStates
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    (run : A.MacroRun initialStates word)
    {states : Finset A.State}
    (hstates : states ∈ run.infStateFinset) :
    states ∈
      A.supportRecurringMacroStates
        ((A.supportConfigurationMullerSkeleton initialStates accepting).InfStates word) := by
  classical
  have hseen : run.StateSeenInfinitelyOften states :=
    (run.mem_infStateFinset states).mp hstates
  rcases
    A.exists_recurringSupportConfigurationState_of_macroRun_stateSeen
      accepting run hseen with
    ⟨configState, hconfigRecurring, hcontains⟩
  refine ⟨configState, ?_, hcontains⟩
  exact
    ((A.supportConfigurationMullerSkeleton initialStates accepting).mem_infStateFinset
      word configState).mp hconfigRecurring

/--
Semantic macro-run acceptance yields an accepting macro-state that is visible
inside a recurring state of the support-edge deterministic skeleton.
-/
theorem AlternatingParityAutomaton.exists_recurringSupportConfigurationState_of_semanticAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    (run : A.MacroRun initialStates word)
    (haccepting : run.SemanticAccepting) :
    ∃ configState :
        (A.supportConfigurationMullerSkeleton initialStates accepting).State,
      configState ∈
        (A.supportConfigurationMullerSkeleton initialStates accepting).infStateFinset word ∧
        ∃ offset : Nat,
          run.states offset ∈ configState.configs ∧
            ∀ state, state ∈ run.states offset ->
              A.AcceptsFrom state (OmegaWord.drop word offset) := by
  classical
  rcases haccepting with ⟨offset, hrecurs, haccepts⟩
  have hseen : run.StateSeenInfinitelyOften (run.states offset) :=
    (run.mem_infStateFinset (run.states offset)).mp hrecurs
  rcases
    A.exists_recurringSupportConfigurationState_of_macroRun_stateSeen
      accepting run hseen with
    ⟨configState, hconfigRecurring, hcontains⟩
  exact ⟨configState, hconfigRecurring, offset, hcontains, haccepts⟩

/--
Specialized support-witness version of the semantic bridge: a semantically
accepting macro-run has a recurring state in the deterministic support-witness
carrier containing an accepting macro-state.
-/
theorem AlternatingParityAutomaton.exists_supportWitnessMuller_recurring_accepting_macroState_of_semanticAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (haccepting : run.SemanticAccepting) :
    ∃ configState : (A.supportWitnessMuller initialStates).State,
      configState ∈ (A.supportWitnessMuller initialStates).infStateFinset word ∧
        ∃ offset : Nat,
          run.states offset ∈ configState.configs ∧
            ∀ state, state ∈ run.states offset ->
              A.AcceptsFrom state (OmegaWord.drop word offset) := by
  rcases
    A.exists_recurringSupportConfigurationState_of_semanticAccepting
      A.supportWitnessAcceptingFamily run haccepting with
    ⟨configState, hrecurring, offset, hcontains, haccepts⟩
  refine ⟨configState, ?_, offset, hcontains, haccepts⟩
  exact
    ((A.supportWitnessMuller initialStates).mem_infStateFinset
      word configState).mpr
      (by simpa [AlternatingParityAutomaton.supportWitnessMuller] using hrecurring)

/--
APA acceptance places the run-tree-derived semantic macro-state inside a
recurring support-configuration state of the deterministic support-witness
Muller skeleton.
-/
theorem AlternatingParityAutomaton.exists_supportWitnessMuller_recurring_accepting_macroState_of_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (haccepts : A.Accepts word) :
    ∃ run : A.MacroRun {A.initial} word,
      run.SemanticAccepting ∧
        ∃ configState : (A.supportWitnessMuller {A.initial}).State,
          configState ∈
              (A.supportWitnessMuller {A.initial}).infStateFinset word ∧
            ∃ offset : Nat,
              run.states offset ∈ configState.configs ∧
                ∀ state, state ∈ run.states offset ->
                  A.AcceptsFrom state (OmegaWord.drop word offset) := by
  rcases haccepts with ⟨runTree, hrunTreeAccepting⟩
  let macroRun := runTree.levelMacroRun
  have hsemantic : macroRun.SemanticAccepting :=
    AlternatingParityAutomaton.levelMacroRun_semanticAccepting
      runTree hrunTreeAccepting
  rcases
    A.exists_supportWitnessMuller_recurring_accepting_macroState_of_semanticAccepting
      macroRun hsemantic with
    ⟨configState, hconfigRecurring, offset, hcontains, hacceptsSuffix⟩
  exact
    ⟨macroRun, hsemantic, configState, hconfigRecurring,
      offset, hcontains, hacceptsSuffix⟩

/--
State-wise version of the previous bridge.  Acceptance from an arbitrary APA
state places the corresponding singleton macro-run inside a recurring
support-witness carrier state, with the recurring macro-state carrying
accepting suffixes for all of its states.
-/
theorem AlternatingParityAutomaton.exists_supportWitnessMuller_recurring_accepting_macroState_of_acceptsFrom
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (haccepts : A.AcceptsFrom root word) :
    ∃ run : A.MacroRun {root} word,
      run.SemanticAccepting ∧
        ∃ configState : (A.supportWitnessMuller {root}).State,
          configState ∈
              (A.supportWitnessMuller {root}).infStateFinset word ∧
            ∃ offset : Nat,
              run.states offset ∈ configState.configs ∧
                ∀ state, state ∈ run.states offset ->
                  A.AcceptsFrom state (OmegaWord.drop word offset) := by
  have hinitial :
      ∀ state, state ∈ ({root} : Finset A.State) ->
        A.AcceptsFrom state word := by
    intro state hstate
    have hstateRoot : state = root := by
      simpa using hstate
    subst state
    exact haccepts
  rcases
    A.exists_semanticAccepting_macroRun_of_accepts_all
      ({root} : Finset A.State) word hinitial with
    ⟨macroRun, hsemantic⟩
  rcases
    A.exists_supportWitnessMuller_recurring_accepting_macroState_of_semanticAccepting
      macroRun hsemantic with
    ⟨configState, hconfigRecurring, offset, hcontains, hacceptsSuffix⟩
  exact
    ⟨macroRun, hsemantic, configState, hconfigRecurring,
      offset, hcontains, hacceptsSuffix⟩

/--
If the APA accepts from `root`, then the state-tagged support-witness carrier
has a recurring state over the corresponding singleton initial support
configuration whose second component contains a macro-state with accepting
suffixes.  This is the state-wise form of the necessary recurrent-state bridge
used by the support-witness determinization route.
-/
theorem AlternatingParityAutomaton.exists_stateSupportWitnessMuller_recurring_accepting_macroState_of_acceptsFrom
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (haccepts : A.AcceptsFrom root word) :
    ∃ run : A.MacroRun {root} word,
      run.SemanticAccepting ∧
        ∃ taggedState : (A.stateSupportWitnessMuller).State,
          taggedState ∈
              (A.stateSupportWitnessMuller).InfStatesFrom
                (root, APASupportConfigurationState.initial {root}) word ∧
            ∃ offset : Nat,
              run.states offset ∈ taggedState.2.configs ∧
                ∀ state, state ∈ run.states offset ->
                  A.AcceptsFrom state (OmegaWord.drop word offset) := by
  rcases
    A.exists_supportWitnessMuller_recurring_accepting_macroState_of_acceptsFrom
      root word haccepts with
    ⟨run, hsemantic, configState, hconfigRecurring,
      offset, hcontains, hacceptsSuffix⟩
  refine
    ⟨run, hsemantic, (root, configState), ?_,
      offset, hcontains, hacceptsSuffix⟩
  exact
    (A.stateSupportWitnessMuller_infStatesFrom_singleton_snd_iff
      root word configState).mp
      (((A.supportWitnessMuller {root}).mem_infStateFinset
        word configState).mp hconfigRecurring)

/--
If a finite target set is visited arbitrarily far along a stream over a finite
type, then some target element is visited infinitely often.
-/
theorem exists_seenInfinitelyOften_of_frequently_mem_finset
    {α : Type u}
    [Fintype α]
    (stream : Nat -> α)
    (targets : Finset α)
    (hfreq : ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ stream k ∈ targets) :
    ∃ target : α,
      target ∈ targets ∧
        ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ stream k = target := by
  classical
  by_contra hnone
  push Not at hnone
  have htargetBound :
      ∀ target ∈ targets,
        ∃ n : Nat, ∀ k : Nat, n ≤ k -> stream k ≠ target := by
    intro target htarget
    exact hnone target htarget
  choose bound hbound using htargetBound
  let boundOf : α -> Nat := fun target =>
    if htarget : target ∈ targets then bound target htarget else 0
  rcases hfreq (targets.sup boundOf) with ⟨k, hk, hkTarget⟩
  have hle : boundOf (stream k) ≤ targets.sup boundOf :=
    Finset.le_sup hkTarget
  have hboundOf :
      boundOf (stream k) = bound (stream k) hkTarget := by
    simp [boundOf, hkTarget]
  exact hbound (stream k) hkTarget k
    (by
      rw [← hboundOf]
      exact le_trans hle hk)
    rfl

/--
If a macro-state recurs infinitely often on a macro-run, then some recurring
state of the deterministic macro-configuration skeleton contains that
macro-state in its reachable configuration component.
-/
theorem AlternatingParityAutomaton.exists_recurringConfigurationState_of_macroRun_stateSeen
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APAMacroConfigurationState A)))
    (run : A.MacroRun initialStates word)
    {states : Finset A.State}
    (hseen : run.StateSeenInfinitelyOften states) :
    ∃ configState :
        (A.macroConfigurationMullerSkeleton initialStates accepting).State,
      configState ∈
        (A.macroConfigurationMullerSkeleton initialStates accepting).infStateFinset word ∧
        states ∈ configState.configs := by
  classical
  let muller := A.macroConfigurationMullerSkeleton initialStates accepting
  let targets : Finset muller.State :=
    Finset.univ.filter (fun configState => states ∈ configState.configs)
  have hfreq :
      ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ muller.run word k ∈ targets := by
    intro n
    rcases hseen n with ⟨k, hk, hkstates⟩
    refine ⟨k, hk, ?_⟩
    rw [Finset.mem_filter]
    constructor
    · simp
    · have hmem :
          run.states k ∈ A.macroConfigurationRun initialStates word k :=
        run.states_mem_macroConfigurationRun k
      have hconfigs :
          (muller.run word k).configs =
            A.macroConfigurationRun initialStates word k := by
        exact A.macroConfigurationMullerSkeleton_run_configs
          initialStates accepting word k
      rw [hkstates] at hmem
      rw [hconfigs]
      exact hmem
  rcases
    exists_seenInfinitelyOften_of_frequently_mem_finset
      (fun n => muller.run word n) targets hfreq with
    ⟨configState, htarget, hconfigSeen⟩
  refine ⟨configState, ?_, ?_⟩
  · exact
      (muller.mem_infStateFinset word configState).mpr
        (by
          intro n
          exact hconfigSeen n)
  · exact (Finset.mem_filter.mp htarget).2

/-- A macro-transition edge occurs infinitely often along a macro-run. -/
def AlternatingParityAutomaton.MacroRun.EdgeSeenInfinitelyOften
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (edge : APAMacroEdge A) :
    Prop :=
  ∀ n : Nat,
    ∃ k : Nat,
      n ≤ k ∧ (run.states k, run.states (k + 1)) = edge

/-- The finite set of macro-transition edges seen infinitely often on a macro-run. -/
noncomputable def AlternatingParityAutomaton.MacroRun.infEdgeFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word) :
    Finset (APAMacroEdge A) := by
  classical
  exact Finset.univ.filter (fun edge => run.EdgeSeenInfinitelyOften edge)

@[simp]
theorem AlternatingParityAutomaton.MacroRun.mem_infEdgeFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (edge : APAMacroEdge A) :
    edge ∈ run.infEdgeFinset ↔ run.EdgeSeenInfinitelyOften edge := by
  classical
  simp [MacroRun.infEdgeFinset]

/-- The source of a recurring macro-edge is a recurring macro-state. -/
theorem AlternatingParityAutomaton.MacroRun.infEdge_source_mem_infStateFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    {edge : APAMacroEdge A}
    (hedge : edge ∈ run.infEdgeFinset) :
    edge.1 ∈ run.infStateFinset := by
  have hseen : run.EdgeSeenInfinitelyOften edge :=
    (run.mem_infEdgeFinset edge).mp hedge
  rw [run.mem_infStateFinset]
  intro n
  rcases hseen n with ⟨k, hk, hkedge⟩
  refine ⟨k, hk, ?_⟩
  exact congrArg Prod.fst hkedge

/-- The target of a recurring macro-edge is a recurring macro-state. -/
theorem AlternatingParityAutomaton.MacroRun.infEdge_target_mem_infStateFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    {edge : APAMacroEdge A}
    (hedge : edge ∈ run.infEdgeFinset) :
    edge.2 ∈ run.infStateFinset := by
  have hseen : run.EdgeSeenInfinitelyOften edge :=
    (run.mem_infEdgeFinset edge).mp hedge
  rw [run.mem_infStateFinset]
  intro n
  rcases hseen n with ⟨k, hk, hkedge⟩
  refine ⟨k + 1, Nat.le_trans hk (Nat.le_succ k), ?_⟩
  exact congrArg Prod.snd hkedge

/--
Every recurring macro-state has at least one outgoing recurring macro-edge in
the same macro-run.
-/
theorem AlternatingParityAutomaton.MacroRun.exists_infEdge_from_stateSeen
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    {states : Finset A.State}
    (hseen : run.StateSeenInfinitelyOften states) :
    ∃ edge : APAMacroEdge A,
      edge ∈ run.infEdgeFinset ∧ edge.1 = states := by
  classical
  let targets : Finset (APAMacroEdge A) :=
    Finset.univ.filter (fun edge => edge.1 = states)
  have hfreq :
      ∀ n : Nat,
        ∃ k : Nat,
          n ≤ k ∧ (run.states k, run.states (k + 1)) ∈ targets := by
    intro n
    rcases hseen n with ⟨k, hk, hkstates⟩
    refine ⟨k, hk, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨by simp, hkstates⟩
  rcases
    exists_seenInfinitelyOften_of_frequently_mem_finset
      (fun n => (run.states n, run.states (n + 1))) targets hfreq with
    ⟨edge, hedgeTarget, hedgeSeen⟩
  refine ⟨edge, ?_, ?_⟩
  · exact (run.mem_infEdgeFinset edge).mpr hedgeSeen
  · exact (Finset.mem_filter.mp hedgeTarget).2

/--
Every macro-state in the finite infinity set has an outgoing recurring
macro-edge whose target is again in the finite infinity set.
-/
theorem AlternatingParityAutomaton.MacroRun.exists_infEdge_from_infStateFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    {states : Finset A.State}
    (hstates : states ∈ run.infStateFinset) :
    ∃ edge : APAMacroEdge A,
      edge ∈ run.infEdgeFinset ∧
        edge.1 = states ∧ edge.2 ∈ run.infStateFinset := by
  have hseen : run.StateSeenInfinitelyOften states :=
    (run.mem_infStateFinset states).mp hstates
  rcases run.exists_infEdge_from_stateSeen hseen with
    ⟨edge, hedge, hsource⟩
  exact ⟨edge, hedge, hsource, run.infEdge_target_mem_infStateFinset hedge⟩

/--
Every recurring individual support edge is carried by some recurring macro-edge
of the same macro-run.
-/
theorem AlternatingParityAutomaton.MacroRun.exists_infEdge_of_infStateEdge
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    {edge : APAStateEdge A}
    (hedge : edge ∈ run.infStateEdgeFinset) :
    ∃ macroEdge : APAMacroEdge A,
      macroEdge ∈ run.infEdgeFinset ∧
        edge.1 ∈ macroEdge.1 ∧ edge.2 ∈ macroEdge.2 := by
  classical
  have hseen : run.StateEdgeSeenInfinitelyOften edge :=
    (run.mem_infStateEdgeFinset edge).mp hedge
  let stream : Nat -> APAMacroEdge A × Finset (APAStateEdge A) :=
    fun n => ((run.states n, run.states (n + 1)), run.stepStateEdges n)
  let targets : Finset (APAMacroEdge A × Finset (APAStateEdge A)) :=
    Finset.univ.filter (fun item => edge ∈ item.2)
  have hfreq :
      ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ stream k ∈ targets := by
    intro n
    rcases hseen n with ⟨k, hk, hedgeStep⟩
    refine ⟨k, hk, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨by simp, hedgeStep⟩
  rcases
    exists_seenInfinitelyOften_of_frequently_mem_finset
      stream targets hfreq with
    ⟨item, hitemTarget, hitemSeen⟩
  refine ⟨item.1, ?_, ?_, ?_⟩
  · exact (run.mem_infEdgeFinset item.1).mpr
      (by
        intro n
        rcases hitemSeen n with ⟨k, hk, hkitem⟩
        exact ⟨k, hk, congrArg Prod.fst hkitem⟩)
  · rcases hitemSeen 0 with ⟨k, _hk, hkitem⟩
    have hedgeItem : edge ∈ item.2 := (Finset.mem_filter.mp hitemTarget).2
    have hstateEdges : item.2 = run.stepStateEdges k := by
      exact (congrArg Prod.snd hkitem).symm
    have hmacro : item.1 = (run.states k, run.states (k + 1)) := by
      exact (congrArg Prod.fst hkitem).symm
    rw [hstateEdges] at hedgeItem
    have hsource := run.stepStateEdges_source_mem k hedgeItem
    simpa [hmacro] using hsource
  · rcases hitemSeen 0 with ⟨k, _hk, hkitem⟩
    have hedgeItem : edge ∈ item.2 := (Finset.mem_filter.mp hitemTarget).2
    have hstateEdges : item.2 = run.stepStateEdges k := by
      exact (congrArg Prod.snd hkitem).symm
    have hmacro : item.1 = (run.states k, run.states (k + 1)) := by
      exact (congrArg Prod.fst hkitem).symm
    rw [hstateEdges] at hedgeItem
    have htarget := run.stepStateEdges_target_mem k hedgeItem
    simpa [hmacro] using htarget

/--
If a macro-transition edge recurs infinitely often on a macro-run, then some
recurring state of the deterministic macro-configuration skeleton contains that
edge in its edge component.
-/
theorem AlternatingParityAutomaton.exists_recurringConfigurationState_of_macroRun_edgeSeen
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APAMacroConfigurationState A)))
    (run : A.MacroRun initialStates word)
    {edge : APAMacroEdge A}
    (hseen : run.EdgeSeenInfinitelyOften edge) :
    ∃ configState :
        (A.macroConfigurationMullerSkeleton initialStates accepting).State,
      configState ∈
        (A.macroConfigurationMullerSkeleton initialStates accepting).infStateFinset word ∧
        edge ∈ configState.edges := by
  classical
  let muller := A.macroConfigurationMullerSkeleton initialStates accepting
  let targets : Finset muller.State :=
    Finset.univ.filter (fun configState => edge ∈ configState.edges)
  have hfreq :
      ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ muller.run word k ∈ targets := by
    intro n
    rcases hseen n with ⟨k, hk, hkedge⟩
    refine ⟨k + 1, Nat.le_trans hk (Nat.le_succ k), ?_⟩
    rw [Finset.mem_filter]
    constructor
    · simp
    · have hedge :
          (run.states k, run.states (k + 1)) ∈
            A.macroConfigurationEdgeRun initialStates word k :=
        run.edge_mem_macroConfigurationEdgeRun k
      have hedges :
          (muller.run word (k + 1)).edges =
            A.macroConfigurationEdgeRun initialStates word k := by
        exact A.macroConfigurationMullerSkeleton_run_edges_succ
          initialStates accepting word k
      rw [hkedge] at hedge
      rw [hedges]
      exact hedge
  rcases
    exists_seenInfinitelyOften_of_frequently_mem_finset
      (fun n => muller.run word n) targets hfreq with
    ⟨configState, htarget, hconfigSeen⟩
  refine ⟨configState, ?_, ?_⟩
  · exact
      (muller.mem_infStateFinset word configState).mpr
        (by
          intro n
          exact hconfigSeen n)
  · exact (Finset.mem_filter.mp htarget).2

/--
The recurring configuration components of the deterministic
macro-configuration skeleton are exactly the recurring configurations of the
plain `macroConfigurationRun`.
-/
theorem AlternatingParityAutomaton.mem_macroConfigurationMullerSkeleton_infStateFinset_image_configs
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (initialStates : Finset A.State)
    (accepting : Set (Set (APAMacroConfigurationState A)))
    (word : OmegaWord Alphabet)
    (configs : Finset (Finset A.State)) :
    (∃ configState :
        (A.macroConfigurationMullerSkeleton initialStates accepting).State,
      configState ∈
        (A.macroConfigurationMullerSkeleton initialStates accepting).infStateFinset word ∧
        configState.configs = configs) ↔
      ∀ n : Nat,
        ∃ k : Nat,
          n ≤ k ∧ A.macroConfigurationRun initialStates word k = configs := by
  classical
  let muller := A.macroConfigurationMullerSkeleton initialStates accepting
  constructor
  · intro hconfigs n
    rcases hconfigs with ⟨configState, hseenFin, hconfig⟩
    have hseen : muller.StateSeenInfinitelyOften word configState :=
      (muller.mem_infStateFinset word configState).mp hseenFin
    rcases hseen n with ⟨k, hk, hkstate⟩
    refine ⟨k, hk, ?_⟩
    have hrun :
        (muller.run word k).configs =
          A.macroConfigurationRun initialStates word k := by
      exact A.macroConfigurationMullerSkeleton_run_configs
        initialStates accepting word k
    have hrun' := hrun
    have hkstateRun : muller.run word k = configState := by
      simpa [DetMullerAutomaton.run] using hkstate
    rw [hkstateRun] at hrun'
    exact hrun'.symm.trans hconfig
  · intro hconfigs
    let targets : Finset muller.State :=
      Finset.univ.filter (fun configState => configState.configs = configs)
    have hfreq :
        ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ muller.run word k ∈ targets := by
      intro n
      rcases hconfigs n with ⟨k, hk, hkconfigs⟩
      refine ⟨k, hk, ?_⟩
      rw [Finset.mem_filter]
      constructor
      · simp
      · have hrun :
            (muller.run word k).configs =
              A.macroConfigurationRun initialStates word k := by
          exact A.macroConfigurationMullerSkeleton_run_configs
            initialStates accepting word k
        simpa [muller, hkconfigs] using hrun
    rcases
      exists_seenInfinitelyOften_of_frequently_mem_finset
        (fun n => muller.run word n) targets hfreq with
      ⟨configState, htarget, hseen⟩
    refine ⟨configState, ?_, ?_⟩
    · exact
        (muller.mem_infStateFinset word configState).mpr
          (by
            intro n
            exact hseen n)
    · exact (Finset.mem_filter.mp htarget).2

/--
If a macro-transition edge recurs infinitely often on a macro-run, then some
recurring state of the support-edge deterministic skeleton contains that edge
in its macro-edge component.
-/
theorem AlternatingParityAutomaton.exists_recurringSupportConfigurationState_of_macroRun_edgeSeen
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    (run : A.MacroRun initialStates word)
    {edge : APAMacroEdge A}
    (hseen : run.EdgeSeenInfinitelyOften edge) :
    ∃ configState :
        (A.supportConfigurationMullerSkeleton initialStates accepting).State,
      configState ∈
        (A.supportConfigurationMullerSkeleton initialStates accepting).infStateFinset word ∧
        edge ∈ configState.macroEdges := by
  classical
  let muller := A.supportConfigurationMullerSkeleton initialStates accepting
  let targets : Finset muller.State :=
    Finset.univ.filter (fun configState => edge ∈ configState.macroEdges)
  have hfreq :
      ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ muller.run word k ∈ targets := by
    intro n
    rcases hseen n with ⟨k, hk, hkedge⟩
    refine ⟨k + 1, Nat.le_trans hk (Nat.le_succ k), ?_⟩
    rw [Finset.mem_filter]
    constructor
    · simp
    · have hedge :
          (run.states k, run.states (k + 1)) ∈
            A.macroConfigurationEdgeRun initialStates word k :=
        run.edge_mem_macroConfigurationEdgeRun k
      have hedges :
          (muller.run word (k + 1)).macroEdges =
            A.macroConfigurationEdgeRun initialStates word k := by
        exact A.supportConfigurationMullerSkeleton_run_macroEdges_succ
          initialStates accepting word k
      rw [hkedge] at hedge
      rw [hedges]
      exact hedge
  rcases
    exists_seenInfinitelyOften_of_frequently_mem_finset
      (fun n => muller.run word n) targets hfreq with
    ⟨configState, htarget, hconfigSeen⟩
  refine ⟨configState, ?_, ?_⟩
  · exact
      (muller.mem_infStateFinset word configState).mpr
        (by
          intro n
          exact hconfigSeen n)
  · exact (Finset.mem_filter.mp htarget).2

theorem AlternatingParityAutomaton.MacroRun.infEdge_mem_supportRecurringMacroEdges
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    (run : A.MacroRun initialStates word)
    {edge : APAMacroEdge A}
    (hedge : edge ∈ run.infEdgeFinset) :
    edge ∈
      A.supportRecurringMacroEdges
        ((A.supportConfigurationMullerSkeleton initialStates accepting).InfStates word) := by
  classical
  have hseen : run.EdgeSeenInfinitelyOften edge :=
    (run.mem_infEdgeFinset edge).mp hedge
  rcases
    A.exists_recurringSupportConfigurationState_of_macroRun_edgeSeen
      accepting run hseen with
    ⟨configState, hconfigRecurring, hedgeConfig⟩
  refine ⟨configState, ?_, hedgeConfig⟩
  exact
    ((A.supportConfigurationMullerSkeleton initialStates accepting).mem_infStateFinset
      word configState).mp hconfigRecurring

/--
A macro-run whose recurring support-edge graph is parity accepting yields the
existential recurrent witness expected by the support-carrier Muller family.
-/
theorem AlternatingParityAutomaton.MacroRun.supportRecurrentWitness_of_recurringSupportAccepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    (run : A.MacroRun initialStates word)
    (haccepting : A.SupportWitnessStateEdgesAccepting run.infStateEdgeFinset) :
    A.SupportRecurrentWitness
      ((A.supportConfigurationMullerSkeleton initialStates accepting).InfStates word) := by
  classical
  refine
    ⟨run.infStateFinset,
      run.infEdgeFinset,
      run.infStateEdgeFinset,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      haccepting⟩
  · exact run.infStateFinset_nonempty
  · intro states hstates
    exact run.infState_mem_supportRecurringMacroStates accepting hstates
  · intro edge hedge
    exact run.infEdge_mem_supportRecurringMacroEdges accepting hedge
  · intro edge hedge
    exact run.infStateEdge_mem_supportRecurringStateEdges accepting hedge
  · intro edge hedge
    exact
      ⟨run.infEdge_source_mem_infStateFinset hedge,
        run.infEdge_target_mem_infStateFinset hedge⟩
  · intro states hstates
    exact run.exists_infEdge_from_infStateFinset hstates
  · intro edge hedge
    rcases run.exists_infEdge_of_infStateEdge hedge with
      ⟨macroEdge, hmacroEdge, hsource, htarget⟩
    refine ⟨?_, ?_⟩
    · exact
        ⟨macroEdge.1,
          run.infEdge_source_mem_infStateFinset hmacroEdge,
          hsource⟩
    · exact
        ⟨macroEdge.2,
          run.infEdge_target_mem_infStateFinset hmacroEdge,
          htarget⟩

/--
Every explicitly chosen individual support edge of an edge-witnessed macro-run
is present in the deterministic support-edge stream at that step.
-/
theorem AlternatingParityAutomaton.EdgeWitnessedMacroRun.stateEdge_mem_macroConfigurationStateEdgeRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (n : Nat)
    {edge : APAStateEdge A}
    (hedge : edge ∈ run.stateEdges n) :
    edge ∈ A.macroConfigurationStateEdgeRun initialStates word n := by
  exact
    (A.mem_macroConfigurationStateEdgeRun initialStates word n edge).mpr
      ⟨run.toMacroRun.states n,
        run.toMacroRun.states_mem_macroConfigurationRun n,
        run.toMacroRun.states (n + 1),
        run.stateEdges n,
        run.step_stateEdges_transition n,
        hedge⟩

/--
If an explicitly chosen support edge recurs infinitely often, then some
recurring state of the support-edge deterministic skeleton contains it.
-/
theorem AlternatingParityAutomaton.exists_recurringSupportConfigurationState_of_edgeWitnessed_stateEdgeSeen
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    (run : A.EdgeWitnessedMacroRun initialStates word)
    {edge : APAStateEdge A}
    (hseen : run.StateEdgeSeenInfinitelyOften edge) :
    ∃ configState :
        (A.supportConfigurationMullerSkeleton initialStates accepting).State,
      configState ∈
        (A.supportConfigurationMullerSkeleton initialStates accepting).infStateFinset word ∧
        edge ∈ configState.stateEdges := by
  classical
  let muller := A.supportConfigurationMullerSkeleton initialStates accepting
  let targets : Finset muller.State :=
    Finset.univ.filter (fun configState => edge ∈ configState.stateEdges)
  have hfreq :
      ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ muller.run word k ∈ targets := by
    intro n
    rcases hseen n with ⟨k, hk, hedge⟩
    refine ⟨k + 1, Nat.le_trans hk (Nat.le_succ k), ?_⟩
    rw [Finset.mem_filter]
    constructor
    · simp
    · have hedgeRun :
          edge ∈ A.macroConfigurationStateEdgeRun initialStates word k :=
        run.stateEdge_mem_macroConfigurationStateEdgeRun k hedge
      have hedges :
          (muller.run word (k + 1)).stateEdges =
            A.macroConfigurationStateEdgeRun initialStates word k := by
        exact A.supportConfigurationMullerSkeleton_run_stateEdges_succ
          initialStates accepting word k
      rw [hedges]
      exact hedgeRun
  rcases
    exists_seenInfinitelyOften_of_frequently_mem_finset
      (fun n => muller.run word n) targets hfreq with
    ⟨configState, htarget, hconfigSeen⟩
  refine ⟨configState, ?_, ?_⟩
  · exact
      (muller.mem_infStateFinset word configState).mpr
        (by
          intro n
          exact hconfigSeen n)
  · exact (Finset.mem_filter.mp htarget).2

theorem AlternatingParityAutomaton.EdgeWitnessedMacroRun.infStateEdge_mem_supportRecurringStateEdges
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    (run : A.EdgeWitnessedMacroRun initialStates word)
    {edge : APAStateEdge A}
    (hedge : edge ∈ run.infStateEdgeFinset) :
    edge ∈
      A.supportRecurringStateEdges
        ((A.supportConfigurationMullerSkeleton initialStates accepting).InfStates word) := by
  have hseen : run.StateEdgeSeenInfinitelyOften edge :=
    (run.mem_infStateEdgeFinset edge).mp hedge
  rcases
    A.exists_recurringSupportConfigurationState_of_edgeWitnessed_stateEdgeSeen
      accepting run hseen with
    ⟨configState, hconfigRecurring, hedgeConfig⟩
  refine ⟨configState, ?_, hedgeConfig⟩
  exact
    ((A.supportConfigurationMullerSkeleton initialStates accepting).mem_infStateFinset
      word configState).mp hconfigRecurring

/--
Every recurring explicit individual support edge is carried by some recurring
macro-edge of the underlying macro-run.
-/
theorem AlternatingParityAutomaton.EdgeWitnessedMacroRun.exists_infEdge_of_infStateEdge
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    {edge : APAStateEdge A}
    (hedge : edge ∈ run.infStateEdgeFinset) :
    ∃ macroEdge : APAMacroEdge A,
      macroEdge ∈ run.toMacroRun.infEdgeFinset ∧
        edge.1 ∈ macroEdge.1 ∧ edge.2 ∈ macroEdge.2 := by
  classical
  have hseen : run.StateEdgeSeenInfinitelyOften edge :=
    (run.mem_infStateEdgeFinset edge).mp hedge
  let stream : Nat -> APAMacroEdge A × Finset (APAStateEdge A) :=
    fun n => ((run.toMacroRun.states n, run.toMacroRun.states (n + 1)),
      run.stateEdges n)
  let targets : Finset (APAMacroEdge A × Finset (APAStateEdge A)) :=
    Finset.univ.filter (fun item => edge ∈ item.2)
  have hfreq :
      ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ stream k ∈ targets := by
    intro n
    rcases hseen n with ⟨k, hk, hedgeStep⟩
    refine ⟨k, hk, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨by simp, hedgeStep⟩
  rcases
    exists_seenInfinitelyOften_of_frequently_mem_finset
      stream targets hfreq with
    ⟨item, hitemTarget, hitemSeen⟩
  refine ⟨item.1, ?_, ?_, ?_⟩
  · exact (run.toMacroRun.mem_infEdgeFinset item.1).mpr
      (by
        intro n
        rcases hitemSeen n with ⟨k, hk, hkitem⟩
        exact ⟨k, hk, congrArg Prod.fst hkitem⟩)
  · rcases hitemSeen 0 with ⟨k, _hk, hkitem⟩
    have hedgeItem : edge ∈ item.2 := (Finset.mem_filter.mp hitemTarget).2
    have hstateEdges : item.2 = run.stateEdges k := by
      exact (congrArg Prod.snd hkitem).symm
    have hmacro : item.1 =
        (run.toMacroRun.states k, run.toMacroRun.states (k + 1)) := by
      exact (congrArg Prod.fst hkitem).symm
    rw [hstateEdges] at hedgeItem
    have hsource := run.stateEdges_source_mem k hedgeItem
    simpa [hmacro] using hsource
  · rcases hitemSeen 0 with ⟨k, _hk, hkitem⟩
    have hedgeItem : edge ∈ item.2 := (Finset.mem_filter.mp hitemTarget).2
    have hstateEdges : item.2 = run.stateEdges k := by
      exact (congrArg Prod.snd hkitem).symm
    have hmacro : item.1 =
        (run.toMacroRun.states k, run.toMacroRun.states (k + 1)) := by
      exact (congrArg Prod.fst hkitem).symm
    rw [hstateEdges] at hedgeItem
    have htarget := run.stateEdges_target_mem k hedgeItem
    simpa [hmacro] using htarget

/--
An edge-witnessed macro-run whose explicit recurring support-edge graph is
parity accepting yields the support-carrier recurrent witness.
-/
theorem AlternatingParityAutomaton.EdgeWitnessedMacroRun.supportRecurrentWitness_of_recurringSupportAccepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APASupportConfigurationState A)))
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (haccepting : A.SupportWitnessStateEdgesAccepting run.infStateEdgeFinset) :
    A.SupportRecurrentWitness
      ((A.supportConfigurationMullerSkeleton initialStates accepting).InfStates word) := by
  classical
  refine
    ⟨run.toMacroRun.infStateFinset,
      run.toMacroRun.infEdgeFinset,
      run.infStateEdgeFinset,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      haccepting⟩
  · exact run.toMacroRun.infStateFinset_nonempty
  · intro states hstates
    exact run.toMacroRun.infState_mem_supportRecurringMacroStates accepting hstates
  · intro edge hedge
    exact run.toMacroRun.infEdge_mem_supportRecurringMacroEdges accepting hedge
  · intro edge hedge
    exact run.infStateEdge_mem_supportRecurringStateEdges accepting hedge
  · intro edge hedge
    exact
      ⟨run.toMacroRun.infEdge_source_mem_infStateFinset hedge,
        run.toMacroRun.infEdge_target_mem_infStateFinset hedge⟩
  · intro states hstates
    exact run.toMacroRun.exists_infEdge_from_infStateFinset hstates
  · intro edge hedge
    rcases run.exists_infEdge_of_infStateEdge hedge with
      ⟨macroEdge, hmacroEdge, hsource, htarget⟩
    refine ⟨?_, ?_⟩
    · exact
        ⟨macroEdge.1,
          run.toMacroRun.infEdge_source_mem_infStateFinset hmacroEdge,
          hsource⟩
    · exact
        ⟨macroEdge.2,
          run.toMacroRun.infEdge_target_mem_infStateFinset hmacroEdge,
          htarget⟩

/--
A concrete edge-witnessed macro-run whose explicit recurring support-edge graph
is parity accepting makes the witness-based support Muller automaton accept.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_accepts_of_edgeWitnessedMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.EdgeWitnessedMacroRun initialStates word)
    (haccepting : A.SupportWitnessStateEdgesAccepting run.infStateEdgeFinset) :
    (A.supportWitnessMuller initialStates).Accepts word := by
  have hwitness :
      A.SupportRecurrentWitness
        ((A.supportWitnessMuller initialStates).InfStates word) := by
    simpa [AlternatingParityAutomaton.supportWitnessMuller] using
      run.supportRecurrentWitness_of_recurringSupportAccepting
        A.supportWitnessAcceptingFamily haccepting
  exact
    (A.supportWitnessMuller_accepts_iff initialStates word).mpr hwitness

/--
Concrete target for the APA-to-support-witness completeness proof.

Once the recurring explicit state-edge graph extracted from an accepting run
tree is shown parity accepting, the support-witness Muller automaton accepts.
The remaining mathematical obligation is exactly the construction of
`haccepting` from `runTree.Accepting`.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_accepts_of_realizedEdgeWitnessedMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {word : OmegaWord Alphabet}
    (runTree : A.Run word)
    (haccepting :
      A.SupportWitnessStateEdgesAccepting
        runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) :
    (A.supportWitnessMuller {A.initial}).Accepts word :=
  A.supportWitnessMuller_accepts_of_edgeWitnessedMacroRun
    runTree.realizedEdgeWitnessedMacroRun haccepting

/--
Conditional APA-completeness bridge for the support-witness Muller automaton.
The only remaining condition is the branch-realizability/coherence of every
infinite path through the explicit recurring edge graph extracted from the
accepting run tree.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_accepts_of_acceptingRun_branchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {word : OmegaWord Alphabet}
    (runTree : A.Run word)
    (haccepting : runTree.Accepting)
    (hrealizable :
      ∀ path : Nat -> A.State,
        (∀ n : Nat,
          (path n, path (n + 1)) ∈
            runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
          ∃ branch : Nat -> Nat, runTree.RealizesStatePath path branch) :
    (A.supportWitnessMuller {A.initial}).Accepts word :=
  A.supportWitnessMuller_accepts_of_realizedEdgeWitnessedMacroRun
    runTree
    (runTree.realizedEdgeWitnessedMacroRun_supportWitnessStateEdgesAccepting_of_branchRealizable
      haccepting hrealizable)

/--
Tail-realization version of
`supportWitnessMuller_accepts_of_acceptingRun_branchRealizable`.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_accepts_of_acceptingRun_tailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {word : OmegaWord Alphabet}
    (runTree : A.Run word)
    (haccepting : runTree.Accepting)
    (hrealizable :
      ∀ path : Nat -> A.State,
        (∀ n : Nat,
          (path n, path (n + 1)) ∈
            runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
          ∃ branch : Nat -> Nat,
            ∃ offset : Nat,
              runTree.ActiveBranch branch ∧
                ∀ n : Nat,
                  runTree.stateAt (branchPrefix branch (offset + n)) = path n) :
    (A.supportWitnessMuller {A.initial}).Accepts word :=
  A.supportWitnessMuller_accepts_of_realizedEdgeWitnessedMacroRun
    runTree
    (runTree.realizedEdgeWitnessedMacroRun_supportWitnessStateEdgesAccepting_of_tailBranchRealizable
      haccepting hrealizable)

/--
If every accepting APA run tree has branch-realizable explicit recurring edge
paths, ordinary APA acceptance implies acceptance by the support-witness Muller
automaton.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_accepts_of_accepts_branchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (haccepts : A.Accepts word)
    (hrealizable :
      ∀ runTree : A.Run word,
        runTree.Accepting ->
          ∀ path : Nat -> A.State,
            (∀ n : Nat,
              (path n, path (n + 1)) ∈
                runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
              ∃ branch : Nat -> Nat, runTree.RealizesStatePath path branch) :
    (A.supportWitnessMuller {A.initial}).Accepts word := by
  rcases haccepts with ⟨runTree, hrunTreeAccepting⟩
  exact A.supportWitnessMuller_accepts_of_acceptingRun_branchRealizable
    runTree hrunTreeAccepting (hrealizable runTree hrunTreeAccepting)

/--
Tail-realization version of
`supportWitnessMuller_accepts_of_accepts_branchRealizable`.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_accepts_of_accepts_tailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (haccepts : A.Accepts word)
    (hrealizable :
      ∀ runTree : A.Run word,
        runTree.Accepting ->
          ∀ path : Nat -> A.State,
            (∀ n : Nat,
              (path n, path (n + 1)) ∈
                runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
              ∃ branch : Nat -> Nat,
                ∃ offset : Nat,
                  runTree.ActiveBranch branch ∧
                    ∀ n : Nat,
                      runTree.stateAt (branchPrefix branch (offset + n)) = path n) :
    (A.supportWitnessMuller {A.initial}).Accepts word := by
  rcases haccepts with ⟨runTree, hrunTreeAccepting⟩
  exact A.supportWitnessMuller_accepts_of_acceptingRun_tailBranchRealizable
    runTree hrunTreeAccepting (hrealizable runTree hrunTreeAccepting)

/--
State-wise form of the conditional APA-completeness bridge.  It packages the
same branch-realizability/coherence obligation after rebasing the APA initial
state to `root`, so it can be used directly for state-wise determinization
certificates.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_accepts_of_acceptsFrom_branchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (haccepts : A.AcceptsFrom root word)
    (hrealizable :
      ∀ runTree : (A.withInitial root).Run word,
        runTree.Accepting ->
          ∀ path : Nat -> A.State,
            (∀ n : Nat,
              (path n, path (n + 1)) ∈
                runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
              ∃ branch : Nat -> Nat, runTree.RealizesStatePath path branch) :
    ((A.withInitial root).supportWitnessMuller
      ({(A.withInitial root).initial} : Finset (A.withInitial root).State)).Accepts
        word :=
  (A.withInitial root).supportWitnessMuller_accepts_of_accepts_branchRealizable
    word haccepts hrealizable

/--
State-wise tail-realization form of the conditional APA-completeness bridge.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_accepts_of_acceptsFrom_tailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (haccepts : A.AcceptsFrom root word)
    (hrealizable :
      ∀ runTree : (A.withInitial root).Run word,
        runTree.Accepting ->
          ∀ path : Nat -> A.State,
            (∀ n : Nat,
              (path n, path (n + 1)) ∈
                runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
              ∃ branch : Nat -> Nat,
                ∃ offset : Nat,
                  runTree.ActiveBranch branch ∧
                    ∀ n : Nat,
                      runTree.stateAt (branchPrefix branch (offset + n)) = path n) :
    ((A.withInitial root).supportWitnessMuller
      ({(A.withInitial root).initial} : Finset (A.withInitial root).State)).Accepts
        word :=
  (A.withInitial root).supportWitnessMuller_accepts_of_accepts_tailBranchRealizable
    word haccepts hrealizable

theorem AlternatingParityAutomaton.supportWitnessMuller_withInitialTo_run
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    APASupportConfigurationState.withInitialTo A root
        (((A.withInitial root).supportWitnessMuller
          ({(A.withInitial root).initial} :
            Finset (A.withInitial root).State)).run word n) =
      (A.supportWitnessMuller ({root} : Finset A.State)).run word n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        APASupportConfigurationState.withInitialTo A root
          (APASupportConfigurationState.step
            (((A.withInitial root).supportWitnessMuller
              ({(A.withInitial root).initial} :
                Finset (A.withInitial root).State)).run word n)
            (word n)) =
        APASupportConfigurationState.step
          ((A.supportWitnessMuller ({root} : Finset A.State)).run word n)
          (word n)
      rw [APASupportConfigurationState.withInitialTo_step, ih]

theorem AlternatingParityAutomaton.supportWitnessMuller_withInitialTo_mem_infStates
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (config : APASupportConfigurationState (A.withInitial root))
    (hconfig :
      config ∈
        ((A.withInitial root).supportWitnessMuller
          ({(A.withInitial root).initial} :
            Finset (A.withInitial root).State)).InfStates word) :
    APASupportConfigurationState.withInitialTo A root config ∈
      (A.supportWitnessMuller ({root} : Finset A.State)).InfStates word := by
  intro n
  rcases hconfig n with ⟨k, hk, hrun⟩
  refine ⟨k, hk, ?_⟩
  change
    (((A.withInitial root).supportWitnessMuller
      ({(A.withInitial root).initial} :
        Finset (A.withInitial root).State)).run word k) = config at hrun
  change
    (A.supportWitnessMuller ({root} : Finset A.State)).run word k =
      APASupportConfigurationState.withInitialTo A root config
  rw [← A.supportWitnessMuller_withInitialTo_run root word k]
  change
    APASupportConfigurationState.withInitialTo A root
      (((A.withInitial root).supportWitnessMuller
        ({(A.withInitial root).initial} :
          Finset (A.withInitial root).State)).run word k) =
        APASupportConfigurationState.withInitialTo A root config
  rw [hrun]

theorem AlternatingParityAutomaton.supportWitnessStateEdgesAccepting_withInitial_iff
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (stateEdges : Finset (APAStateEdge A)) :
    (A.withInitial root).SupportWitnessStateEdgesAccepting stateEdges ↔
      A.SupportWitnessStateEdgesAccepting stateEdges := by
  constructor
  · intro haccepting path hpath
    rcases haccepting path hpath with ⟨p, hpEven, hpSeen, hpMin⟩
    refine ⟨p, hpEven, ?_, ?_⟩
    · simpa [AlternatingParityAutomaton.withInitial,
        AlternatingParityAutomaton.SupportEdgePathPrioritySeenInfinitelyOften] using
        hpSeen
    · intro q hq
      apply hpMin q
      simpa [AlternatingParityAutomaton.withInitial,
        AlternatingParityAutomaton.SupportEdgePathPrioritySeenInfinitelyOften] using
        hq
  · intro haccepting path hpath
    rcases haccepting path hpath with ⟨p, hpEven, hpSeen, hpMin⟩
    refine ⟨p, hpEven, ?_, ?_⟩
    · simpa [AlternatingParityAutomaton.withInitial,
        AlternatingParityAutomaton.SupportEdgePathPrioritySeenInfinitelyOften] using
        hpSeen
    · intro q hq
      apply hpMin q
      simpa [AlternatingParityAutomaton.withInitial,
        AlternatingParityAutomaton.SupportEdgePathPrioritySeenInfinitelyOften] using
        hq

theorem AlternatingParityAutomaton.supportRecurringMacroStates_withInitialTo_mem
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    {states : Finset A.State}
    (hstates :
      states ∈
        (A.withInitial root).supportRecurringMacroStates
          (((A.withInitial root).supportWitnessMuller
            ({(A.withInitial root).initial} :
              Finset (A.withInitial root).State)).InfStates word)) :
    states ∈ A.supportRecurringMacroStates
      ((A.supportWitnessMuller ({root} : Finset A.State)).InfStates word) := by
  rcases hstates with ⟨config, hconfig, hmem⟩
  exact
    ⟨APASupportConfigurationState.withInitialTo A root config,
      A.supportWitnessMuller_withInitialTo_mem_infStates
        root word config hconfig,
      hmem⟩

theorem AlternatingParityAutomaton.supportRecurringMacroEdges_withInitialTo_mem
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    {edge : APAMacroEdge A}
    (hedge :
      edge ∈
        (A.withInitial root).supportRecurringMacroEdges
          (((A.withInitial root).supportWitnessMuller
            ({(A.withInitial root).initial} :
              Finset (A.withInitial root).State)).InfStates word)) :
    edge ∈ A.supportRecurringMacroEdges
      ((A.supportWitnessMuller ({root} : Finset A.State)).InfStates word) := by
  rcases hedge with ⟨config, hconfig, hmem⟩
  exact
    ⟨APASupportConfigurationState.withInitialTo A root config,
      A.supportWitnessMuller_withInitialTo_mem_infStates
        root word config hconfig,
      hmem⟩

theorem AlternatingParityAutomaton.supportRecurringStateEdges_withInitialTo_mem
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    {edge : APAStateEdge A}
    (hedge :
      edge ∈
        (A.withInitial root).supportRecurringStateEdges
          (((A.withInitial root).supportWitnessMuller
            ({(A.withInitial root).initial} :
              Finset (A.withInitial root).State)).InfStates word)) :
    edge ∈ A.supportRecurringStateEdges
      ((A.supportWitnessMuller ({root} : Finset A.State)).InfStates word) := by
  rcases hedge with ⟨config, hconfig, hmem⟩
  exact
    ⟨APASupportConfigurationState.withInitialTo A root config,
      A.supportWitnessMuller_withInitialTo_mem_infStates
        root word config hconfig,
      hmem⟩

theorem AlternatingParityAutomaton.supportRecurrentWitness_withInitialTo
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (hwitness :
      (A.withInitial root).SupportRecurrentWitness
        (((A.withInitial root).supportWitnessMuller
          ({(A.withInitial root).initial} :
            Finset (A.withInitial root).State)).InfStates word)) :
    A.SupportRecurrentWitness
      ((A.supportWitnessMuller ({root} : Finset A.State)).InfStates word) := by
  rcases hwitness with
    ⟨macroStates, macroEdges, stateEdges, hnonempty, hstates, hedges,
      hstateEdges, hedgeClosed, hprogress, hstateEdgeEndpoints, haccepting⟩
  refine
    ⟨macroStates, macroEdges, stateEdges, hnonempty, ?_, ?_, ?_,
      hedgeClosed, hprogress, hstateEdgeEndpoints, ?_⟩
  · intro states hmem
    exact
      A.supportRecurringMacroStates_withInitialTo_mem
        root word (hstates states hmem)
  · intro edge hmem
    exact
      A.supportRecurringMacroEdges_withInitialTo_mem
        root word (hedges edge hmem)
  · intro edge hmem
    exact
      A.supportRecurringStateEdges_withInitialTo_mem
        root word (hstateEdges edge hmem)
  · exact
      (A.supportWitnessStateEdgesAccepting_withInitial_iff
        root stateEdges).mp haccepting

theorem AlternatingParityAutomaton.supportWitnessMuller_accepts_withInitialTo
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (haccepts :
      ((A.withInitial root).supportWitnessMuller
        ({(A.withInitial root).initial} :
          Finset (A.withInitial root).State)).Accepts word) :
    (A.supportWitnessMuller ({root} : Finset A.State)).Accepts word := by
  have hwitnessRebased :
      (A.withInitial root).SupportRecurrentWitness
        (((A.withInitial root).supportWitnessMuller
          ({(A.withInitial root).initial} :
            Finset (A.withInitial root).State)).InfStates word) :=
    ((A.withInitial root).supportWitnessMuller_accepts_iff
      ({(A.withInitial root).initial} :
        Finset (A.withInitial root).State) word).mp haccepts
  exact
    (A.supportWitnessMuller_accepts_iff
      ({root} : Finset A.State) word).mpr
      (A.supportRecurrentWitness_withInitialTo root word hwitnessRebased)

theorem AlternatingParityAutomaton.supportWitnessMuller_acceptsFrom_of_acceptsFrom_branchRealizable_onOriginal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (haccepts : A.AcceptsFrom root word)
    (hrealizable :
      ∀ runTree : (A.withInitial root).Run word,
        runTree.Accepting ->
          ∀ path : Nat -> A.State,
            (∀ n : Nat,
              (path n, path (n + 1)) ∈
                runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
              ∃ branch : Nat -> Nat, runTree.RealizesStatePath path branch) :
    (A.supportWitnessMuller ({root} : Finset A.State)).Accepts word :=
  A.supportWitnessMuller_accepts_withInitialTo root word
    (A.supportWitnessMuller_accepts_of_acceptsFrom_branchRealizable
      root word haccepts hrealizable)

/--
Original-state version of the state-wise tail-realization completeness bridge.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_acceptsFrom_of_acceptsFrom_tailBranchRealizable_onOriginal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (haccepts : A.AcceptsFrom root word)
    (hrealizable :
      ∀ runTree : (A.withInitial root).Run word,
        runTree.Accepting ->
          ∀ path : Nat -> A.State,
            (∀ n : Nat,
              (path n, path (n + 1)) ∈
                runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
              ∃ branch : Nat -> Nat,
                ∃ offset : Nat,
                  runTree.ActiveBranch branch ∧
                    ∀ n : Nat,
                      runTree.stateAt (branchPrefix branch (offset + n)) = path n) :
    (A.supportWitnessMuller ({root} : Finset A.State)).Accepts word :=
  A.supportWitnessMuller_accepts_withInitialTo root word
    (A.supportWitnessMuller_accepts_of_acceptsFrom_tailBranchRealizable
      root word haccepts hrealizable)

/--
Existential tail-realization criterion for support-witness completeness.

For completeness of the support-witness Muller carrier it is enough to choose
one accepting run tree for each accepted state/word and prove tail-realization
there.  This is the form naturally produced by a saturated tableau
construction; it avoids requiring every accepting run tree to be saturated.
-/
def AlternatingParityAutomaton.SupportWitnessExistsTailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    A.AcceptsFrom state word ->
      ∃ runTree : (A.withInitial state).Run word,
        runTree.Accepting ∧
          ∀ path : Nat -> A.State,
            (∀ n : Nat,
              (path n, path (n + 1)) ∈
                runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
              ∃ branch : Nat -> Nat,
                ∃ offset : Nat,
                  runTree.ActiveBranch branch ∧
                    ∀ n : Nat,
                      runTree.stateAt (branchPrefix branch (offset + n)) = path n

/--
Existential accepting edge-witnessed macro-run criterion.

This is the support-witness completeness target that avoids committing to the
raw recurring edge set of one run tree.  For each accepted state/word, it is
enough to construct an edge-witnessed macro-run over the rebased singleton APA
whose selected recurring individual support-edge graph is parity accepting.
The selected graph may be a pruned recurrent witness, unlike
`realizedEdgeWitnessedMacroRun.infStateEdgeFinset`.
-/
def AlternatingParityAutomaton.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    A.AcceptsFrom state word ->
      ∃ run :
        (A.withInitial state).EdgeWitnessedMacroRun
          ({(A.withInitial state).initial} :
            Finset (A.withInitial state).State)
          word,
        (A.withInitial state).SupportWitnessStateEdgesAccepting
          run.infStateEdgeFinset

/--
Flexible variant of `SupportWitnessExistsAcceptingEdgeWitnessedMacroRun`.

Instead of proving directly that the exact recurring-edge finset of the chosen
edge-witnessed macro-run is accepting, it is enough to provide any finite
accepting support graph that contains those recurring edges.  Monotonicity of
`SupportWitnessStateEdgesAccepting` then recovers the exact endpoint.
-/
def AlternatingParityAutomaton.SupportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    A.AcceptsFrom state word ->
      ∃ run :
        (A.withInitial state).EdgeWitnessedMacroRun
          ({(A.withInitial state).initial} :
            Finset (A.withInitial state).State)
          word,
        ∃ acceptedEdges : Finset (APAStateEdge (A.withInitial state)),
          run.infStateEdgeFinset ⊆ acceptedEdges ∧
            (A.withInitial state).SupportWitnessStateEdgesAccepting acceptedEdges

theorem AlternatingParityAutomaton.supportWitnessExistsAcceptingEdgeWitnessedMacroRun_of_subgraphAccepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (hwitness :
      A.SupportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting) :
    A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun := by
  intro state word haccepts
  rcases hwitness state word haccepts with
    ⟨run, acceptedEdges, hsubset, haccepting⟩
  exact
    ⟨run,
      (A.withInitial state).supportWitnessStateEdgesAccepting_of_subset
        haccepting hsubset⟩

/--
Tail-realizability criterion for the flexible subgraph endpoint.

For each accepted state/word, choose an accepting run tree and a finite support
graph containing the recurring explicit edges of that run tree.  If every path
through the chosen graph is realized by a suffix of an active accepting branch,
then the graph is parity accepting and yields the flexible edge-witnessed
macro-run endpoint.
-/
def AlternatingParityAutomaton.SupportWitnessExistsRealizedSubgraphTailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    A.AcceptsFrom state word ->
      ∃ runTree : (A.withInitial state).Run word,
        runTree.Accepting ∧
          ∃ acceptedEdges : Finset (APAStateEdge (A.withInitial state)),
            runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset ⊆ acceptedEdges ∧
              ∀ path : Nat -> (A.withInitial state).State,
                (∀ n : Nat, (path n, path (n + 1)) ∈ acceptedEdges) ->
                  ∃ branch : Nat -> Nat,
                    ∃ offset : Nat,
                      runTree.ActiveBranch branch ∧
                        ∀ n : Nat,
                          runTree.stateAt (branchPrefix branch (offset + n)) =
                            path n

theorem AlternatingParityAutomaton.supportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting_of_realizedSubgraphTailBranchRealizable
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (hrealizable :
      A.SupportWitnessExistsRealizedSubgraphTailBranchRealizable) :
    A.SupportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting := by
  intro state word haccepts
  rcases hrealizable state word haccepts with
    ⟨runTree, hrunTreeAccepting, acceptedEdges, hsubset, htail⟩
  refine
    ⟨runTree.realizedEdgeWitnessedMacroRun,
      acceptedEdges,
      hsubset,
      ?_⟩
  exact
    (A.withInitial state).supportWitnessStateEdgesAccepting_of_tailBranchRealizable
      runTree hrunTreeAccepting htail

theorem AlternatingParityAutomaton.supportWitnessExistsAcceptingEdgeWitnessedMacroRun_of_realizedSubgraphTailBranchRealizable
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (hrealizable :
      A.SupportWitnessExistsRealizedSubgraphTailBranchRealizable) :
    A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun :=
  A.supportWitnessExistsAcceptingEdgeWitnessedMacroRun_of_subgraphAccepting
    (A.supportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting_of_realizedSubgraphTailBranchRealizable
      hrealizable)

/--
The older exact recurring-edge tail-branch criterion is the special case of the
new subgraph criterion where the chosen accepting support graph is exactly the
realized run's recurring explicit edge finset.
-/
theorem AlternatingParityAutomaton.supportWitnessExistsRealizedSubgraphTailBranchRealizable_of_existsTailBranchRealizable
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (hrealizable : A.SupportWitnessExistsTailBranchRealizable) :
    A.SupportWitnessExistsRealizedSubgraphTailBranchRealizable := by
  intro state word haccepts
  rcases hrealizable state word haccepts with
    ⟨runTree, hrunTreeAccepting, htail⟩
  exact
    ⟨runTree,
      hrunTreeAccepting,
      runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset,
      (fun _edge hedge => hedge),
      htail⟩

theorem AlternatingParityAutomaton.supportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting_of_existsTailBranchRealizable
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (hrealizable : A.SupportWitnessExistsTailBranchRealizable) :
    A.SupportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting :=
  A.supportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting_of_realizedSubgraphTailBranchRealizable
    (A.supportWitnessExistsRealizedSubgraphTailBranchRealizable_of_existsTailBranchRealizable
      hrealizable)

theorem AlternatingParityAutomaton.supportWitnessExistsAcceptingEdgeWitnessedMacroRun_of_existsTailBranchRealizable
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (hrealizable : A.SupportWitnessExistsTailBranchRealizable) :
    A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun :=
  A.supportWitnessExistsAcceptingEdgeWitnessedMacroRun_of_realizedSubgraphTailBranchRealizable
    (A.supportWitnessExistsRealizedSubgraphTailBranchRealizable_of_existsTailBranchRealizable
      hrealizable)

/--
If explicit macro-run support choices are realizable by APA run trees, then
acceptance by the concrete nondeterministic Muller macro-run automaton implies
acceptance from every state in the initial macro-state.
-/
theorem AlternatingParityAutomaton.acceptsFrom_all_initial_of_edgeWitnessedMacroRunMuller_accepts
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (haccepts : (A.edgeWitnessedMacroRunMuller initialStates).Accepts word) :
    ∀ state, state ∈ initialStates -> A.AcceptsFrom state word := by
  rcases
    A.exists_acceptingEdgeWitnessedMacroRun_of_edgeWitnessedMacroRunMuller_accepts
      haccepts with
    ⟨run, haccepting⟩
  exact
    run.acceptsFrom_all_initial_of_supportAccepting_realized
      (run.supportAccepting_of_infStateEdgeFinset_accepting haccepting)
      run.hasRunTreeRealization

/--
Concrete APA-to-nondeterministic-Muller compilation through edge-witnessed
macro-runs.

The remaining mathematical obligation is explicit: every accepting APA run has
an accepting edge-witnessed macro-run over the rebased singleton automaton.
-/
noncomputable def AlternatingParityAutomaton.edgeWitnessedMacroRunMullerCompilation
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hcomplete : A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun) :
    APARunToNondetMullerCompilation.{u, v, v} A where
  muller :=
    (A.withInitial A.initial).edgeWitnessedMacroRunMuller
      ({(A.withInitial A.initial).initial} :
        Finset (A.withInitial A.initial).State)
  correct := by
    intro word
    constructor
    · intro hmuller
      have hfrom :
        (A.withInitial A.initial).AcceptsFrom
          (A.withInitial A.initial).initial word :=
      AlternatingParityAutomaton.acceptsFrom_all_initial_of_edgeWitnessedMacroRunMuller_accepts
        (A := A.withInitial A.initial)
        hmuller
        (A.withInitial A.initial).initial
        (by simp)
      simpa [AlternatingParityAutomaton.AcceptsFrom,
        AlternatingParityAutomaton.withInitial] using hfrom
    · intro haccepts
      have hacceptsFrom : A.AcceptsFrom A.initial word := by
        simpa using haccepts
      rcases hcomplete A.initial word hacceptsFrom with
        ⟨run, haccepting⟩
      exact
        AlternatingParityAutomaton.edgeWitnessedMacroRunMuller_accepts_of_acceptingEdgeWitnessedMacroRun
          (A := A.withInitial A.initial)
          run haccepting

/--
Uniform compiler constructor for the edge-witnessed macro-run route.
-/
noncomputable def APARunToNondetMullerCompiler.ofEdgeWitnessedMacroRun
    {Alphabet : Type u}
    (hcomplete :
      ∀ A : AlternatingParityAutomaton.{u, v} Alphabet,
        A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun) :
    APARunToNondetMullerCompiler.{u, v, v} Alphabet where
  compile := fun A =>
    A.edgeWitnessedMacroRunMullerCompilation
      (hcomplete A)

/--
Existential fixed-point/tableau recurrence criterion.

This is the proof target expected from the canonical LTL tableau: for every
accepted state/word, construct one accepting run tree that is atom-complete and
has timed atom support for every recurring state path.
-/
def AlternatingParityAutomaton.SupportWitnessExistsAtomCompleteTimedAtoms
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    A.AcceptsFrom state word ->
      ∃ runTree : (A.withInitial state).Run word,
        runTree.Accepting ∧
          runTree.AtomComplete ∧
            ∀ path : Nat -> A.State,
              (∀ n : Nat,
                (path n, path (n + 1)) ∈
                  runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
                runTree.StatePathTimedAtomTailSupport path

/--
Existential subtree-local child-coherence criterion.

This is the canonical tableau-shaped target without the too-strong demand that
every syntactic transition atom be spawned.  For each accepted state/word we
choose one accepting run tree, and every path through its recurring state-edge
graph must have a subtree occurrence where each matching node has an active
child for the next path state.
-/
def AlternatingParityAutomaton.SupportWitnessExistsTailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    A.AcceptsFrom state word ->
      ∃ runTree : (A.withInitial state).Run word,
        runTree.Accepting ∧
          ∀ path : Nat -> A.State,
            (∀ n : Nat,
              (path n, path (n + 1)) ∈
                runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
              runTree.StatePathTailCoherentChildren path

/--
Existential node-local recurring-edge completeness.

This is the exact branch-stability target for a chosen accepting run tree:
every recurring state edge is available below every active occurrence of its
source.  It is stronger than the subtree-local path condition but often easier
to prove directly from a deterministic/tableau expansion discipline.
-/
def AlternatingParityAutomaton.SupportWitnessExistsRecurringEdgesNodeLocalComplete
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    A.AcceptsFrom state word ->
      ∃ runTree : (A.withInitial state).Run word,
        runTree.Accepting ∧
          runTree.RecurringStateEdgesNodeLocalComplete

/--
Original-state completeness bridge using an existentially chosen
tail-realizing accepting run tree.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_acceptsFrom_of_acceptsFrom_existsTailBranchRealizable_onOriginal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (haccepts : A.AcceptsFrom root word)
    (hrealizable : A.SupportWitnessExistsTailBranchRealizable) :
    (A.supportWitnessMuller ({root} : Finset A.State)).Accepts word := by
  rcases hrealizable root word haccepts with
    ⟨runTree, hrunTreeAccepting, htail⟩
  exact
    A.supportWitnessMuller_accepts_withInitialTo root word
      ((A.withInitial root).supportWitnessMuller_accepts_of_acceptingRun_tailBranchRealizable
        runTree hrunTreeAccepting htail)

/--
Original-state completeness bridge using an existentially selected
edge-witnessed macro-run with an accepting recurring support-edge graph.

This is the safer generic target for LTL/tableau completeness: the witness may
choose a recurrent accepting support graph directly, instead of using every
raw recurring edge of the canonical run tree.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_acceptsFrom_of_acceptsFrom_existsAcceptingEdgeWitnessedMacroRun_onOriginal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (haccepts : A.AcceptsFrom root word)
    (hwitness : A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun) :
    (A.supportWitnessMuller ({root} : Finset A.State)).Accepts word := by
  rcases hwitness root word haccepts with ⟨run, hrunAccepting⟩
  exact
    A.supportWitnessMuller_accepts_withInitialTo root word
      ((A.withInitial root).supportWitnessMuller_accepts_of_edgeWitnessedMacroRun
        run hrunAccepting)

/--
Original-state completeness bridge using the flexible subgraph-accepting
edge-witnessed macro-run endpoint.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_acceptsFrom_of_acceptsFrom_existsEdgeWitnessedMacroRunSubgraphAccepting_onOriginal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (root : A.State)
    (word : OmegaWord Alphabet)
    (haccepts : A.AcceptsFrom root word)
    (hwitness : A.SupportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting) :
    (A.supportWitnessMuller ({root} : Finset A.State)).Accepts word :=
  A.supportWitnessMuller_acceptsFrom_of_acceptsFrom_existsAcceptingEdgeWitnessedMacroRun_onOriginal
    root word haccepts
    (A.supportWitnessExistsAcceptingEdgeWitnessedMacroRun_of_subgraphAccepting
      hwitness)

/-- Soundness direction for the support-witness singleton Muller languages. -/
def AlternatingParityAutomaton.SupportWitnessSound
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ->
      A.AcceptsFrom state word

/--
To prove support-witness soundness it is enough to show that every accepted
singleton operational witness can be spliced into a semantically accepting
macro-run.  This isolates the remaining construction from the already-proved
semantic macro-run soundness theorem.
-/
theorem AlternatingParityAutomaton.supportWitnessSound_of_operationalWitness_semanticMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun) :
    A.SupportWitnessSound := by
  intro state word haccepts
  exact
    (A.supportOperationalWitness_of_supportWitnessMuller_accepts
      haccepts).acceptsFrom_of_hasSemanticMacroRun
        (hsemantic state word haccepts) (by simp)

/--
Support-witness soundness is equivalent to semantic macro-run reconstruction for
accepted singleton operational witnesses.

The forward direction uses the generic semantic macro-run construction from APA
acceptance; the reverse direction is
`supportWitnessSound_of_operationalWitness_semanticMacroRun`.
-/
theorem AlternatingParityAutomaton.supportWitnessSound_iff_operationalWitness_semanticMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    A.SupportWitnessSound ↔
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun := by
  constructor
  · intro hsound state word haccepts
    rw [
      (A.supportOperationalWitness_of_supportWitnessMuller_accepts
        haccepts).hasSemanticMacroRun_iff_accepts_all]
    intro initialState hinitialState
    have hstate : initialState = state := by
      simpa using hinitialState
    subst initialState
    exact hsound state word haccepts
  · intro hsemantic
    exact A.supportWitnessSound_of_operationalWitness_semanticMacroRun hsemantic

/--
Equivalent packaging of the remaining endpoint-continuation obligation for
support-witness soundness.  It is often easier to prove by first extracting a
late prefix from the operational recurrence data.
-/
theorem AlternatingParityAutomaton.supportWitnessSound_of_operationalWitness_prefix_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset)) :
    A.SupportWitnessSound := by
  refine
    A.supportWitnessSound_of_operationalWitness_semanticMacroRun ?_
  intro state word haccepts
  rcases hpref state word haccepts with ⟨offset, pref, hacceptsTail⟩
  exact
    (A.supportOperationalWitness_of_supportWitnessMuller_accepts
      haccepts).hasSemanticMacroRun_of_prefix_accepts pref hacceptsTail

/--
The two operational soundness obligations used by the support-witness route are
equivalent: an accepted operational witness has a semantic accepting macro-run
iff it has a finite prefix whose frontier states all accept the remaining
suffix.
-/
theorem AlternatingParityAutomaton.operationalWitness_semanticMacroRun_iff_prefix_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    (∀ (state : A.State) (word : OmegaWord Alphabet),
      ∀ haccepts :
        (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
        (A.supportOperationalWitness_of_supportWitnessMuller_accepts
          haccepts).HasSemanticMacroRun) ↔
      (∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset)) := by
  constructor
  · intro hsemantic state word haccepts
    exact
      (A.supportOperationalWitness_of_supportWitnessMuller_accepts
        haccepts).exists_prefix_accepts_of_hasSemanticMacroRun
          (hsemantic state word haccepts)
  · intro hpref state word haccepts
    rcases hpref state word haccepts with
      ⟨offset, pref, hacceptsTail⟩
    exact
      (A.supportOperationalWitness_of_supportWitnessMuller_accepts
        haccepts).hasSemanticMacroRun_of_prefix_accepts
          pref hacceptsTail

/--
Support-witness soundness is also equivalent to the finite-prefix continuation
obligation.  This is the exact generic target used by the canonical LTL
`prefixSatisfies` route: once an accepted support-witness run exposes a finite
frontier whose states accept the remaining suffix, soundness follows, and
conversely soundness supplies such a frontier via semantic macro-runs.
-/
theorem AlternatingParityAutomaton.supportWitnessSound_iff_operationalWitness_prefix_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    A.SupportWitnessSound ↔
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset) := by
  rw [A.supportWitnessSound_iff_operationalWitness_semanticMacroRun]
  exact A.operationalWitness_semanticMacroRun_iff_prefix_accepts

/--
Branch-coherence needed for the support-witness completeness direction.

Every infinite path through the explicit recurring state-edge graph extracted
from an accepting run tree must be realized by an active branch of that tree.
-/
def AlternatingParityAutomaton.SupportWitnessBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    ∀ runTree : (A.withInitial state).Run word,
      runTree.Accepting ->
        ∀ path : Nat -> A.State,
          (∀ n : Nat,
            (path n, path (n + 1)) ∈
              runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
            ∃ branch : Nat -> Nat, runTree.RealizesStatePath path branch

/--
Tail-realization form of support-witness completeness.

An infinite path through the recurring support-edge graph only has to occur as
a suffix of an accepting run-tree branch.  This is the natural recurrence-level
obligation; the generic parity bridge above removes the finite prefix.
-/
def AlternatingParityAutomaton.SupportWitnessTailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    ∀ runTree : (A.withInitial state).Run word,
      runTree.Accepting ->
        ∀ path : Nat -> A.State,
          (∀ n : Nat,
            (path n, path (n + 1)) ∈
              runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
            ∃ branch : Nat -> Nat,
              ∃ offset : Nat,
                runTree.ActiveBranch branch ∧
                  ∀ n : Nat,
                    runTree.stateAt (branchPrefix branch (offset + n)) = path n

/--
Local tail-child-extension version of `SupportWitnessTailBranchRealizable`.

This is the shape expected from a recurrence proof: after choosing an active
occurrence of the path head, every realized prefix can be extended by one
active child that follows the next recurring state edge.
-/
def AlternatingParityAutomaton.SupportWitnessTailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    ∀ runTree : (A.withInitial state).Run word,
      runTree.Accepting ->
        ∀ path : Nat -> A.State,
          (∀ n : Nat,
            (path n, path (n + 1)) ∈
            runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
            runTree.StatePathTailCoherentChildren path

/--
Support-witness recurrence criterion phrased as a node-local completeness
property of every accepting run tree's recurring edge graph.

This is the remaining semantic obligation in a form that rules out the invalid
level-wise shortcut: recurring edges must be available below every active
occurrence of their source.
-/
def AlternatingParityAutomaton.SupportWitnessRecurringEdgesNodeLocalComplete
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    ∀ runTree : (A.withInitial state).Run word,
      runTree.Accepting ->
        runTree.RecurringStateEdgesNodeLocalComplete

/--
Support-witness recurrence criterion phrased in the fixed-point/tableau style.

Every accepting run tree is saturated enough to realize all transition atoms,
and every path through its recurring edge graph has a tail occurrence where the
next path state is a timed transition atom at each matching subtree node.
This avoids the invalid untimed shortcut from recurrence of `(q, q')` to
availability of `q'` at every later occurrence of `q`.
-/
def AlternatingParityAutomaton.SupportWitnessAtomCompleteTimedAtoms
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    ∀ runTree : (A.withInitial state).Run word,
      runTree.Accepting ->
        runTree.AtomComplete ∧
          ∀ path : Nat -> A.State,
            (∀ n : Nat,
              (path n, path (n + 1)) ∈
                runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
              runTree.StatePathTimedAtomTailSupport path

/--
Node-local completeness of recurring edges implies the subtree-local
tail-child-extension target.
-/
theorem AlternatingParityAutomaton.supportWitnessTailPathChildCoherent_of_recurringEdgesNodeLocalComplete
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hlocal : A.SupportWitnessRecurringEdgesNodeLocalComplete) :
    A.SupportWitnessTailPathChildCoherent := by
  intro state word runTree haccepting path hpath
  exact
    runTree.statePathTailCoherentChildren_of_recurringStateEdgesNodeLocalComplete
      (hlocal state word runTree haccepting) hpath

/--
The atom-complete timed-atom criterion implies the subtree-local
tail-child-extension target.
-/
theorem AlternatingParityAutomaton.supportWitnessTailPathChildCoherent_of_atomCompleteTimedAtoms
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (htimed : A.SupportWitnessAtomCompleteTimedAtoms) :
    A.SupportWitnessTailPathChildCoherent := by
  intro state word runTree haccepting path hpath
  rcases htimed state word runTree haccepting with ⟨hatomComplete, hpathTimed⟩
  exact
    runTree.statePathTailCoherentChildren_of_atomComplete_and_timedAtomTailSupport
      hatomComplete (hpathTimed path hpath)

/--
The existential atom-complete timed-atom criterion implies the existential
tail-realization criterion.
-/
theorem AlternatingParityAutomaton.supportWitnessExistsTailBranchRealizable_of_existsAtomCompleteTimedAtoms
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (htimed : A.SupportWitnessExistsAtomCompleteTimedAtoms) :
    A.SupportWitnessExistsTailBranchRealizable := by
  intro state word haccepts
  rcases htimed state word haccepts with
    ⟨runTree, haccepting, hatomComplete, hpathTimed⟩
  refine ⟨runTree, haccepting, ?_⟩
  intro path hpath
  exact
    runTree.exists_tailRealizingBranch_of_tailCoherentChildren path
      (runTree.statePathTailCoherentChildren_of_atomComplete_and_timedAtomTailSupport
        hatomComplete (hpathTimed path hpath))

/--
Existential subtree-local child-coherence implies existential tail-realization.
-/
theorem AlternatingParityAutomaton.supportWitnessExistsTailBranchRealizable_of_existsTailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hcoherent : A.SupportWitnessExistsTailPathChildCoherent) :
    A.SupportWitnessExistsTailBranchRealizable := by
  intro state word haccepts
  rcases hcoherent state word haccepts with
    ⟨runTree, haccepting, hpathCoherent⟩
  refine ⟨runTree, haccepting, ?_⟩
  intro path hpath
  exact
    runTree.exists_tailRealizingBranch_of_tailCoherentChildren path
      (hpathCoherent path hpath)

/--
Existential node-local recurring-edge completeness implies existential
subtree-local child-coherence.
-/
theorem AlternatingParityAutomaton.supportWitnessExistsTailPathChildCoherent_of_existsRecurringEdgesNodeLocalComplete
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hlocal : A.SupportWitnessExistsRecurringEdgesNodeLocalComplete) :
    A.SupportWitnessExistsTailPathChildCoherent := by
  intro state word haccepts
  rcases hlocal state word haccepts with
    ⟨runTree, haccepting, hnodeLocal⟩
  refine ⟨runTree, haccepting, ?_⟩
  intro path hpath
  exact
    runTree.statePathTailCoherentChildren_of_recurringStateEdgesNodeLocalComplete
      hnodeLocal hpath

/--
Threaded nested-realization version of `SupportWitnessTailPathChildCoherent`.

This names the concrete remaining recurrence task: choose a base active node
for the path head and show that every path-following suffix in that subtree has
an active one-step extension to the next path state.
-/
def AlternatingParityAutomaton.SupportWitnessThreadedTailRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    ∀ runTree : (A.withInitial state).Run word,
      runTree.Accepting ->
        ∀ path : Nat -> A.State,
          (∀ n : Nat,
            (path n, path (n + 1)) ∈
              runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
            runTree.StatePathThreadedTailRealization path

/--
Branch-stable node-local form of the support-witness recurrence obligation.

For every path through the recurring explicit state-edge graph of an accepting
run tree, one can choose an active base occurrence of the path head such that
every already-followed suffix has a concrete active child realizing the next
path edge.  This is the exact branch-sensitive condition needed to rule out the
invalid shortcut from level-wise recurrence to arbitrary same-state nodes.
-/
def AlternatingParityAutomaton.SupportWitnessNodeLocalTailRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    ∀ runTree : (A.withInitial state).Run word,
      runTree.Accepting ->
        ∀ path : Nat -> A.State,
          (∀ n : Nat,
            (path n, path (n + 1)) ∈
              runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
            ∃ node : Node,
              ∃ hpathNode : runTree.PathActive node,
                runTree.stateAt node = path 0 ∧
                  ∀ (hnode : runTree.active node) (suffix : Node),
                    (runTree.subRun node hnode).PathActive suffix ->
                      runTree.stateAt (suffix ++ node) = path suffix.length ->
                        runTree.StateEdgeRealizedFromNode
                          (suffix ++ node)
                          (path suffix.length, path (suffix.length + 1))

/--
The older subtree-local child-extension target is already strong enough to
produce the exact node-local support-witness target.

This removes a small artificial distinction between the two recurrence
interfaces: proving `SupportWitnessTailPathChildCoherent` now immediately
unlocks all node-local DPA compilation routes.
-/
theorem AlternatingParityAutomaton.supportWitnessNodeLocalTailRealizable_of_tailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hcoherent : A.SupportWitnessTailPathChildCoherent) :
    A.SupportWitnessNodeLocalTailRealizable := by
  intro state word runTree haccepting path hpath
  exact
    (runTree.statePathThreadedTailRealization_iff_nodeLocalEdges).mp
      (runTree.statePathThreadedTailRealization_of_tailCoherentChildren
        (hcoherent state word runTree haccepting path hpath))

theorem AlternatingParityAutomaton.supportWitnessThreadedTailRealizable_of_nodeLocal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hlocal : A.SupportWitnessNodeLocalTailRealizable) :
    A.SupportWitnessThreadedTailRealizable := by
  intro state word runTree haccepting path hpath
  exact
    (runTree.statePathThreadedTailRealization_iff_nodeLocalEdges).mpr
      (hlocal state word runTree haccepting path hpath)

/--
The exact node-local recurrence target is sufficient for the tail-realization
obligation used by the support-witness completeness proof.
-/
theorem AlternatingParityAutomaton.supportWitnessTailBranchRealizable_of_nodeLocal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hlocal : A.SupportWitnessNodeLocalTailRealizable) :
    A.SupportWitnessTailBranchRealizable := by
  intro state word runTree haccepting path hpath
  exact
    runTree.exists_tailRealizingBranch_of_tailCoherentChildren path
      (runTree.statePathTailCoherentChildren_of_threadedTailRealization
        ((A.supportWitnessThreadedTailRealizable_of_nodeLocal hlocal)
          state word runTree haccepting path hpath))

theorem AlternatingParityAutomaton.supportWitnessTailBranchRealizable_of_branchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hrealizable : A.SupportWitnessBranchRealizable) :
    A.SupportWitnessTailBranchRealizable := by
  intro state word runTree haccepting path hpath
  rcases hrealizable state word runTree haccepting path hpath with
    ⟨branch, hbranchActive, hstate⟩
  refine ⟨branch, 0, hbranchActive, ?_⟩
  intro n
  simpa using hstate n

/--
Threaded nested realizations imply the local tail-child-extension criterion.
-/
theorem AlternatingParityAutomaton.supportWitnessTailPathChildCoherent_of_threadedTailRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hthreaded : A.SupportWitnessThreadedTailRealizable) :
    A.SupportWitnessTailPathChildCoherent := by
  intro state word runTree haccepting path hpath
  exact
    runTree.statePathTailCoherentChildren_of_threadedTailRealization
      (hthreaded state word runTree haccepting path hpath)

/--
Threaded nested realizations are sufficient for the tail-realizability
obligation used by support-witness completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessTailBranchRealizable_of_threadedTailRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hthreaded : A.SupportWitnessThreadedTailRealizable) :
    A.SupportWitnessTailBranchRealizable := by
  intro state word runTree haccepting path hpath
  exact
    runTree.exists_tailRealizingBranch_of_tailCoherentChildren path
      (runTree.statePathTailCoherentChildren_of_threadedTailRealization
        (hthreaded state word runTree haccepting path hpath))

/--
The local tail-child-extension condition is sufficient for the
tail-realizability obligation used by support-witness completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessTailBranchRealizable_of_tailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hcoherent : A.SupportWitnessTailPathChildCoherent) :
    A.SupportWitnessTailBranchRealizable := by
  intro state word runTree haccepting path hpath
  exact
    runTree.exists_tailRealizingBranch_of_tailCoherentChildren path
      (hcoherent state word runTree haccepting path hpath)

/--
Local child-extension version of `SupportWitnessBranchRealizable`.

For each path through the recurring explicit edge graph, it is enough to prove
that the path can always be extended by one active child from any active node
that already realizes the current state.  The generic infinite-branch choice is
then automatic.
-/
def AlternatingParityAutomaton.SupportWitnessPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ (state : A.State) (word : OmegaWord Alphabet),
    ∀ runTree : (A.withInitial state).Run word,
      runTree.Accepting ->
        ∀ path : Nat -> A.State,
          (∀ n : Nat,
            (path n, path (n + 1)) ∈
              runTree.realizedEdgeWitnessedMacroRun.infStateEdgeFinset) ->
            runTree.StatePathCoherentChildren path

/--
The local child-extension form is sufficient for the explicit
branch-realizability obligation used by support-witness completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessBranchRealizable_of_pathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hcoherent : A.SupportWitnessPathChildCoherent) :
    A.SupportWitnessBranchRealizable := by
  intro state word runTree haccepting path hpath
  exact
    runTree.exists_realizingBranch_of_coherentChildren path
      (hcoherent state word runTree haccepting path hpath)

/--
The local child-extension condition also implies the weaker tail-realization
condition.  This keeps older path-child routes compatible with the newer
recurrence-level support-witness interface.
-/
theorem AlternatingParityAutomaton.supportWitnessTailBranchRealizable_of_pathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hcoherent : A.SupportWitnessPathChildCoherent) :
    A.SupportWitnessTailBranchRealizable :=
  A.supportWitnessTailBranchRealizable_of_branchRealizable
    (A.supportWitnessBranchRealizable_of_pathChildCoherent hcoherent)

/--
The exact semantic bridge still needed by the concrete support-witness
determinization route: soundness plus branch-coherent completeness give the
state-wise singleton language equivalence.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_sound_and_branchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsound : A.SupportWitnessSound)
    (hrealizable : A.SupportWitnessBranchRealizable) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word := by
  intro state word
  constructor
  · exact hsound state word
  · intro haccepts
    exact
      A.supportWitnessMuller_acceptsFrom_of_acceptsFrom_branchRealizable_onOriginal
        state word haccepts (hrealizable state word)

/--
Support-witness singleton language equivalence from soundness plus the weaker
tail-realization form of completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_sound_and_tailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsound : A.SupportWitnessSound)
    (hrealizable : A.SupportWitnessTailBranchRealizable) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word := by
  intro state word
  constructor
  · exact hsound state word
  · intro haccepts
    exact
      A.supportWitnessMuller_acceptsFrom_of_acceptsFrom_tailBranchRealizable_onOriginal
        state word haccepts (hrealizable state word)

/--
Support-witness singleton language equivalence from soundness plus an
existentially chosen tail-realizing accepting run tree for each accepted
state/word.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_sound_and_existsTailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsound : A.SupportWitnessSound)
    (hrealizable : A.SupportWitnessExistsTailBranchRealizable) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word := by
  intro state word
  constructor
  · exact hsound state word
  · intro haccepts
    exact
      A.supportWitnessMuller_acceptsFrom_of_acceptsFrom_existsTailBranchRealizable_onOriginal
        state word haccepts hrealizable

/--
Support-witness singleton language equivalence from soundness plus an
existentially selected accepting edge-witnessed macro-run for each accepted
state/word.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_sound_and_existsAcceptingEdgeWitnessedMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsound : A.SupportWitnessSound)
    (hwitness : A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word := by
  intro state word
  constructor
  · exact hsound state word
  · intro haccepts
    exact
      A.supportWitnessMuller_acceptsFrom_of_acceptsFrom_existsAcceptingEdgeWitnessedMacroRun_onOriginal
        state word haccepts hwitness

/--
Support-witness singleton language equivalence from soundness plus the
flexible subgraph-accepting edge-witnessed macro-run endpoint.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_sound_and_existsEdgeWitnessedMacroRunSubgraphAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsound : A.SupportWitnessSound)
    (hwitness : A.SupportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_existsAcceptingEdgeWitnessedMacroRun
    hsound
    (A.supportWitnessExistsAcceptingEdgeWitnessedMacroRun_of_subgraphAccepting
      hwitness)

/--
Support-witness singleton language equivalence from soundness plus an
existentially chosen atom-complete timed-atom accepting run tree for each
accepted state/word.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_sound_and_existsAtomCompleteTimedAtoms
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsound : A.SupportWitnessSound)
    (htimed : A.SupportWitnessExistsAtomCompleteTimedAtoms) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_existsTailBranchRealizable
    hsound
    (A.supportWitnessExistsTailBranchRealizable_of_existsAtomCompleteTimedAtoms
      htimed)

/--
Support-witness singleton language equivalence from soundness plus an
existentially chosen subtree-local child-coherent accepting run tree for each
accepted state/word.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_sound_and_existsTailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsound : A.SupportWitnessSound)
    (hcoherent : A.SupportWitnessExistsTailPathChildCoherent) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_existsTailBranchRealizable
    hsound
    (A.supportWitnessExistsTailBranchRealizable_of_existsTailPathChildCoherent
      hcoherent)

/--
Support-witness singleton language equivalence from soundness plus an
existentially chosen node-local accepting run tree.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_sound_and_existsRecurringEdgesNodeLocalComplete
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsound : A.SupportWitnessSound)
    (hlocal : A.SupportWitnessExistsRecurringEdgesNodeLocalComplete) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_existsTailPathChildCoherent
    hsound
    (A.supportWitnessExistsTailPathChildCoherent_of_existsRecurringEdgesNodeLocalComplete
      hlocal)

/--
Support-witness singleton language equivalence from soundness plus the local
child-extension coherence form of completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_sound_and_pathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsound : A.SupportWitnessSound)
    (hcoherent : A.SupportWitnessPathChildCoherent) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_tailBranchRealizable
    hsound
    (A.supportWitnessTailBranchRealizable_of_pathChildCoherent hcoherent)

/--
Support-witness singleton language equivalence from soundness plus the exact
branch-stable node-local recurrence target.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_sound_and_nodeLocal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsound : A.SupportWitnessSound)
    (hlocal : A.SupportWitnessNodeLocalTailRealizable) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_tailBranchRealizable
    hsound
    (A.supportWitnessTailBranchRealizable_of_nodeLocal hlocal)

/--
Concrete support-witness equivalence from soundness and the subtree-local
tail-child-extension recurrence target.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_sound_and_tailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsound : A.SupportWitnessSound)
    (hcoherent : A.SupportWitnessTailPathChildCoherent) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_nodeLocal
    hsound
    (A.supportWitnessNodeLocalTailRealizable_of_tailPathChildCoherent
      hcoherent)

/--
Concrete support-witness equivalence from soundness and the fixed-point/tableau
timed-atom recurrence target.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_sound_and_atomCompleteTimedAtoms
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsound : A.SupportWitnessSound)
    (htimed : A.SupportWitnessAtomCompleteTimedAtoms) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_tailPathChildCoherent
    hsound
    (A.supportWitnessTailPathChildCoherent_of_atomCompleteTimedAtoms htimed)

/--
Conditional concrete Muller state-compilation from the support-witness carrier.

After proving `SupportWitnessSound` and `SupportWitnessBranchRealizable`, this
is the state-wise APA-to-Muller compilation needed by the LTL backend.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfSoundAndBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hrealizable : A.SupportWitnessBranchRealizable) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_branchRealizable
      hsound hrealizable)

/--
Conditional concrete DPA state-compilation from the support-witness carrier,
using the proved Muller-to-DPA/LAR construction.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfSoundAndBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hrealizable : A.SupportWitnessBranchRealizable) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_branchRealizable
      hsound hrealizable)

/--
Conditional concrete Muller state-compilation from support-witness soundness
and tail-realization completeness.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfSoundAndTailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hrealizable : A.SupportWitnessTailBranchRealizable) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_tailBranchRealizable
      hsound hrealizable)

/--
Conditional concrete DPA state-compilation from support-witness soundness and
tail-realization completeness, using the proved Muller-to-DPA/LAR backend.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfSoundAndTailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hrealizable : A.SupportWitnessTailBranchRealizable) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_tailBranchRealizable
      hsound hrealizable)

/--
Conditional concrete Muller state-compilation from support-witness soundness
and an existentially chosen tail-realizing accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfSoundAndExistsTailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hrealizable : A.SupportWitnessExistsTailBranchRealizable) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_existsTailBranchRealizable
      hsound hrealizable)

/--
Conditional concrete DPA state-compilation from support-witness soundness and
an existentially chosen tail-realizing accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfSoundAndExistsTailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hrealizable : A.SupportWitnessExistsTailBranchRealizable) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_existsTailBranchRealizable
      hsound hrealizable)

/--
Conditional concrete Muller state-compilation from support-witness soundness
and an existentially selected accepting edge-witnessed macro-run.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfSoundAndExistsAcceptingEdgeWitnessedMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hwitness : A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_existsAcceptingEdgeWitnessedMacroRun
      hsound hwitness)

/--
Conditional concrete DPA state-compilation from support-witness soundness and
an existentially selected accepting edge-witnessed macro-run.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfSoundAndExistsAcceptingEdgeWitnessedMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hwitness : A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_existsAcceptingEdgeWitnessedMacroRun
      hsound hwitness)

/--
Conditional concrete Muller state-compilation from support-witness soundness
and an existentially selected macro-run whose recurring support edges are
contained in an accepting finite subgraph.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfSoundAndExistsEdgeWitnessedMacroRunSubgraphAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hwitness : A.SupportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfSoundAndExistsAcceptingEdgeWitnessedMacroRun
    cert hsound
    (A.supportWitnessExistsAcceptingEdgeWitnessedMacroRun_of_subgraphAccepting
      hwitness)

/--
Conditional concrete DPA state-compilation from support-witness soundness and
an existentially selected macro-run whose recurring support edges are contained
in an accepting finite subgraph.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfSoundAndExistsEdgeWitnessedMacroRunSubgraphAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hwitness : A.SupportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfSoundAndExistsAcceptingEdgeWitnessedMacroRun
    cert hsound
    (A.supportWitnessExistsAcceptingEdgeWitnessedMacroRun_of_subgraphAccepting
      hwitness)

/--
Conditional concrete Muller state-compilation from support-witness soundness
and an existentially chosen subtree-local child-coherent accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfSoundAndExistsTailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hcoherent : A.SupportWitnessExistsTailPathChildCoherent) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_existsTailPathChildCoherent
      hsound hcoherent)

/--
Conditional concrete DPA state-compilation from support-witness soundness and
an existentially chosen subtree-local child-coherent accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfSoundAndExistsTailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hcoherent : A.SupportWitnessExistsTailPathChildCoherent) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_existsTailPathChildCoherent
      hsound hcoherent)

/--
Conditional concrete Muller state-compilation from support-witness soundness
and an existentially chosen node-local accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfSoundAndExistsRecurringEdgesNodeLocalComplete
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hlocal : A.SupportWitnessExistsRecurringEdgesNodeLocalComplete) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_existsRecurringEdgesNodeLocalComplete
      hsound hlocal)

/--
Conditional concrete DPA state-compilation from support-witness soundness and
an existentially chosen node-local accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfSoundAndExistsRecurringEdgesNodeLocalComplete
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hlocal : A.SupportWitnessExistsRecurringEdgesNodeLocalComplete) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_existsRecurringEdgesNodeLocalComplete
      hsound hlocal)

/--
Conditional concrete DPA state-compilation from support-witness soundness and
the subtree-local tail-child-extension recurrence target.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfSoundAndTailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hcoherent : A.SupportWitnessTailPathChildCoherent) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_tailPathChildCoherent
      hsound hcoherent)

/--
Conditional concrete DPA state-compilation from support-witness soundness and
the fixed-point/tableau timed-atom recurrence target.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfSoundAndAtomCompleteTimedAtoms
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (htimed : A.SupportWitnessAtomCompleteTimedAtoms) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_atomCompleteTimedAtoms
      hsound htimed)

/--
Conditional concrete Muller state-compilation from support-witness soundness
and an existentially chosen atom-complete timed-atom accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfSoundAndExistsAtomCompleteTimedAtoms
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (htimed : A.SupportWitnessExistsAtomCompleteTimedAtoms) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_existsAtomCompleteTimedAtoms
      hsound htimed)

/--
Conditional concrete DPA state-compilation from support-witness soundness and
an existentially chosen atom-complete timed-atom accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfSoundAndExistsAtomCompleteTimedAtoms
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (htimed : A.SupportWitnessExistsAtomCompleteTimedAtoms) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_existsAtomCompleteTimedAtoms
      hsound htimed)

/--
Conditional concrete DPA state-compilation from support-witness soundness and
the exact branch-stable node-local recurrence target.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfSoundAndNodeLocal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hlocal : A.SupportWitnessNodeLocalTailRealizable) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_nodeLocal hsound hlocal)

/--
Concrete state-wise Muller determinization from support-witness soundness and
the local child-extension coherence form of completeness.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfSoundAndPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hcoherent : A.SupportWitnessPathChildCoherent) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_pathChildCoherent
      hsound hcoherent)

/--
Concrete state-wise DPA compilation from support-witness soundness and local
child-extension coherence, using the proved Muller-to-DPA/LAR backend.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfSoundAndPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsound : A.SupportWitnessSound)
    (hcoherent : A.SupportWitnessPathChildCoherent) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_sound_and_pathChildCoherent
      hsound hcoherent)

/--
The concrete support-witness equivalence using the semantic macro-run
realization obligation for soundness and branch-coherence for completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalSemantic_and_branchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hrealizable : A.SupportWitnessBranchRealizable) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_branchRealizable
    (A.supportWitnessSound_of_operationalWitness_semanticMacroRun hsemantic)
    hrealizable

/--
Concrete support-witness equivalence using the semantic macro-run realization
obligation for soundness and the weaker tail-realization form for
completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalSemantic_and_tailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hrealizable : A.SupportWitnessTailBranchRealizable) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_tailBranchRealizable
    (A.supportWitnessSound_of_operationalWitness_semanticMacroRun hsemantic)
    hrealizable

/--
Concrete support-witness equivalence using the semantic macro-run realization
obligation for soundness and the exact branch-stable node-local recurrence
target for completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalSemantic_and_nodeLocal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hlocal : A.SupportWitnessNodeLocalTailRealizable) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_nodeLocal
    (A.supportWitnessSound_of_operationalWitness_semanticMacroRun hsemantic)
    hlocal

/--
Concrete support-witness equivalence using operational semantic macro-runs for
soundness and the fixed-point/tableau timed-atom recurrence target for
completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalSemantic_and_atomCompleteTimedAtoms
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (htimed : A.SupportWitnessAtomCompleteTimedAtoms) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_atomCompleteTimedAtoms
    (A.supportWitnessSound_of_operationalWitness_semanticMacroRun hsemantic)
    htimed

/--
Concrete support-witness equivalence from operational semantic macro-runs for
soundness and local child-extension coherence for completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalSemantic_and_pathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hcoherent : A.SupportWitnessPathChildCoherent) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_pathChildCoherent
    (A.supportWitnessSound_of_operationalWitness_semanticMacroRun hsemantic)
    hcoherent

/--
Concrete support-witness equivalence from operational semantic macro-runs for
soundness and an existentially chosen subtree-local child-coherent accepting
run tree for completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalSemantic_and_existsTailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hcoherent : A.SupportWitnessExistsTailPathChildCoherent) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_existsTailPathChildCoherent
    (A.supportWitnessSound_of_operationalWitness_semanticMacroRun hsemantic)
    hcoherent

/--
Concrete support-witness equivalence from operational semantic macro-runs for
soundness and an existentially selected accepting edge-witnessed macro-run for
completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalSemantic_and_existsAcceptingEdgeWitnessedMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hwitness : A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_existsAcceptingEdgeWitnessedMacroRun
    (A.supportWitnessSound_of_operationalWitness_semanticMacroRun hsemantic)
    hwitness

/--
Concrete support-witness equivalence from operational semantic macro-runs for
soundness and the flexible subgraph-accepting edge-witnessed macro-run endpoint.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalSemantic_and_existsEdgeWitnessedMacroRunSubgraphAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hwitness : A.SupportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_existsEdgeWitnessedMacroRunSubgraphAccepting
    (A.supportWitnessSound_of_operationalWitness_semanticMacroRun hsemantic)
    hwitness

/--
Concrete support-witness equivalence from operational semantic macro-runs for
soundness and an existentially chosen node-local accepting run tree for
completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalSemantic_and_existsRecurringEdgesNodeLocalComplete
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hlocal : A.SupportWitnessExistsRecurringEdgesNodeLocalComplete) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_existsRecurringEdgesNodeLocalComplete
    (A.supportWitnessSound_of_operationalWitness_semanticMacroRun hsemantic)
    hlocal

/--
Concrete support-witness equivalence where the soundness side is supplied in
the prefix-continuation form: every accepted operational witness has a finite
macro-run prefix whose frontier states all accept the remaining suffix.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalPrefix_and_branchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hrealizable : A.SupportWitnessBranchRealizable) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_branchRealizable
    (A.supportWitnessSound_of_operationalWitness_prefix_accepts hpref)
    hrealizable

/--
Concrete support-witness equivalence from prefix-continuation soundness and
tail-realization completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalPrefix_and_tailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hrealizable : A.SupportWitnessTailBranchRealizable) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_tailBranchRealizable
    (A.supportWitnessSound_of_operationalWitness_prefix_accepts hpref)
    hrealizable

/--
Concrete support-witness equivalence from prefix-continuation soundness and
the exact branch-stable node-local recurrence target for completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalPrefix_and_nodeLocal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hlocal : A.SupportWitnessNodeLocalTailRealizable) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_nodeLocal
    (A.supportWitnessSound_of_operationalWitness_prefix_accepts hpref)
    hlocal

/--
Concrete support-witness equivalence from prefix-continuation soundness and the
fixed-point/tableau timed-atom recurrence target.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalPrefix_and_atomCompleteTimedAtoms
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (htimed : A.SupportWitnessAtomCompleteTimedAtoms) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_atomCompleteTimedAtoms
    (A.supportWitnessSound_of_operationalWitness_prefix_accepts hpref)
    htimed

/--
Concrete support-witness equivalence from prefix-continuation soundness and
local child-extension coherence for completeness.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalPrefix_and_pathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hcoherent : A.SupportWitnessPathChildCoherent) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_pathChildCoherent
    (A.supportWitnessSound_of_operationalWitness_prefix_accepts hpref)
    hcoherent

/--
Concrete support-witness equivalence from prefix-continuation soundness and an
existentially chosen subtree-local child-coherent accepting run tree.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalPrefix_and_existsTailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hcoherent : A.SupportWitnessExistsTailPathChildCoherent) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_existsTailPathChildCoherent
    (A.supportWitnessSound_of_operationalWitness_prefix_accepts hpref)
    hcoherent

/--
Concrete support-witness equivalence from prefix-continuation soundness and an
existentially selected accepting edge-witnessed macro-run.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalPrefix_and_existsAcceptingEdgeWitnessedMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hwitness : A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_existsAcceptingEdgeWitnessedMacroRun
    (A.supportWitnessSound_of_operationalWitness_prefix_accepts hpref)
    hwitness

/--
Concrete support-witness equivalence from prefix-continuation soundness and
the flexible subgraph-accepting edge-witnessed macro-run endpoint.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalPrefix_and_existsEdgeWitnessedMacroRunSubgraphAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hwitness : A.SupportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_existsEdgeWitnessedMacroRunSubgraphAccepting
    (A.supportWitnessSound_of_operationalWitness_prefix_accepts hpref)
    hwitness

/--
Concrete support-witness equivalence from prefix-continuation soundness and an
existentially chosen node-local accepting run tree.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_correct_of_operationalPrefix_and_existsRecurringEdgesNodeLocalComplete
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hlocal : A.SupportWitnessExistsRecurringEdgesNodeLocalComplete) :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word ↔
        A.AcceptsFrom state word :=
  A.supportWitnessMuller_correct_of_sound_and_existsRecurringEdgesNodeLocalComplete
    (A.supportWitnessSound_of_operationalWitness_prefix_accepts hpref)
    hlocal

/--
Conditional concrete Muller state-compilation phrased against the remaining
operational obligations rather than the abstract `SupportWitnessSound` field.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalSemanticAndBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hrealizable : A.SupportWitnessBranchRealizable) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_branchRealizable
      hsemantic hrealizable)

/--
Conditional concrete Muller state-compilation from operational semantic
soundness and tail-realization completeness.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalSemanticAndTailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hrealizable : A.SupportWitnessTailBranchRealizable) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_tailBranchRealizable
      hsemantic hrealizable)

/--
Conditional concrete Muller state-compilation from operational semantic
soundness and the node-local completeness target.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalSemanticAndNodeLocal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hlocal : A.SupportWitnessNodeLocalTailRealizable) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_nodeLocal
      hsemantic hlocal)

/--
Conditional concrete Muller state-compilation from operational semantic
soundness and local child-extension coherence.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalSemanticAndPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hcoherent : A.SupportWitnessPathChildCoherent) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_pathChildCoherent
      hsemantic hcoherent)

/--
Conditional concrete Muller state-compilation from operational semantic
soundness and an existentially chosen tail-child-coherent accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalSemanticAndExistsTailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hcoherent : A.SupportWitnessExistsTailPathChildCoherent) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_existsTailPathChildCoherent
      hsemantic hcoherent)

/--
Conditional concrete Muller state-compilation from operational semantic
soundness and an existentially selected accepting edge-witnessed macro-run.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalSemanticAndExistsAcceptingEdgeWitnessedMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hwitness : A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_existsAcceptingEdgeWitnessedMacroRun
      hsemantic hwitness)

/--
Conditional concrete Muller state-compilation from operational semantic
soundness and an existentially selected macro-run whose recurring support edges
are contained in an accepting finite subgraph.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalSemanticAndExistsEdgeWitnessedMacroRunSubgraphAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hwitness : A.SupportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfOperationalSemanticAndExistsAcceptingEdgeWitnessedMacroRun
    cert hsemantic
    (A.supportWitnessExistsAcceptingEdgeWitnessedMacroRun_of_subgraphAccepting
      hwitness)

/--
Conditional concrete Muller state-compilation from operational semantic
soundness and an existentially chosen node-local accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalSemanticAndExistsRecurringEdgesNodeLocalComplete
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hlocal : A.SupportWitnessExistsRecurringEdgesNodeLocalComplete) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_existsRecurringEdgesNodeLocalComplete
      hsemantic hlocal)

/--
Conditional concrete Muller state-compilation from the support-witness carrier,
using the prefix-continuation form of the soundness obligation and
branch-coherence for completeness.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalPrefixAndBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hrealizable : A.SupportWitnessBranchRealizable) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_branchRealizable
      hpref hrealizable)

/--
Conditional concrete Muller state-compilation from prefix-continuation
soundness and tail-realization completeness.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalPrefixAndTailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hrealizable : A.SupportWitnessTailBranchRealizable) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_tailBranchRealizable
      hpref hrealizable)

/--
Conditional concrete Muller state-compilation from prefix-continuation
soundness and the node-local completeness target.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalPrefixAndNodeLocal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hlocal : A.SupportWitnessNodeLocalTailRealizable) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_nodeLocal
      hpref hlocal)

/--
Conditional concrete Muller state-compilation from prefix-continuation soundness
and local child-extension coherence.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalPrefixAndPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hcoherent : A.SupportWitnessPathChildCoherent) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_pathChildCoherent
      hpref hcoherent)

/--
Conditional concrete Muller state-compilation from prefix-continuation
soundness and an existentially chosen tail-child-coherent accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalPrefixAndExistsTailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hcoherent : A.SupportWitnessExistsTailPathChildCoherent) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_existsTailPathChildCoherent
      hpref hcoherent)

/--
Conditional concrete Muller state-compilation from prefix-continuation
soundness and an existentially selected accepting edge-witnessed macro-run.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalPrefixAndExistsAcceptingEdgeWitnessedMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hwitness : A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_existsAcceptingEdgeWitnessedMacroRun
      hpref hwitness)

/--
Conditional concrete Muller state-compilation from prefix-continuation
soundness and an existentially selected macro-run whose recurring support edges
are contained in an accepting finite subgraph.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalPrefixAndExistsEdgeWitnessedMacroRunSubgraphAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hwitness : A.SupportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfOperationalPrefixAndExistsAcceptingEdgeWitnessedMacroRun
    cert hpref
    (A.supportWitnessExistsAcceptingEdgeWitnessedMacroRun_of_subgraphAccepting
      hwitness)

/--
Conditional concrete Muller state-compilation from prefix-continuation
soundness and an existentially chosen node-local accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessMullerRunStateCompilationOfOperationalPrefixAndExistsRecurringEdgesNodeLocalComplete
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hlocal : A.SupportWitnessExistsRecurringEdgesNodeLocalComplete) :
    APAToMullerStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessMullerRunStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_existsRecurringEdgesNodeLocalComplete
      hpref hlocal)

/--
Conditional concrete DPA state-compilation from the support-witness carrier,
with the exact remaining semantic macro-run and branch-coherence obligations.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalSemanticAndBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hrealizable : A.SupportWitnessBranchRealizable) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_branchRealizable
      hsemantic hrealizable)

/--
Conditional concrete DPA state-compilation from operational semantic soundness
and tail-realization completeness, using the proved Muller-to-DPA/LAR backend.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalSemanticAndTailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hrealizable : A.SupportWitnessTailBranchRealizable) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_tailBranchRealizable
      hsemantic hrealizable)

/--
Conditional concrete DPA state-compilation from operational semantic soundness
and the node-local completeness target, using the proved Muller-to-DPA/LAR
backend.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalSemanticAndNodeLocal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hlocal : A.SupportWitnessNodeLocalTailRealizable) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_nodeLocal
      hsemantic hlocal)

/--
Conditional concrete DPA state-compilation from operational semantic soundness
and the fixed-point/tableau timed-atom recurrence target.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalSemanticAndAtomCompleteTimedAtoms
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (htimed : A.SupportWitnessAtomCompleteTimedAtoms) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_atomCompleteTimedAtoms
      hsemantic htimed)

/--
Conditional concrete DPA state-compilation from operational semantic soundness
and local child-extension coherence.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalSemanticAndPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hcoherent : A.SupportWitnessPathChildCoherent) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_pathChildCoherent
      hsemantic hcoherent)

/--
Conditional concrete DPA state-compilation from operational semantic soundness
and an existentially chosen tail-child-coherent accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalSemanticAndExistsTailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hcoherent : A.SupportWitnessExistsTailPathChildCoherent) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_existsTailPathChildCoherent
      hsemantic hcoherent)

/--
Conditional concrete DPA state-compilation from operational semantic soundness
and an existentially selected accepting edge-witnessed macro-run.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalSemanticAndExistsAcceptingEdgeWitnessedMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hwitness : A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_existsAcceptingEdgeWitnessedMacroRun
      hsemantic hwitness)

/--
Conditional concrete DPA state-compilation from operational semantic soundness
and an existentially selected macro-run whose recurring support edges are
contained in an accepting finite subgraph.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalSemanticAndExistsEdgeWitnessedMacroRunSubgraphAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hwitness : A.SupportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfOperationalSemanticAndExistsAcceptingEdgeWitnessedMacroRun
    cert hsemantic
    (A.supportWitnessExistsAcceptingEdgeWitnessedMacroRun_of_subgraphAccepting
      hwitness)

/--
Conditional concrete DPA state-compilation from operational semantic soundness
and an existentially chosen node-local accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalSemanticAndExistsRecurringEdgesNodeLocalComplete
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hsemantic :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          (A.supportOperationalWitness_of_supportWitnessMuller_accepts
            haccepts).HasSemanticMacroRun)
    (hlocal : A.SupportWitnessExistsRecurringEdgesNodeLocalComplete) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalSemantic_and_existsRecurringEdgesNodeLocalComplete
      hsemantic hlocal)

/--
Conditional concrete DPA state-compilation from the support-witness carrier,
using the prefix-continuation form of the soundness obligation and the proved
Muller-to-DPA/LAR construction.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalPrefixAndBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hrealizable : A.SupportWitnessBranchRealizable) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_branchRealizable
      hpref hrealizable)

/--
Conditional concrete DPA state-compilation from prefix-continuation soundness
and tail-realization completeness, using the proved Muller-to-DPA/LAR backend.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalPrefixAndTailBranchRealizable
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hrealizable : A.SupportWitnessTailBranchRealizable) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_tailBranchRealizable
      hpref hrealizable)

/--
Conditional concrete DPA state-compilation from prefix-continuation soundness
and the node-local completeness target, using the proved Muller-to-DPA/LAR
backend.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalPrefixAndNodeLocal
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hlocal : A.SupportWitnessNodeLocalTailRealizable) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_nodeLocal
      hpref hlocal)

/--
Conditional concrete DPA state-compilation from prefix-continuation soundness
and the fixed-point/tableau timed-atom recurrence target.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalPrefixAndAtomCompleteTimedAtoms
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (htimed : A.SupportWitnessAtomCompleteTimedAtoms) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_atomCompleteTimedAtoms
      hpref htimed)

/--
Conditional concrete DPA state-compilation from prefix-continuation soundness
and local child-extension coherence.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalPrefixAndPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hcoherent : A.SupportWitnessPathChildCoherent) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_pathChildCoherent
      hpref hcoherent)

/--
Conditional concrete DPA state-compilation from prefix-continuation soundness
and an existentially chosen tail-child-coherent accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalPrefixAndExistsTailPathChildCoherent
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hcoherent : A.SupportWitnessExistsTailPathChildCoherent) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_existsTailPathChildCoherent
      hpref hcoherent)

/--
Conditional concrete DPA state-compilation from prefix-continuation soundness
and an existentially selected accepting edge-witnessed macro-run.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalPrefixAndExistsAcceptingEdgeWitnessedMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hwitness : A.SupportWitnessExistsAcceptingEdgeWitnessedMacroRun) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_existsAcceptingEdgeWitnessedMacroRun
      hpref hwitness)

/--
Conditional concrete DPA state-compilation from prefix-continuation soundness
and an existentially selected macro-run whose recurring support edges are
contained in an accepting finite subgraph.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalPrefixAndExistsEdgeWitnessedMacroRunSubgraphAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hwitness : A.SupportWitnessExistsEdgeWitnessedMacroRunSubgraphAccepting) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfOperationalPrefixAndExistsAcceptingEdgeWitnessedMacroRun
    cert hpref
    (A.supportWitnessExistsAcceptingEdgeWitnessedMacroRun_of_subgraphAccepting
      hwitness)

/--
Conditional concrete DPA state-compilation from prefix-continuation soundness
and an existentially chosen node-local accepting run tree.
-/
noncomputable def AlternatingParityAutomaton.supportWitnessDPAStateCompilationOfOperationalPrefixAndExistsRecurringEdgesNodeLocalComplete
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate)
    (hpref :
      ∀ (state : A.State) (word : OmegaWord Alphabet),
        ∀ haccepts :
          (A.supportWitnessMuller ({state} : Finset A.State)).Accepts word,
          ∃ offset : Nat,
            ∃ pref : A.MacroRunPrefix ({state} : Finset A.State) word offset,
              ∀ nextState, nextState ∈ pref.states offset ->
                A.AcceptsFrom nextState (OmegaWord.drop word offset))
    (hlocal : A.SupportWitnessExistsRecurringEdgesNodeLocalComplete) :
    APAToDPAStateCompilation.{u, v, v} A cert.toLanguageCertificate :=
  A.supportWitnessDPAStateCompilationOfCorrect cert
    (A.supportWitnessMuller_correct_of_operationalPrefix_and_existsRecurringEdgesNodeLocalComplete
      hpref hlocal)

/--
A concrete macro-run whose recurring support-edge graph is parity accepting
makes the witness-based support Muller automaton accept the word.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_accepts_of_macroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (haccepting : A.SupportWitnessStateEdgesAccepting run.infStateEdgeFinset) :
    (A.supportWitnessMuller initialStates).Accepts word := by
  have hwitness :
      A.SupportRecurrentWitness
        ((A.supportWitnessMuller initialStates).InfStates word) := by
    simpa [AlternatingParityAutomaton.supportWitnessMuller] using
      run.supportRecurrentWitness_of_recurringSupportAccepting
        A.supportWitnessAcceptingFamily haccepting
  exact
    (A.supportWitnessMuller_accepts_iff initialStates word).mpr hwitness

/--
For a concrete macro-run, acceptance by the provisional support-configuration
Muller condition is strong enough to make the witness-based support Muller
automaton accept.
-/
theorem AlternatingParityAutomaton.supportWitnessMuller_accepts_of_supportConfigurationMuller_accepts
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (run : A.MacroRun initialStates word)
    (haccepts : (A.supportConfigurationMuller initialStates).Accepts word) :
    (A.supportWitnessMuller initialStates).Accepts word :=
  A.supportWitnessMuller_accepts_of_macroRun run
    (run.supportWitnessStateEdgesAccepting_of_supportConfigurationMuller_accepts haccepts)

/--
Semantic macro-run acceptance yields an accepting macro-state that is visible
inside a recurring state of the deterministic configuration skeleton.
-/
theorem AlternatingParityAutomaton.exists_recurringConfigurationState_of_semanticAccepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {initialStates : Finset A.State}
    {word : OmegaWord Alphabet}
    (accepting : Set (Set (APAMacroConfigurationState A)))
    (run : A.MacroRun initialStates word)
    (haccepting : run.SemanticAccepting) :
    ∃ configState :
        (A.macroConfigurationMullerSkeleton initialStates accepting).State,
      configState ∈
        (A.macroConfigurationMullerSkeleton initialStates accepting).infStateFinset word ∧
        ∃ offset : Nat,
          run.states offset ∈ configState.configs ∧
            ∀ state, state ∈ run.states offset ->
              A.AcceptsFrom state (OmegaWord.drop word offset) := by
  classical
  rcases haccepting with ⟨offset, hrecurs, haccepts⟩
  have hseen : run.StateSeenInfinitelyOften (run.states offset) :=
    (run.mem_infStateFinset (run.states offset)).mp hrecurs
  rcases
    A.exists_recurringConfigurationState_of_macroRun_stateSeen
      accepting run hseen with
    ⟨configState, hconfigRecurring, hcontains⟩
  exact ⟨configState, hconfigRecurring, offset, hcontains, haccepts⟩

end DistributedSynthesis
