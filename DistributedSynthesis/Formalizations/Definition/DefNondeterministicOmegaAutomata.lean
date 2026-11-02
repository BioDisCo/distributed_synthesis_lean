/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import DistributedSynthesis.Formalizations.Definition.DefOmegaAutomata

/-!
# Nondeterministic omega automata

This file adds the nondeterministic Büchi and Streett word automata used as the
standard intermediate target for Safra/Piterman determinization.  The
definitions are intentionally semantic: a word is accepted when there exists an
infinite run satisfying the relevant omega condition.
-/

namespace DistributedSynthesis

universe u v w

/-- A finite nondeterministic Büchi automaton over infinite words. -/
structure NondetBuchiAutomaton (Alphabet : Type u) where
  State : Type v
  stateFinite : Fintype State
  initial : State
  step : State -> Alphabet -> State -> Prop
  accepting : State -> Prop

attribute [instance] NondetBuchiAutomaton.stateFinite

namespace NondetBuchiAutomaton

/-- A run of a nondeterministic Büchi automaton from an explicit state. -/
structure RunFrom {Alphabet : Type u}
    (A : NondetBuchiAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) where
  path : Nat -> A.State
  initial_state : path 0 = state
  step_valid :
    ∀ n : Nat, A.step (path n) (word n) (path (n + 1))

/-- A predicate holds infinitely often along a nondeterministic run path. -/
def SeenInfinitelyOftenOn {Alphabet : Type u}
    {A : NondetBuchiAutomaton.{u, v} Alphabet}
    (path : Nat -> A.State)
    (predicate : A.State -> Prop) : Prop :=
  ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ predicate (path k)

/-- Büchi acceptance for a particular run. -/
def RunFrom.Accepts {Alphabet : Type u}
    {A : NondetBuchiAutomaton.{u, v} Alphabet}
    {state : A.State}
    {word : OmegaWord Alphabet}
    (run : A.RunFrom state word) : Prop :=
  SeenInfinitelyOftenOn run.path A.accepting

/-- Acceptance from an explicit initial state. -/
def AcceptsFrom {Alphabet : Type u}
    (A : NondetBuchiAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) : Prop :=
  ∃ run : A.RunFrom state word, run.Accepts

/-- Acceptance from the automaton's initial state. -/
def Accepts {Alphabet : Type u}
    (A : NondetBuchiAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) : Prop :=
  A.AcceptsFrom A.initial word

@[simp]
theorem acceptsFrom_initial {Alphabet : Type u}
    (A : NondetBuchiAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    A.AcceptsFrom A.initial word = A.Accepts word :=
  rfl

/-- The omega-language accepted by a nondeterministic Büchi automaton. -/
def Language {Alphabet : Type u}
    (A : NondetBuchiAutomaton.{u, v} Alphabet) :
    Set (OmegaWord Alphabet) :=
  { word | A.Accepts word }

/-- Language recognition predicate for nondeterministic Büchi automata. -/
def Recognizes {Alphabet : Type u}
    (A : NondetBuchiAutomaton.{u, v} Alphabet)
    (language : Set (OmegaWord Alphabet)) : Prop :=
  ∀ word : OmegaWord Alphabet, A.Accepts word ↔ word ∈ language

end NondetBuchiAutomaton

/-- A finite nondeterministic Streett automaton over infinite words. -/
structure NondetStreettAutomaton (Alphabet : Type u) where
  State : Type v
  stateFinite : Fintype State
  initial : State
  step : State -> Alphabet -> State -> Prop
  Index : Type w
  indexFinite : Fintype Index
  request : Index -> State -> Prop
  grant : Index -> State -> Prop

attribute [instance] NondetStreettAutomaton.stateFinite
attribute [instance] NondetStreettAutomaton.indexFinite

namespace NondetStreettAutomaton

/-- A run of a nondeterministic Streett automaton from an explicit state. -/
structure RunFrom {Alphabet : Type u}
    (A : NondetStreettAutomaton.{u, v, w} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) where
  path : Nat -> A.State
  initial_state : path 0 = state
  step_valid :
    ∀ n : Nat, A.step (path n) (word n) (path (n + 1))

/-- A predicate holds infinitely often along a nondeterministic run path. -/
def SeenInfinitelyOftenOn {Alphabet : Type u}
    {A : NondetStreettAutomaton.{u, v, w} Alphabet}
    (path : Nat -> A.State)
    (predicate : A.State -> Prop) : Prop :=
  ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ predicate (path k)

/--
Streett acceptance for a particular run: for every pair, infinitely many
requests imply infinitely many grants.
-/
def RunFrom.Accepts {Alphabet : Type u}
    {A : NondetStreettAutomaton.{u, v, w} Alphabet}
    {state : A.State}
    {word : OmegaWord Alphabet}
    (run : A.RunFrom state word) : Prop :=
  ∀ index : A.Index,
    SeenInfinitelyOftenOn run.path (A.request index) ->
      SeenInfinitelyOftenOn run.path (A.grant index)

/-- Acceptance from an explicit initial state. -/
def AcceptsFrom {Alphabet : Type u}
    (A : NondetStreettAutomaton.{u, v, w} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) : Prop :=
  ∃ run : A.RunFrom state word, run.Accepts

/-- Acceptance from the automaton's initial state. -/
def Accepts {Alphabet : Type u}
    (A : NondetStreettAutomaton.{u, v, w} Alphabet)
    (word : OmegaWord Alphabet) : Prop :=
  A.AcceptsFrom A.initial word

@[simp]
theorem acceptsFrom_initial {Alphabet : Type u}
    (A : NondetStreettAutomaton.{u, v, w} Alphabet)
    (word : OmegaWord Alphabet) :
    A.AcceptsFrom A.initial word = A.Accepts word :=
  rfl

/-- The omega-language accepted by a nondeterministic Streett automaton. -/
def Language {Alphabet : Type u}
    (A : NondetStreettAutomaton.{u, v, w} Alphabet) :
    Set (OmegaWord Alphabet) :=
  { word | A.Accepts word }

/-- Language recognition predicate for nondeterministic Streett automata. -/
def Recognizes {Alphabet : Type u}
    (A : NondetStreettAutomaton.{u, v, w} Alphabet)
    (language : Set (OmegaWord Alphabet)) : Prop :=
  ∀ word : OmegaWord Alphabet, A.Accepts word ↔ word ∈ language

end NondetStreettAutomaton

/-- A finite nondeterministic Muller automaton over infinite words. -/
structure NondetMullerAutomaton (Alphabet : Type u) where
  State : Type v
  stateFinite : Fintype State
  initial : State
  step : State -> Alphabet -> State -> Prop
  accepting : Set (Finset State)

attribute [instance] NondetMullerAutomaton.stateFinite

namespace NondetMullerAutomaton

/-- A run of a nondeterministic Muller automaton from an explicit state. -/
structure RunFrom {Alphabet : Type u}
    (A : NondetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) where
  path : Nat -> A.State
  initial_state : path 0 = state
  step_valid :
    ∀ n : Nat, A.step (path n) (word n) (path (n + 1))

/-- A state appears infinitely often along a nondeterministic run path. -/
def RunFrom.StateSeenInfinitelyOften {Alphabet : Type u}
    {A : NondetMullerAutomaton.{u, v} Alphabet}
    {state : A.State}
    {word : OmegaWord Alphabet}
    (run : A.RunFrom state word)
    (q : A.State) : Prop :=
  ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ run.path k = q

/-- The finite set of states visited infinitely often by a Muller run. -/
noncomputable def RunFrom.infStateFinset {Alphabet : Type u}
    {A : NondetMullerAutomaton.{u, v} Alphabet}
    {state : A.State}
    {word : OmegaWord Alphabet}
    (run : A.RunFrom state word) : Finset A.State := by
  classical
  exact Finset.univ.filter run.StateSeenInfinitelyOften

theorem RunFrom.mem_infStateFinset {Alphabet : Type u}
    {A : NondetMullerAutomaton.{u, v} Alphabet}
    {state q : A.State}
    {word : OmegaWord Alphabet}
    (run : A.RunFrom state word) :
    q ∈ run.infStateFinset ↔ run.StateSeenInfinitelyOften q := by
  classical
  simp [RunFrom.infStateFinset]

/--
For a finite-state run, seeing a predicate infinitely often is equivalent to
some recurring state satisfying that predicate.
-/
theorem RunFrom.seenInfinitelyOftenOn_iff_exists_mem_infStateFinset
    {Alphabet : Type u}
    {A : NondetMullerAutomaton.{u, v} Alphabet}
    {state : A.State}
    {word : OmegaWord Alphabet}
    (run : A.RunFrom state word)
    (predicate : A.State -> Prop) :
    (∀ n : Nat, ∃ k : Nat, n ≤ k ∧ predicate (run.path k)) ↔
      ∃ q : A.State, q ∈ run.infStateFinset ∧ predicate q := by
  classical
  constructor
  · intro hseen
    have hfreq :
        ∃ᶠ n in Filter.atTop, predicate (run.path n) :=
      (Filter.frequently_atTop).2 hseen
    have hfreqExists :
        ∃ᶠ n in Filter.atTop,
          ∃ q ∈ (Finset.univ : Finset A.State),
            q = run.path n ∧ predicate q :=
      hfreq.mono fun n hn =>
        ⟨run.path n, Finset.mem_univ _, rfl, hn⟩
    rw [Finset.frequently_exists] at hfreqExists
    rcases hfreqExists with ⟨q, _hquniv, hqfreq⟩
    have hqInf : run.StateSeenInfinitelyOften q := by
      intro n
      rcases (Filter.frequently_atTop).1 hqfreq n with
        ⟨k, hk, hqk, _hqpred⟩
      exact ⟨k, hk, hqk.symm⟩
    have hqPred : predicate q := by
      rcases (Filter.frequently_atTop).1 hqfreq 0 with
        ⟨_k, _hk, _hqk, hqpred⟩
      exact hqpred
    exact ⟨q, (run.mem_infStateFinset).mpr hqInf, hqPred⟩
  · rintro ⟨q, hqinf, hqpred⟩ n
    rcases (run.mem_infStateFinset).mp hqinf n with ⟨k, hk, hkq⟩
    exact ⟨k, hk, by simpa [hkq] using hqpred⟩

/-- Muller acceptance for a particular run. -/
noncomputable def RunFrom.Accepts {Alphabet : Type u}
    {A : NondetMullerAutomaton.{u, v} Alphabet}
    {state : A.State}
    {word : OmegaWord Alphabet}
    (run : A.RunFrom state word) : Prop :=
  run.infStateFinset ∈ A.accepting

/-- Acceptance from an explicit initial state. -/
noncomputable def AcceptsFrom {Alphabet : Type u}
    (A : NondetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) : Prop :=
  ∃ run : A.RunFrom state word, run.Accepts

/-- Acceptance from the automaton's initial state. -/
noncomputable def Accepts {Alphabet : Type u}
    (A : NondetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) : Prop :=
  A.AcceptsFrom A.initial word

@[simp]
theorem acceptsFrom_initial {Alphabet : Type u}
    (A : NondetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    A.AcceptsFrom A.initial word = A.Accepts word :=
  rfl

/-- The omega-language accepted by a nondeterministic Muller automaton. -/
noncomputable def Language {Alphabet : Type u}
    (A : NondetMullerAutomaton.{u, v} Alphabet) :
    Set (OmegaWord Alphabet) :=
  { word | A.Accepts word }

/-- Language recognition predicate for nondeterministic Muller automata. -/
noncomputable def Recognizes {Alphabet : Type u}
    (A : NondetMullerAutomaton.{u, v} Alphabet)
    (language : Set (OmegaWord Alphabet)) : Prop :=
  ∀ word : OmegaWord Alphabet, A.Accepts word ↔ word ∈ language

end NondetMullerAutomaton

namespace NondetStreettAutomaton

/--
View a nondeterministic Streett automaton as a nondeterministic Muller
automaton over the same transition graph.

The Muller accepting sets are exactly those recurring-state sets that satisfy
all Streett pairs: if some request state for a pair recurs, then some matching
grant state recurs.
-/
def toMuller {Alphabet : Type u}
    (A : NondetStreettAutomaton.{u, v, w} Alphabet) :
    NondetMullerAutomaton.{u, v} Alphabet where
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  step := A.step
  accepting :=
    { recurring |
      ∀ index : A.Index,
        (∃ q : A.State, q ∈ recurring ∧ A.request index q) ->
          ∃ q : A.State, q ∈ recurring ∧ A.grant index q }

namespace RunFrom

/-- Repackage a Streett run as a run of the Muller view. -/
def toMuller {Alphabet : Type u}
    {A : NondetStreettAutomaton.{u, v, w} Alphabet}
    {state : A.State}
    {word : OmegaWord Alphabet}
    (run : A.RunFrom state word) :
    A.toMuller.RunFrom state word where
  path := run.path
  initial_state := run.initial_state
  step_valid := run.step_valid

/-- Repackage a run of the Muller view as a Streett run. -/
def ofMuller {Alphabet : Type u}
    {A : NondetStreettAutomaton.{u, v, w} Alphabet}
    {state : A.State}
    {word : OmegaWord Alphabet}
    (run : A.toMuller.RunFrom state word) :
    A.RunFrom state word where
  path := run.path
  initial_state := run.initial_state
  step_valid := run.step_valid

end RunFrom

theorem toMuller_acceptsFrom_iff {Alphabet : Type u}
    (A : NondetStreettAutomaton.{u, v, w} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    A.toMuller.AcceptsFrom state word ↔ A.AcceptsFrom state word := by
  classical
  constructor
  · intro h
    rcases h with ⟨mullerRun, hmullerAccepts⟩
    refine ⟨NondetStreettAutomaton.RunFrom.ofMuller mullerRun, ?_⟩
    have hmullerAccepting :
        ∀ index : A.Index,
          (∃ q : A.State,
            q ∈ mullerRun.infStateFinset ∧ A.request index q) ->
            ∃ q : A.State,
              q ∈ mullerRun.infStateFinset ∧ A.grant index q := by
      simpa [NondetStreettAutomaton.toMuller,
        NondetMullerAutomaton.RunFrom.Accepts] using hmullerAccepts
    intro index hrequest
    have hrequestRecurring :
        ∃ q : A.State,
          q ∈ mullerRun.infStateFinset ∧ A.request index q :=
      (mullerRun.seenInfinitelyOftenOn_iff_exists_mem_infStateFinset
        (A.request index)).mp hrequest
    rcases hmullerAccepting index hrequestRecurring with
      ⟨q, hqinf, hqgrant⟩
    have hqseen : mullerRun.StateSeenInfinitelyOften q :=
      (mullerRun.mem_infStateFinset).mp hqinf
    intro n
    rcases hqseen n with ⟨k, hk, hkq⟩
    exact ⟨k, hk, by simpa [NondetStreettAutomaton.RunFrom.ofMuller, hkq] using hqgrant⟩
  · intro h
    rcases h with ⟨streettRun, hstreettAccepts⟩
    let mullerRun : A.toMuller.RunFrom state word := streettRun.toMuller
    refine ⟨mullerRun, ?_⟩
    dsimp [NondetMullerAutomaton.RunFrom.Accepts,
      NondetStreettAutomaton.toMuller]
    intro index hrequestRecurring
    have hrequest :
        NondetStreettAutomaton.SeenInfinitelyOftenOn
          streettRun.path (A.request index) := by
      intro n
      rcases hrequestRecurring with ⟨q, hqinf, hqrequest⟩
      have hqseen : mullerRun.StateSeenInfinitelyOften q :=
        (mullerRun.mem_infStateFinset).mp hqinf
      rcases hqseen n with ⟨k, hk, hkq⟩
      have hpathq : streettRun.path k = q := by
        simpa [mullerRun, NondetStreettAutomaton.RunFrom.toMuller] using hkq
      exact ⟨k, hk, by
        simpa [hpathq] using hqrequest⟩
    have hgrant := hstreettAccepts index hrequest
    exact
      (mullerRun.seenInfinitelyOftenOn_iff_exists_mem_infStateFinset
        (A.grant index)).mp hgrant

theorem toMuller_accepts_iff {Alphabet : Type u}
    (A : NondetStreettAutomaton.{u, v, w} Alphabet)
    (word : OmegaWord Alphabet) :
    A.toMuller.Accepts word ↔ A.Accepts word :=
  A.toMuller_acceptsFrom_iff A.initial word

/-- The Muller view recognizes the same language as the Streett automaton. -/
theorem toMuller_recognizes {Alphabet : Type u}
    (A : NondetStreettAutomaton.{u, v, w} Alphabet) :
    A.toMuller.Recognizes A.Language := by
  intro word
  exact A.toMuller_accepts_iff word

end NondetStreettAutomaton

namespace NondetMullerAutomaton

/--
View a nondeterministic Muller automaton as a nondeterministic Streett automaton.

The Streett automaton guesses, on the first transition, the finite set `F` of
states that will be seen infinitely often.  It then keeps that guess fixed.  The
Streett pairs enforce three facts: the guessed set is Muller-accepting, every
state inside the guess recurs infinitely often, and every state outside the guess
recurs only finitely often.
-/
def toStreett {Alphabet : Type u}
    (A : NondetMullerAutomaton.{u, v} Alphabet) :
    NondetStreettAutomaton.{u, v, v} Alphabet where
  State := A.State × Option (Finset A.State)
  stateFinite := inferInstance
  initial := (A.initial, none)
  step := fun state letter nextState =>
    A.step state.1 letter nextState.1 ∧
      match state.2 with
      | none => ∃ recurring : Finset A.State, nextState.2 = some recurring
      | some recurring => nextState.2 = some recurring
  Index := Unit ⊕ (A.State × Bool)
  indexFinite := inferInstance
  request := fun index state =>
    match index with
    | Sum.inl _ => True
    | Sum.inr (q, true) =>
        ∃ recurring : Finset A.State, state.2 = some recurring ∧ q ∈ recurring
    | Sum.inr (q, false) =>
        ∃ recurring : Finset A.State,
          state.2 = some recurring ∧ q ∉ recurring ∧ state.1 = q
  grant := fun index state =>
    match index with
    | Sum.inl _ =>
        ∃ recurring : Finset A.State, state.2 = some recurring ∧
          recurring ∈ A.accepting
    | Sum.inr (q, true) => state.1 = q
    | Sum.inr (_q, false) => False

namespace RunFrom

/-- The Muller run lifted to the Streett view with the accepting recurrent set as guess. -/
noncomputable def toStreett {Alphabet : Type u}
    {A : NondetMullerAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.RunFrom A.initial word) :
    (A.toStreett).RunFrom (A.initial, none) word where
  path := fun n =>
    match n with
    | 0 => (run.path 0, none)
    | n + 1 => (run.path (n + 1), some run.infStateFinset)
  initial_state := by
    simp [NondetMullerAutomaton.toStreett, run.initial_state]
  step_valid := by
    intro n
    cases n with
    | zero =>
        constructor
        · exact run.step_valid 0
        · exact ⟨run.infStateFinset, rfl⟩
    | succ n =>
        constructor
        · exact run.step_valid (n + 1)
        · rfl

end RunFrom

theorem toStreett_accepts_of_accepts {Alphabet : Type u}
    (A : NondetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (h : A.Accepts word) :
    A.toStreett.Accepts word := by
  classical
  rcases h with ⟨run, haccepts⟩
  refine ⟨run.toStreett, ?_⟩
  intro index hrequest
  cases index with
  | inl unitIndex =>
      intro n
      refine ⟨n + 1, Nat.le_succ n, ?_⟩
      exact ⟨run.infStateFinset, rfl, haccepts⟩
  | inr qb =>
      rcases qb with ⟨q, memberSide⟩
      cases memberSide
      · by_cases hq : q ∈ run.infStateFinset
        · exfalso
          rcases hrequest 1 with ⟨k, hk, hkreq⟩
          cases k with
          | zero => omega
          | succ k =>
              rcases hkreq with ⟨recurring, hrecurring, hqnot, hqstate⟩
              injection hrecurring with hrecurringEq
              exact hqnot (hrecurringEq ▸ hq)
        · exfalso
          have hseen : run.StateSeenInfinitelyOften q := by
            intro n
            rcases hrequest (max n 1) with ⟨k, hk, hkreq⟩
            have hnle : n ≤ k := le_trans (Nat.le_max_left n 1) hk
            cases k with
            | zero => omega
            | succ k =>
                rcases hkreq with ⟨recurring, _hrecurring, _hqnot, hqstate⟩
                exact ⟨k + 1, hnle, hqstate⟩
          exact hq ((run.mem_infStateFinset).mpr hseen)
      · by_cases hq : q ∈ run.infStateFinset
        · have hseen : run.StateSeenInfinitelyOften q :=
            (run.mem_infStateFinset).mp hq
          intro n
          rcases hseen n with ⟨k, hk, hqstate⟩
          cases k with
          | zero =>
              refine ⟨0, hk, ?_⟩
              simpa using hqstate
          | succ k =>
              refine ⟨k + 1, hk, ?_⟩
              simpa using hqstate
        · exfalso
          rcases hrequest 1 with ⟨k, hk, hkreq⟩
          cases k with
          | zero => omega
          | succ k =>
              rcases hkreq with ⟨recurring, hrecurring, hqmem⟩
              injection hrecurring with hrecurringEq
              exact hq (hrecurringEq ▸ hqmem)

theorem accepts_of_toStreett_accepts {Alphabet : Type u}
    (A : NondetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (h : A.toStreett.Accepts word) :
    A.Accepts word := by
  classical
  rcases h with ⟨streettRun, hstreettAccepts⟩
  have hstep0 := streettRun.step_valid 0
  have hpath0 : (streettRun.path 0).2 = none := by
    simpa [NondetMullerAutomaton.toStreett] using
      congrArg Prod.snd streettRun.initial_state
  simp [NondetMullerAutomaton.toStreett, hpath0] at hstep0
  rcases hstep0.2 with ⟨recurring, hrecurringOne⟩
  have hguessSucc :
      ∀ n : Nat, (streettRun.path (n + 1)).2 = some recurring := by
    intro n
    induction n with
    | zero =>
        simpa using hrecurringOne
    | succ n ih =>
        have hstep := streettRun.step_valid (n + 1)
        simpa [NondetMullerAutomaton.toStreett, ih] using hstep.2
  have hguess :
      ∀ n : Nat, 1 ≤ n -> (streettRun.path n).2 = some recurring := by
    intro n hn
    cases n with
    | zero => omega
    | succ n =>
        exact hguessSucc n
  let mullerRun : A.RunFrom A.initial word :=
    { path := fun n => (streettRun.path n).1
      initial_state := by
        exact congrArg Prod.fst streettRun.initial_state
      step_valid := by
        intro n
        exact (streettRun.step_valid n).1 }
  have hrecurringAccepting : recurring ∈ A.accepting := by
    have hrequest :
        NondetStreettAutomaton.SeenInfinitelyOftenOn
          streettRun.path ((A.toStreett).request (Sum.inl ())) := by
      intro n
      exact ⟨n, le_rfl, trivial⟩
    have hgrant := hstreettAccepts (Sum.inl ()) hrequest
    rcases hgrant 1 with ⟨k, hk, hkgrant⟩
    rcases hkgrant with ⟨grantRecurring, hgrantGuess, hgrantAccepting⟩
    have hkpos : 1 ≤ k := hk
    have hkguess := hguess k hkpos
    rw [hkguess] at hgrantGuess
    injection hgrantGuess with hEq
    simpa [hEq] using hgrantAccepting
  have hinfEq : mullerRun.infStateFinset = recurring := by
    ext q
    constructor
    · intro hqinf
      by_contra hqnot
      have hseen : mullerRun.StateSeenInfinitelyOften q :=
        (mullerRun.mem_infStateFinset).mp hqinf
      have hrequest :
          NondetStreettAutomaton.SeenInfinitelyOftenOn
            streettRun.path ((A.toStreett).request (Sum.inr (q, false))) := by
        intro n
        rcases hseen (max n 1) with ⟨k, hk, hqstate⟩
        have hnle : n ≤ k := le_trans (Nat.le_max_left n 1) hk
        have hkpos : 1 ≤ k := le_trans (Nat.le_max_right n 1) hk
        exact ⟨k, hnle, recurring, hguess k hkpos, hqnot, hqstate⟩
      have hgrant := hstreettAccepts (Sum.inr (q, false)) hrequest
      rcases hgrant 0 with ⟨_k, _hk, hfalse⟩
      exact False.elim hfalse
    · intro hqmem
      have hrequest :
          NondetStreettAutomaton.SeenInfinitelyOftenOn
            streettRun.path ((A.toStreett).request (Sum.inr (q, true))) := by
        intro n
        let k := max n 1
        have hnle : n ≤ k := Nat.le_max_left n 1
        have hkpos : 1 ≤ k := Nat.le_max_right n 1
        exact ⟨k, hnle, recurring, hguess k hkpos, hqmem⟩
      have hgrant := hstreettAccepts (Sum.inr (q, true)) hrequest
      have hseen : mullerRun.StateSeenInfinitelyOften q := by
        intro n
        rcases hgrant n with ⟨k, hk, hqstate⟩
        exact ⟨k, hk, hqstate⟩
      exact (mullerRun.mem_infStateFinset).mpr hseen
  refine ⟨mullerRun, ?_⟩
  simpa [NondetMullerAutomaton.RunFrom.Accepts, hinfEq] using hrecurringAccepting

theorem toStreett_accepts_iff {Alphabet : Type u}
    (A : NondetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    A.toStreett.Accepts word ↔ A.Accepts word := by
  constructor
  · exact A.accepts_of_toStreett_accepts word
  · exact A.toStreett_accepts_of_accepts word

/-- The Streett view recognizes the same language as the Muller automaton. -/
theorem toStreett_recognizes {Alphabet : Type u}
    (A : NondetMullerAutomaton.{u, v} Alphabet) :
    A.toStreett.Recognizes A.Language := by
  intro word
  exact A.toStreett_accepts_iff word

end NondetMullerAutomaton

namespace NondetBuchiAutomaton

/--
View a nondeterministic Büchi automaton as a one-pair nondeterministic Streett
automaton.  The request is always active, so the Streett condition requires
the Büchi accepting set to be visited infinitely often.
-/
def toStreett {Alphabet : Type u}
    (A : NondetBuchiAutomaton.{u, v} Alphabet) :
    NondetStreettAutomaton.{u, v, 0} Alphabet where
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  step := A.step
  Index := Unit
  indexFinite := inferInstance
  request := fun _ _ => True
  grant := fun _ state => A.accepting state

/-- Repackage a Büchi run as a run of the one-pair Streett view. -/
def RunFrom.toStreett {Alphabet : Type u}
    {A : NondetBuchiAutomaton.{u, v} Alphabet}
    {state : A.State}
    {word : OmegaWord Alphabet}
    (run : A.RunFrom state word) :
    (A.toStreett).RunFrom state word where
  path := run.path
  initial_state := run.initial_state
  step_valid := run.step_valid

/-- Repackage a run of the one-pair Streett view as a Büchi run. -/
def RunFrom.ofStreett {Alphabet : Type u}
    {A : NondetBuchiAutomaton.{u, v} Alphabet}
    {state : A.State}
    {word : OmegaWord Alphabet}
    (run : (A.toStreett).RunFrom state word) :
    A.RunFrom state word where
  path := run.path
  initial_state := run.initial_state
  step_valid := run.step_valid

theorem toStreett_acceptsFrom_iff {Alphabet : Type u}
    (A : NondetBuchiAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    A.toStreett.AcceptsFrom state word ↔ A.AcceptsFrom state word := by
  constructor
  · intro h
    rcases h with ⟨run, haccepts⟩
    refine ⟨RunFrom.ofStreett run, ?_⟩
    have hrequest :
        NondetStreettAutomaton.SeenInfinitelyOftenOn
          run.path ((A.toStreett).request ()) := by
      intro n
      exact ⟨n, le_rfl, trivial⟩
    exact haccepts () hrequest
  · intro h
    rcases h with ⟨run, haccepts⟩
    refine ⟨run.toStreett, ?_⟩
    intro index _hrequest
    cases index
    exact haccepts

theorem toStreett_accepts_iff {Alphabet : Type u}
    (A : NondetBuchiAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    A.toStreett.Accepts word ↔ A.Accepts word :=
  A.toStreett_acceptsFrom_iff A.initial word

/-- The one-pair Streett view recognizes the same language as the Büchi automaton. -/
theorem toStreett_recognizes {Alphabet : Type u}
    (A : NondetBuchiAutomaton.{u, v} Alphabet) :
    A.toStreett.Recognizes A.Language := by
  intro word
  exact A.toStreett_accepts_iff word

end NondetBuchiAutomaton

end DistributedSynthesis
