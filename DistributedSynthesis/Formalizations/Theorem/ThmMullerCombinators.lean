/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finite.Defs
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic
import DistributedSynthesis.Formalizations.Definition.DefMullerAutomata

/-!
# Deterministic Muller automaton combinators

Muller acceptance gives a clean deterministic intermediate for Boolean
closure.  The product acceptance condition is phrased using projections of the
actual set of product states seen infinitely often.
-/

namespace DistributedSynthesis

universe u v w

namespace DetMullerAutomaton

/-- A certified conversion from a deterministic Muller automaton to a DPA. -/
structure ToDPACompilation {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet) where
  dpa : DetParityAutomaton.{u, w} Alphabet
  correct :
    ∀ word : OmegaWord Alphabet,
      dpa.Accepts word ↔ A.Accepts word

/-- Package a DPA recognizing the same language as a Muller-to-DPA compilation. -/
def ToDPACompilation.ofRecognizes {Alphabet : Type u}
    {A : DetMullerAutomaton.{u, v} Alphabet}
    (dpa : DetParityAutomaton.{u, w} Alphabet)
    (h : dpa.Recognizes A.Language) :
    A.ToDPACompilation where
  dpa := dpa
  correct := h

/-- A certified Muller-to-DPA conversion preserves recognized languages. -/
theorem ToDPACompilation.recognizes {Alphabet : Type u}
    {A : DetMullerAutomaton.{u, v} Alphabet}
    (compilation : A.ToDPACompilation)
    (language : Set (OmegaWord Alphabet))
    (hA : A.Recognizes language) :
    compilation.dpa.Recognizes language := by
  intro word
  rw [compilation.correct, hA]

/-- Complement a deterministic Muller automaton by complementing its accepting family. -/
def compl {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet) :
    DetMullerAutomaton Alphabet where
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  step := A.step
  accepting := A.acceptingᶜ

@[simp]
theorem compl_runFrom {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    A.compl.runFrom state word n = A.runFrom state word n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      change A.step (A.compl.runFrom state word n) (word n) =
        A.step (A.runFrom state word n) (word n)
      rw [ih]

@[simp]
theorem compl_run {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    A.compl.run word n = A.run word n :=
  compl_runFrom A A.initial word n

theorem compl_infStatesFrom {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    A.compl.InfStatesFrom state word = A.InfStatesFrom state word := by
  ext q
  constructor
  · intro h n
    rcases h n with ⟨k, hk, hkq⟩
    exact ⟨k, hk, by simpa [compl_runFrom] using hkq⟩
  · intro h n
    rcases h n with ⟨k, hk, hkq⟩
    exact ⟨k, hk, by simpa [compl_runFrom] using hkq⟩

theorem compl_acceptsFrom_iff {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    A.compl.AcceptsFrom state word ↔ ¬ A.AcceptsFrom state word := by
  change A.compl.InfStatesFrom state word ∉ A.accepting ↔
    A.InfStatesFrom state word ∉ A.accepting
  rw [compl_infStatesFrom]
  rfl

theorem compl_accepts_iff {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    A.compl.Accepts word ↔ ¬ A.Accepts word :=
  compl_acceptsFrom_iff A A.initial word

/-- Complement recognizes the complement language. -/
theorem compl_recognizes {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (language : Set (OmegaWord Alphabet))
    (hA : A.Recognizes language) :
    A.compl.Recognizes languageᶜ := by
  intro word
  rw [compl_accepts_iff, hA]
  rfl

/-- Synchronous product of deterministic Muller automata for language intersection. -/
def inter {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet) :
    DetMullerAutomaton Alphabet where
  State := A.State × B.State
  stateFinite := inferInstance
  initial := (A.initial, B.initial)
  step state letter := (A.step state.1 letter, B.step state.2 letter)
  accepting S := Prod.fst '' S ∈ A.accepting ∧ Prod.snd '' S ∈ B.accepting

@[simp]
theorem inter_runFrom {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet)
    (state : A.State × B.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (A.inter B).runFrom state word n =
      (A.runFrom state.1 word n, B.runFrom state.2 word n) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      change
        (A.step ((A.inter B).runFrom state word n).1 (word n),
            B.step ((A.inter B).runFrom state word n).2 (word n)) =
          (A.step (A.runFrom state.1 word n) (word n),
            B.step (B.runFrom state.2 word n) (word n))
      rw [ih]

@[simp]
theorem inter_run {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (A.inter B).run word n = (A.run word n, B.run word n) :=
  inter_runFrom A B (A.initial, B.initial) word n

private theorem left_state_seen_of_inter_state_seen {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet)
    (state : A.State × B.State)
    (word : OmegaWord Alphabet)
    (q : A.State × B.State) :
    (A.inter B).StateSeenInfinitelyOftenFrom state word q ->
      A.StateSeenInfinitelyOftenFrom state.1 word q.1 := by
  intro h n
  rcases h n with ⟨k, hk, hkq⟩
  refine ⟨k, hk, ?_⟩
  simpa using congrArg Prod.fst hkq

private theorem right_state_seen_of_inter_state_seen {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet)
    (state : A.State × B.State)
    (word : OmegaWord Alphabet)
    (q : A.State × B.State) :
    (A.inter B).StateSeenInfinitelyOftenFrom state word q ->
      B.StateSeenInfinitelyOftenFrom state.2 word q.2 := by
  intro h n
  rcases h n with ⟨k, hk, hkq⟩
  refine ⟨k, hk, ?_⟩
  simpa using congrArg Prod.snd hkq

private theorem exists_inter_state_seen_of_left_seen {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet)
    (state : A.State × B.State)
    (word : OmegaWord Alphabet)
    (q₁ : A.State) :
    A.StateSeenInfinitelyOftenFrom state.1 word q₁ ->
      ∃ q₂ : B.State,
        (A.inter B).StateSeenInfinitelyOftenFrom state word (q₁, q₂) := by
  classical
  intro hq₁
  have hTimesInf : Set.Infinite {n : Nat | A.runFrom state.1 word n = q₁} := by
    rw [← Nat.frequently_atTop_iff_infinite]
    rw [Filter.frequently_atTop]
    exact hq₁
  haveI : Infinite {n : Nat // A.runFrom state.1 word n = q₁} :=
    Set.Infinite.to_subtype hTimesInf
  obtain ⟨q₂, hfiber⟩ :=
    Finite.exists_infinite_fiber
      (fun n : {n : Nat // A.runFrom state.1 word n = q₁} =>
        B.runFrom state.2 word n.1)
  refine ⟨q₂, ?_⟩
  let fiberSet : Set {n : Nat // A.runFrom state.1 word n = q₁} :=
    {n | B.runFrom state.2 word n.1 = q₂}
  have hfiberSet : fiberSet.Infinite := by
    simpa [fiberSet, Set.preimage, Set.mem_singleton_iff] using
      (Set.infinite_coe_iff.1 hfiber)
  have hImageInf : (Subtype.val '' fiberSet).Infinite :=
    hfiberSet.image (fun x _ y _ hxy => Subtype.ext hxy)
  have hPairTimesInf :
      Set.Infinite
        {n : Nat |
          A.runFrom state.1 word n = q₁ ∧ B.runFrom state.2 word n = q₂} := by
    refine hImageInf.mono ?_
    intro n hn
    rcases hn with ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  have hfreq :
      ∃ᶠ n in Filter.atTop,
        A.runFrom state.1 word n = q₁ ∧ B.runFrom state.2 word n = q₂ := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact hPairTimesInf
  rw [Filter.frequently_atTop] at hfreq
  intro n
  rcases hfreq n with ⟨k, hk, hkpair⟩
  refine ⟨k, hk, ?_⟩
  simpa [inter_runFrom, hkpair.1, hkpair.2]

private theorem exists_inter_state_seen_of_right_seen {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet)
    (state : A.State × B.State)
    (word : OmegaWord Alphabet)
    (q₂ : B.State) :
    B.StateSeenInfinitelyOftenFrom state.2 word q₂ ->
      ∃ q₁ : A.State,
        (A.inter B).StateSeenInfinitelyOftenFrom state word (q₁, q₂) := by
  classical
  intro hq₂
  have hTimesInf : Set.Infinite {n : Nat | B.runFrom state.2 word n = q₂} := by
    rw [← Nat.frequently_atTop_iff_infinite]
    rw [Filter.frequently_atTop]
    exact hq₂
  haveI : Infinite {n : Nat // B.runFrom state.2 word n = q₂} :=
    Set.Infinite.to_subtype hTimesInf
  obtain ⟨q₁, hfiber⟩ :=
    Finite.exists_infinite_fiber
      (fun n : {n : Nat // B.runFrom state.2 word n = q₂} =>
        A.runFrom state.1 word n.1)
  refine ⟨q₁, ?_⟩
  let fiberSet : Set {n : Nat // B.runFrom state.2 word n = q₂} :=
    {n | A.runFrom state.1 word n.1 = q₁}
  have hfiberSet : fiberSet.Infinite := by
    simpa [fiberSet, Set.preimage, Set.mem_singleton_iff] using
      (Set.infinite_coe_iff.1 hfiber)
  have hImageInf : (Subtype.val '' fiberSet).Infinite :=
    hfiberSet.image (fun x _ y _ hxy => Subtype.ext hxy)
  have hPairTimesInf :
      Set.Infinite
        {n : Nat |
          A.runFrom state.1 word n = q₁ ∧ B.runFrom state.2 word n = q₂} := by
    refine hImageInf.mono ?_
    intro n hn
    rcases hn with ⟨m, hm, rfl⟩
    exact ⟨hm, m.2⟩
  have hfreq :
      ∃ᶠ n in Filter.atTop,
        A.runFrom state.1 word n = q₁ ∧ B.runFrom state.2 word n = q₂ := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact hPairTimesInf
  rw [Filter.frequently_atTop] at hfreq
  intro n
  rcases hfreq n with ⟨k, hk, hkpair⟩
  refine ⟨k, hk, ?_⟩
  simpa [inter_runFrom, hkpair.1, hkpair.2]

theorem inter_infStatesFrom_fst {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet)
    (state : A.State × B.State)
    (word : OmegaWord Alphabet) :
    Prod.fst '' (A.inter B).InfStatesFrom state word =
      A.InfStatesFrom state.1 word := by
  ext q₁
  constructor
  · intro h
    rcases h with ⟨q, hq, hqfst⟩
    cases hqfst
    exact left_state_seen_of_inter_state_seen A B state word q hq
  · intro hq₁
    rcases exists_inter_state_seen_of_left_seen A B state word q₁ hq₁ with ⟨q₂, hpair⟩
    exact ⟨(q₁, q₂), hpair, rfl⟩

theorem inter_infStatesFrom_snd {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet)
    (state : A.State × B.State)
    (word : OmegaWord Alphabet) :
    Prod.snd '' (A.inter B).InfStatesFrom state word =
      B.InfStatesFrom state.2 word := by
  ext q₂
  constructor
  · intro h
    rcases h with ⟨q, hq, hqsnd⟩
    cases hqsnd
    exact right_state_seen_of_inter_state_seen A B state word q hq
  · intro hq₂
    rcases exists_inter_state_seen_of_right_seen A B state word q₂ hq₂ with ⟨q₁, hpair⟩
    exact ⟨(q₁, q₂), hpair, rfl⟩

theorem inter_acceptsFrom_iff {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet)
    (state : A.State × B.State)
    (word : OmegaWord Alphabet) :
    (A.inter B).AcceptsFrom state word ↔
      A.AcceptsFrom state.1 word ∧ B.AcceptsFrom state.2 word := by
  change
    (Prod.fst '' (A.inter B).InfStatesFrom state word ∈ A.accepting ∧
        Prod.snd '' (A.inter B).InfStatesFrom state word ∈ B.accepting) ↔
      A.InfStatesFrom state.1 word ∈ A.accepting ∧
        B.InfStatesFrom state.2 word ∈ B.accepting
  rw [inter_infStatesFrom_fst A B state word, inter_infStatesFrom_snd A B state word]

theorem inter_accepts_iff {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet)
    (word : OmegaWord Alphabet) :
    (A.inter B).Accepts word ↔ A.Accepts word ∧ B.Accepts word :=
  inter_acceptsFrom_iff A B (A.initial, B.initial) word

/-- Synchronous Muller product recognizes language intersection. -/
theorem inter_recognizes {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet)
    (languageA languageB : Set (OmegaWord Alphabet))
    (hA : A.Recognizes languageA)
    (hB : B.Recognizes languageB) :
    (A.inter B).Recognizes (languageA ∩ languageB) := by
  intro word
  rw [inter_accepts_iff, hA, hB]
  rfl

/-- Synchronous product of deterministic Muller automata for language union. -/
def union {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet) :
    DetMullerAutomaton Alphabet :=
  (A.compl.inter B.compl).compl

theorem union_accepts_iff {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet)
    (word : OmegaWord Alphabet) :
    (A.union B).Accepts word ↔ A.Accepts word ∨ B.Accepts word := by
  by_cases hA : A.Accepts word <;>
    by_cases hB : B.Accepts word <;>
      simp [union, compl_accepts_iff, inter_accepts_iff, hA, hB]

/-- Synchronous Muller product recognizes language union. -/
theorem union_recognizes {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (B : DetMullerAutomaton.{u, w} Alphabet)
    (languageA languageB : Set (OmegaWord Alphabet))
    (hA : A.Recognizes languageA)
    (hB : B.Recognizes languageB) :
    (A.union B).Recognizes (languageA ∪ languageB) := by
  intro word
  rw [union_accepts_iff, hA, hB]
  rfl

end DetMullerAutomaton

namespace DetParityAutomaton

/-- View a deterministic parity automaton as a deterministic Muller automaton. -/
def toMuller {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet) :
    DetMullerAutomaton Alphabet where
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  step := A.step
  accepting S :=
    ∃ p : Nat,
      NatEven p ∧
        (∃ q : A.State, q ∈ S ∧ A.priority q = p) ∧
          ∀ q : A.State, q ∈ S -> p ≤ A.priority q

@[simp]
theorem toMuller_runFrom {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    A.toMuller.runFrom state word n = A.runFrom state word n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      change A.step (A.toMuller.runFrom state word n) (word n) =
        A.step (A.runFrom state word n) (word n)
      rw [ih]

private theorem prioritySeen_from_stateSeen {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (q : A.State) :
    A.toMuller.StateSeenInfinitelyOftenFrom state word q ->
      A.PrioritySeenInfinitelyOftenFrom state word (A.priority q) := by
  intro h n
  rcases h n with ⟨k, hk, hkq⟩
  refine ⟨k, hk, ?_⟩
  have hkq' : A.runFrom state word k = q := by
    simpa [toMuller_runFrom] using hkq
  simpa [hkq']

private theorem exists_stateSeen_of_prioritySeen {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (p : Nat) :
    A.PrioritySeenInfinitelyOftenFrom state word p ->
      ∃ q : A.State,
        A.toMuller.StateSeenInfinitelyOftenFrom state word q ∧ A.priority q = p := by
  classical
  intro hp
  have hTimesInf : Set.Infinite {n : Nat | A.priority (A.runFrom state word n) = p} := by
    rw [← Nat.frequently_atTop_iff_infinite]
    rw [Filter.frequently_atTop]
    exact hp
  haveI : Infinite {n : Nat // A.priority (A.runFrom state word n) = p} :=
    Set.Infinite.to_subtype hTimesInf
  obtain ⟨q, hfiber⟩ :=
    Finite.exists_infinite_fiber
      (fun n : {n : Nat // A.priority (A.runFrom state word n) = p} =>
        A.runFrom state word n.1)
  refine ⟨q, ?_, ?_⟩
  · let fiberSet : Set {n : Nat // A.priority (A.runFrom state word n) = p} :=
      {n | A.runFrom state word n.1 = q}
    have hfiberSet : fiberSet.Infinite := by
      simpa [fiberSet, Set.preimage, Set.mem_singleton_iff] using
        (Set.infinite_coe_iff.1 hfiber)
    have hImageInf : (Subtype.val '' fiberSet).Infinite :=
      hfiberSet.image (fun x _ y _ hxy => Subtype.ext hxy)
    have hStateTimesInf : Set.Infinite {n : Nat | A.runFrom state word n = q} := by
      refine hImageInf.mono ?_
      intro n hn
      rcases hn with ⟨m, hm, rfl⟩
      exact hm
    have hfreq : ∃ᶠ n in Filter.atTop, A.runFrom state word n = q := by
      rw [Nat.frequently_atTop_iff_infinite]
      exact hStateTimesInf
    rw [Filter.frequently_atTop] at hfreq
    intro n
    rcases hfreq n with ⟨k, hk, hkq⟩
    exact ⟨k, hk, by simpa [toMuller_runFrom] using hkq⟩
  · rcases (Set.infinite_coe_iff.1 hfiber).nonempty with ⟨n, hn⟩
    have hrun : A.runFrom state word n.1 = q := by
      simpa [Set.preimage, Set.mem_singleton_iff] using hn
    rw [← hrun]
    exact n.2

theorem toMuller_prioritySeen_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (p : Nat) :
    A.PrioritySeenInfinitelyOftenFrom state word p ↔
      ∃ q : A.State,
        A.toMuller.StateSeenInfinitelyOftenFrom state word q ∧ A.priority q = p := by
  constructor
  · exact exists_stateSeen_of_prioritySeen A state word p
  · intro h
    rcases h with ⟨q, hq, hprio⟩
    rw [← hprio]
    exact prioritySeen_from_stateSeen A state word q hq

theorem toMuller_acceptsFrom_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    A.toMuller.AcceptsFrom state word ↔ A.AcceptsFrom state word := by
  constructor
  · intro h
    rcases h with ⟨p, hpEven, ⟨q, hqInf, hqprio⟩, hpMinState⟩
    refine ⟨p, hpEven, ?_, ?_⟩
    · rw [← hqprio]
      exact prioritySeen_from_stateSeen A state word q hqInf
    · intro r hr
      rcases (toMuller_prioritySeen_iff A state word r).mp hr with ⟨qᵣ, hqᵣInf, hqᵣprio⟩
      rw [← hqᵣprio]
      exact hpMinState qᵣ hqᵣInf
  · intro h
    rcases h with ⟨p, hpEven, hpInf, hpMin⟩
    rcases (toMuller_prioritySeen_iff A state word p).mp hpInf with ⟨q, hqInf, hqprio⟩
    refine ⟨p, hpEven, ⟨q, hqInf, hqprio⟩, ?_⟩
    intro q' hq'Inf
    exact hpMin (A.priority q') (prioritySeen_from_stateSeen A state word q' hq'Inf)

theorem toMuller_accepts_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    A.toMuller.Accepts word ↔ A.Accepts word :=
  toMuller_acceptsFrom_iff A A.initial word

/-- DPA-to-Muller conversion preserves the recognized omega-language. -/
theorem toMuller_recognizes {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (language : Set (OmegaWord Alphabet))
    (hA : A.Recognizes language) :
    A.toMuller.Recognizes language := by
  intro word
  rw [toMuller_accepts_iff, hA]

end DetParityAutomaton

end DistributedSynthesis
