/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefOmegaAutomata

/-!
# Deterministic Muller automata

This file adds a deterministic Muller intermediate for the LTL automata
backend.  Boolean closure is direct for Muller acceptance and can later be
combined with a Muller-to-parity construction.
-/

namespace DistributedSynthesis

universe u v

/-- A deterministic Muller automaton over infinite words. -/
structure DetMullerAutomaton (Alphabet : Type u) where
  State : Type v
  stateFinite : Fintype State
  initial : State
  step : State -> Alphabet -> State
  accepting : Set (Set State)

attribute [instance] DetMullerAutomaton.stateFinite

namespace DetMullerAutomaton

/-- Run of a deterministic Muller automaton from an explicit state. -/
def runFrom {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    Nat -> A.State
  | 0 => state
  | n + 1 => A.step (runFrom A state word n) (word n)

/-- Run from the initial state. -/
def run {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    Nat -> A.State :=
  A.runFrom A.initial word

@[simp]
theorem run_zero {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    A.run word 0 = A.initial :=
  rfl

@[simp]
theorem run_succ {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    A.run word (n + 1) = A.step (A.run word n) (word n) :=
  rfl

@[simp]
theorem runFrom_drop {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (n k : Nat) :
    A.runFrom (A.runFrom state word n) (OmegaWord.drop word n) k =
      A.runFrom state word (n + k) := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      calc
        A.runFrom (A.runFrom state word n) (OmegaWord.drop word n) (k + 1)
            =
          A.step
            (A.runFrom (A.runFrom state word n) (OmegaWord.drop word n) k)
            (OmegaWord.drop word n k) := rfl
        _ = A.step (A.runFrom state word (n + k)) (word (n + k)) := by
              rw [ih]
              rfl
        _ = A.runFrom state word ((n + k) + 1) := rfl
        _ = A.runFrom state word (n + (k + 1)) := by
              congr 1

/-- A state occurs infinitely often along a run from an explicit state. -/
def StateSeenInfinitelyOftenFrom {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (q : A.State) :
    Prop :=
  ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ A.runFrom state word k = q

/-- A state occurs infinitely often along the initial run. -/
def StateSeenInfinitelyOften {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (q : A.State) :
    Prop :=
  A.StateSeenInfinitelyOftenFrom A.initial word q

/-- Some state occurs infinitely often along every run of a finite Muller automaton. -/
theorem exists_stateSeenInfinitelyOftenFrom {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    ∃ q : A.State, A.StateSeenInfinitelyOftenFrom state word q := by
  classical
  let runState : Nat -> A.State := fun n => A.runFrom state word n
  obtain ⟨loopState, hloop⟩ := Finite.exists_infinite_fiber runState
  refine ⟨loopState, ?_⟩
  have hfreq : ∃ᶠ n in Filter.atTop, runState n = loopState := by
    rw [Nat.frequently_atTop_iff_infinite]
    simpa [runState, Set.preimage, Set.mem_singleton_iff] using
      (Set.infinite_coe_iff.1 hloop)
  rw [Filter.frequently_atTop] at hfreq
  intro n
  rcases hfreq n with ⟨k, hk, hkloop⟩
  exact ⟨k, hk, by simpa [runState] using hkloop⟩

theorem stateSeenInfinitelyOftenFrom_runFrom_drop_iff {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (n : Nat)
    (q : A.State) :
    A.StateSeenInfinitelyOftenFrom
        (A.runFrom state word n) (OmegaWord.drop word n) q ↔
      A.StateSeenInfinitelyOftenFrom state word q := by
  constructor
  · intro h m
    rcases h m with ⟨k, hk, hkq⟩
    refine ⟨n + k, ?_, ?_⟩
    · omega
    · simpa [runFrom_drop] using hkq
  · intro h m
    rcases h (n + m) with ⟨k, hk, hkq⟩
    refine ⟨k - n, ?_, ?_⟩
    · omega
    · have hnle : n ≤ k := by omega
      have hidx : n + (k - n) = k := Nat.add_sub_of_le hnle
      rw [runFrom_drop]
      simpa [hidx] using hkq

/-- Some state occurs infinitely often along every initial run. -/
theorem exists_stateSeenInfinitelyOften {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    ∃ q : A.State, A.StateSeenInfinitelyOften word q :=
  A.exists_stateSeenInfinitelyOftenFrom A.initial word

/-- The set of states seen infinitely often from an explicit state. -/
def InfStatesFrom {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    Set A.State :=
  { q | A.StateSeenInfinitelyOftenFrom state word q }

/-- The finite set of states seen infinitely often from an explicit state. -/
noncomputable def infStateFinsetFrom {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    Finset A.State := by
  classical
  exact Finset.univ.filter
    (fun q => A.StateSeenInfinitelyOftenFrom state word q)

@[simp]
theorem mem_infStateFinsetFrom {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (q : A.State) :
    q ∈ A.infStateFinsetFrom state word ↔
      A.StateSeenInfinitelyOftenFrom state word q := by
  classical
  simp [infStateFinsetFrom]

/-- The concrete finite infinity set represents the semantic Muller infinity set. -/
theorem coe_infStateFinsetFrom {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    (A.infStateFinsetFrom state word : Set A.State) =
      A.InfStatesFrom state word := by
  ext q
  exact A.mem_infStateFinsetFrom state word q

theorem infStatesFrom_runFrom_drop {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    A.InfStatesFrom (A.runFrom state word n) (OmegaWord.drop word n) =
      A.InfStatesFrom state word := by
  ext q
  exact A.stateSeenInfinitelyOftenFrom_runFrom_drop_iff state word n q

theorem infStateFinsetFrom_runFrom_drop {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    A.infStateFinsetFrom (A.runFrom state word n) (OmegaWord.drop word n) =
      A.infStateFinsetFrom state word := by
  classical
  ext q
  simp [stateSeenInfinitelyOftenFrom_runFrom_drop_iff]

/-- The finite infinity set of a finite Muller run is nonempty. -/
theorem infStateFinsetFrom_nonempty {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    (A.infStateFinsetFrom state word).Nonempty := by
  rcases A.exists_stateSeenInfinitelyOftenFrom state word with ⟨q, hq⟩
  exact ⟨q, (A.mem_infStateFinsetFrom state word q).mpr hq⟩

/--
If a state is not seen infinitely often, then from some point on it is never
seen again.
-/
theorem eventually_ne_of_not_stateSeenInfinitelyOftenFrom {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (q : A.State)
    (hnot : ¬ A.StateSeenInfinitelyOftenFrom state word q) :
    ∃ n : Nat, ∀ k : Nat, n ≤ k -> A.runFrom state word k ≠ q := by
  classical
  rw [StateSeenInfinitelyOftenFrom] at hnot
  push Not at hnot
  exact hnot

/--
After some finite time, every visited state belongs to the Muller infinity set.
-/
theorem eventually_mem_infStateFinsetFrom {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    ∃ n : Nat,
      ∀ k : Nat,
        n ≤ k ->
          A.runFrom state word k ∈ A.infStateFinsetFrom state word := by
  classical
  let bad : Finset A.State :=
    Finset.univ.filter
      (fun q => ¬ A.StateSeenInfinitelyOftenFrom state word q)
  have hbadBound :
      ∀ q ∈ bad,
        ∃ n : Nat, ∀ k : Nat, n ≤ k -> A.runFrom state word k ≠ q := by
    intro q hq
    rw [Finset.mem_filter] at hq
    exact A.eventually_ne_of_not_stateSeenInfinitelyOftenFrom state word q hq.2
  choose bound hbound using hbadBound
  let boundOf : A.State -> Nat := fun q =>
    if hq : q ∈ bad then bound q hq else 0
  refine ⟨bad.sup boundOf, ?_⟩
  intro k hk
  rw [A.mem_infStateFinsetFrom]
  by_contra hnot
  have hbad : A.runFrom state word k ∈ bad := by
    rw [Finset.mem_filter]
    exact ⟨by simp, hnot⟩
  have hle : boundOf (A.runFrom state word k) ≤ bad.sup boundOf :=
    Finset.le_sup hbad
  have hboundOf :
      boundOf (A.runFrom state word k) =
        bound (A.runFrom state word k) hbad := by
    simp [boundOf, hbad]
  exact hbound (A.runFrom state word k) hbad k
    (by
      rw [← hboundOf]
      exact le_trans hle hk)
    rfl

/--
Each state in the finite Muller infinity set is visited at least once after any
given time.
-/
theorem infStateFinsetFrom_seen_after {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    {q : A.State}
    (hq : q ∈ A.infStateFinsetFrom state word)
    (n : Nat) :
    ∃ k : Nat, n ≤ k ∧ A.runFrom state word k = q := by
  exact (A.mem_infStateFinsetFrom state word q).mp hq n

/--
For any infinitely recurring state and any base time, there is a first later
visit to that state.
-/
theorem infStateFinsetFrom_first_seen_after {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    {q : A.State}
    (hq : q ∈ A.infStateFinsetFrom state word)
    (base : Nat) :
    ∃ k : Nat,
      base < k ∧
        A.runFrom state word k = q ∧
          ∀ j : Nat,
            base < j ->
              j < k ->
                A.runFrom state word j ≠ q := by
  classical
  have hexists :
      ∃ k : Nat, base < k ∧ A.runFrom state word k = q := by
    rcases A.infStateFinsetFrom_seen_after state word hq (base + 1) with
      ⟨k, hk, hkq⟩
    exact ⟨k, by omega, hkq⟩
  let k := Nat.find hexists
  have hkSpec : base < k ∧ A.runFrom state word k = q := Nat.find_spec hexists
  refine ⟨k, hkSpec.1, hkSpec.2, ?_⟩
  intro j hbasej hjk hjq
  exact Nat.find_min hexists hjk ⟨hbasej, hjq⟩

/--
After any base time, there is a finite later horizon by which every state in
the Muller infinity set has appeared at least once.
-/
theorem exists_horizon_seen_all_infStateFinsetFrom {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (base : Nat) :
    ∃ horizon : Nat,
      base ≤ horizon ∧
        ∀ q : A.State,
          q ∈ A.infStateFinsetFrom state word ->
            ∃ k : Nat, base ≤ k ∧ k ≤ horizon ∧ A.runFrom state word k = q := by
  classical
  let infs := A.infStateFinsetFrom state word
  have hseen :
      ∀ q ∈ infs, ∃ k : Nat, base ≤ k ∧ A.runFrom state word k = q := by
    intro q hq
    exact A.infStateFinsetFrom_seen_after state word hq base
  choose witness hwitness using hseen
  let witnessOf : A.State -> Nat := fun q =>
    if hq : q ∈ infs then witness q hq else base
  refine ⟨infs.sup witnessOf, ?_, ?_⟩
  · rcases A.infStateFinsetFrom_nonempty state word with ⟨q, hq⟩
    have hqInfs : q ∈ infs := hq
    have hle : witnessOf q ≤ infs.sup witnessOf := Finset.le_sup hqInfs
    have hbase : base ≤ witnessOf q := by
      simpa [witnessOf, hqInfs] using (hwitness q hqInfs).1
    exact le_trans hbase hle
  · intro q hq
    have hqInfs : q ∈ infs := hq
    refine ⟨witness q hq, (hwitness q hq).1, ?_, (hwitness q hq).2⟩
    have hle : witnessOf q ≤ infs.sup witnessOf := Finset.le_sup hqInfs
    have hwo : witnessOf q = witness q hq := by
      simp [witnessOf, hqInfs]
    rwa [hwo] at hle

/-- The set of states seen infinitely often from the initial state. -/
def InfStates {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    Set A.State :=
  A.InfStatesFrom A.initial word

/-- The finite set of states seen infinitely often from the initial state. -/
noncomputable def infStateFinset {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    Finset A.State :=
  A.infStateFinsetFrom A.initial word

@[simp]
theorem mem_infStateFinset {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (q : A.State) :
    q ∈ A.infStateFinset word ↔ A.StateSeenInfinitelyOften word q := by
  classical
  simp [infStateFinset, StateSeenInfinitelyOften]

/-- The initial finite infinity set represents the initial semantic infinity set. -/
theorem coe_infStateFinset {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    (A.infStateFinset word : Set A.State) = A.InfStates word := by
  exact A.coe_infStateFinsetFrom A.initial word

/-- The finite infinity set of an initial finite Muller run is nonempty. -/
theorem infStateFinset_nonempty {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    (A.infStateFinset word).Nonempty :=
  A.infStateFinsetFrom_nonempty A.initial word

/-- Muller acceptance from an explicit state. -/
def AcceptsFrom {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    Prop :=
  A.InfStatesFrom state word ∈ A.accepting

/-- Muller acceptance from the initial state. -/
def Accepts {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    Prop :=
  A.AcceptsFrom A.initial word

theorem acceptsFrom_iff_infStateFinsetFrom_accepting {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    A.AcceptsFrom state word ↔
      (A.infStateFinsetFrom state word : Set A.State) ∈ A.accepting := by
  rw [AcceptsFrom, coe_infStateFinsetFrom]

theorem accepts_iff_infStateFinset_accepting {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    A.Accepts word ↔
      (A.infStateFinset word : Set A.State) ∈ A.accepting := by
  rw [Accepts, acceptsFrom_iff_infStateFinsetFrom_accepting, infStateFinset]

theorem acceptsFrom_runFrom_drop_iff {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    A.AcceptsFrom (A.runFrom state word n) (OmegaWord.drop word n) ↔
      A.AcceptsFrom state word := by
  rw [AcceptsFrom, AcceptsFrom, infStatesFrom_runFrom_drop]

theorem acceptsFrom_run_drop_iff {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    A.AcceptsFrom (A.run word n) (OmegaWord.drop word n) ↔
      A.Accepts word := by
  simpa [Accepts, run] using
    A.acceptsFrom_runFrom_drop_iff A.initial word n

/-- The omega-language accepted by a deterministic Muller automaton. -/
def Language {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet) :
    Set (OmegaWord Alphabet) :=
  { word | A.Accepts word }

/-- A deterministic Muller automaton recognizes an omega-language. -/
def Recognizes {Alphabet : Type u}
    (A : DetMullerAutomaton.{u, v} Alphabet)
    (language : Set (OmegaWord Alphabet)) :
    Prop :=
  ∀ word, A.Accepts word ↔ word ∈ language

end DetMullerAutomaton

end DistributedSynthesis
