/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefLTL
import DistributedSynthesis.Formalizations.Definition.DefPathSummary
import Mathlib.Tactic

/-!
# Omega-word semantics for deterministic parity automata

The paper already uses `DetParityAutomaton` as the finite automaton target.
This file adds its standard infinite-word run and parity-acceptance semantics.
-/

namespace DistributedSynthesis

universe u v

namespace DetParityAutomaton

/-- Even natural numbers, stated directly to keep this file independent of parity imports. -/
def NatEven (p : Nat) : Prop :=
  ∃ m : Nat, p = 2 * m

/-- Run of a deterministic parity automaton from an explicit state. -/
def runFrom {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    Nat -> A.State
  | 0 => state
  | n + 1 => A.step (runFrom A state word n) (word n)

/-- Run of a deterministic parity automaton from its initial state. -/
def run {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    Nat -> A.State :=
  A.runFrom A.initial word

/-- The same deterministic parity automaton with a different initial state. -/
def withInitial {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State) :
    DetParityAutomaton Alphabet where
  State := A.State
  stateFinite := A.stateFinite
  initial := state
  step := A.step
  priority := A.priority

@[simp]
theorem run_zero {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    A.run word 0 = A.initial :=
  rfl

@[simp]
theorem run_succ {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    A.run word (n + 1) = A.step (A.run word n) (word n) :=
  rfl

@[simp]
theorem runFrom_step_drop {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    A.runFrom (A.step state (word 0)) (OmegaWord.drop word 1) n =
      A.runFrom state word (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        A.step
            (A.runFrom (A.step state (word 0)) (OmegaWord.drop word 1) n)
            (OmegaWord.drop word 1 n) =
          A.step (A.runFrom state word (n + 1)) (word (n + 1))
      rw [ih]
      simp [OmegaWord.drop, Nat.add_comm]

@[simp]
theorem runFrom_drop {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
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

@[simp]
theorem withInitial_run {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (A.withInitial state).run word n = A.runFrom state word n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change A.step ((A.withInitial state).run word n) (word n) =
        A.step (A.runFrom state word n) (word n)
      rw [ih]

/-- Priority `p` occurs infinitely often along the run on `word`. -/
def PrioritySeenInfinitelyOften {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (p : Nat) :
    Prop :=
  ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ A.priority (A.run word k) = p

/-- Priority `p` occurs infinitely often along the run from an explicit state. -/
def PrioritySeenInfinitelyOftenFrom {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (p : Nat) :
    Prop :=
  ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ A.priority (A.runFrom state word k) = p

@[simp]
theorem prioritySeenInfinitelyOftenFrom_initial {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (p : Nat) :
    A.PrioritySeenInfinitelyOftenFrom A.initial word p =
      A.PrioritySeenInfinitelyOften word p :=
  rfl

theorem withInitial_prioritySeenInfinitelyOften_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (p : Nat) :
    (A.withInitial state).PrioritySeenInfinitelyOften word p ↔
      A.PrioritySeenInfinitelyOftenFrom state word p := by
  constructor
  · intro h n
    rcases h n with ⟨k, hk, hkprio⟩
    exact ⟨k, hk, by simpa [PrioritySeenInfinitelyOften] using hkprio⟩
  · intro h n
    rcases h n with ⟨k, hk, hkprio⟩
    exact ⟨k, hk, by simpa [PrioritySeenInfinitelyOften] using hkprio⟩

theorem prioritySeenInfinitelyOftenFrom_step_drop_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (p : Nat) :
    A.PrioritySeenInfinitelyOftenFrom
        (A.step state (word 0)) (OmegaWord.drop word 1) p ↔
      A.PrioritySeenInfinitelyOftenFrom state word p := by
  constructor
  · intro h n
    rcases h n with ⟨k, hk, hkprio⟩
    refine ⟨k + 1, Nat.le_trans hk (Nat.le_succ k), ?_⟩
    simpa using hkprio
  · intro h n
    rcases h (n + 1) with ⟨k, hk, hkprio⟩
    cases k with
    | zero =>
        cases Nat.not_succ_le_zero n hk
    | succ k =>
        refine ⟨k, Nat.succ_le_succ_iff.mp hk, ?_⟩
        simpa using hkprio

theorem prioritySeenInfinitelyOftenFrom_runFrom_drop_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (n p : Nat) :
    A.PrioritySeenInfinitelyOftenFrom
        (A.runFrom state word n) (OmegaWord.drop word n) p ↔
      A.PrioritySeenInfinitelyOftenFrom state word p := by
  constructor
  · intro h m
    rcases h m with ⟨k, hk, hkprio⟩
    refine ⟨n + k, ?_, ?_⟩
    · omega
    · simpa [runFrom_drop] using hkprio
  · intro h m
    rcases h (n + m) with ⟨k, hk, hkprio⟩
    refine ⟨k - n, ?_, ?_⟩
    · omega
    · have hnle : n ≤ k := by omega
      have hidx : n + (k - n) = k := Nat.add_sub_of_le hnle
      rw [runFrom_drop]
      simpa [hidx] using hkprio
/--
Parity acceptance using the minimum priority seen infinitely often.

This formulation avoids separately proving that such a minimum exists; a
compiler correctness theorem may provide the witnessing priority directly.
-/
def AcceptsFrom {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    Prop :=
  ∃ p : Nat,
    NatEven p ∧
      A.PrioritySeenInfinitelyOftenFrom state word p ∧
        ∀ q : Nat, A.PrioritySeenInfinitelyOftenFrom state word q -> p ≤ q

/-- Acceptance from the initial state. -/
def Accepts {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    Prop :=
  A.AcceptsFrom A.initial word

@[simp]
theorem acceptsFrom_initial {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    A.AcceptsFrom A.initial word = A.Accepts word :=
  rfl

@[simp]
theorem withInitial_accepts_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    (A.withInitial state).Accepts word ↔ A.AcceptsFrom state word := by
  constructor
  · intro h
    rcases h with ⟨p, hpEven, hpInf, hpMin⟩
    refine ⟨p, hpEven, ?_, ?_⟩
    · exact (withInitial_prioritySeenInfinitelyOften_iff A state word p).mp hpInf
    · intro q hq
      exact hpMin q
        ((withInitial_prioritySeenInfinitelyOften_iff A state word q).mpr hq)
  · intro h
    rcases h with ⟨p, hpEven, hpInf, hpMin⟩
    refine ⟨p, hpEven, ?_, ?_⟩
    · exact (withInitial_prioritySeenInfinitelyOften_iff A state word p).mpr hpInf
    · intro q hq
      exact hpMin q
        ((withInitial_prioritySeenInfinitelyOften_iff A state word q).mp hq)

theorem acceptsFrom_step_drop_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    A.AcceptsFrom (A.step state (word 0)) (OmegaWord.drop word 1) ↔
      A.AcceptsFrom state word := by
  constructor
  · intro h
    rcases h with ⟨p, hpEven, hpInf, hpMin⟩
    refine ⟨p, hpEven, ?_, ?_⟩
    · exact (prioritySeenInfinitelyOftenFrom_step_drop_iff A state word p).mp hpInf
    · intro q hq
      exact hpMin q
        ((prioritySeenInfinitelyOftenFrom_step_drop_iff A state word q).mpr hq)
  · intro h
    rcases h with ⟨p, hpEven, hpInf, hpMin⟩
    refine ⟨p, hpEven, ?_, ?_⟩
    · exact (prioritySeenInfinitelyOftenFrom_step_drop_iff A state word p).mpr hpInf
    · intro q hq
      exact hpMin q
        ((prioritySeenInfinitelyOftenFrom_step_drop_iff A state word q).mp hq)

theorem acceptsFrom_runFrom_drop_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    A.AcceptsFrom (A.runFrom state word n) (OmegaWord.drop word n) ↔
      A.AcceptsFrom state word := by
  constructor
  · intro h
    rcases h with ⟨p, hpEven, hpInf, hpMin⟩
    refine ⟨p, hpEven, ?_, ?_⟩
    · exact (prioritySeenInfinitelyOftenFrom_runFrom_drop_iff A state word n p).mp hpInf
    · intro q hq
      exact hpMin q
        ((prioritySeenInfinitelyOftenFrom_runFrom_drop_iff A state word n q).mpr hq)
  · intro h
    rcases h with ⟨p, hpEven, hpInf, hpMin⟩
    refine ⟨p, hpEven, ?_, ?_⟩
    · exact (prioritySeenInfinitelyOftenFrom_runFrom_drop_iff A state word n p).mpr hpInf
    · intro q hq
      exact hpMin q
        ((prioritySeenInfinitelyOftenFrom_runFrom_drop_iff A state word n q).mp hq)

/--
Positive parity-acceptance constructor: an even priority seen infinitely often
with no strictly smaller priority seen infinitely often witnesses acceptance.

This is the converse companion to the consumers of `AcceptsFrom` above.  A
determinization-correctness argument naturally produces exactly these two facts
about the run -- a recurrent even priority and the absence of any smaller
recurrent priority -- and this lemma packages them as the minimum-priority
witness required by `AcceptsFrom`.
-/
theorem acceptsFrom_of_even_seen_of_no_smaller {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    {p : Nat}
    (hpEven : NatEven p)
    (hpInf : A.PrioritySeenInfinitelyOftenFrom state word p)
    (hpMin : ∀ q : Nat, q < p ->
      ¬ A.PrioritySeenInfinitelyOftenFrom state word q) :
    A.AcceptsFrom state word :=
  ⟨p, hpEven, hpInf, fun q hq => not_lt.mp fun hlt => hpMin q hlt hq⟩

/-- Initial-state form of `acceptsFrom_of_even_seen_of_no_smaller`. -/
theorem accepts_of_even_seen_of_no_smaller {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    {p : Nat}
    (hpEven : NatEven p)
    (hpInf : A.PrioritySeenInfinitelyOften word p)
    (hpMin : ∀ q : Nat, q < p ->
      ¬ A.PrioritySeenInfinitelyOften word q) :
    A.Accepts word :=
  acceptsFrom_of_even_seen_of_no_smaller A A.initial word hpEven hpInf hpMin

/--
Some priority is seen infinitely often along any run.

The state space is finite, so the run `n ↦ A.run word n` takes some value on an
infinite set of indices; its priority is then seen infinitely often.  This is
the pigeonhole backbone of parity acceptance: it guarantees the set of
infinitely-often priorities is nonempty.
-/
theorem exists_prioritySeenInfinitelyOften {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    ∃ p : Nat, A.PrioritySeenInfinitelyOften word p := by
  classical
  obtain ⟨s, hs⟩ := Finite.exists_infinite_fiber (A.run word)
  have hinf : ((A.run word) ⁻¹' {s}).Infinite := Set.infinite_coe_iff.mp hs
  refine ⟨A.priority s, ?_⟩
  intro n
  obtain ⟨k, hk, hkn⟩ := hinf.exists_gt n
  have hks : A.run word k = s := hk
  exact ⟨k, le_of_lt hkn, by rw [hks]⟩

/--
A minimum infinitely-often priority exists.

Combined with finiteness above, the nonempty set of infinitely-often priorities
has a least element, since the naturals are well-ordered.  This is the witness
that the parity-acceptance `AcceptsFrom` minimum quantifier ranges over.
-/
theorem exists_min_prioritySeenInfinitelyOften {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    ∃ p : Nat,
      A.PrioritySeenInfinitelyOften word p ∧
        ∀ q : Nat, A.PrioritySeenInfinitelyOften word q -> p ≤ q := by
  classical
  have hex : ∃ p : Nat, A.PrioritySeenInfinitelyOften word p :=
    exists_prioritySeenInfinitelyOften A word
  exact ⟨Nat.find hex, Nat.find_spec hex, fun q hq => Nat.find_min' hex hq⟩

/--
Acceptance is decided by the parity of the minimum infinitely-often priority.

Given any witnessing minimum `p`, the automaton accepts exactly when `p` is even.
This is the standard parity-acceptance reformulation: it turns a determinization
proof into the single task of showing the minimum recurrent priority is even.
-/
theorem accepts_iff_natEven_of_min {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    {p : Nat}
    (hpInf : A.PrioritySeenInfinitelyOften word p)
    (hpMin : ∀ q : Nat, A.PrioritySeenInfinitelyOften word q -> p ≤ q) :
    A.Accepts word ↔ NatEven p := by
  constructor
  · rintro ⟨p', hp'Even, hp'Inf, hp'Min⟩
    have hle : p ≤ p' := hpMin p' hp'Inf
    have hge : p' ≤ p := hp'Min p hpInf
    rw [le_antisymm hle hge]
    exact hp'Even
  · intro hpEven
    exact accepts_of_even_seen_of_no_smaller A word hpEven hpInf
      (fun q hq hqInf => absurd (hpMin q hqInf) (not_le.mpr hq))

/-- The omega-language accepted from an explicit state. -/
def LanguageFrom {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State) :
    Set (OmegaWord Alphabet) :=
  { word | A.AcceptsFrom state word }

/-- The omega-language accepted by a deterministic parity automaton. -/
def Language {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet) :
    Set (OmegaWord Alphabet) :=
  { word | A.Accepts word }

@[simp]
theorem languageFrom_initial {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet) :
    A.LanguageFrom A.initial = A.Language :=
  rfl

/-- State-wise recognition of a family of omega-languages. -/
def RecognizesFrom {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (language : A.State -> Set (OmegaWord Alphabet)) :
    Prop :=
  ∀ state word, A.AcceptsFrom state word ↔ word ∈ language state

/-- A deterministic parity automaton recognizes an omega-language. -/
def Recognizes {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (language : Set (OmegaWord Alphabet)) :
    Prop :=
  ∀ word, A.Accepts word ↔ word ∈ language

/-- State-wise recognition implies ordinary initial-language recognition. -/
theorem recognizes_of_recognizesFrom {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (language : A.State -> Set (OmegaWord Alphabet))
    (h : A.RecognizesFrom language) :
    A.Recognizes (language A.initial) := by
  intro word
  exact h A.initial word

/--
State-wise recognition is equivalent to ordinary recognition after rebasing the
initial state to each source state.
-/
theorem recognizesFrom_iff_withInitial_recognizes {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (language : A.State -> Set (OmegaWord Alphabet)) :
    A.RecognizesFrom language ↔
      ∀ state : A.State, (A.withInitial state).Recognizes (language state) := by
  constructor
  · intro h state word
    rw [withInitial_accepts_iff]
    exact h state word
  · intro h state word
    rw [← withInitial_accepts_iff]
    exact h state word

end DetParityAutomaton

end DistributedSynthesis
