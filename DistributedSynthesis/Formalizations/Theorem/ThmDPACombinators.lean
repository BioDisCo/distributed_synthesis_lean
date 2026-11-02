/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finite.Defs
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic
import DistributedSynthesis.Formalizations.Definition.DefOmegaAutomata

/-!
# Deterministic parity automaton combinators

This file starts the constructive automata toolkit needed for a full LTL
compiler.  The first operation is the temporal `next`/delay construction.
-/

namespace DistributedSynthesis

universe u v

namespace DetParityAutomaton

/-- The DPA accepting every omega-word. -/
def top {Alphabet : Type u} : DetParityAutomaton Alphabet where
  State := Unit
  stateFinite := inferInstance
  initial := ()
  step _ _ := ()
  priority _ := 0

/-- The DPA accepting no omega-word. -/
def bottom {Alphabet : Type u} : DetParityAutomaton Alphabet where
  State := Unit
  stateFinite := inferInstance
  initial := ()
  step _ _ := ()
  priority _ := 1

@[simp]
theorem top_runFrom {Alphabet : Type u}
    (state : (top : DetParityAutomaton Alphabet).State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (top : DetParityAutomaton Alphabet).runFrom state word n = () := by
  cases state
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [runFrom, top]

@[simp]
theorem bottom_runFrom {Alphabet : Type u}
    (state : (bottom : DetParityAutomaton Alphabet).State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (bottom : DetParityAutomaton Alphabet).runFrom state word n = () := by
  cases state
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [runFrom, bottom]

@[simp]
theorem top_acceptsFrom {Alphabet : Type u}
    (state : (top : DetParityAutomaton Alphabet).State)
    (word : OmegaWord Alphabet) :
    (top : DetParityAutomaton Alphabet).AcceptsFrom state word := by
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro n
    exact ⟨n, Nat.le_refl n, by simp [top]⟩
  · intro q _hq
    exact Nat.zero_le q

@[simp]
theorem top_accepts {Alphabet : Type u}
    (word : OmegaWord Alphabet) :
    (top : DetParityAutomaton Alphabet).Accepts word := by
  exact top_acceptsFrom () word

@[simp]
theorem bottom_not_acceptsFrom {Alphabet : Type u}
    (state : (bottom : DetParityAutomaton Alphabet).State)
    (word : OmegaWord Alphabet) :
    ¬ (bottom : DetParityAutomaton Alphabet).AcceptsFrom state word := by
  intro h
  rcases h with ⟨p, hpEven, hpInf, _hpMin⟩
  have hp_one : p = 1 := by
    rcases hpInf 0 with ⟨k, _hk, hkprio⟩
    simpa [PrioritySeenInfinitelyOftenFrom, bottom] using hkprio.symm
  rcases hpEven with ⟨m, hm⟩
  omega

@[simp]
theorem bottom_acceptsFrom_iff {Alphabet : Type u}
    (state : (bottom : DetParityAutomaton Alphabet).State)
    (word : OmegaWord Alphabet) :
    (bottom : DetParityAutomaton Alphabet).AcceptsFrom state word ↔ False := by
  exact ⟨bottom_not_acceptsFrom state word, False.elim⟩

@[simp]
theorem bottom_accepts_iff {Alphabet : Type u}
    (word : OmegaWord Alphabet) :
    (bottom : DetParityAutomaton Alphabet).Accepts word ↔ False := by
  exact bottom_acceptsFrom_iff () word

/-- `top` recognizes the universal omega-language. -/
theorem top_recognizes {Alphabet : Type u} :
    (top : DetParityAutomaton Alphabet).Recognizes Set.univ := by
  intro word
  simp [Set.mem_univ]

/-- `bottom` recognizes the empty omega-language. -/
theorem bottom_recognizes {Alphabet : Type u} :
    (bottom : DetParityAutomaton Alphabet).Recognizes ∅ := by
  intro word
  simp

/-- Universe-polymorphic DPA accepting every omega-word. -/
def topAt {Alphabet : Type u} : DetParityAutomaton.{u, v} Alphabet where
  State := ULift.{v, 0} Unit
  stateFinite := inferInstance
  initial := ULift.up ()
  step _ _ := ULift.up ()
  priority _ := 0

/-- Universe-polymorphic DPA accepting no omega-word. -/
def bottomAt {Alphabet : Type u} : DetParityAutomaton.{u, v} Alphabet where
  State := ULift.{v, 0} Unit
  stateFinite := inferInstance
  initial := ULift.up ()
  step _ _ := ULift.up ()
  priority _ := 1

@[simp]
theorem topAt_runFrom {Alphabet : Type u}
    (state : (topAt : DetParityAutomaton.{u, v} Alphabet).State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (topAt : DetParityAutomaton.{u, v} Alphabet).runFrom state word n =
      ULift.up () := by
  induction n with
  | zero =>
      cases state
      rfl
  | succ n ih =>
      simp [runFrom, topAt]

@[simp]
theorem bottomAt_runFrom {Alphabet : Type u}
    (state : (bottomAt : DetParityAutomaton.{u, v} Alphabet).State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (bottomAt : DetParityAutomaton.{u, v} Alphabet).runFrom state word n =
      ULift.up () := by
  induction n with
  | zero =>
      cases state
      rfl
  | succ n ih =>
      simp [runFrom, bottomAt]

@[simp]
theorem topAt_acceptsFrom {Alphabet : Type u}
    (state : (topAt : DetParityAutomaton.{u, v} Alphabet).State)
    (word : OmegaWord Alphabet) :
    (topAt : DetParityAutomaton.{u, v} Alphabet).AcceptsFrom state word := by
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro n
    exact ⟨n, Nat.le_refl n, by simp [topAt]⟩
  · intro q _hq
    exact Nat.zero_le q

@[simp]
theorem topAt_accepts {Alphabet : Type u}
    (word : OmegaWord Alphabet) :
    (topAt : DetParityAutomaton.{u, v} Alphabet).Accepts word := by
  exact topAt_acceptsFrom (ULift.up ()) word

@[simp]
theorem bottomAt_not_acceptsFrom {Alphabet : Type u}
    (state : (bottomAt : DetParityAutomaton.{u, v} Alphabet).State)
    (word : OmegaWord Alphabet) :
    ¬ (bottomAt : DetParityAutomaton.{u, v} Alphabet).AcceptsFrom state word := by
  intro h
  rcases h with ⟨p, hpEven, hpInf, _hpMin⟩
  have hp_one : p = 1 := by
    rcases hpInf 0 with ⟨k, _hk, hkprio⟩
    simpa [PrioritySeenInfinitelyOftenFrom, bottomAt] using hkprio.symm
  rcases hpEven with ⟨m, hm⟩
  omega

@[simp]
theorem bottomAt_acceptsFrom_iff {Alphabet : Type u}
    (state : (bottomAt : DetParityAutomaton.{u, v} Alphabet).State)
    (word : OmegaWord Alphabet) :
    (bottomAt : DetParityAutomaton.{u, v} Alphabet).AcceptsFrom state word ↔ False := by
  exact ⟨bottomAt_not_acceptsFrom state word, False.elim⟩

@[simp]
theorem bottomAt_accepts_iff {Alphabet : Type u}
    (word : OmegaWord Alphabet) :
    (bottomAt : DetParityAutomaton.{u, v} Alphabet).Accepts word ↔ False := by
  exact bottomAt_acceptsFrom_iff (ULift.up ()) word

theorem topAt_recognizes {Alphabet : Type u} :
    (topAt : DetParityAutomaton.{u, v} Alphabet).Recognizes Set.univ := by
  intro word
  simp [Set.mem_univ]

theorem bottomAt_recognizes {Alphabet : Type u} :
    (bottomAt : DetParityAutomaton.{u, v} Alphabet).Recognizes ∅ := by
  intro word
  simp

/--
A DPA for a one-letter test.  It reads the first input letter, then moves to an
accepting or rejecting sink according to the decidable predicate.
-/
def letterTest {Alphabet : Type u}
    (predicate : Alphabet -> Prop)
    [DecidablePred predicate] :
    DetParityAutomaton.{u, v} Alphabet where
  State := ULift.{v, 0} (Option Bool)
  stateFinite := inferInstance
  initial := ULift.up none
  step state letter :=
    ULift.up
      (match state.down with
      | none => some (decide (predicate letter))
      | some accepted => some accepted)
  priority state :=
    match state.down with
    | none => 0
    | some true => 0
    | some false => 1

@[simp]
theorem letterTest_runFrom_some {Alphabet : Type u}
    (predicate : Alphabet -> Prop)
    [DecidablePred predicate]
    (accepted : Bool)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (letterTest predicate).runFrom (ULift.up (some accepted)) word n =
      ULift.up (some accepted) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        (letterTest predicate).step
          ((letterTest predicate).runFrom (ULift.up (some accepted)) word n) (word n) =
            ULift.up (some accepted)
      rw [ih]
      cases accepted <;> rfl

@[simp]
theorem letterTest_run_succ {Alphabet : Type u}
    (predicate : Alphabet -> Prop)
    [DecidablePred predicate]
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (letterTest predicate).run word (n + 1) =
      ULift.up (some (decide (predicate (word 0)))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        (letterTest predicate).step
          ((letterTest predicate).run word (n + 1)) (word (n + 1)) =
            ULift.up (some (decide (predicate (word 0))))
      rw [ih]
      by_cases h : predicate (word 0) <;> simp [letterTest, h]

theorem letterTest_accepts_of_predicate {Alphabet : Type u}
    (predicate : Alphabet -> Prop)
    [DecidablePred predicate]
    (word : OmegaWord Alphabet)
    (h : predicate (word 0)) :
    (letterTest predicate).Accepts word := by
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro n
    refine ⟨n + 1, Nat.le_succ_of_le (Nat.le_refl n), ?_⟩
    have hrun :
        (letterTest predicate).runFrom (letterTest predicate).initial word (n + 1) =
          ULift.up (some true) := by
      simpa [DetParityAutomaton.run, letterTest, h] using
        (letterTest_run_succ predicate word n)
    rw [hrun]
    rfl
  · intro q hq
    exact Nat.zero_le q

theorem letterTest_not_accepts_of_not_predicate {Alphabet : Type u}
    (predicate : Alphabet -> Prop)
    [DecidablePred predicate]
    (word : OmegaWord Alphabet)
    (h : ¬ predicate (word 0)) :
    ¬ (letterTest predicate).Accepts word := by
  intro haccepts
  rcases haccepts with ⟨p, hpEven, hpInf, hpMin⟩
  have honeInf :
      (letterTest predicate).PrioritySeenInfinitelyOften word 1 := by
    intro n
    refine ⟨n + 1, Nat.le_succ_of_le (Nat.le_refl n), ?_⟩
    have hrun :
        (letterTest predicate).run word (n + 1) =
          ULift.up (some false) := by
      simpa [letterTest, h] using
        (letterTest_run_succ predicate word n)
    change (letterTest predicate).priority
      ((letterTest predicate).run word (n + 1)) = 1
    rw [hrun]
    rfl
  have hp_le_one := hpMin 1 honeInf
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    rcases hpInf 1 with ⟨k, hk, hkprio⟩
    cases k with
    | zero => omega
    | succ k =>
        have hprio :
            (letterTest predicate).priority
              ((letterTest predicate).runFrom
                (letterTest predicate).initial word (k + 1)) = 1 := by
          have hrun :
              (letterTest predicate).runFrom
                  (letterTest predicate).initial word (k + 1) =
                ULift.up (some false) := by
            simpa [DetParityAutomaton.run, letterTest, h] using
              (letterTest_run_succ predicate word k)
          rw [hrun]
          rfl
        rw [hprio] at hkprio
        omega
  have hp_eq_one : p = 1 := by
    omega
  rcases hpEven with ⟨m, hm⟩
  omega

@[simp]
theorem letterTest_accepts_iff {Alphabet : Type u}
    (predicate : Alphabet -> Prop)
    [DecidablePred predicate]
    (word : OmegaWord Alphabet) :
    (letterTest predicate).Accepts word ↔ predicate (word 0) := by
  constructor
  · intro haccepts
    by_contra h
    exact letterTest_not_accepts_of_not_predicate predicate word h haccepts
  · intro h
    exact letterTest_accepts_of_predicate predicate word h

theorem letterTest_recognizes {Alphabet : Type u}
    (predicate : Alphabet -> Prop)
    [DecidablePred predicate] :
    (letterTest predicate).Recognizes { word | predicate (word 0) } := by
  intro word
  exact letterTest_accepts_iff predicate word

/-- Add a fixed offset to every priority, preserving states and transitions. -/
def shiftPriority {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (offset : Nat) :
    DetParityAutomaton Alphabet where
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  step := A.step
  priority state := A.priority state + offset

@[simp]
theorem shiftPriority_runFrom {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (offset : Nat)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (A.shiftPriority offset).runFrom state word n =
      A.runFrom state word n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      change
        A.step ((A.shiftPriority offset).runFrom state word n) (word n) =
          A.step (A.runFrom state word n) (word n)
      rw [ih]

@[simp]
theorem shiftPriority_run {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (offset : Nat)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (A.shiftPriority offset).run word n = A.run word n :=
  shiftPriority_runFrom A offset A.initial word n

theorem shiftPriority_prioritySeenFrom_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (offset : Nat)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (p : Nat) :
    (A.shiftPriority offset).PrioritySeenInfinitelyOftenFrom state word (p + offset) ↔
      A.PrioritySeenInfinitelyOftenFrom state word p := by
  constructor
  · intro h n
    rcases h n with ⟨k, hk, hkprio⟩
    refine ⟨k, hk, ?_⟩
    change A.priority ((A.shiftPriority offset).runFrom state word k) + offset =
      p + offset at hkprio
    have hprio := Nat.add_right_cancel hkprio
    simpa [shiftPriority_runFrom] using hprio
  · intro h n
    rcases h n with ⟨k, hk, hkprio⟩
    refine ⟨k, hk, ?_⟩
    change A.priority ((A.shiftPriority offset).runFrom state word k) + offset =
      p + offset
    simpa [shiftPriority_runFrom, hkprio]

theorem shiftPriority_prioritySeen_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (offset : Nat)
    (word : OmegaWord Alphabet)
    (p : Nat) :
    (A.shiftPriority offset).PrioritySeenInfinitelyOften word (p + offset) ↔
      A.PrioritySeenInfinitelyOften word p :=
  shiftPriority_prioritySeenFrom_iff A offset A.initial word p

theorem shiftPriority_prioritySeenFrom_eq_zero_lt {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (offset : Nat)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (q : Nat)
    (hq : q < offset) :
    ¬ (A.shiftPriority offset).PrioritySeenInfinitelyOftenFrom state word q := by
  intro h
  rcases h 0 with ⟨k, _hk, hkprio⟩
  change A.priority ((A.shiftPriority offset).runFrom state word k) + offset = q at hkprio
  omega

theorem shiftPriority_prioritySeen_eq_zero_lt {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (offset : Nat)
    (word : OmegaWord Alphabet)
    (q : Nat)
    (hq : q < offset) :
    ¬ (A.shiftPriority offset).PrioritySeenInfinitelyOften word q :=
  shiftPriority_prioritySeenFrom_eq_zero_lt A offset A.initial word q hq

theorem natEven_add_two_iff (p : Nat) :
    NatEven (p + 2) ↔ NatEven p := by
  constructor
  · intro h
    rcases h with ⟨m, hm⟩
    cases m with
    | zero => omega
    | succ m =>
        refine ⟨m, ?_⟩
        omega
  · intro h
    rcases h with ⟨m, hm⟩
    refine ⟨m + 1, ?_⟩
    omega

theorem natEven_add_one_not_even (p : Nat) :
    NatEven p -> ¬ NatEven (p + 1) := by
  intro hp hsucc
  rcases hp with ⟨m, hm⟩
  rcases hsucc with ⟨n, hn⟩
  omega

theorem natEven_or_natEven_succ (p : Nat) :
    NatEven p ∨ NatEven (p + 1) := by
  induction p with
  | zero =>
      exact Or.inl ⟨0, rfl⟩
  | succ p ih =>
      rcases ih with hp | hp
      · right
        rcases hp with ⟨m, hm⟩
        refine ⟨m + 1, ?_⟩
        omega
      · exact Or.inl hp

theorem shiftPriority_two_acceptsFrom_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    (A.shiftPriority 2).AcceptsFrom state word ↔
      A.AcceptsFrom state word := by
  constructor
  · intro h
    rcases h with ⟨p, hpEven, hpInf, hpMin⟩
    have h2le : 2 ≤ p := by
      by_contra hnot
      have hlt : p < 2 := Nat.lt_of_not_ge hnot
      exact shiftPriority_prioritySeenFrom_eq_zero_lt A 2 state word p hlt hpInf
    refine ⟨p - 2, ?_, ?_, ?_⟩
    · have hpadd : p - 2 + 2 = p := Nat.sub_add_cancel h2le
      rw [← natEven_add_two_iff, hpadd]
      exact hpEven
    · have hpadd : p - 2 + 2 = p := Nat.sub_add_cancel h2le
      rw [← shiftPriority_prioritySeenFrom_iff A 2 state word (p - 2), hpadd]
      exact hpInf
    · intro q hq
      have hshift :
          (A.shiftPriority 2).PrioritySeenInfinitelyOftenFrom state word (q + 2) :=
        (shiftPriority_prioritySeenFrom_iff A 2 state word q).mpr hq
      have hp_le : p ≤ q + 2 := hpMin (q + 2) hshift
      omega
  · intro h
    rcases h with ⟨p, hpEven, hpInf, hpMin⟩
    refine ⟨p + 2, ?_, ?_, ?_⟩
    · rw [natEven_add_two_iff]
      exact hpEven
    · exact (shiftPriority_prioritySeenFrom_iff A 2 state word p).mpr hpInf
    · intro q hq
      by_cases hq2 : q < 2
      · exact False.elim (shiftPriority_prioritySeenFrom_eq_zero_lt A 2 state word q hq2 hq)
      · have h2le : 2 ≤ q := Nat.le_of_not_gt hq2
        have hqadd : q - 2 + 2 = q := Nat.sub_add_cancel h2le
        have hqOrig : A.PrioritySeenInfinitelyOftenFrom state word (q - 2) := by
          rw [← shiftPriority_prioritySeenFrom_iff A 2 state word (q - 2), hqadd]
          exact hq
        have hp_le : p ≤ q - 2 := hpMin (q - 2) hqOrig
        omega

theorem shiftPriority_two_accepts_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    (A.shiftPriority 2).Accepts word ↔ A.Accepts word :=
  shiftPriority_two_acceptsFrom_iff A A.initial word

/--
Shifting every priority by one flips the parity of any existing minimum
priority seen infinitely often.  This is the easy direction of DPA
complementation; the converse needs a finite-run minimum-existence theorem.
-/
theorem shiftPriority_one_not_acceptsFrom_of_acceptsFrom {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    A.AcceptsFrom state word ->
      ¬ (A.shiftPriority 1).AcceptsFrom state word := by
  intro h hshift
  rcases h with ⟨p, hpEven, hpInf, hpMin⟩
  rcases hshift with ⟨q, hqEven, hqInf, hqMin⟩
  have h1le : 1 ≤ q := by
    by_contra hnot
    have hlt : q < 1 := Nat.lt_of_not_ge hnot
    exact shiftPriority_prioritySeenFrom_eq_zero_lt A 1 state word q hlt hqInf
  have hqadd : q - 1 + 1 = q := Nat.sub_add_cancel h1le
  have hqOrig : A.PrioritySeenInfinitelyOftenFrom state word (q - 1) := by
    rw [← shiftPriority_prioritySeenFrom_iff A 1 state word (q - 1), hqadd]
    exact hqInf
  have hp_le : p ≤ q - 1 := hpMin (q - 1) hqOrig
  have hpShift :
      (A.shiftPriority 1).PrioritySeenInfinitelyOftenFrom state word (p + 1) :=
    (shiftPriority_prioritySeenFrom_iff A 1 state word p).mpr hpInf
  have hq_le : q ≤ p + 1 := hqMin (p + 1) hpShift
  have hq_eq : q = p + 1 := by omega
  rw [hq_eq] at hqEven
  exact natEven_add_one_not_even p hpEven hqEven

theorem shiftPriority_one_not_accepts_of_accepts {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    A.Accepts word -> ¬ (A.shiftPriority 1).Accepts word :=
  shiftPriority_one_not_acceptsFrom_of_acceptsFrom A A.initial word

theorem not_acceptsFrom_of_shiftPriority_one_acceptsFrom {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    (A.shiftPriority 1).AcceptsFrom state word ->
      ¬ A.AcceptsFrom state word := by
  intro hshift h
  exact shiftPriority_one_not_acceptsFrom_of_acceptsFrom A state word h hshift

theorem not_accepts_of_shiftPriority_one_accepts {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    (A.shiftPriority 1).Accepts word -> ¬ A.Accepts word :=
  not_acceptsFrom_of_shiftPriority_one_acceptsFrom A A.initial word

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
If a priority appears infinitely often in a finite DPA run, then some concrete
run state with that priority appears infinitely often.
-/
theorem exists_runStateSeenInfinitelyOftenFrom_of_prioritySeenInfinitelyOftenFrom
    {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    {p : Nat}
    (hp : A.PrioritySeenInfinitelyOftenFrom state word p) :
    ∃ q : A.State,
      A.priority q = p ∧
        ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ A.runFrom state word k = q := by
  classical
  let targets : Finset A.State := Finset.univ.filter (fun q => A.priority q = p)
  have hfreq :
      ∀ n : Nat,
        ∃ k : Nat, n ≤ k ∧ A.runFrom state word k ∈ targets := by
    intro n
    rcases hp n with ⟨k, hk, hkprio⟩
    refine ⟨k, hk, ?_⟩
    simp [targets, hkprio]
  rcases exists_seenInfinitelyOften_of_frequently_mem_finset
      (fun n : Nat => A.runFrom state word n) targets hfreq with
    ⟨q, hqTarget, hqSeen⟩
  refine ⟨q, ?_, hqSeen⟩
  simpa [targets] using hqTarget

/-- Some priority occurs infinitely often along every run of a finite DPA. -/
theorem exists_prioritySeenInfinitelyOftenFrom {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    ∃ p : Nat, A.PrioritySeenInfinitelyOftenFrom state word p := by
  classical
  let runState : Nat -> A.State := fun n => A.runFrom state word n
  obtain ⟨loopState, hloop⟩ := Finite.exists_infinite_fiber runState
  refine ⟨A.priority loopState, ?_⟩
  have hfreq : ∃ᶠ n in Filter.atTop, runState n = loopState := by
    rw [Nat.frequently_atTop_iff_infinite]
    simpa [runState, Set.preimage, Set.mem_singleton_iff] using (Set.infinite_coe_iff.1 hloop)
  rw [Filter.frequently_atTop] at hfreq
  intro n
  rcases hfreq n with ⟨k, hk, hkloop⟩
  exact ⟨k, hk, by simp [runState] at hkloop; simp [hkloop]⟩

/-- The infinitely-often priorities of a finite DPA run have a least element. -/
theorem exists_min_prioritySeenInfinitelyOftenFrom {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    ∃ p : Nat,
      A.PrioritySeenInfinitelyOftenFrom state word p ∧
        ∀ q : Nat, A.PrioritySeenInfinitelyOftenFrom state word q -> p ≤ q := by
  classical
  let seen : Set Nat := {p | A.PrioritySeenInfinitelyOftenFrom state word p}
  have hseenFinite : seen.Finite := by
    refine (Set.finite_range A.priority).subset ?_
    intro p hp
    rcases hp 0 with ⟨k, _hk, hkprio⟩
    exact ⟨A.runFrom state word k, hkprio⟩
  have hseenNonempty : seen.Nonempty := by
    rcases exists_prioritySeenInfinitelyOftenFrom A state word with ⟨p, hp⟩
    exact ⟨p, hp⟩
  rcases Set.exists_min_image seen id hseenFinite hseenNonempty with ⟨p, hpSeen, hpMin⟩
  exact ⟨p, hpSeen, fun q hq => hpMin q hq⟩

/-- Acceptance is exactly evenness of the least priority seen infinitely often. -/
theorem acceptsFrom_iff_min_priority_even {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    A.AcceptsFrom state word ↔
      ∃ p : Nat,
        A.PrioritySeenInfinitelyOftenFrom state word p ∧
          (∀ q : Nat, A.PrioritySeenInfinitelyOftenFrom state word q -> p ≤ q) ∧
            DetParityAutomaton.NatEven p := by
  constructor
  · intro h
    rcases h with ⟨p, hpEven, hpSeen, hpMin⟩
    exact ⟨p, hpSeen, hpMin, hpEven⟩
  · intro h
    rcases h with ⟨p, hpSeen, hpMin, hpEven⟩
    exact ⟨p, hpEven, hpSeen, hpMin⟩

/--
Rejection supplies the odd least recurring priority of the run.

This is the contrapositive form used by the lasso extraction: once the DPA
rejects, choose the minimum priority seen infinitely often; it cannot be even.
-/
theorem exists_min_prioritySeenInfinitelyOftenFrom_not_even_of_not_acceptsFrom
    {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (hreject : ¬ A.AcceptsFrom state word) :
    ∃ p : Nat,
      A.PrioritySeenInfinitelyOftenFrom state word p ∧
        (∀ q : Nat, A.PrioritySeenInfinitelyOftenFrom state word q -> p ≤ q) ∧
          ¬ DetParityAutomaton.NatEven p := by
  rcases A.exists_min_prioritySeenInfinitelyOftenFrom state word with
    ⟨p, hpSeen, hpMin⟩
  refine ⟨p, hpSeen, hpMin, ?_⟩
  intro hpEven
  exact hreject
    ((A.acceptsFrom_iff_min_priority_even state word).mpr
      ⟨p, hpSeen, hpMin, hpEven⟩)

/-- Initial-state form of rejection yielding an odd least recurring priority. -/
theorem exists_min_prioritySeenInfinitelyOften_not_even_of_not_accepts
    {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (hreject : ¬ A.Accepts word) :
    ∃ p : Nat,
      A.PrioritySeenInfinitelyOften word p ∧
        (∀ q : Nat, A.PrioritySeenInfinitelyOften word q -> p ≤ q) ∧
          ¬ DetParityAutomaton.NatEven p := by
  exact
    A.exists_min_prioritySeenInfinitelyOftenFrom_not_even_of_not_acceptsFrom
      A.initial word hreject

/--
Rejected runs have a concrete recurrent state carrying the odd least recurring
priority.
-/
theorem exists_recurrent_runState_min_priority_not_even_of_not_acceptsFrom
    {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (hreject : ¬ A.AcceptsFrom state word) :
    ∃ p : Nat,
      ∃ q : A.State,
        A.priority q = p ∧
          (∀ n : Nat, ∃ k : Nat, n ≤ k ∧ A.runFrom state word k = q) ∧
            (∀ r : Nat, A.PrioritySeenInfinitelyOftenFrom state word r -> p ≤ r) ∧
              ¬ DetParityAutomaton.NatEven p := by
  rcases
      A.exists_min_prioritySeenInfinitelyOftenFrom_not_even_of_not_acceptsFrom
        state word hreject with
    ⟨p, hpSeen, hpMin, hpOdd⟩
  rcases
      A.exists_runStateSeenInfinitelyOftenFrom_of_prioritySeenInfinitelyOftenFrom
        state word hpSeen with
    ⟨q, hqPriority, hqSeen⟩
  exact ⟨p, q, hqPriority, hqSeen, hpMin, hpOdd⟩

/-- Initial-state version of `exists_recurrent_runState_min_priority_not_even_of_not_acceptsFrom`. -/
theorem exists_recurrent_runState_min_priority_not_even_of_not_accepts
    {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (hreject : ¬ A.Accepts word) :
    ∃ p : Nat,
      ∃ q : A.State,
        A.priority q = p ∧
          (∀ n : Nat, ∃ k : Nat, n ≤ k ∧ A.run word k = q) ∧
            (∀ r : Nat, A.PrioritySeenInfinitelyOften word r -> p ≤ r) ∧
              ¬ DetParityAutomaton.NatEven p := by
  exact
    A.exists_recurrent_runState_min_priority_not_even_of_not_acceptsFrom
      A.initial word hreject

/--
After a least recurring priority `p` has been chosen, all later priorities are
eventually at least `p`.

This is the DPA-side form of the paper sentence: after deleting a finite prefix,
no priority smaller than the least recurring priority appears.
-/
theorem exists_eventually_priority_ge_of_min_prioritySeenInfinitelyOftenFrom
    {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    {p : Nat}
    (hpMin :
      ∀ q : Nat, A.PrioritySeenInfinitelyOftenFrom state word q -> p ≤ q) :
    ∃ N : Nat,
      ∀ k : Nat, N ≤ k -> p ≤ A.priority (A.runFrom state word k) := by
  classical
  by_contra hno
  push Not at hno
  let targets : Finset A.State :=
    Finset.univ.filter (fun q => A.priority q < p)
  have hfreq :
      ∀ n : Nat,
        ∃ k : Nat, n ≤ k ∧ A.runFrom state word k ∈ targets := by
    intro n
    rcases hno n with ⟨k, hk, hkLt⟩
    refine ⟨k, hk, ?_⟩
    simp [targets, hkLt]
  rcases exists_seenInfinitelyOften_of_frequently_mem_finset
      (fun n : Nat => A.runFrom state word n) targets hfreq with
    ⟨q, hqTarget, hqSeen⟩
  have hqLt : A.priority q < p := by
    simpa [targets] using hqTarget
  have hqPrioritySeen :
      A.PrioritySeenInfinitelyOftenFrom state word (A.priority q) := by
    intro n
    rcases hqSeen n with ⟨k, hk, hkq⟩
    exact ⟨k, hk, by rw [hkq]⟩
  have hle : p ≤ A.priority q := hpMin (A.priority q) hqPrioritySeen
  exact (Nat.not_lt_of_ge hle) hqLt

/--
Negative-form version of
`exists_eventually_priority_ge_of_min_prioritySeenInfinitelyOftenFrom`: after
the cutoff, no smaller priority appears.
-/
theorem exists_eventually_not_priority_lt_of_min_prioritySeenInfinitelyOftenFrom
    {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    {p : Nat}
    (hpMin :
      ∀ q : Nat, A.PrioritySeenInfinitelyOftenFrom state word q -> p ≤ q) :
    ∃ N : Nat,
      ∀ k : Nat, N ≤ k -> ¬ A.priority (A.runFrom state word k) < p := by
  rcases
      A.exists_eventually_priority_ge_of_min_prioritySeenInfinitelyOftenFrom
        state word hpMin with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk hlt
  exact (Nat.not_lt_of_ge (hN k hk)) hlt

/-- Initial-state version of `exists_eventually_priority_ge_of_min_prioritySeenInfinitelyOftenFrom`. -/
theorem exists_eventually_priority_ge_of_min_prioritySeenInfinitelyOften
    {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    {p : Nat}
    (hpMin :
      ∀ q : Nat, A.PrioritySeenInfinitelyOften word q -> p ≤ q) :
    ∃ N : Nat,
      ∀ k : Nat, N ≤ k -> p ≤ A.priority (A.run word k) := by
  exact
    A.exists_eventually_priority_ge_of_min_prioritySeenInfinitelyOftenFrom
      A.initial word hpMin

/-- Initial-state negative-form no-smaller-priority cutoff. -/
theorem exists_eventually_not_priority_lt_of_min_prioritySeenInfinitelyOften
    {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    {p : Nat}
    (hpMin :
      ∀ q : Nat, A.PrioritySeenInfinitelyOften word q -> p ≤ q) :
    ∃ N : Nat,
      ∀ k : Nat, N ≤ k -> ¬ A.priority (A.run word k) < p := by
  exact
    A.exists_eventually_not_priority_lt_of_min_prioritySeenInfinitelyOftenFrom
      A.initial word hpMin

/--
A rejected run supplies a recurrent odd-minimum state and a finite cutoff after
which no smaller priority appears.
-/
theorem exists_recurrent_runState_min_priority_not_even_and_eventually_ge_of_not_acceptsFrom
    {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (hreject : ¬ A.AcceptsFrom state word) :
    ∃ p : Nat,
      ∃ q : A.State,
        ∃ N : Nat,
          A.priority q = p ∧
            (∀ n : Nat, ∃ k : Nat, n ≤ k ∧ A.runFrom state word k = q) ∧
              (∀ k : Nat, N ≤ k -> p ≤ A.priority (A.runFrom state word k)) ∧
                ¬ DetParityAutomaton.NatEven p := by
  rcases
      A.exists_recurrent_runState_min_priority_not_even_of_not_acceptsFrom
        state word hreject with
    ⟨p, q, hqPriority, hqSeen, hpMin, hpOdd⟩
  rcases
      A.exists_eventually_priority_ge_of_min_prioritySeenInfinitelyOftenFrom
        state word hpMin with
    ⟨N, hN⟩
  exact ⟨p, q, N, hqPriority, hqSeen, hN, hpOdd⟩

/-- Initial-state version of rejected-run recurrent state plus no-lower cutoff. -/
theorem exists_recurrent_runState_min_priority_not_even_and_eventually_ge_of_not_accepts
    {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (hreject : ¬ A.Accepts word) :
    ∃ p : Nat,
      ∃ q : A.State,
        ∃ N : Nat,
          A.priority q = p ∧
            (∀ n : Nat, ∃ k : Nat, n ≤ k ∧ A.run word k = q) ∧
              (∀ k : Nat, N ≤ k -> p ≤ A.priority (A.run word k)) ∧
                ¬ DetParityAutomaton.NatEven p := by
  exact
    A.exists_recurrent_runState_min_priority_not_even_and_eventually_ge_of_not_acceptsFrom
      A.initial word hreject

/--
Finite recurring-priority criterion for a DPA run.

If `recurring` is exactly the finite set of priorities seen infinitely often,
then acceptance is decided by the parity of the minimum element of that set.
This is the core lasso/cycle criterion used by finite-game executions.
-/
theorem acceptsFrom_iff_finset_min_recurring_even {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (recurring : Finset Nat)
    (hrecurringNonempty : recurring.Nonempty)
    (hrecurring :
      ∀ p : Nat,
        A.PrioritySeenInfinitelyOftenFrom state word p ↔ p ∈ recurring) :
    A.AcceptsFrom state word ↔
      DetParityAutomaton.NatEven (recurring.min' hrecurringNonempty) := by
  constructor
  · intro h
    rcases (A.acceptsFrom_iff_min_priority_even state word).mp h with
      ⟨p, hpSeen, hpMin, hpEven⟩
    have hminLeP : recurring.min' hrecurringNonempty ≤ p :=
      recurring.min'_le p ((hrecurring p).mp hpSeen)
    have hpLeMin :
        p ≤ recurring.min' hrecurringNonempty :=
      hpMin (recurring.min' hrecurringNonempty)
        ((hrecurring (recurring.min' hrecurringNonempty)).mpr
          (recurring.min'_mem hrecurringNonempty))
    have hpEq : p = recurring.min' hrecurringNonempty :=
      Nat.le_antisymm hpLeMin hminLeP
    rwa [← hpEq]
  · intro hminEven
    exact
      (A.acceptsFrom_iff_min_priority_even state word).mpr
        ⟨recurring.min' hrecurringNonempty,
          (hrecurring (recurring.min' hrecurringNonempty)).mpr
            (recurring.min'_mem hrecurringNonempty),
          fun q hq =>
            recurring.min'_le q ((hrecurring q).mp hq),
          hminEven⟩

/--
Finite eventual-recurring-priority criterion.

If, after some finite prefix, every priority lies in `recurring`, and every
priority in `recurring` appears infinitely often, then `recurring` is exactly
the recurring-priority set.  Hence acceptance is decided by the minimum element
of `recurring`.
-/
theorem acceptsFrom_iff_eventual_recurring_finset_min_even {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (recurring : Finset Nat)
    (hrecurringNonempty : recurring.Nonempty)
    (heventual :
      ∃ N : Nat,
        ∀ k : Nat,
          N ≤ k ->
            A.priority (A.runFrom state word k) ∈ recurring)
    (hfrequent :
      ∀ p : Nat,
        p ∈ recurring ->
          A.PrioritySeenInfinitelyOftenFrom state word p) :
    A.AcceptsFrom state word ↔
      DetParityAutomaton.NatEven (recurring.min' hrecurringNonempty) := by
  rcases heventual with ⟨N, hN⟩
  exact
    A.acceptsFrom_iff_finset_min_recurring_even
      state word recurring hrecurringNonempty
      (fun p => by
        constructor
        · intro hpSeen
          rcases hpSeen N with ⟨k, hk, hkprio⟩
          rw [← hkprio]
          exact hN k hk
        · exact hfrequent p)

/--
Cycle-priority criterion for an eventually periodic DPA run.

This is the form used by finite games: after a finite prefix, every later
priority is one of the priorities on a non-empty finite cycle, and each cycle
priority recurs infinitely often.  Acceptance is therefore just parity of the
least priority on that cycle.
-/
theorem acceptsFrom_iff_eventual_cycle_priority_min_even {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (start period : Nat)
    (hperiodPositive : 0 < period)
    (hcover :
      ∀ k : Nat,
        start ≤ k ->
          ∃ i : Nat,
            i < period ∧
              A.priority (A.runFrom state word k) =
                A.priority (A.runFrom state word (start + i)))
    (hcycleFrequent :
      ∀ i : Nat,
        i < period ->
          A.PrioritySeenInfinitelyOftenFrom state word
            (A.priority (A.runFrom state word (start + i)))) :
    A.AcceptsFrom state word ↔
      DetParityAutomaton.NatEven
        (((Finset.range period).image
          (fun i : Nat => A.priority (A.runFrom state word (start + i)))).min'
            (Finset.image_nonempty.mpr
              (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hperiodPositive)))) := by
  classical
  let recurring : Finset Nat :=
    (Finset.range period).image
      (fun i : Nat => A.priority (A.runFrom state word (start + i)))
  have hrecurringNonempty : recurring.Nonempty :=
    Finset.image_nonempty.mpr
      (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hperiodPositive))
  have heventual :
      ∃ N : Nat,
        ∀ k : Nat,
          N ≤ k ->
            A.priority (A.runFrom state word k) ∈ recurring := by
    refine ⟨start, ?_⟩
    intro k hk
    rcases hcover k hk with ⟨i, hi, hprio⟩
    rw [hprio]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  have hfrequent :
      ∀ p : Nat,
        p ∈ recurring ->
          A.PrioritySeenInfinitelyOftenFrom state word p := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, hip⟩
    rw [← hip]
    exact hcycleFrequent i (Finset.mem_range.mp hi)
  exact
    A.acceptsFrom_iff_eventual_recurring_finset_min_even
      state word recurring hrecurringNonempty heventual hfrequent

/--
Cycle-priority criterion where recurrence is supplied by an explicit period.

This is closer to the output of a finite transition-graph loop search: coverage
says every sufficiently late priority is represented in the cycle window, and
`hperiodic` says every cycle-window priority repeats along the arithmetic
progression with step `period`.
-/
theorem acceptsFrom_iff_eventual_periodic_cycle_priority_min_even {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (start period : Nat)
    (hperiodPositive : 0 < period)
    (hcover :
      ∀ k : Nat,
        start ≤ k ->
          ∃ i : Nat,
            i < period ∧
              A.priority (A.runFrom state word k) =
                A.priority (A.runFrom state word (start + i)))
    (hperiodic :
      ∀ i n : Nat,
        i < period ->
          A.priority (A.runFrom state word (start + i + n * period)) =
            A.priority (A.runFrom state word (start + i))) :
    A.AcceptsFrom state word ↔
      DetParityAutomaton.NatEven
        (((Finset.range period).image
          (fun i : Nat => A.priority (A.runFrom state word (start + i)))).min'
            (Finset.image_nonempty.mpr
              (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hperiodPositive)))) := by
  refine
    A.acceptsFrom_iff_eventual_cycle_priority_min_even
      state word start period hperiodPositive hcover ?_
  intro i hi n
  refine ⟨start + i + n * period, ?_, ?_⟩
  · have hperiodOne : 1 ≤ period := hperiodPositive
    have hnle : n ≤ n * period := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left n hperiodOne
    omega
  · exact hperiodic i n hi

/--
If the first position of a nonempty cycle window has priority `p` and no
cycle-window priority is smaller than `p`, then the finite minimum of the
cycle-window priorities is exactly `p`.
-/
theorem cycle_priority_min_eq_of_entry_priority_le_all
    (period : Nat)
    (priorityOf : Nat -> Nat)
    (hperiodPositive : 0 < period)
    {p : Nat}
    (hentry : priorityOf 0 = p)
    (hcycleLower : ∀ i : Nat, i < period -> p ≤ priorityOf i) :
    (((Finset.range period).image priorityOf).min'
      (Finset.image_nonempty.mpr
        (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hperiodPositive)))) = p := by
  classical
  let priorities : Finset Nat := (Finset.range period).image priorityOf
  have hprioritiesNonempty : priorities.Nonempty :=
    Finset.image_nonempty.mpr
      (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hperiodPositive))
  have hpMem : p ∈ priorities := by
    rw [← hentry]
    exact Finset.mem_image.mpr
      ⟨0, Finset.mem_range.mpr hperiodPositive, rfl⟩
  have hminLe : priorities.min' hprioritiesNonempty ≤ p :=
    priorities.min'_le p hpMem
  have hpLeMin : p ≤ priorities.min' hprioritiesNonempty := by
    have hminMem : priorities.min' hprioritiesNonempty ∈ priorities :=
      priorities.min'_mem hprioritiesNonempty
    rcases Finset.mem_image.mp hminMem with ⟨i, hi, hpriority⟩
    rw [← hpriority]
    exact hcycleLower i (Finset.mem_range.mp hi)
  have hEq : priorities.min' hprioritiesNonempty = p :=
    Nat.le_antisymm hminLe hpLeMin
  simpa [priorities] using hEq

/--
If some position in a nonempty cycle window has priority `p` and no cycle-window
priority is smaller than `p`, then the finite minimum of the cycle-window
priorities is exactly `p`.
-/
theorem cycle_priority_min_eq_of_witness_priority_le_all
    (period : Nat)
    (priorityOf : Nat -> Nat)
    (hperiodPositive : 0 < period)
    (witness : Nat)
    (hwitnessLt : witness < period)
    {p : Nat}
    (hwitness : priorityOf witness = p)
    (hcycleLower : ∀ i : Nat, i < period -> p ≤ priorityOf i) :
    (((Finset.range period).image priorityOf).min'
      (Finset.image_nonempty.mpr
        (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hperiodPositive)))) = p := by
  classical
  let priorities : Finset Nat := (Finset.range period).image priorityOf
  have hprioritiesNonempty : priorities.Nonempty :=
    Finset.image_nonempty.mpr
      (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hperiodPositive))
  have hpMem : p ∈ priorities := by
    rw [← hwitness]
    exact Finset.mem_image.mpr
      ⟨witness, Finset.mem_range.mpr hwitnessLt, rfl⟩
  have hminLe : priorities.min' hprioritiesNonempty ≤ p :=
    priorities.min'_le p hpMem
  have hpLeMin : p ≤ priorities.min' hprioritiesNonempty := by
    have hminMem : priorities.min' hprioritiesNonempty ∈ priorities :=
      priorities.min'_mem hprioritiesNonempty
    rcases Finset.mem_image.mp hminMem with ⟨i, hi, hpriority⟩
    rw [← hpriority]
    exact hcycleLower i (Finset.mem_range.mp hi)
  have hEq : priorities.min' hprioritiesNonempty = p :=
    Nat.le_antisymm hminLe hpLeMin
  simpa [priorities] using hEq

/--
Odd-entry/lower-bound form of the cycle-minimum parity argument.

This is the DPA-side package used after lasso extraction: the selected cycle
contains the odd least recurring priority at its entry, and the cutoff guarantees
that no smaller priority appears on the cycle.
-/
theorem not_natEven_cycle_priority_min_of_entry_priority_le_all
    (period : Nat)
    (priorityOf : Nat -> Nat)
    (hperiodPositive : 0 < period)
    {p : Nat}
    (hentry : priorityOf 0 = p)
    (hcycleLower : ∀ i : Nat, i < period -> p ≤ priorityOf i)
    (hpOdd : ¬ DetParityAutomaton.NatEven p) :
    ¬ DetParityAutomaton.NatEven
      (((Finset.range period).image priorityOf).min'
        (Finset.image_nonempty.mpr
          (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hperiodPositive)))) := by
  rw [cycle_priority_min_eq_of_entry_priority_le_all
    period priorityOf hperiodPositive hentry hcycleLower]
  exact hpOdd

/--
Odd-witness/lower-bound form of the cycle-minimum parity argument.

This is the form aligned with the paper lasso proof: the selected cycle may be
entered at a state different from the odd recurrent state, as long as the cycle
contains that odd-priority state and no lower priority.
-/
theorem not_natEven_cycle_priority_min_of_witness_priority_le_all
    (period : Nat)
    (priorityOf : Nat -> Nat)
    (hperiodPositive : 0 < period)
    (witness : Nat)
    (hwitnessLt : witness < period)
    {p : Nat}
    (hwitness : priorityOf witness = p)
    (hcycleLower : ∀ i : Nat, i < period -> p ≤ priorityOf i)
    (hpOdd : ¬ DetParityAutomaton.NatEven p) :
    ¬ DetParityAutomaton.NatEven
      (((Finset.range period).image priorityOf).min'
        (Finset.image_nonempty.mpr
          (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hperiodPositive)))) := by
  rw [cycle_priority_min_eq_of_witness_priority_le_all
    period priorityOf hperiodPositive witness hwitnessLt hwitness hcycleLower]
  exact hpOdd

/--
If a DPA run returns to the same state after `period` steps and the word repeats
from `start`, then the whole run repeats from `start`.
-/
theorem runFrom_loop_shift {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet)
    (start period : Nat)
    (hloop :
      A.runFrom state word (start + period) =
        A.runFrom state word start)
    (hword :
      ∀ m : Nat, word (start + period + m) = word (start + m)) :
    ∀ m : Nat,
      A.runFrom state word (start + period + m) =
        A.runFrom state word (start + m) := by
  intro m
  induction m with
  | zero =>
      simpa [Nat.add_assoc] using hloop
  | succ m ih =>
      have hleft :
          start + period + (m + 1) = (start + period + m) + 1 := by
        omega
      have hright :
          start + (m + 1) = (start + m) + 1 := by
        omega
      rw [hleft, hright]
      change
        A.step (A.runFrom state word (start + period + m))
            (word (start + period + m)) =
          A.step (A.runFrom state word (start + m))
            (word (start + m))
      rw [ih, hword m]

/-- Initial-state version of `runFrom_loop_shift`. -/
theorem run_loop_shift {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (start period : Nat)
    (hloop : A.run word (start + period) = A.run word start)
    (hword :
      ∀ m : Nat, word (start + period + m) = word (start + m)) :
    ∀ m : Nat,
      A.run word (start + period + m) = A.run word (start + m) := by
  exact A.runFrom_loop_shift A.initial word start period hloop hword

/--
A looping DPA state and periodic word labels make the priorities on the cycle
window recur along all later periods.
-/
theorem priority_periodic_of_run_loop {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (start period : Nat)
    (hloop : A.run word (start + period) = A.run word start)
    (hword :
      ∀ m : Nat, word (start + period + m) = word (start + m)) :
    ∀ i n : Nat,
      i < period ->
        A.priority (A.run word (start + i + n * period)) =
          A.priority (A.run word (start + i)) := by
  intro i n hi
  have hshift := A.run_loop_shift word start period hloop hword
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        A.priority (A.run word (start + i + (n + 1) * period))
            =
          A.priority (A.run word (start + period + (i + n * period))) := by
            congr 2
            have hmul : (n + 1) * period = n * period + period := by
              rw [Nat.succ_mul]
            omega
        _ =
          A.priority (A.run word (start + (i + n * period))) := by
            exact congrArg A.priority (hshift (i + n * period))
        _ =
          A.priority (A.run word (start + i + n * period)) := by
            congr 2
            omega
        _ =
          A.priority (A.run word (start + i)) := ih

theorem shiftPriority_one_acceptsFrom_iff_not_acceptsFrom {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet) :
    (A.shiftPriority 1).AcceptsFrom state word ↔
      ¬ A.AcceptsFrom state word := by
  constructor
  · exact not_acceptsFrom_of_shiftPriority_one_acceptsFrom A state word
  · intro hnot
    rcases exists_min_prioritySeenInfinitelyOftenFrom (A.shiftPriority 1) state word with
      ⟨q, hqInf, hqMin⟩
    have h1le : 1 ≤ q := by
      by_contra hnotLe
      have hlt : q < 1 := Nat.lt_of_not_ge hnotLe
      exact shiftPriority_prioritySeenFrom_eq_zero_lt A 1 state word q hlt hqInf
    have hqadd : q - 1 + 1 = q := Nat.sub_add_cancel h1le
    have hqOrig : A.PrioritySeenInfinitelyOftenFrom state word (q - 1) := by
      rw [← shiftPriority_prioritySeenFrom_iff A 1 state word (q - 1), hqadd]
      exact hqInf
    have hqOrigMin :
        ∀ r : Nat, A.PrioritySeenInfinitelyOftenFrom state word r -> q - 1 ≤ r := by
      intro r hr
      have hshift :
          (A.shiftPriority 1).PrioritySeenInfinitelyOftenFrom state word (r + 1) :=
        (shiftPriority_prioritySeenFrom_iff A 1 state word r).mpr hr
      have hqle : q ≤ r + 1 := hqMin (r + 1) hshift
      omega
    have hqEven : NatEven q := by
      by_contra hqOdd
      have hpredEven : NatEven (q - 1) := by
        rcases natEven_or_natEven_succ (q - 1) with hpred | hsucc
        · exact hpred
        · exfalso
          apply hqOdd
          simpa [hqadd] using hsucc
      exact hnot ⟨q - 1, hpredEven, hqOrig, hqOrigMin⟩
    exact ⟨q, hqEven, hqInf, hqMin⟩

theorem shiftPriority_one_accepts_iff_not_accepts {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    (A.shiftPriority 1).Accepts word ↔ ¬ A.Accepts word :=
  shiftPriority_one_acceptsFrom_iff_not_acceptsFrom A A.initial word

/-- Shifting all priorities by one recognizes the complement omega-language. -/
theorem shiftPriority_one_recognizes_compl {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (language : Set (OmegaWord Alphabet))
    (hA : A.Recognizes language) :
    (A.shiftPriority 1).Recognizes (languageᶜ) := by
  intro word
  rw [shiftPriority_one_accepts_iff_not_accepts, hA]
  rfl

/-- Shifting all priorities by two preserves a recognized omega-language. -/
theorem shiftPriority_two_recognizes {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (language : Set (OmegaWord Alphabet))
    (hA : A.Recognizes language) :
    (A.shiftPriority 2).Recognizes language := by
  intro word
  rw [shiftPriority_two_accepts_iff, hA]

/-- Pull a deterministic parity automaton back along an alphabet map. -/
def comap {Alphabet : Type u} {Alphabet' : Type v}
    (A : DetParityAutomaton Alphabet)
    (f : Alphabet' -> Alphabet) :
    DetParityAutomaton Alphabet' where
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  step state letter := A.step state (f letter)
  priority := A.priority

@[simp]
theorem comap_runFrom {Alphabet : Type u} {Alphabet' : Type v}
    (A : DetParityAutomaton Alphabet)
    (f : Alphabet' -> Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet')
    (n : Nat) :
    (A.comap f).runFrom state word n =
      A.runFrom state (OmegaWord.map f word) n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      change
        A.step ((A.comap f).runFrom state word n) (f (word n)) =
          A.step (A.runFrom state (OmegaWord.map f word) n) (f (word n))
      rw [ih]

@[simp]
theorem comap_run {Alphabet : Type u} {Alphabet' : Type v}
    (A : DetParityAutomaton Alphabet)
    (f : Alphabet' -> Alphabet)
    (word : OmegaWord Alphabet')
    (n : Nat) :
    (A.comap f).run word n = A.run (OmegaWord.map f word) n := by
  exact comap_runFrom A f A.initial word n

theorem comap_prioritySeenFrom_iff {Alphabet : Type u} {Alphabet' : Type v}
    (A : DetParityAutomaton Alphabet)
    (f : Alphabet' -> Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet')
    (p : Nat) :
    (A.comap f).PrioritySeenInfinitelyOftenFrom state word p ↔
      A.PrioritySeenInfinitelyOftenFrom state (OmegaWord.map f word) p := by
  constructor
  · intro h n
    rcases h n with ⟨k, hk, hkprio⟩
    refine ⟨k, hk, ?_⟩
    change A.priority ((A.comap f).runFrom state word k) = p at hkprio
    simpa [comap_runFrom] using hkprio
  · intro h n
    rcases h n with ⟨k, hk, hkprio⟩
    refine ⟨k, hk, ?_⟩
    change A.priority ((A.comap f).runFrom state word k) = p
    simpa [comap_runFrom] using hkprio

theorem comap_acceptsFrom_iff {Alphabet : Type u} {Alphabet' : Type v}
    (A : DetParityAutomaton Alphabet)
    (f : Alphabet' -> Alphabet)
    (state : A.State)
    (word : OmegaWord Alphabet') :
    (A.comap f).AcceptsFrom state word ↔
      A.AcceptsFrom state (OmegaWord.map f word) := by
  constructor
  · intro h
    rcases h with ⟨p, hpEven, hpInf, hpMin⟩
    refine ⟨p, hpEven, (comap_prioritySeenFrom_iff A f state word p).mp hpInf, ?_⟩
    intro q hq
    exact hpMin q ((comap_prioritySeenFrom_iff A f state word q).mpr hq)
  · intro h
    rcases h with ⟨p, hpEven, hpInf, hpMin⟩
    refine ⟨p, hpEven, (comap_prioritySeenFrom_iff A f state word p).mpr hpInf, ?_⟩
    intro q hq
    exact hpMin q ((comap_prioritySeenFrom_iff A f state word q).mp hq)

theorem comap_accepts_iff {Alphabet : Type u} {Alphabet' : Type v}
    (A : DetParityAutomaton Alphabet)
    (f : Alphabet' -> Alphabet)
    (word : OmegaWord Alphabet') :
    (A.comap f).Accepts word ↔ A.Accepts (OmegaWord.map f word) := by
  exact comap_acceptsFrom_iff A f A.initial word

/-- Pullback recognizes inverse images of omega-languages. -/
theorem comap_recognizes {Alphabet : Type u} {Alphabet' : Type v}
    (A : DetParityAutomaton Alphabet)
    (f : Alphabet' -> Alphabet)
    (language : Set (OmegaWord Alphabet))
    (hA : A.Recognizes language) :
    (A.comap f).Recognizes { word | OmegaWord.map f word ∈ language } := by
  intro word
  rw [comap_accepts_iff, hA]
  rfl

/-- Delay a deterministic parity automaton by one input letter. -/
def next {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet) :
    DetParityAutomaton Alphabet where
  State := Option A.State
  stateFinite := inferInstance
  initial := none
  step state letter :=
    match state with
    | none => some A.initial
    | some q => some (A.step q letter)
  priority state :=
    match state with
    | none => 1
    | some q => A.priority q

@[simp]
theorem next_run_succ {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    A.next.run word (n + 1) = some (A.run (OmegaWord.drop word 1) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [run_succ, ih]
      simp [next, OmegaWord.drop, Nat.add_comm]

theorem next_priority_seen_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (p : Nat) :
    A.next.PrioritySeenInfinitelyOften word p ↔
      A.PrioritySeenInfinitelyOften (OmegaWord.drop word 1) p := by
  constructor
  · intro h n
    rcases h (n + 1) with ⟨k, hk, hkprio⟩
    cases k with
    | zero =>
        cases Nat.not_succ_le_zero n hk
    | succ j =>
        refine ⟨j, Nat.succ_le_succ_iff.mp hk, ?_⟩
        rw [next_run_succ] at hkprio
        simpa [next] using hkprio
  · intro h n
    rcases h n with ⟨k, hk, hkprio⟩
    refine ⟨k + 1, Nat.le_trans hk (Nat.le_succ k), ?_⟩
    rw [next_run_succ]
    simpa [next] using hkprio

/-- The delay construction recognizes the one-step shifted language. -/
theorem next_accepts_iff {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    A.next.Accepts word ↔ A.Accepts (OmegaWord.drop word 1) := by
  constructor
  · intro h
    rcases h with ⟨p, hpEven, hpInf, hpMin⟩
    refine ⟨p, hpEven, (next_priority_seen_iff A word p).mp hpInf, ?_⟩
    intro q hq
    exact hpMin q ((next_priority_seen_iff A word q).mpr hq)
  · intro h
    rcases h with ⟨p, hpEven, hpInf, hpMin⟩
    refine ⟨p, hpEven, (next_priority_seen_iff A word p).mpr hpInf, ?_⟩
    intro q hq
    exact hpMin q ((next_priority_seen_iff A word q).mp hq)

/-- If `A` recognizes an LTL formula, `A.next` recognizes its `X`-shift. -/
theorem next_recognizes_ltl_next {AP : Type u} {Alphabet : Type v}
    (interp : AP -> Alphabet -> Prop)
    (φ : LTL AP)
    (A : DetParityAutomaton Alphabet)
    (hA : ∀ word : OmegaWord Alphabet,
      A.Accepts word ↔ LTL.Satisfies interp word φ)
    (word : OmegaWord Alphabet) :
    A.next.Accepts word ↔ LTL.Satisfies interp word (LTL.next φ) := by
  rw [next_accepts_iff, hA]
  rfl

end DetParityAutomaton

end DistributedSynthesis
