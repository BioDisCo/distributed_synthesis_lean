/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Data.Fintype.Option
import Mathlib.Tactic
import DistributedSynthesis.Formalizations.Definition.DefOmegaAutomata
import DistributedSynthesis.Formalizations.Theorem.ThmLTLtoDPA

/-!
# Constructive DPA compiler for propositional LTL

This is the first concrete, verified compiler in the LTL library.  It handles
the Boolean fragment of LTL, whose truth depends only on the current letter.
The automaton reads the first letter, stores the truth value forever, and uses
parity priorities `0`/`1`.
-/

namespace DistributedSynthesis

universe u v

namespace LTL

/-- The Boolean, non-temporal fragment of LTL. -/
inductive Propositional (AP : Type u) : Type u where
  | verum : Propositional AP
  | falsum : Propositional AP
  | atom : AP -> Propositional AP
  | neg : Propositional AP -> Propositional AP
  | conj : Propositional AP -> Propositional AP -> Propositional AP
  | disj : Propositional AP -> Propositional AP -> Propositional AP
deriving Repr, DecidableEq

namespace Propositional

/-- Embed propositional formulas into full LTL. -/
def toLTL {AP : Type u} : Propositional AP -> LTL AP
  | verum => LTL.verum
  | falsum => LTL.falsum
  | atom ap => LTL.atom ap
  | neg φ => LTL.neg φ.toLTL
  | conj φ ψ => LTL.conj φ.toLTL ψ.toLTL
  | disj φ ψ => LTL.disj φ.toLTL ψ.toLTL

/-- Evaluate a propositional formula on one letter. -/
def Eval {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (letter : Letter) :
    Propositional AP -> Prop
  | verum => True
  | falsum => False
  | atom ap => interp ap letter
  | neg φ => ¬ Eval interp letter φ
  | conj φ ψ => Eval interp letter φ ∧ Eval interp letter ψ
  | disj φ ψ => Eval interp letter φ ∨ Eval interp letter ψ

noncomputable instance evalDecidable {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (letter : Letter)
    (φ : Propositional AP) :
    Decidable (Eval interp letter φ) := by
  induction φ with
  | verum => exact isTrue trivial
  | falsum => exact isFalse id
  | atom ap => exact inferInstanceAs (Decidable (interp ap letter))
  | neg φ ih => exact inferInstanceAs (Decidable (¬ Eval interp letter φ))
  | conj φ ψ ihφ ihψ =>
      exact inferInstanceAs (Decidable (Eval interp letter φ ∧ Eval interp letter ψ))
  | disj φ ψ ihφ ihψ =>
      exact inferInstanceAs (Decidable (Eval interp letter φ ∨ Eval interp letter ψ))

/-- Propositional evaluation agrees with full LTL semantics after embedding. -/
theorem satisfies_toLTL {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ : Propositional AP) :
    LTL.Satisfies interp word φ.toLTL ↔ Eval interp (word 0) φ := by
  induction φ with
  | verum => simp [toLTL, Eval, LTL.Satisfies]
  | falsum => simp [toLTL, Eval, LTL.Satisfies]
  | atom ap => simp [toLTL, Eval, LTL.Satisfies]
  | neg φ ih => simp [toLTL, Eval, LTL.Satisfies, ih]
  | conj φ ψ ihφ ihψ => simp [toLTL, Eval, LTL.Satisfies, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [toLTL, Eval, LTL.Satisfies, ihφ, ihψ]

/--
Any propositional-until witness can be replaced by the first right-side
witness.  This is the key bounded-minimum fact needed by deterministic
monitors for `φ U ψ`: before the first right-side hit, the left side still
holds and the right side has not occurred.
-/
theorem until_first_witness {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (h :
      ∃ n : Nat,
        Eval interp (word n) ψ ∧
          ∀ k : Nat, k < n -> Eval interp (word k) φ) :
    ∃ n : Nat,
      Eval interp (word n) ψ ∧
        ∀ k : Nat,
          k < n -> Eval interp (word k) φ ∧ ¬ Eval interp (word k) ψ := by
  classical
  rcases h with ⟨n, hnψ, hbefore⟩
  let hp : ∃ j : Nat, Eval interp (word j) ψ := ⟨n, hnψ⟩
  refine ⟨Nat.find hp, Nat.find_spec hp, ?_⟩
  intro k hk
  constructor
  · have hfind_le_n : Nat.find hp ≤ n := Nat.find_min' hp hnψ
    exact hbefore k (Nat.lt_of_lt_of_le hk hfind_le_n)
  · exact Nat.find_min hp hk

/-- Forget the "first witness" strengthening of `until_first_witness`. -/
theorem until_first_witness_forget {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (h :
      ∃ n : Nat,
        Eval interp (word n) ψ ∧
          ∀ k : Nat,
            k < n -> Eval interp (word k) φ ∧ ¬ Eval interp (word k) ψ) :
    ∃ n : Nat,
      Eval interp (word n) ψ ∧
        ∀ k : Nat, k < n -> Eval interp (word k) φ := by
  rcases h with ⟨n, hnψ, hbefore⟩
  exact ⟨n, hnψ, fun k hk => (hbefore k hk).1⟩

/-- Embedded propositional `until` is exactly the expected finite-prefix predicate. -/
theorem satisfies_until_toLTL {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP) :
    LTL.Satisfies interp word (LTL.until φ.toLTL ψ.toLTL) ↔
      ∃ n : Nat,
        Eval interp (word n) ψ ∧
          ∀ k : Nat, k < n -> Eval interp (word k) φ := by
  constructor
  · intro h
    rcases h with ⟨n, hnψ, hbefore⟩
    refine ⟨n, ?_, ?_⟩
    · exact (satisfies_toLTL interp (OmegaWord.drop word n) ψ).mp hnψ
    · intro k hk
      exact (satisfies_toLTL interp (OmegaWord.drop word k) φ).mp (hbefore k hk)
  · intro h
    rcases h with ⟨n, hnψ, hbefore⟩
    refine ⟨n, ?_, ?_⟩
    · exact (satisfies_toLTL interp (OmegaWord.drop word n) ψ).mpr hnψ
    · intro k hk
      exact (satisfies_toLTL interp (OmegaWord.drop word k) φ).mpr (hbefore k hk)

/-- Embedded propositional `release` is exactly the expected prefix predicate. -/
theorem satisfies_release_toLTL {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP) :
    LTL.Satisfies interp word (LTL.release φ.toLTL ψ.toLTL) ↔
      ∀ n : Nat,
        Eval interp (word n) ψ ∨
          ∃ k : Nat, k < n ∧ Eval interp (word k) φ := by
  constructor
  · intro h n
    rcases h n with hnψ | ⟨k, hk, hkφ⟩
    · exact Or.inl ((satisfies_toLTL interp (OmegaWord.drop word n) ψ).mp hnψ)
    · exact Or.inr ⟨k, hk,
        (satisfies_toLTL interp (OmegaWord.drop word k) φ).mp hkφ⟩
  · intro h n
    rcases h n with hnψ | ⟨k, hk, hkφ⟩
    · exact Or.inl ((satisfies_toLTL interp (OmegaWord.drop word n) ψ).mpr hnψ)
    · exact Or.inr ⟨k, hk,
        (satisfies_toLTL interp (OmegaWord.drop word k) φ).mpr hkφ⟩

/-- State after reading the first letter: either no letter yet, or the stored truth value. -/
abbrev FirstLetterState := Option Bool

/-- Deterministic parity automaton for a propositional formula. -/
noncomputable def dpa {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    DetParityAutomaton Letter where
  State := FirstLetterState
  stateFinite := inferInstance
  initial := none
  step state letter :=
    match state with
    | none => some (decide (Eval interp letter φ))
    | some value => some value
  priority state :=
    match state with
    | some true => 0
    | _ => 1

@[simp]
theorem dpa_priority_some_true {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    (dpa interp φ).priority (some true) = 0 :=
  rfl

@[simp]
theorem dpa_priority_some_false {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    (dpa interp φ).priority (some false) = 1 :=
  rfl

@[simp]
theorem dpa_run_succ {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP)
    (word : OmegaWord Letter)
    (n : Nat) :
    (dpa interp φ).run word (n + 1) =
      some (decide (Eval interp (word 0) φ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [DetParityAutomaton.run_succ, ih]
      rfl

private theorem dpa_accepts_of_eval {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP)
    (word : OmegaWord Letter)
    (h : Eval interp (word 0) φ) :
    (dpa interp φ).Accepts word := by
  refine ⟨0, ⟨⟨0, rfl⟩, ?_, ?_⟩⟩
  · intro n
    refine ⟨n + 1, Nat.le_succ n, ?_⟩
    change
      (dpa interp φ).priority ((dpa interp φ).run word (n + 1)) = 0
    rw [dpa_run_succ]
    simp [h]
  · intro q _hq
    exact Nat.zero_le q

private theorem not_accepts_dpa_of_not_eval {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP)
    (word : OmegaWord Letter)
    (h : ¬ Eval interp (word 0) φ) :
    ¬ (dpa interp φ).Accepts word := by
  intro hacc
  rcases hacc with ⟨p, hpEven, hpInf, hpMin⟩
  have hprio : ∀ k : Nat, 1 ≤ k -> (dpa interp φ).priority ((dpa interp φ).run word k) = 1 := by
    intro k hk
    cases k with
    | zero => cases hk
    | succ n =>
        rw [dpa_run_succ]
        simp [h]
  have hp_eq_one : p = 1 := by
    rcases hpInf 1 with ⟨k, hk, hkprio⟩
    have := hprio k hk
    exact hkprio.symm.trans this
  rcases hpEven with ⟨m, hm⟩
  omega

/-- The propositional DPA recognizes exactly the embedded propositional formula. -/
theorem dpa_correct {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP)
    (word : OmegaWord Letter) :
    (dpa interp φ).Accepts word ↔ LTL.Satisfies interp word φ.toLTL := by
  rw [satisfies_toLTL]
  constructor
  · intro hacc
    by_contra hfalse
    exact not_accepts_dpa_of_not_eval interp φ word hfalse hacc
  · exact dpa_accepts_of_eval interp φ word

/-- Package the propositional DPA in the reusable formula-compilation interface. -/
noncomputable def toFormulaCompilation {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    LTLFormulaDPACompilation.{u, v, 0} interp φ.toLTL where
  dpa := dpa interp φ
  correct := dpa_correct interp φ

/--
Package `X φ` for propositional `φ` using the reusable DPA delay
construction.
-/
noncomputable def nextFormulaCompilation {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    LTLFormulaDPACompilation.{u, v, 0} interp (LTL.next φ.toLTL) :=
  (toFormulaCompilation interp φ).next

/-!
## First temporal construction: eventually propositional

The following DPA is a constructive temporal step beyond the purely
current-letter fragment.  It recognizes `◇φ` when `φ` is propositional: the
state records whether a satisfying letter has occurred already.
-/

/-- DPA for `eventually φ`, where `φ` is propositional. -/
noncomputable def eventuallyDPA {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    DetParityAutomaton Letter where
  State := Bool
  stateFinite := inferInstance
  initial := false
  step seen letter := seen || decide (Eval interp letter φ)
  priority seen :=
    if seen then
      0
    else
      1

@[simp]
theorem eventuallyDPA_priority_true {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    (eventuallyDPA interp φ).priority true = 0 :=
  rfl

@[simp]
theorem eventuallyDPA_priority_false {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    (eventuallyDPA interp φ).priority false = 1 :=
  rfl

@[simp]
theorem eventuallyDPA_run_eq {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP)
    (word : OmegaWord Letter)
    (n : Nat) :
    (eventuallyDPA interp φ).run word n =
      decide (∃ k : Nat, k < n ∧ Eval interp (word k) φ) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [DetParityAutomaton.run_succ, ih]
      by_cases hseen : ∃ k : Nat, k < n ∧ Eval interp (word k) φ
      · have hsucc : ∃ k : Nat, k < n + 1 ∧ Eval interp (word k) φ := by
          rcases hseen with ⟨k, hk, hkEval⟩
          exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self n), hkEval⟩
        have hsuccLe : ∃ k : Nat, k ≤ n ∧ Eval interp (word k) φ := by
          rcases hseen with ⟨k, hk, hkEval⟩
          exact ⟨k, Nat.le_of_lt hk, hkEval⟩
        simpa [eventuallyDPA, hseen, Nat.lt_succ_iff] using hsuccLe
      · by_cases hnow : Eval interp (word n) φ
        · have hsucc : ∃ k : Nat, k < n + 1 ∧ Eval interp (word k) φ :=
            ⟨n, Nat.lt_succ_self n, hnow⟩
          have hsuccLe : ∃ k : Nat, k ≤ n ∧ Eval interp (word k) φ :=
            ⟨n, le_rfl, hnow⟩
          simpa [eventuallyDPA, hseen, hnow, Nat.lt_succ_iff] using hsuccLe
        · have hsucc : ¬ ∃ k : Nat, k < n + 1 ∧ Eval interp (word k) φ := by
            intro h
            rcases h with ⟨k, hk, hkEval⟩
            have hkle : k ≤ n := Nat.lt_succ_iff.mp hk
            rcases Nat.lt_or_eq_of_le hkle with hklt | hkeq
            · exact hseen ⟨k, hklt, hkEval⟩
            · exact hnow (by simpa [hkeq] using hkEval)
          have hsuccLe : ∀ k : Nat, k ≤ n -> ¬ Eval interp (word k) φ := by
            intro k hk hkEval
            exact hsucc ⟨k, Nat.lt_succ_iff.mpr hk, hkEval⟩
          simpa [eventuallyDPA, hseen, hnow, Nat.lt_succ_iff] using hsuccLe

theorem eventuallyDPA_accepts_iff_exists_eval {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP)
    (word : OmegaWord Letter) :
    (eventuallyDPA interp φ).Accepts word ↔
      ∃ n : Nat, Eval interp (word n) φ := by
  constructor
  · intro hacc
    by_contra hnever
    have hprio :
        ∀ k : Nat,
          (eventuallyDPA interp φ).priority
            ((eventuallyDPA interp φ).run word k) = 1 := by
      intro k
      rw [eventuallyDPA_run_eq]
      have hnone : ¬ ∃ i : Nat, i < k ∧ Eval interp (word i) φ := by
        intro h
        rcases h with ⟨i, _hi, hEval⟩
        exact hnever ⟨i, hEval⟩
      simp [eventuallyDPA, hnone]
    rcases hacc with ⟨p, hpEven, hpInf, _hpMin⟩
    have hp_eq_one : p = 1 := by
      rcases hpInf 0 with ⟨k, _hk, hkprio⟩
      exact hkprio.symm.trans (hprio k)
    rcases hpEven with ⟨m, hm⟩
    omega
  · intro h
    rcases h with ⟨n, hnEval⟩
    refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
    · intro m
      refine ⟨max m (n + 1), Nat.le_max_left m (n + 1), ?_⟩
      change
        (eventuallyDPA interp φ).priority
          ((eventuallyDPA interp φ).run word (max m (n + 1))) = 0
      rw [eventuallyDPA_run_eq]
      have hseen :
          ∃ k : Nat, (k < m ∨ k ≤ n) ∧ Eval interp (word k) φ :=
        ⟨n, Or.inr le_rfl, hnEval⟩
      simpa [eventuallyDPA, Nat.lt_succ_iff] using hseen
    · intro q _hq
      exact Nat.zero_le q

theorem eventuallyDPA_correct {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP)
    (word : OmegaWord Letter) :
    (eventuallyDPA interp φ).Accepts word ↔
      LTL.Satisfies interp word (LTL.eventually φ.toLTL) := by
  rw [eventuallyDPA_accepts_iff_exists_eval]
  constructor
  · intro h
    rcases h with ⟨n, hnEval⟩
    refine ⟨n, ?_, ?_⟩
    · exact (satisfies_toLTL interp (OmegaWord.drop word n) φ).mpr hnEval
    · intro k _hk
      trivial
  · intro h
    rcases h with ⟨n, hnSat, _hbefore⟩
    exact ⟨n, (satisfies_toLTL interp (OmegaWord.drop word n) φ).mp hnSat⟩

/--
Package the `eventually`-propositional DPA in the reusable
formula-compilation interface.
-/
noncomputable def eventuallyFormulaCompilation {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    LTLFormulaDPACompilation.{u, v, 0} interp (LTL.eventually φ.toLTL) where
  dpa := eventuallyDPA interp φ
  correct := eventuallyDPA_correct interp φ

/-- Compile `X◇φ` for propositional `φ`. -/
noncomputable def nextEventuallyFormulaCompilation {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    LTLFormulaDPACompilation.{u, v, 0} interp (LTL.next (LTL.eventually φ.toLTL)) :=
  (eventuallyFormulaCompilation interp φ).next

/--
Package the same construction as the explicit until formula `⊤ U φ`.
-/
noncomputable def untilVerumFormulaCompilation {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    LTLFormulaDPACompilation.{u, v, 0} interp (LTL.until LTL.verum φ.toLTL) where
  dpa := eventuallyDPA interp φ
  correct := by
    intro word
    simpa [LTL.eventually] using eventuallyDPA_correct interp φ word

/-!
## Propositional until

The monitor for `φ U ψ` has three states: pending, accepted, and rejected.
The pending state means every letter read so far satisfied `φ` and none
satisfied `ψ`; the accepted and rejected states are absorbing.
-/

/-- State of the deterministic monitor for propositional until. -/
abbrev UntilState := Option Bool

def untilPending {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (n : Nat) : Prop :=
  ∀ k : Nat, k < n -> ¬ Eval interp (word k) ψ ∧ Eval interp (word k) φ

def untilAccepted {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (n : Nat) : Prop :=
  ∃ j : Nat,
    j < n ∧
      Eval interp (word j) ψ ∧
        ∀ k : Nat, k < j -> ¬ Eval interp (word k) ψ ∧ Eval interp (word k) φ

def untilRejected {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (n : Nat) : Prop :=
  ∃ j : Nat,
    j < n ∧
      ¬ Eval interp (word j) ψ ∧
        ¬ Eval interp (word j) φ ∧
          ∀ k : Nat, k < j -> ¬ Eval interp (word k) ψ ∧ Eval interp (word k) φ

/-- DPA for `φ U ψ`, where both sides are propositional. -/
noncomputable def untilDPA {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP) :
    DetParityAutomaton Letter where
  State := UntilState
  stateFinite := inferInstance
  initial := none
  step state letter :=
    match state with
    | some true => some true
    | some false => some false
    | none =>
        if Eval interp letter ψ then
          some true
        else if Eval interp letter φ then
          none
        else
          some false
  priority state :=
    match state with
    | some true => 0
    | _ => 1

@[simp]
theorem untilDPA_priority_some_true {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP) :
    (untilDPA interp φ ψ).priority (some true) = 0 :=
  rfl

@[simp]
theorem untilDPA_priority_none {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP) :
    (untilDPA interp φ ψ).priority none = 1 :=
  rfl

@[simp]
theorem untilDPA_priority_some_false {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP) :
    (untilDPA interp φ ψ).priority (some false) = 1 :=
  rfl

theorem untilPending_succ_iff {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (n : Nat) :
    untilPending interp word φ ψ (n + 1) ↔
      untilPending interp word φ ψ n ∧
        ¬ Eval interp (word n) ψ ∧ Eval interp (word n) φ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro k hk
      exact h k (Nat.lt_trans hk (Nat.lt_succ_self n))
    · exact h n (Nat.lt_succ_self n)
  · intro h k hk
    rcases h with ⟨hpending, hnow⟩
    have hkle : k ≤ n := Nat.lt_succ_iff.mp hk
    rcases Nat.lt_or_eq_of_le hkle with hklt | hkeq
    · exact hpending k hklt
    · simpa [hkeq] using hnow

theorem untilAccepted_succ_iff {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (n : Nat) :
    untilAccepted interp word φ ψ (n + 1) ↔
      untilAccepted interp word φ ψ n ∨
        untilPending interp word φ ψ n ∧ Eval interp (word n) ψ := by
  constructor
  · intro h
    rcases h with ⟨j, hjlt, hjψ, hbefore⟩
    have hjle : j ≤ n := Nat.lt_succ_iff.mp hjlt
    rcases Nat.lt_or_eq_of_le hjle with hjlt_n | rfl
    · exact Or.inl ⟨j, hjlt_n, hjψ, hbefore⟩
    · exact Or.inr ⟨hbefore, hjψ⟩
  · intro h
    rcases h with ⟨j, hjlt, hjψ, hbefore⟩ | ⟨hpending, hnψ⟩
    · exact ⟨j, Nat.lt_trans hjlt (Nat.lt_succ_self n), hjψ, hbefore⟩
    · exact ⟨n, Nat.lt_succ_self n, hnψ, hpending⟩

theorem untilRejected_succ_iff {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (n : Nat) :
    untilRejected interp word φ ψ (n + 1) ↔
      untilRejected interp word φ ψ n ∨
        untilPending interp word φ ψ n ∧
          ¬ Eval interp (word n) ψ ∧ ¬ Eval interp (word n) φ := by
  constructor
  · intro h
    rcases h with ⟨j, hjlt, hjψ, hjφ, hbefore⟩
    have hjle : j ≤ n := Nat.lt_succ_iff.mp hjlt
    rcases Nat.lt_or_eq_of_le hjle with hjlt_n | rfl
    · exact Or.inl ⟨j, hjlt_n, hjψ, hjφ, hbefore⟩
    · exact Or.inr ⟨hbefore, hjψ, hjφ⟩
  · intro h
    rcases h with ⟨j, hjlt, hjψ, hjφ, hbefore⟩ | ⟨hpending, hnψ, hnφ⟩
    · exact ⟨j, Nat.lt_trans hjlt (Nat.lt_succ_self n), hjψ, hjφ, hbefore⟩
    · exact ⟨n, Nat.lt_succ_self n, hnψ, hnφ, hpending⟩

theorem untilDPA_run_classification {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP)
    (word : OmegaWord Letter)
    (n : Nat) :
    ((untilDPA interp φ ψ).run word n = none ↔
        untilPending interp word φ ψ n) ∧
      ((untilDPA interp φ ψ).run word n = some true ↔
        untilAccepted interp word φ ψ n) ∧
      ((untilDPA interp φ ψ).run word n = some false ↔
        untilRejected interp word φ ψ n) := by
  induction n with
  | zero =>
      simp [DetParityAutomaton.run, DetParityAutomaton.runFrom, untilDPA,
        untilPending, untilAccepted, untilRejected]
  | succ n ih =>
      rcases ih with ⟨ihPending, ihAccepted, ihRejected⟩
      constructor
      · constructor
        · intro h
          rw [DetParityAutomaton.run_succ] at h
          cases hstate : (untilDPA interp φ ψ).run word n with
          | none =>
              have hpending : untilPending interp word φ ψ n :=
                ihPending.mp hstate
              rw [hstate] at h
              by_cases hnψ : Eval interp (word n) ψ
              · simp [untilDPA, hnψ] at h
              · by_cases hnφ : Eval interp (word n) φ
                · exact (untilPending_succ_iff interp word φ ψ n).mpr
                    ⟨hpending, hnψ, hnφ⟩
                · simp [untilDPA, hnψ, hnφ] at h
          | some b =>
              cases b <;> rw [hstate] at h <;> simp [untilDPA] at h
        · intro hpendingSucc
          rw [DetParityAutomaton.run_succ]
          have hpending :=
            (untilPending_succ_iff interp word φ ψ n).mp hpendingSucc
          have hstate : (untilDPA interp φ ψ).run word n = none :=
            ihPending.mpr hpending.1
          rw [hstate]
          simp [untilDPA, hpending.2.1, hpending.2.2]
      · constructor
        · constructor
          · intro h
            rw [DetParityAutomaton.run_succ] at h
            cases hstate : (untilDPA interp φ ψ).run word n with
            | none =>
                have hpending : untilPending interp word φ ψ n :=
                  ihPending.mp hstate
                rw [hstate] at h
                by_cases hnψ : Eval interp (word n) ψ
                · exact (untilAccepted_succ_iff interp word φ ψ n).mpr
                    (Or.inr ⟨hpending, hnψ⟩)
                · simp [untilDPA, hnψ] at h
            | some b =>
                cases b
                · rw [hstate] at h
                  simp [untilDPA] at h
                · have haccepted : untilAccepted interp word φ ψ n :=
                    ihAccepted.mp hstate
                  exact (untilAccepted_succ_iff interp word φ ψ n).mpr
                    (Or.inl haccepted)
          · intro hacceptedSucc
            rw [DetParityAutomaton.run_succ]
            rcases (untilAccepted_succ_iff interp word φ ψ n).mp hacceptedSucc with
                haccepted | ⟨hpending, hnψ⟩
            · have hstate : (untilDPA interp φ ψ).run word n = some true :=
                ihAccepted.mpr haccepted
              rw [hstate]
              simp [untilDPA]
            · have hstate : (untilDPA interp φ ψ).run word n = none :=
                ihPending.mpr hpending
              rw [hstate]
              simp [untilDPA, hnψ]
        · constructor
          · intro h
            rw [DetParityAutomaton.run_succ] at h
            cases hstate : (untilDPA interp φ ψ).run word n with
            | none =>
                have hpending : untilPending interp word φ ψ n :=
                  ihPending.mp hstate
                rw [hstate] at h
                by_cases hnψ : Eval interp (word n) ψ
                · simp [untilDPA, hnψ] at h
                · by_cases hnφ : Eval interp (word n) φ
                  · simp [untilDPA, hnψ, hnφ] at h
                  · exact (untilRejected_succ_iff interp word φ ψ n).mpr
                      (Or.inr ⟨hpending, hnψ, hnφ⟩)
            | some b =>
                cases b
                · have hrejected : untilRejected interp word φ ψ n :=
                    ihRejected.mp hstate
                  exact (untilRejected_succ_iff interp word φ ψ n).mpr
                    (Or.inl hrejected)
                · rw [hstate] at h
                  simp [untilDPA] at h
          · intro hrejectedSucc
            rw [DetParityAutomaton.run_succ]
            rcases (untilRejected_succ_iff interp word φ ψ n).mp hrejectedSucc with
                hrejected | ⟨hpending, hnψ, hnφ⟩
            · have hstate : (untilDPA interp φ ψ).run word n = some false :=
                ihRejected.mpr hrejected
              rw [hstate]
              simp [untilDPA]
            · have hstate : (untilDPA interp φ ψ).run word n = none :=
                ihPending.mpr hpending
              rw [hstate]
              simp [untilDPA, hnψ, hnφ]

theorem untilDPA_run_none_iff {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP)
    (word : OmegaWord Letter)
    (n : Nat) :
    (untilDPA interp φ ψ).run word n = none ↔
      untilPending interp word φ ψ n :=
  (untilDPA_run_classification interp φ ψ word n).1

theorem untilDPA_run_some_true_iff {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP)
    (word : OmegaWord Letter)
    (n : Nat) :
    (untilDPA interp φ ψ).run word n = some true ↔
      untilAccepted interp word φ ψ n :=
  (untilDPA_run_classification interp φ ψ word n).2.1

theorem untilDPA_run_some_false_iff {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP)
    (word : OmegaWord Letter)
    (n : Nat) :
    (untilDPA interp φ ψ).run word n = some false ↔
      untilRejected interp word φ ψ n :=
  (untilDPA_run_classification interp φ ψ word n).2.2

theorem untilAccepted_forget {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (n : Nat)
    (h : untilAccepted interp word φ ψ n) :
    ∃ j : Nat,
      Eval interp (word j) ψ ∧
        ∀ k : Nat, k < j -> Eval interp (word k) φ := by
  rcases h with ⟨j, _hjlt, hjψ, hbefore⟩
  exact ⟨j, hjψ, fun k hk => (hbefore k hk).2⟩

theorem untilDPA_accepts_iff_until_eval {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP)
    (word : OmegaWord Letter) :
    (untilDPA interp φ ψ).Accepts word ↔
      ∃ n : Nat,
        Eval interp (word n) ψ ∧
          ∀ k : Nat, k < n -> Eval interp (word k) φ := by
  constructor
  · intro hacc
    by_contra hnone
    have hnotTrue :
        ∀ k : Nat, (untilDPA interp φ ψ).run word k ≠ some true := by
      intro k htrue
      have haccepted : untilAccepted interp word φ ψ k :=
        (untilDPA_run_some_true_iff interp φ ψ word k).mp htrue
      exact hnone (untilAccepted_forget interp word φ ψ k haccepted)
    have hprio :
        ∀ k : Nat,
          (untilDPA interp φ ψ).priority
            ((untilDPA interp φ ψ).run word k) = 1 := by
      intro k
      cases hstate : (untilDPA interp φ ψ).run word k with
      | none =>
          rfl
      | some b =>
          cases b
          · rfl
          · exact False.elim (hnotTrue k hstate)
    rcases hacc with ⟨p, hpEven, hpInf, _hpMin⟩
    have hp_eq_one : p = 1 := by
      rcases hpInf 0 with ⟨k, _hk, hkprio⟩
      exact hkprio.symm.trans (hprio k)
    rcases hpEven with ⟨m, hm⟩
    omega
  · intro h
    rcases until_first_witness interp word φ ψ h with ⟨n, hnψ, hbefore⟩
    refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
    · intro m
      refine ⟨max m (n + 1), Nat.le_max_left m (n + 1), ?_⟩
      change
        (untilDPA interp φ ψ).priority
          ((untilDPA interp φ ψ).run word (max m (n + 1))) = 0
      have hrun :
          (untilDPA interp φ ψ).run word (max m (n + 1)) = some true :=
        (untilDPA_run_some_true_iff interp φ ψ word (max m (n + 1))).mpr
          ⟨n, by omega, hnψ, fun k hk => ⟨(hbefore k hk).2, (hbefore k hk).1⟩⟩
      rw [hrun]
      rfl
    · intro q _hq
      exact Nat.zero_le q

theorem untilDPA_correct {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP)
    (word : OmegaWord Letter) :
    (untilDPA interp φ ψ).Accepts word ↔
      LTL.Satisfies interp word (LTL.until φ.toLTL ψ.toLTL) := by
  rw [untilDPA_accepts_iff_until_eval]
  exact (satisfies_until_toLTL interp word φ ψ).symm

/-- Package the propositional-`until` DPA in the reusable compiler interface. -/
noncomputable def untilFormulaCompilation {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP) :
    LTLFormulaDPACompilation.{u, v, 0} interp (LTL.until φ.toLTL ψ.toLTL) where
  dpa := untilDPA interp φ ψ
  correct := untilDPA_correct interp φ ψ

/-!
## Propositional release

For `φ R ψ`, pending is accepting: if `φ` never occurs but `ψ` holds forever,
the release formula is true.  A missing `ψ` before any earlier `φ` moves to a
rejecting sink.
-/

/-- State of the deterministic monitor for propositional release. -/
abbrev ReleaseState := Option Bool

def releasePending {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (n : Nat) : Prop :=
  ∀ k : Nat, k < n -> ¬ Eval interp (word k) φ ∧ Eval interp (word k) ψ

def releaseAccepted {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (n : Nat) : Prop :=
  ∃ j : Nat,
    j < n ∧
      Eval interp (word j) φ ∧
        Eval interp (word j) ψ ∧
          ∀ k : Nat, k < j -> ¬ Eval interp (word k) φ ∧ Eval interp (word k) ψ

def releaseRejected {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (n : Nat) : Prop :=
  ∃ j : Nat,
    j < n ∧
      ¬ Eval interp (word j) ψ ∧
        ∀ k : Nat, k < j -> ¬ Eval interp (word k) φ ∧ Eval interp (word k) ψ

/-- DPA for `φ R ψ`, where both sides are propositional. -/
noncomputable def releaseDPA {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP) :
    DetParityAutomaton Letter where
  State := ReleaseState
  stateFinite := inferInstance
  initial := none
  step state letter :=
    match state with
    | some true => some true
    | some false => some false
    | none =>
        if Eval interp letter ψ then
          if Eval interp letter φ then
            some true
          else
            none
        else
          some false
  priority state :=
    match state with
    | some false => 1
    | _ => 0

@[simp]
theorem releaseDPA_priority_some_true {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP) :
    (releaseDPA interp φ ψ).priority (some true) = 0 :=
  rfl

@[simp]
theorem releaseDPA_priority_none {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP) :
    (releaseDPA interp φ ψ).priority none = 0 :=
  rfl

@[simp]
theorem releaseDPA_priority_some_false {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP) :
    (releaseDPA interp φ ψ).priority (some false) = 1 :=
  rfl

theorem releasePending_succ_iff {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (n : Nat) :
    releasePending interp word φ ψ (n + 1) ↔
      releasePending interp word φ ψ n ∧
        ¬ Eval interp (word n) φ ∧ Eval interp (word n) ψ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro k hk
      exact h k (Nat.lt_trans hk (Nat.lt_succ_self n))
    · exact h n (Nat.lt_succ_self n)
  · intro h k hk
    rcases h with ⟨hpending, hnow⟩
    have hkle : k ≤ n := Nat.lt_succ_iff.mp hk
    rcases Nat.lt_or_eq_of_le hkle with hklt | hkeq
    · exact hpending k hklt
    · simpa [hkeq] using hnow

theorem releaseAccepted_succ_iff {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (n : Nat) :
    releaseAccepted interp word φ ψ (n + 1) ↔
      releaseAccepted interp word φ ψ n ∨
        releasePending interp word φ ψ n ∧
          Eval interp (word n) φ ∧ Eval interp (word n) ψ := by
  constructor
  · intro h
    rcases h with ⟨j, hjlt, hjφ, hjψ, hbefore⟩
    have hjle : j ≤ n := Nat.lt_succ_iff.mp hjlt
    rcases Nat.lt_or_eq_of_le hjle with hjlt_n | rfl
    · exact Or.inl ⟨j, hjlt_n, hjφ, hjψ, hbefore⟩
    · exact Or.inr ⟨hbefore, hjφ, hjψ⟩
  · intro h
    rcases h with ⟨j, hjlt, hjφ, hjψ, hbefore⟩ | ⟨hpending, hnφ, hnψ⟩
    · exact ⟨j, Nat.lt_trans hjlt (Nat.lt_succ_self n), hjφ, hjψ, hbefore⟩
    · exact ⟨n, Nat.lt_succ_self n, hnφ, hnψ, hpending⟩

theorem releaseRejected_succ_iff {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (n : Nat) :
    releaseRejected interp word φ ψ (n + 1) ↔
      releaseRejected interp word φ ψ n ∨
        releasePending interp word φ ψ n ∧ ¬ Eval interp (word n) ψ := by
  constructor
  · intro h
    rcases h with ⟨j, hjlt, hjψ, hbefore⟩
    have hjle : j ≤ n := Nat.lt_succ_iff.mp hjlt
    rcases Nat.lt_or_eq_of_le hjle with hjlt_n | rfl
    · exact Or.inl ⟨j, hjlt_n, hjψ, hbefore⟩
    · exact Or.inr ⟨hbefore, hjψ⟩
  · intro h
    rcases h with ⟨j, hjlt, hjψ, hbefore⟩ | ⟨hpending, hnψ⟩
    · exact ⟨j, Nat.lt_trans hjlt (Nat.lt_succ_self n), hjψ, hbefore⟩
    · exact ⟨n, Nat.lt_succ_self n, hnψ, hpending⟩

theorem releaseDPA_run_classification {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP)
    (word : OmegaWord Letter)
    (n : Nat) :
    ((releaseDPA interp φ ψ).run word n = none ↔
        releasePending interp word φ ψ n) ∧
      ((releaseDPA interp φ ψ).run word n = some true ↔
        releaseAccepted interp word φ ψ n) ∧
      ((releaseDPA interp φ ψ).run word n = some false ↔
        releaseRejected interp word φ ψ n) := by
  induction n with
  | zero =>
      simp [DetParityAutomaton.run, DetParityAutomaton.runFrom, releaseDPA,
        releasePending, releaseAccepted, releaseRejected]
  | succ n ih =>
      rcases ih with ⟨ihPending, ihAccepted, ihRejected⟩
      constructor
      · constructor
        · intro h
          rw [DetParityAutomaton.run_succ] at h
          cases hstate : (releaseDPA interp φ ψ).run word n with
          | none =>
              have hpending : releasePending interp word φ ψ n :=
                ihPending.mp hstate
              rw [hstate] at h
              by_cases hnψ : Eval interp (word n) ψ
              · by_cases hnφ : Eval interp (word n) φ
                · simp [releaseDPA, hnψ, hnφ] at h
                · exact (releasePending_succ_iff interp word φ ψ n).mpr
                    ⟨hpending, hnφ, hnψ⟩
              · simp [releaseDPA, hnψ] at h
          | some b =>
              cases b <;> rw [hstate] at h <;> simp [releaseDPA] at h
        · intro hpendingSucc
          rw [DetParityAutomaton.run_succ]
          have hpending :=
            (releasePending_succ_iff interp word φ ψ n).mp hpendingSucc
          have hstate : (releaseDPA interp φ ψ).run word n = none :=
            ihPending.mpr hpending.1
          rw [hstate]
          simp [releaseDPA, hpending.2.2, hpending.2.1]
      · constructor
        · constructor
          · intro h
            rw [DetParityAutomaton.run_succ] at h
            cases hstate : (releaseDPA interp φ ψ).run word n with
            | none =>
                have hpending : releasePending interp word φ ψ n :=
                  ihPending.mp hstate
                rw [hstate] at h
                by_cases hnψ : Eval interp (word n) ψ
                · by_cases hnφ : Eval interp (word n) φ
                  · exact (releaseAccepted_succ_iff interp word φ ψ n).mpr
                      (Or.inr ⟨hpending, hnφ, hnψ⟩)
                  · simp [releaseDPA, hnψ, hnφ] at h
                · simp [releaseDPA, hnψ] at h
            | some b =>
                cases b
                · rw [hstate] at h
                  simp [releaseDPA] at h
                · have haccepted : releaseAccepted interp word φ ψ n :=
                    ihAccepted.mp hstate
                  exact (releaseAccepted_succ_iff interp word φ ψ n).mpr
                    (Or.inl haccepted)
          · intro hacceptedSucc
            rw [DetParityAutomaton.run_succ]
            rcases (releaseAccepted_succ_iff interp word φ ψ n).mp hacceptedSucc with
                haccepted | ⟨hpending, hnφ, hnψ⟩
            · have hstate : (releaseDPA interp φ ψ).run word n = some true :=
                ihAccepted.mpr haccepted
              rw [hstate]
              simp [releaseDPA]
            · have hstate : (releaseDPA interp φ ψ).run word n = none :=
                ihPending.mpr hpending
              rw [hstate]
              simp [releaseDPA, hnψ, hnφ]
        · constructor
          · intro h
            rw [DetParityAutomaton.run_succ] at h
            cases hstate : (releaseDPA interp φ ψ).run word n with
            | none =>
                have hpending : releasePending interp word φ ψ n :=
                  ihPending.mp hstate
                rw [hstate] at h
                by_cases hnψ : Eval interp (word n) ψ
                · simp [releaseDPA, hnψ] at h
                · exact (releaseRejected_succ_iff interp word φ ψ n).mpr
                    (Or.inr ⟨hpending, hnψ⟩)
            | some b =>
                cases b
                · have hrejected : releaseRejected interp word φ ψ n :=
                    ihRejected.mp hstate
                  exact (releaseRejected_succ_iff interp word φ ψ n).mpr
                    (Or.inl hrejected)
                · rw [hstate] at h
                  simp [releaseDPA] at h
          · intro hrejectedSucc
            rw [DetParityAutomaton.run_succ]
            rcases (releaseRejected_succ_iff interp word φ ψ n).mp hrejectedSucc with
                hrejected | ⟨hpending, hnψ⟩
            · have hstate : (releaseDPA interp φ ψ).run word n = some false :=
                ihRejected.mpr hrejected
              rw [hstate]
              simp [releaseDPA]
            · have hstate : (releaseDPA interp φ ψ).run word n = none :=
                ihPending.mpr hpending
              rw [hstate]
              simp [releaseDPA, hnψ]

theorem releaseDPA_run_none_iff {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP)
    (word : OmegaWord Letter)
    (n : Nat) :
    (releaseDPA interp φ ψ).run word n = none ↔
      releasePending interp word φ ψ n :=
  (releaseDPA_run_classification interp φ ψ word n).1

theorem releaseDPA_run_some_true_iff {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP)
    (word : OmegaWord Letter)
    (n : Nat) :
    (releaseDPA interp φ ψ).run word n = some true ↔
      releaseAccepted interp word φ ψ n :=
  (releaseDPA_run_classification interp φ ψ word n).2.1

theorem releaseDPA_run_some_false_iff {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP)
    (word : OmegaWord Letter)
    (n : Nat) :
    (releaseDPA interp φ ψ).run word n = some false ↔
      releaseRejected interp word φ ψ n :=
  (releaseDPA_run_classification interp φ ψ word n).2.2

theorem releaseRejected_forget {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (n : Nat)
    (h : releaseRejected interp word φ ψ n) :
    ∃ j : Nat,
      ¬ Eval interp (word j) ψ ∧
        ∀ k : Nat, k < j -> ¬ Eval interp (word k) φ := by
  rcases h with ⟨j, _hjlt, hjψ, hbefore⟩
  exact ⟨j, hjψ, fun k hk => (hbefore k hk).1⟩

theorem release_violation_first {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : Propositional AP)
    (h :
      ∃ n : Nat,
        ¬ Eval interp (word n) ψ ∧
          ∀ k : Nat, k < n -> ¬ Eval interp (word k) φ) :
    ∃ n : Nat,
      ¬ Eval interp (word n) ψ ∧
        ∀ k : Nat, k < n -> ¬ Eval interp (word k) φ ∧ Eval interp (word k) ψ := by
  classical
  let bad : Nat -> Prop :=
    fun n => ¬ Eval interp (word n) ψ ∧
      ∀ k : Nat, k < n -> ¬ Eval interp (word k) φ
  have hbad : ∃ n : Nat, bad n := h
  refine ⟨Nat.find hbad, (Nat.find_spec hbad).1, ?_⟩
  intro k hk
  constructor
  · exact (Nat.find_spec hbad).2 k hk
  · by_contra hkψ
    have hkbad : bad k := by
      refine ⟨hkψ, ?_⟩
      intro r hr
      exact (Nat.find_spec hbad).2 r (Nat.lt_trans hr hk)
    exact Nat.find_min hbad hk hkbad

theorem releaseDPA_accepts_iff_release_eval {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP)
    (word : OmegaWord Letter) :
    (releaseDPA interp φ ψ).Accepts word ↔
      ∀ n : Nat,
        Eval interp (word n) ψ ∨
          ∃ k : Nat, k < n ∧ Eval interp (word k) φ := by
  constructor
  · intro hacc n
    by_contra hbadAtN
    have hnψ : ¬ Eval interp (word n) ψ := by
      intro hnψ
      exact hbadAtN (Or.inl hnψ)
    have hnoφ : ∀ k : Nat, k < n -> ¬ Eval interp (word k) φ := by
      intro k hk hkφ
      exact hbadAtN (Or.inr ⟨k, hk, hkφ⟩)
    rcases release_violation_first interp word φ ψ ⟨n, hnψ, hnoφ⟩ with
      ⟨j, hjψ, hbefore⟩
    have hrun :
        (releaseDPA interp φ ψ).run word (j + 1) = some false :=
      (releaseDPA_run_some_false_iff interp φ ψ word (j + 1)).mpr
        ⟨j, Nat.lt_succ_self j, hjψ, hbefore⟩
    have hprio :
        ∀ k : Nat,
          j + 1 ≤ k ->
            (releaseDPA interp φ ψ).priority
              ((releaseDPA interp φ ψ).run word k) = 1 := by
      intro k hk
      have hrej : releaseRejected interp word φ ψ k :=
        ⟨j, hk, hjψ, hbefore⟩
      have hstate : (releaseDPA interp φ ψ).run word k = some false :=
        (releaseDPA_run_some_false_iff interp φ ψ word k).mpr hrej
      rw [hstate]
      rfl
    rcases hacc with ⟨p, hpEven, hpInf, _hpMin⟩
    have hp_eq_one : p = 1 := by
      rcases hpInf (j + 1) with ⟨k, hk, hkprio⟩
      exact hkprio.symm.trans (hprio k hk)
    rcases hpEven with ⟨m, hm⟩
    omega
  · intro hrel
    have hnotRejected :
        ∀ k : Nat, (releaseDPA interp φ ψ).run word k ≠ some false := by
      intro k hfalse
      have hrejected : releaseRejected interp word φ ψ k :=
        (releaseDPA_run_some_false_iff interp φ ψ word k).mp hfalse
      rcases releaseRejected_forget interp word φ ψ k hrejected with
        ⟨j, hjψ, hbefore⟩
      rcases hrel j with hjrel | ⟨r, hrlt, hrφ⟩
      · exact hjψ hjrel
      · exact (hbefore r hrlt) hrφ
    refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
    · intro n
      refine ⟨n, le_rfl, ?_⟩
      change
        (releaseDPA interp φ ψ).priority
          ((releaseDPA interp φ ψ).run word n) = 0
      cases hstate : (releaseDPA interp φ ψ).run word n with
      | none =>
          rfl
      | some b =>
          cases b
          · exact False.elim (hnotRejected n hstate)
          · rfl
    · intro q _hq
      exact Nat.zero_le q

theorem releaseDPA_correct {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP)
    (word : OmegaWord Letter) :
    (releaseDPA interp φ ψ).Accepts word ↔
      LTL.Satisfies interp word (LTL.release φ.toLTL ψ.toLTL) := by
  rw [releaseDPA_accepts_iff_release_eval]
  exact (satisfies_release_toLTL interp word φ ψ).symm

/-- Package the propositional-`release` DPA in the reusable compiler interface. -/
noncomputable def releaseFormulaCompilation {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ ψ : Propositional AP) :
    LTLFormulaDPACompilation.{u, v, 0} interp (LTL.release φ.toLTL ψ.toLTL) where
  dpa := releaseDPA interp φ ψ
  correct := releaseDPA_correct interp φ ψ

/-!
## Always propositional

The dual one-state-memory monitor recognizes `□φ`, where `φ` is
propositional: the state records whether all letters seen so far satisfy the
guard.
-/

/-- DPA for `always φ`, where `φ` is propositional. -/
noncomputable def alwaysDPA {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    DetParityAutomaton Letter where
  State := Bool
  stateFinite := inferInstance
  initial := true
  step good letter := good && decide (Eval interp letter φ)
  priority good :=
    if good then
      0
    else
      1

@[simp]
theorem alwaysDPA_priority_true {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    (alwaysDPA interp φ).priority true = 0 :=
  rfl

@[simp]
theorem alwaysDPA_priority_false {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    (alwaysDPA interp φ).priority false = 1 :=
  rfl

@[simp]
theorem alwaysDPA_run_eq {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP)
    (word : OmegaWord Letter)
    (n : Nat) :
    (alwaysDPA interp φ).run word n =
      decide (∀ k : Nat, k < n -> Eval interp (word k) φ) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [DetParityAutomaton.run_succ, ih]
      by_cases hall : ∀ k : Nat, k < n -> Eval interp (word k) φ
      · by_cases hnow : Eval interp (word n) φ
        · have hsucc : ∀ k : Nat, k < n + 1 -> Eval interp (word k) φ := by
            intro k hk
            have hkle : k ≤ n := Nat.lt_succ_iff.mp hk
            rcases Nat.lt_or_eq_of_le hkle with hklt | hkeq
            · exact hall k hklt
            · simpa [hkeq] using hnow
          have hiff :
              (∀ k : Nat, k < n -> Eval interp (word k) φ) ↔
                ∀ k : Nat, k ≤ n -> Eval interp (word k) φ := by
            constructor
            · intro _ k hk
              exact hsucc k (Nat.lt_succ_iff.mpr hk)
            · intro h k hk
              exact h k (Nat.le_of_lt hk)
          simpa [alwaysDPA, hall, hnow, Nat.lt_succ_iff] using hiff
        · have hsucc : ¬ ∀ k : Nat, k < n + 1 -> Eval interp (word k) φ := by
            intro h
            exact hnow (h n (Nat.lt_succ_self n))
          simpa [alwaysDPA, hall, hnow, Nat.lt_succ_iff] using hsucc
      · have hsucc : ¬ ∀ k : Nat, k < n + 1 -> Eval interp (word k) φ := by
          intro h
          exact hall (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self n)))
        have hsuccLe : ¬ ∀ k : Nat, k ≤ n -> Eval interp (word k) φ := by
          intro h
          exact hall (fun k hk => h k (Nat.le_of_lt hk))
        simpa [alwaysDPA, hall, Nat.lt_succ_iff] using hsuccLe

theorem alwaysDPA_accepts_iff_forall_eval {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP)
    (word : OmegaWord Letter) :
    (alwaysDPA interp φ).Accepts word ↔
      ∀ n : Nat, Eval interp (word n) φ := by
  constructor
  · intro hacc n
    by_contra hbad
    have hprio :
        ∀ k : Nat,
          n + 1 ≤ k ->
            (alwaysDPA interp φ).priority
              ((alwaysDPA interp φ).run word k) = 1 := by
      intro k hk
      rw [alwaysDPA_run_eq]
      have hnotAll : ¬ ∀ i : Nat, i < k -> Eval interp (word i) φ := by
        intro hall
        exact hbad (hall n (by omega))
      simp [alwaysDPA, hnotAll]
    rcases hacc with ⟨p, hpEven, hpInf, _hpMin⟩
    have hp_eq_one : p = 1 := by
      rcases hpInf (n + 1) with ⟨k, hk, hkprio⟩
      exact hkprio.symm.trans (hprio k hk)
    rcases hpEven with ⟨m, hm⟩
    omega
  · intro hall
    refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
    · intro n
      refine ⟨n, le_rfl, ?_⟩
      change
        (alwaysDPA interp φ).priority
          ((alwaysDPA interp φ).run word n) = 0
      rw [alwaysDPA_run_eq]
      have hprefix : ∀ k : Nat, k < n -> Eval interp (word k) φ := by
        intro k _hk
        exact hall k
      simpa [alwaysDPA] using hprefix
    · intro q _hq
      exact Nat.zero_le q

theorem alwaysDPA_correct {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP)
    (word : OmegaWord Letter) :
    (alwaysDPA interp φ).Accepts word ↔
      LTL.Satisfies interp word (LTL.always φ.toLTL) := by
  rw [alwaysDPA_accepts_iff_forall_eval]
  rw [LTL.satisfies_always]
  constructor
  · intro h n
    exact (satisfies_toLTL interp (OmegaWord.drop word n) φ).mpr (h n)
  · intro h n
    exact (satisfies_toLTL interp (OmegaWord.drop word n) φ).mp (h n)

/--
Package the `always`-propositional DPA in the reusable formula-compilation
interface.
-/
noncomputable def alwaysFormulaCompilation {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    LTLFormulaDPACompilation.{u, v, 0} interp (LTL.always φ.toLTL) where
  dpa := alwaysDPA interp φ
  correct := alwaysDPA_correct interp φ

/-- Compile `X□φ` for propositional `φ`. -/
noncomputable def nextAlwaysFormulaCompilation {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    LTLFormulaDPACompilation.{u, v, 0} interp (LTL.next (LTL.always φ.toLTL)) :=
  (alwaysFormulaCompilation interp φ).next

/--
Package the same construction as the explicit release formula `⊥ R φ`.
-/
noncomputable def releaseFalsumFormulaCompilation {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (φ : Propositional AP) :
    LTLFormulaDPACompilation.{u, v, 0} interp (LTL.release LTL.falsum φ.toLTL) where
  dpa := alwaysDPA interp φ
  correct := by
    intro word
    simpa [LTL.always] using alwaysDPA_correct interp φ word

end Propositional

end LTL

end DistributedSynthesis
