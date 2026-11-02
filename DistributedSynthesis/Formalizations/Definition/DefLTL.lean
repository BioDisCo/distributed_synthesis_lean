/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Data.List.Basic
import DistributedSynthesis.Basic

/-!
# Linear-time temporal logic

This file gives a reusable syntax and semantics for LTL over an abstract
set of atomic propositions.  The interpretation of atoms is intentionally
parametric in the letter type, so graph-dependent specifications can use
letters such as round records and let atoms inspect their graph component.
-/

namespace DistributedSynthesis

universe u v

/-- Infinite words over an alphabet. -/
abbrev OmegaWord (Letter : Type u) := Nat -> Letter

/-- Drop the first `n` letters of an infinite word. -/
def OmegaWord.drop {Letter : Type u} (word : OmegaWord Letter) (n : Nat) :
    OmegaWord Letter :=
  fun k => word (n + k)

/-- Map every letter of an infinite word. -/
def OmegaWord.map {Letter : Type u} {Letter' : Type v}
    (f : Letter -> Letter')
    (word : OmegaWord Letter) :
    OmegaWord Letter' :=
  fun n => f (word n)

@[simp]
theorem OmegaWord.drop_zero {Letter : Type u} (word : OmegaWord Letter) :
    OmegaWord.drop word 0 = word := by
  funext k
  simp [OmegaWord.drop]

@[simp]
theorem OmegaWord.drop_apply {Letter : Type u} (word : OmegaWord Letter)
    (n k : Nat) :
    OmegaWord.drop word n k = word (n + k) :=
  rfl

@[simp]
theorem OmegaWord.drop_drop {Letter : Type u} (word : OmegaWord Letter)
    (n k : Nat) :
    OmegaWord.drop (OmegaWord.drop word n) k = OmegaWord.drop word (n + k) := by
  funext i
  simp [OmegaWord.drop, Nat.add_assoc]

@[simp]
theorem OmegaWord.map_apply {Letter : Type u} {Letter' : Type v}
    (f : Letter -> Letter')
    (word : OmegaWord Letter)
    (n : Nat) :
    OmegaWord.map f word n = f (word n) :=
  rfl

@[simp]
theorem OmegaWord.map_drop {Letter : Type u} {Letter' : Type v}
    (f : Letter -> Letter')
    (word : OmegaWord Letter)
    (n : Nat) :
    OmegaWord.map f (OmegaWord.drop word n) =
      OmegaWord.drop (OmegaWord.map f word) n := by
  funext k
  rfl

/-- Linear-time temporal formulas over atomic propositions `AP`. -/
inductive LTL (AP : Type u) : Type u where
  | verum : LTL AP
  | falsum : LTL AP
  | atom : AP -> LTL AP
  | neg : LTL AP -> LTL AP
  | conj : LTL AP -> LTL AP -> LTL AP
  | disj : LTL AP -> LTL AP -> LTL AP
  | next : LTL AP -> LTL AP
  | until : LTL AP -> LTL AP -> LTL AP
  | release : LTL AP -> LTL AP -> LTL AP
deriving Repr, DecidableEq

namespace LTL

/-- Number of constructors in an LTL formula. -/
def size {AP : Type u} : LTL AP -> Nat
  | verum => 1
  | falsum => 1
  | atom _ => 1
  | neg φ => φ.size + 1
  | conj φ ψ => φ.size + ψ.size + 1
  | disj φ ψ => φ.size + ψ.size + 1
  | next φ => φ.size + 1
  | LTL.until φ ψ => φ.size + ψ.size + 1
  | LTL.release φ ψ => φ.size + ψ.size + 1

/-- Immediate and nested subformulas, including the formula itself. -/
def subformulas {AP : Type u} : LTL AP -> List (LTL AP)
  | verum => [verum]
  | falsum => [falsum]
  | atom ap => [atom ap]
  | neg φ => neg φ :: φ.subformulas
  | conj φ ψ => conj φ ψ :: (φ.subformulas ++ ψ.subformulas)
  | disj φ ψ => disj φ ψ :: (φ.subformulas ++ ψ.subformulas)
  | next φ => next φ :: φ.subformulas
  | LTL.until φ ψ => LTL.until φ ψ :: (φ.subformulas ++ ψ.subformulas)
  | LTL.release φ ψ => LTL.release φ ψ :: (φ.subformulas ++ ψ.subformulas)

@[simp]
theorem mem_subformulas_self {AP : Type u} (φ : LTL AP) :
    φ ∈ φ.subformulas := by
  cases φ <;> simp [subformulas]

/-- Atomic propositions occurring in a formula, with duplicates permitted. -/
def atoms {AP : Type u} : LTL AP -> List AP
  | verum => []
  | falsum => []
  | atom ap => [ap]
  | neg φ => φ.atoms
  | conj φ ψ => φ.atoms ++ ψ.atoms
  | disj φ ψ => φ.atoms ++ ψ.atoms
  | next φ => φ.atoms
  | LTL.until φ ψ => φ.atoms ++ ψ.atoms
  | LTL.release φ ψ => φ.atoms ++ ψ.atoms

/-- Relabel atomic propositions in a formula. -/
def map {AP : Type u} {AP' : Type v} (f : AP -> AP') : LTL AP -> LTL AP'
  | verum => verum
  | falsum => falsum
  | atom ap => atom (f ap)
  | neg φ => neg (φ.map f)
  | conj φ ψ => conj (φ.map f) (ψ.map f)
  | disj φ ψ => disj (φ.map f) (ψ.map f)
  | next φ => next (φ.map f)
  | LTL.until φ ψ => LTL.until (φ.map f) (ψ.map f)
  | LTL.release φ ψ => LTL.release (φ.map f) (ψ.map f)

/-- Eventually `φ`. -/
def eventually {AP : Type u} (φ : LTL AP) : LTL AP :=
  LTL.until verum φ

/-- Always `φ`. -/
def always {AP : Type u} (φ : LTL AP) : LTL AP :=
  LTL.release falsum φ

/-- Semantic satisfaction of an LTL formula on an infinite word. -/
def Satisfies {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter) :
    LTL AP -> Prop
  | verum => True
  | falsum => False
  | atom ap => interp ap (word 0)
  | neg φ => ¬ Satisfies interp word φ
  | conj φ ψ => Satisfies interp word φ ∧ Satisfies interp word ψ
  | disj φ ψ => Satisfies interp word φ ∨ Satisfies interp word ψ
  | next φ => Satisfies interp (OmegaWord.drop word 1) φ
  | LTL.until φ ψ =>
      ∃ n : Nat,
        Satisfies interp (OmegaWord.drop word n) ψ ∧
          ∀ k : Nat, k < n -> Satisfies interp (OmegaWord.drop word k) φ
  | LTL.release φ ψ =>
      ∀ n : Nat,
        Satisfies interp (OmegaWord.drop word n) ψ ∨
          ∃ k : Nat, k < n ∧ Satisfies interp (OmegaWord.drop word k) φ

/-- A formula denotes the language of words satisfying it. -/
def Language {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (φ : LTL AP) :
    Set (OmegaWord Letter) :=
  { word | Satisfies interp word φ }

@[simp]
theorem satisfies_map {AP : Type u} {AP' : Type v} {Letter : Type w}
    (interp : AP' -> Letter -> Prop)
    (f : AP -> AP')
    (word : OmegaWord Letter)
    (φ : LTL AP) :
    Satisfies interp word (φ.map f) ↔
      Satisfies (fun ap letter => interp (f ap) letter) word φ := by
  induction φ generalizing word with
  | verum => simp [map, Satisfies]
  | falsum => simp [map, Satisfies]
  | atom ap => simp [map, Satisfies]
  | neg φ ih => simp [map, Satisfies, ih]
  | conj φ ψ ihφ ihψ => simp [map, Satisfies, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [map, Satisfies, ihφ, ihψ]
  | next φ ih => simp [map, Satisfies, ih]
  | «until» φ ψ ihφ ihψ =>
      simp [map, Satisfies, ihφ, ihψ]
  | «release» φ ψ ihφ ihψ =>
      simp [map, Satisfies, ihφ, ihψ]

@[simp]
theorem satisfies_word_map {AP : Type u} {Letter : Type v} {Letter' : Type w}
    (interp : AP -> Letter' -> Prop)
    (f : Letter -> Letter')
    (word : OmegaWord Letter)
    (φ : LTL AP) :
    Satisfies interp (OmegaWord.map f word) φ ↔
      Satisfies (fun ap letter => interp ap (f letter)) word φ := by
  induction φ generalizing word with
  | verum => simp [Satisfies]
  | falsum => simp [Satisfies]
  | atom ap => simp [Satisfies]
  | neg φ ih => simp [Satisfies, ih]
  | conj φ ψ ihφ ihψ => simp [Satisfies, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [Satisfies, ihφ, ihψ]
  | next φ ih =>
      rw [Satisfies, Satisfies, ← OmegaWord.map_drop]
      exact ih (OmegaWord.drop word 1)
  | «until» φ ψ ihφ ihψ =>
      constructor
      · intro h
        rcases h with ⟨n, hψ, hφ⟩
        refine ⟨n, ?_, ?_⟩
        · rw [← ihψ (OmegaWord.drop word n)]
          simpa [OmegaWord.map_drop] using hψ
        · intro k hk
          rw [← ihφ (OmegaWord.drop word k)]
          simpa [OmegaWord.map_drop] using hφ k hk
      · intro h
        rcases h with ⟨n, hψ, hφ⟩
        refine ⟨n, ?_, ?_⟩
        · simpa [OmegaWord.map_drop] using
            (ihψ (OmegaWord.drop word n)).mpr hψ
        · intro k hk
          simpa [OmegaWord.map_drop] using
            (ihφ (OmegaWord.drop word k)).mpr (hφ k hk)
  | «release» φ ψ ihφ ihψ =>
      constructor
      · intro h n
        rcases h n with hψ | hφ
        · left
          rw [← ihψ (OmegaWord.drop word n)]
          simpa [OmegaWord.map_drop] using hψ
        · right
          rcases hφ with ⟨k, hk, hφk⟩
          refine ⟨k, hk, ?_⟩
          rw [← ihφ (OmegaWord.drop word k)]
          simpa [OmegaWord.map_drop] using hφk
      · intro h n
        rcases h n with hψ | hφ
        · left
          simpa [OmegaWord.map_drop] using
            (ihψ (OmegaWord.drop word n)).mpr hψ
        · right
          rcases hφ with ⟨k, hk, hφk⟩
          refine ⟨k, hk, ?_⟩
          simpa [OmegaWord.map_drop] using
            (ihφ (OmegaWord.drop word k)).mpr hφk

@[simp]
theorem satisfies_eventually {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ : LTL AP) :
    Satisfies interp word (eventually φ) ↔
      ∃ n : Nat, Satisfies interp (OmegaWord.drop word n) φ := by
  simp [eventually, Satisfies]

@[simp]
theorem satisfies_always {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ : LTL AP) :
    Satisfies interp word (always φ) ↔
      ∀ n : Nat, Satisfies interp (OmegaWord.drop word n) φ := by
  constructor
  · intro h n
    rcases h n with hφ | hbad
    · exact hφ
    · rcases hbad with ⟨k, hk, hfalse⟩
      exact False.elim hfalse
  · intro h n
    exact Or.inl (h n)

end LTL

end DistributedSynthesis
