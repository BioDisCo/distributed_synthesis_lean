/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Copyright Dominique Larchey-Wendling (LORIA -- CNRS).
Lean adaptation of MMA.v by Dominique Larchey-Wendling, from the Coq library
of undecidability proofs, revision 11c41e0637f0c5219ad1c4c92d11609b7e072c31.
See README.md and LICENSE-MPL-2.0 in this directory.
-/
import Mathlib.Tactic
import Mathlib.Computability.Primrec.List

/-! # Alternate Minsky machines with finitely many registers

This is the upstream MMA instruction convention: decrement jumps on a positive
counter and falls through on zero. It must not be confused with upstream MM,
whose decrement branches the other way. Lean represents a register vector as
`Fin n → Nat`, and an instruction as a register plus an optional jump target:
`none` means increment, `some j` means conditional decrement.
-/
namespace DistributedSynthesis.CounterMachine.MMA

abbrev Instr (n : Nat) := Fin n × Option Nat
abbrev Program (n : Nat) := List (Instr n)
abbrev Registers (n : Nat) := Fin n → Nat
abbrev Cfg (n : Nat) := Nat × Registers n
abbrev HaltingInput (n : Nat) := Program n × Registers n

def lookup {n : Nat} (P : Program n) (i : Nat) : Option (Instr n) :=
  if i = 0 then none else P[i-1]?

def next {n : Nat} (ρ : Instr n) (x : Cfg n) : Cfg n :=
  match ρ.2 with
  | none => (x.1+1, Function.update x.2 ρ.1 (x.2 ρ.1+1))
  | some j => if x.2 ρ.1 = 0 then (x.1+1, x.2)
      else (j, Function.update x.2 ρ.1 (x.2 ρ.1-1))

def Step {n : Nat} (P : Program n) (x y : Cfg n) : Prop :=
  ∃ ρ, lookup P x.1 = some ρ ∧ y = next ρ x
abbrev Reaches {n : Nat} (P : Program n) := Relation.ReflTransGen (Step P)
def Stops {n : Nat} (P : Program n) (x : Cfg n) : Prop := ∀ y, ¬ Step P x y
def Terminates {n : Nat} (P : Program n) (x : Cfg n) : Prop :=
  ∃ y, Reaches P x y ∧ Stops P y
def Halts {n : Nat} (d : HaltingInput n) : Prop := Terminates d.1 (1,d.2)

theorem next_inc {n : Nat} (r : Fin n) (i : Nat) (v : Registers n) :
    next (r,none) (i,v) = (i+1, Function.update v r (v r+1)) := rfl

theorem next_dec_zero {n : Nat} (r : Fin n) (i j : Nat) (v : Registers n)
    (h : v r = 0) : next (r,some j) (i,v) = (i+1,v) := by simp [next,h]

theorem next_dec_pos {n : Nat} (r : Fin n) (i j k : Nat) (v : Registers n)
    (h : v r = k+1) : next (r,some j) (i,v) = (j,Function.update v r k) := by
  simp [next,h]

theorem stops_iff {n : Nat} (P : Program n) (x : Cfg n) :
    Stops P x ↔ lookup P x.1 = none := by
  cases h : lookup P x.1 with
  | none => simp [Stops, Step, h]
  | some ρ =>
    constructor
    · intro hs; exact False.elim (hs _ ⟨ρ,h,rfl⟩)
    · intro hh; cases hh

end DistributedSynthesis.CounterMachine.MMA
