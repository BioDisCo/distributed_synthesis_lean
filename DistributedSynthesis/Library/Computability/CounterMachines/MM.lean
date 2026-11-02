/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Copyright Dominique Larchey-Wendling (LORIA -- CNRS).
Lean adaptation of MM.v, Coq library of undecidability proofs,
revision 11c41e0637f0c5219ad1c4c92d11609b7e072c31.
See README.md, upstream/MM.v, and LICENSE-MPL-2.0.
-/
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.StateTransition

/-! # MM register machines: jump on zero

Unlike MMA, DEC jumps on zero and falls through after decrementing a positive
register. The model retains arbitrary code base addresses; the halting problem
starts at base one. Instructions and vectors have explicit Mathlib encodings.
-/
namespace DistributedSynthesis.CounterMachine.MM

abbrev Instr (n : Nat) := Fin n × Option Nat
abbrev Program (n : Nat) := List (Instr n)
abbrev Registers (n : Nat) := Fin n → Nat
abbrev Cfg (n : Nat) := Nat × Registers n
abbrev HaltingInput (n : Nat) := Program n × Registers n

def inc {n : Nat} (r : Fin n) : Instr n := (r,none)
def dec {n : Nat} (r : Fin n) (j : Nat) : Instr n := (r,some j)

def lookup {n : Nat} (P : Program n) (base pc : Nat) : Option (Instr n) :=
  if base ≤ pc then P[pc-base]? else none

theorem lookup_eq_none {n : Nat} (P : Program n) (base pc : Nat) :
    lookup P base pc = none ↔ pc < base ∨ base + P.length ≤ pc := by
  by_cases h : base ≤ pc
  · simp only [lookup,if_pos h,List.getElem?_eq_none_iff]; omega
  · simp [lookup,h]; omega

def next {n : Nat} (ρ : Instr n) (x : Cfg n) : Cfg n :=
  match ρ.2 with
  | none => (x.1+1,Function.update x.2 ρ.1 (x.2 ρ.1+1))
  | some j => if x.2 ρ.1 = 0 then (j,x.2)
      else (x.1+1,Function.update x.2 ρ.1 (x.2 ρ.1-1))

def step {n : Nat} (P : Program n) (base : Nat) (x : Cfg n) : Option (Cfg n) :=
  (lookup P base x.1).map (fun ρ => next ρ x)

abbrev Reaches {n : Nat} (P : Program n) (base : Nat) := StateTransition.Reaches (step P base)
abbrev Reaches₁ {n : Nat} (P : Program n) (base : Nat) := StateTransition.Reaches₁ (step P base)

def Terminates {n : Nat} (P : Program n) (base : Nat) (x : Cfg n) : Prop :=
  (StateTransition.eval (step P base) x).Dom
def Halts {n : Nat} (d : HaltingInput n) : Prop := Terminates d.1 1 (1,d.2)

theorem terminates_iff_reaches_outside {n : Nat} (P : Program n) (base : Nat) (x : Cfg n) :
    Terminates P base x ↔ ∃ y, Reaches P base x y ∧ (y.1 < base ∨ base+P.length ≤ y.1) := by
  simp only [Terminates,Part.dom_iff_mem,StateTransition.mem_eval,step,Option.map_eq_none_iff,
    lookup_eq_none]

def runSteps {n : Nat} (P : Program n) (base : Nat) : Nat → Cfg n → Option (Cfg n)
  | 0,x => some x
  | t+1,x => (step P base x).bind (runSteps P base t)

theorem runSteps_reaches {n : Nat} (P : Program n) (base t : Nat) (x y : Cfg n)
    (h : runSteps P base t x = some y) : Reaches P base x y := by
  induction t generalizing x with
  | zero => cases h; exact .refl
  | succ t ih =>
    cases hs : step P base x with
    | none => simp [runSteps,hs] at h
    | some z =>
      exact Relation.ReflTransGen.head (by simp [hs])
        (ih z (by simpa [runSteps,hs] using h))

theorem runSteps_reaches₁ {n : Nat} (P : Program n) (base t : Nat) (x y : Cfg n)
    (ht : 0 < t) (h : runSteps P base t x = some y) : Reaches₁ P base x y := by
  cases t with
  | zero => cases ht
  | succ t =>
    cases hs : step P base x with
    | none => simp [runSteps,hs] at h
    | some z =>
      exact Relation.TransGen.head' (by simp [hs])
        (runSteps_reaches P base t z y (by simpa [runSteps,hs] using h))

def Placed {n : Nat} (P : Program n) (base i : Nat) (code : Program n) : Prop :=
  ∀ j, j < code.length → lookup P base (i+j) = code[j]?

theorem placed_self {n : Nat} (code : Program n) (base : Nat) : Placed code base base code := by
  intro j hj
  simp [lookup]

theorem Placed.left {n : Nat} {P A B : Program n} {base i : Nat}
    (h : Placed P base i (A ++ B)) : Placed P base i A := by
  intro j hj
  have hh := h j (by simp only [List.length_append]; omega)
  simpa [List.getElem?_append_left hj] using hh

theorem Placed.right {n : Nat} {P A B : Program n} {base i : Nat}
    (h : Placed P base i (A ++ B)) : Placed P base (i+A.length) B := by
  intro j hj
  have hh := h (A.length+j) (by simp only [List.length_append]; omega)
  simpa [Nat.add_assoc,List.getElem?_append_right (show A.length ≤ A.length+j by omega)] using hh

end DistributedSynthesis.CounterMachine.MM
