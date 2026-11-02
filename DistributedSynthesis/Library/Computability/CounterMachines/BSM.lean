/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Copyright Dominique Larchey-Wendling (LORIA -- CNRS).
Lean adaptation of the binary-stack semantics in BSM.v, from the Coq library
of undecidability proofs, revision 11c41e0637f0c5219ad1c4c92d11609b7e072c31.
See README.md, upstream/BSM.v, and LICENSE-MPL-2.0 in this directory.
-/
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.StateTransition

/-! # Rocq binary stack machines

A program is a finite instruction list placed at a base address. PUSH pushes
one bit and falls through. POP removes a bit and branches as follows: true
falls through; false jumps to its first target; empty jumps to its second
target without changing the stack. Missing addresses halt.

Instructions use a sum representation rather than Rocq's inductive type, and
stack vectors use `Fin n → List Bool`. These representations already carry
Mathlib's primitive-recursive encodings. `Eval` is the big-step semantics,
factored through `next`; `eval_iff` identifies it with deterministic termination.
No universality or source-undecidability theorem is assumed.
-/
namespace DistributedSynthesis.CounterMachine.BSM

abbrev Instr (n : Nat) := Fin n × (Bool ⊕ (Nat × Nat))
abbrev Program (n : Nat) := List (Instr n)
abbrev Stacks (n : Nat) := Fin n → List Bool
abbrev Cfg (n : Nat) := Nat × Stacks n
abbrev HaltingInput (n : Nat) := Nat × Program n × Stacks n

def push {n : Nat} (k : Fin n) (b : Bool) : Instr n := (k,.inl b)
def pop {n : Nat} (k : Fin n) (f e : Nat) : Instr n := (k,.inr (f,e))

def lookup {n : Nat} (P : Program n) (base pc : Nat) : Option (Instr n) :=
  if base ≤ pc then P[pc-base]? else none

theorem lookup_eq_none {n : Nat} (P : Program n) (base pc : Nat) :
    lookup P base pc = none ↔ pc < base ∨ base + P.length ≤ pc := by
  by_cases h : base ≤ pc
  · simp only [lookup,if_pos h,List.getElem?_eq_none_iff]
    omega
  · simp [lookup,h]
    omega

def next {n : Nat} (ρ : Instr n) (x : Cfg n) : Cfg n :=
  match ρ.2 with
  | .inl b => (x.1+1,Function.update x.2 ρ.1 (b :: x.2 ρ.1))
  | .inr (f,e) => match x.2 ρ.1 with
    | [] => (e,x.2)
    | false :: l => (f,Function.update x.2 ρ.1 l)
    | true :: l => (x.1+1,Function.update x.2 ρ.1 l)

@[simp] theorem next_push {n : Nat} (k : Fin n) (b : Bool) (i : Nat) (s : Stacks n) :
    next (push k b) (i,s) = (i+1,Function.update s k (b :: s k)) := rfl

theorem next_pop_empty {n : Nat} (k : Fin n) (i f e : Nat) (s : Stacks n) (h : s k = []) :
    next (pop k f e) (i,s) = (e,s) := by simp [next,pop,h]

theorem next_pop_false {n : Nat} (k : Fin n) (i f e : Nat) (s : Stacks n)
    (l : List Bool) (h : s k = false :: l) :
    next (pop k f e) (i,s) = (f,Function.update s k l) := by simp [next,pop,h]

theorem next_pop_true {n : Nat} (k : Fin n) (i f e : Nat) (s : Stacks n)
    (l : List Bool) (h : s k = true :: l) :
    next (pop k f e) (i,s) = (i+1,Function.update s k l) := by simp [next,pop,h]

def step {n : Nat} (P : Program n) (base : Nat) (x : Cfg n) : Option (Cfg n) :=
  (lookup P base x.1).map (fun ρ => next ρ x)

abbrev Reaches {n : Nat} (P : Program n) (base : Nat) := StateTransition.Reaches (step P base)
abbrev Reaches₁ {n : Nat} (P : Program n) (base : Nat) := StateTransition.Reaches₁ (step P base)

inductive Eval {n : Nat} (P : Program n) (base : Nat) : Cfg n → Cfg n → Prop
  | out (x) (h : lookup P base x.1 = none) : Eval P base x x
  | exec (x y) (ρ) (h : lookup P base x.1 = some ρ)
      (rest : Eval P base (next ρ x) y) : Eval P base x y

theorem step_eq_none {n : Nat} (P : Program n) (base : Nat) (x : Cfg n) :
    step P base x = none ↔ lookup P base x.1 = none := by simp [step]

theorem eval_iff {n : Nat} (P : Program n) (base : Nat) (x y : Cfg n) :
    Eval P base x y ↔ Reaches P base x y ∧ step P base y = none := by
  constructor
  · intro h
    induction h with
    | out x h => exact ⟨.refl,(step_eq_none P base x).mpr h⟩
    | exec x y ρ h rest ih =>
      exact ⟨Relation.ReflTransGen.head (by simp [step,h]) ih.1,ih.2⟩
  · rintro ⟨h,hs⟩
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact .out y ((step_eq_none P base y).mp hs)
    | @head x z hx hz ih =>
      cases hρ : lookup P base x.1 with
      | none => simp [step,hρ] at hx
      | some ρ =>
        have hn : next ρ x = z := by simpa [step,hρ] using hx
        subst z
        exact .exec x y ρ hρ ih

def Terminates {n : Nat} (P : Program n) (base : Nat) (x : Cfg n) : Prop :=
  (StateTransition.eval (step P base) x).Dom

theorem terminates_iff_eval {n : Nat} (P : Program n) (base : Nat) (x : Cfg n) :
    Terminates P base x ↔ ∃ y, Eval P base x y := by
  simp only [Terminates,Part.dom_iff_mem,StateTransition.mem_eval,eval_iff]

def Halts {n : Nat} (d : HaltingInput n) : Prop := Terminates d.2.1 d.1 (d.1,d.2.2)

end DistributedSynthesis.CounterMachine.BSM
