/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import Mathlib.Tactic

/-! # Independent semantics of the classical zero-initialized MM2 problem

The instructions, one-based addresses, and relational halting predicate
follow the source pinned in SOURCE-UNDECIDABILITY.md. This module has no
dependency on the distributed synthesis construction.
-/
namespace DistributedSynthesis.CounterMachine.MM2

inductive Instr where
  | incA | incB
  | decA (target : Nat) | decB (target : Nat)
deriving DecidableEq, Repr
abbrev Program := List Instr
abbrev Cfg := Nat × (Nat × Nat)

def lookup (P : Program) (i : Nat) : Option Instr :=
  if i = 0 then none else P[i-1]?

/-- The six instruction transitions in the cited source, independently of
the target machine's `next` and `op` definitions. -/
inductive Atom : Instr → Cfg → Cfg → Prop
  | incA (i a b) : Atom .incA (i,(a,b)) (i+1,(a+1,b))
  | incB (i a b) : Atom .incB (i,(a,b)) (i+1,(a,b+1))
  | decAPos (i j a b) : Atom (.decA j) (i,(a+1,b)) (j,(a,b))
  | decBPos (i j a b) : Atom (.decB j) (i,(a,b+1)) (j,(a,b))
  | decAZero (i j b) : Atom (.decA j) (i,(0,b)) (i+1,(0,b))
  | decBZero (i j a) : Atom (.decB j) (i,(a,0)) (i+1,(a,0))
def Step (P : Program) (x y : Cfg) : Prop :=
  ∃ ρ, lookup P x.1 = some ρ ∧ Atom ρ x y
def Stops (P : Program) (x : Cfg) : Prop := ∀ y, ¬ Step P x y
def ZeroHalts (P : Program) : Prop :=
  ∃ y, Relation.ReflTransGen (Step P) (1,(0,0)) y ∧ Stops P y

/-- The source defines occurrence by a list prefix, not by zero-based lookup. -/
def InstrAt (ρ : Instr) (i : Nat) (P : Program) : Prop :=
  ∃ l r, P = l ++ ρ :: r ∧ 1+l.length = i
theorem lookup_iff_instrAt (P : Program) (i : Nat) (ρ : Instr) :
    lookup P i = some ρ ↔ InstrAt ρ i P := by
  constructor
  · intro h
    have hi : i ≠ 0 := by intro hi; simp [lookup,hi] at h
    have hg : P[i-1]? = some ρ := by simpa [lookup,hi] using h
    obtain ⟨hlt,he⟩ := List.getElem?_eq_some_iff.mp hg
    refine ⟨P.take (i-1),P.drop i,?_,?_⟩
    · have ht := List.take_concat_get (l := P) hlt
      rw [he] at ht
      have hd := List.take_append_drop i P
      rw [show i = (i-1)+1 by omega,← ht] at hd
      simpa [List.append_assoc,show i-1+1 = i by omega] using hd.symm
    · simp only [List.length_take]
      omega
  · rintro ⟨l,r,rfl,rfl⟩
    simp [lookup,Nat.add_comm]

def atomNext (ρ : Instr) (x : Cfg) : Cfg :=
  match ρ with
  | .incA => (x.1+1,(x.2.1+1,x.2.2))
  | .incB => (x.1+1,(x.2.1,x.2.2+1))
  | .decA j => if x.2.1 = 0 then (x.1+1,x.2) else (j,(x.2.1-1,x.2.2))
  | .decB j => if x.2.2 = 0 then (x.1+1,x.2) else (j,(x.2.1,x.2.2-1))
theorem atom_iff (ρ : Instr) (x y : Cfg) : Atom ρ x y ↔ y = atomNext ρ x := by
  constructor
  · intro h; cases h <;> simp [atomNext]
  · rintro rfl
    rcases x with ⟨i,a,b⟩
    cases ρ with
    | incA => exact .incA i a b
    | incB => exact .incB i a b
    | decA j =>
      cases a with
      | zero => exact .decAZero i j b
      | succ a => exact .decAPos i j a b
    | decB j =>
      cases b with
      | zero => exact .decBZero i j a
      | succ b => exact .decBPos i j a b

/-- A stopped source configuration is held fixed only for defining its
infinite trace. `Step` above still has no outgoing edge at that point. -/
def advance (P : Program) (x : Cfg) : Cfg :=
  match lookup P x.1 with
  | none => x
  | some ρ => atomNext ρ x
def run (P : Program) : Nat → Cfg
  | 0 => (1,(0,0))
  | n+1 => advance P (run P n)
theorem stops_iff (P : Program) (x : Cfg) : Stops P x ↔ lookup P x.1 = none := by
  cases h : lookup P x.1 with
  | none => simp [Stops,Step,h]
  | some ρ =>
    constructor
    · intro hs; exact False.elim (hs _ ⟨ρ,h,(atom_iff ρ x _).mpr rfl⟩)
    · intro hh; cases hh
theorem step_eq (P : Program) {x y : Cfg} (h : Step P x y) : y = advance P x := by
  obtain ⟨ρ,hl,ha⟩ := h
  simpa [advance,hl] using (atom_iff _ _ _).mp ha
theorem run_reachable (P : Program) (n : Nat) :
    Relation.ReflTransGen (Step P) (1,(0,0)) (run P n) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    cases h : lookup P (run P n).1 with
    | none => simpa [run,advance,h] using ih
    | some ρ =>
      apply ih.tail
      exact ⟨ρ,h,(atom_iff _ _ _).mpr (by simp [run,advance,h])⟩
theorem reachable_in_run (P : Program) {y : Cfg}
    (h : Relation.ReflTransGen (Step P) (1,(0,0)) y) : ∃ n, run P n = y := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | tail h hs ih =>
    obtain ⟨n,rfl⟩ := ih
    exact ⟨n+1,(step_eq P hs).symm⟩
theorem zeroHalts_iff_run (P : Program) :
    ZeroHalts P ↔ ∃ n, lookup P (run P n).1 = none := by
  constructor
  · rintro ⟨y,hy,hs⟩
    obtain ⟨n,rfl⟩ := reachable_in_run P hy
    exact ⟨n,(stops_iff P _).mp hs⟩
  · rintro ⟨n,hn⟩
    exact ⟨run P n,run_reachable P n,(stops_iff P _).mpr hn⟩

end DistributedSynthesis.CounterMachine.MM2

