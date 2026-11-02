/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.FiniteSearch
import Mathlib.Tactic.FunProp

/-! # `fun_prop` support for Mathlib primitive recursion

These are uncurried interfaces to existing Mathlib theorems. Proof search
produces ordinary kernel-checked `Primrec` proofs; it does not infer
computability from executable Lean code.
-/
attribute [fun_prop] Primrec PrimrecPred
attribute [fun_prop] Primrec.id Primrec.const Primrec.comp Primrec.fst Primrec.snd Primrec.pair
attribute [fun_prop] Primrec.succ Primrec.list_length Primrec.list_range
attribute [fun_prop] PrimrecPred.comp
attribute [fun_prop] Primrec.ite PrimrecPred.and PrimrecPred.or PrimrecPred.not

namespace DistributedSynthesis.PrimrecFunProp

@[fun_prop] theorem add : Primrec (fun x : Nat × Nat => x.1 + x.2) := Primrec.nat_add
@[fun_prop] theorem mul : Primrec (fun x : Nat × Nat => x.1 * x.2) := Primrec.nat_mul
@[fun_prop] theorem sub : Primrec (fun x : Nat × Nat => x.1 - x.2) := Primrec.nat_sub
@[fun_prop] theorem div : Primrec (fun x : Nat × Nat => x.1 / x.2) := Primrec.nat_div
@[fun_prop] theorem mod : Primrec (fun x : Nat × Nat => x.1 % x.2) := Primrec.nat_mod
@[fun_prop] theorem lt : PrimrecPred (fun x : Nat × Nat => x.1 < x.2) := Primrec.nat_lt
@[fun_prop] theorem le : PrimrecPred (fun x : Nat × Nat => x.1 ≤ x.2) := Primrec.nat_le

variable {X A B : Type*} [Primcodable X] [Primcodable A] [Primcodable B]

@[fun_prop] theorem eq [DecidableEq A] : PrimrecPred (fun x : A × A => x.1 = x.2) := Primrec.eq
@[fun_prop] theorem decide_primrec {p : X → Prop} [DecidablePred p] (hp : PrimrecPred p) :
    Primrec (fun x => decide (p x)) := hp.decide
@[fun_prop] theorem getD (d : A) : Primrec (fun x : List A × Nat => x.1.getD x.2 d) :=
  Primrec.list_getD d
@[fun_prop] theorem cons : Primrec (fun x : A × List A => x.1 :: x.2) := Primrec.list_cons
@[fun_prop] theorem append : Primrec (fun x : List A × List A => x.1 ++ x.2) := Primrec.list_append
@[fun_prop] theorem map {xs : X → List A} {f : X → A → B}
    (hxs : Primrec xs) (hf : Primrec (fun x : X × A => f x.1 x.2)) :
    Primrec (fun x => (xs x).map (f x)) := Primrec.list_map hxs hf
@[fun_prop] theorem flatMap {xs : X → List A} {f : X → A → List B}
    (hxs : Primrec xs) (hf : Primrec (fun x : X × A => f x.1 x.2)) :
    Primrec (fun x => (xs x).flatMap (f x)) := Primrec.list_flatMap hxs hf
@[fun_prop] theorem exists_mem {xs : X → List A} {p : X → A → Prop}
    (hxs : Primrec xs) (hp : PrimrecPred (fun x : X × A => p x.1 x.2)) :
    PrimrecPred (fun x => ∃ a ∈ xs x, p x a) := FiniteSearch.exists_mem hxs hp
@[fun_prop] theorem forall_mem {xs : X → List A} {p : X → A → Prop}
    (hxs : Primrec xs) (hp : PrimrecPred (fun x : X × A => p x.1 x.2)) :
    PrimrecPred (fun x => ∀ a ∈ xs x, p x a) := FiniteSearch.forall_mem hxs hp
@[fun_prop] theorem exists_lt {n : X → Nat} {p : X → Nat → Prop}
    (hn : Primrec n) (hp : PrimrecPred (fun x : X × Nat => p x.1 x.2)) :
    PrimrecPred (fun x => ∃ a < n x, p x a) := FiniteSearch.exists_lt hn hp
@[fun_prop] theorem forall_lt {n : X → Nat} {p : X → Nat → Prop}
    (hn : Primrec n) (hp : PrimrecPred (fun x : X × Nat => p x.1 x.2)) :
    PrimrecPred (fun x => ∀ a < n x, p x a) := FiniteSearch.forall_lt hn hp

@[fun_prop] theorem filter {xs : X → List A} {p : X → A → Prop}
    [∀ x, DecidablePred (p x)]
    (hxs : Primrec xs) (hp : PrimrecPred (fun x : X × A => p x.1 x.2)) :
    Primrec (fun x => (xs x).filter (fun a => decide (p x a))) :=
  hp.primrecRel.swap.listFilter.comp hxs Primrec.id

theorem predicate_const (p : Prop) : PrimrecPred (fun _ : X => p) := by
  classical
  exact (Primrec.const (decide p)).primrecPred

theorem predicate_ite {c p q : X → Prop} [DecidablePred c]
    (hc : PrimrecPred c) (hp : PrimrecPred p) (hq : PrimrecPred q) :
    PrimrecPred (fun x => if c x then p x else q x) :=
  ((hc.and hp).or (hc.not.and hq)).of_eq (fun x => by split_ifs <;> simp_all)

end DistributedSynthesis.PrimrecFunProp
