/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Library.Computability.FiniteSearch
import Mathlib.Tactic.FunProp

/-! Kernel-checked closure rules for the numeric block compiler. -/
namespace Characterisation.PeriodicBlocks.PrimitiveRecursive
open DistributedSynthesis
attribute [fun_prop] Primrec PrimrecPred
attribute [fun_prop] Primrec.id Primrec.fst Primrec.snd Primrec.const Primrec.pair Primrec.comp
attribute [fun_prop] PrimrecPred.comp PrimrecPred.and PrimrecPred.or PrimrecPred.not
attribute [fun_prop] Primrec.list_length Primrec.list_range

@[fun_prop] theorem add : Primrec (fun x : Nat × Nat => x.1+x.2) := Primrec.nat_add
@[fun_prop] theorem mul : Primrec (fun x : Nat × Nat => x.1*x.2) := Primrec.nat_mul
@[fun_prop] theorem sub : Primrec (fun x : Nat × Nat => x.1-x.2) := Primrec.nat_sub
@[fun_prop] theorem div : Primrec (fun x : Nat × Nat => x.1/x.2) := Primrec.nat_div
@[fun_prop] theorem mod : Primrec (fun x : Nat × Nat => x.1%x.2) := Primrec.nat_mod
@[fun_prop] theorem getD {X : Type*} [Primcodable X] (d : X) :
    Primrec (fun x : List X × Nat => x.1.getD x.2 d) := Primrec.list_getD d
@[fun_prop] theorem take {X : Type*} [Primcodable X] :
    Primrec (fun x : Nat × List X => x.2.take x.1) := Primrec.list_take
@[fun_prop] theorem idxOf {X : Type*} [Primcodable X] [DecidableEq X] :
    Primrec (fun x : X × List X => x.2.idxOf x.1) := Primrec.list_idxOf
@[fun_prop] theorem product {X Y : Type*} [Primcodable X] [Primcodable Y] :
    Primrec (fun x : List X × List Y => x.1.product x.2) := FiniteSearch.product_primrec
@[fun_prop] theorem tables : Primrec (fun x : Nat × Nat => FiniteSearch.tables x.1 x.2) :=
  FiniteSearch.tables_primrec
@[fun_prop] theorem words {X : Type*} [Primcodable X] :
    Primrec (fun x : List X × Nat => FiniteSearch.words x.1 x.2) := FiniteSearch.words_primrec
@[fun_prop] theorem minWith : Primrec (fun x : Nat × List Nat => FiniteSearch.minWith x.1 x.2) :=
  FiniteSearch.minWith_primrec
@[fun_prop] theorem eq {X : Type*} [Primcodable X] : PrimrecPred (fun x : X × X => x.1=x.2) := Primrec.eq
@[fun_prop] theorem lt : PrimrecPred (fun x : Nat × Nat => x.1<x.2) := Primrec.nat_lt

section Closure
variable {X Y Z : Type*} [Primcodable X] [Primcodable Y] [Primcodable Z]
@[fun_prop] theorem map {xs : X → List Y} {f : X → Y → Z}
    (hxs : Primrec xs) (hf : Primrec (fun x : X × Y => f x.1 x.2)) :
    Primrec (fun x => (xs x).map (f x)) := Primrec.list_map hxs hf.to₂
@[fun_prop] theorem flatMap {xs : X → List Y} {f : X → Y → List Z}
    (hxs : Primrec xs) (hf : Primrec (fun x : X × Y => f x.1 x.2)) :
    Primrec (fun x => (xs x).flatMap (f x)) := Primrec.list_flatMap hxs hf.to₂
@[fun_prop] theorem foldl {xs : X → List Y} {z : X → Z} {f : X → Z → Y → Z}
    (hxs : Primrec xs) (hz : Primrec z) (hf : Primrec (fun x : X × Z × Y => f x.1 x.2.1 x.2.2)) :
    Primrec (fun x => (xs x).foldl (f x) (z x)) := Primrec.list_foldl hxs hz hf.to₂
@[fun_prop] theorem implication {p q : X → Prop} (hp : PrimrecPred p) (hq : PrimrecPred q) :
    PrimrecPred (fun x => p x → q x) := (hp.not.or hq).of_eq (fun _ => by tauto)
@[fun_prop] theorem forall_mem {xs : X → List Y} {p : X → Y → Prop}
    (hxs : Primrec xs) (hp : PrimrecPred (fun x : X × Y => p x.1 x.2)) :
    PrimrecPred (fun x => ∀ y ∈ xs x, p x y) := FiniteSearch.forall_mem hxs hp.primrecRel
@[fun_prop] theorem forall_lt {n : X → Nat} {p : X → Nat → Prop}
    (hn : Primrec n) (hp : PrimrecPred (fun x : X × Nat => p x.1 x.2)) :
    PrimrecPred (fun x => ∀ i < n x, p x i) := FiniteSearch.forall_lt hn hp.primrecRel
@[fun_prop] theorem exists_lt {n : X → Nat} {p : X → Nat → Prop}
    (hn : Primrec n) (hp : PrimrecPred (fun x : X × Nat => p x.1 x.2)) :
    PrimrecPred (fun x => ∃ i < n x, p x i) := FiniteSearch.exists_lt hn hp.primrecRel
end Closure
end Characterisation.PeriodicBlocks.PrimitiveRecursive
