/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! # Lookup in uniformly sized flattened tables -/
namespace DistributedSynthesis.FiniteTableLookup

theorem flat_length {X Y : Type*} (xs : List X) (f : X → List Y) (k : Nat)
    (hf : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons,List.length_append,hf x (List.mem_cons_self ..),
      ih (fun y hy => hf y (List.mem_cons_of_mem _ hy))]
    simp [Nat.add_mul,Nat.add_comm]

theorem flat_lookup {X Y : Type*} (xs : List X) (f : X → List Y) (k : Nat)
    (hf : ∀ x ∈ xs, (f x).length = k) (i j : Nat) (hi : i < xs.length) (hj : j < k) :
    (xs.flatMap f)[i*k+j]? = (f xs[i])[j]? := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.flatMap_cons,List.getElem_cons_zero]
      exact List.getElem?_append_left (by rw [hf x (List.mem_cons_self ..)]; exact hj)
    | succ i =>
      rw [List.flatMap_cons,List.getElem?_append_right (by
        rw [hf x (List.mem_cons_self ..)]
        rw [Nat.add_mul,Nat.one_mul]
        omega)]
      rw [hf x (List.mem_cons_self ..)]
      have he : (i+1)*k+j-k = i*k+j := by rw [Nat.add_mul,Nat.one_mul]; omega
      rw [he]
      exact ih (fun y hy => hf y (List.mem_cons_of_mem _ hy)) i (by simpa using hi)

theorem lookup3 {X Y Z W : Type*} (xs : List X) (ys : List Y) (zs : List Z)
    (f : X → Y → Z → W) (q : Fin xs.length) (l : Fin ys.length) (b : Fin zs.length) (fallback : W) :
    (xs.flatMap (fun x => ys.flatMap (fun y => zs.map (f x y)))).getD
      ((q.val*ys.length+l.val)*zs.length+b.val) fallback = f xs[q.val] ys[l.val] zs[b.val] := by
  rw [List.getD_eq_getElem?_getD]
  have hinner : l.val*zs.length+b.val < ys.length*zs.length := by
    simpa only [finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm] using (finProdFinEquiv (l,b)).isLt
  rw [show (q.val*ys.length+l.val)*zs.length+b.val = q.val*(ys.length*zs.length)+(l.val*zs.length+b.val) by ring]
  rw [flat_lookup xs _ (ys.length*zs.length)
    (fun x _ => flat_length ys (fun y => zs.map (f x y)) zs.length (fun y _ => List.length_map _)) q.val _ q.isLt hinner]
  rw [flat_lookup ys _ zs.length (fun _ _ => List.length_map _) l.val b.val l.isLt b.isLt,
    List.getElem?_map,List.getElem?_eq_getElem b.isLt]
  rfl
end DistributedSynthesis.FiniteTableLookup
