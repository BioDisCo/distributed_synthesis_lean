/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.FiniteSearch
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Finite function tables with an explicit domain numbering -/
namespace DistributedSynthesis.FiniteFunctionCodes

def prod {X Y : Type*} {n m : Nat} (e : X ≃ Fin n) (f : Y ≃ Fin m) :
    X × Y ≃ Fin (n*m) := (e.prodCongr f).trans finProdFinEquiv

def encode {X : Type*} {n m : Nat} (e : X ≃ Fin n) (f : X → Fin m) : List Nat :=
  List.ofFn (fun i => (f (e.symm i)).val)

def decode {X : Type*} {n m : Nat} (e : X ≃ Fin n) (xs : List Nat) : X → Fin (m+1) :=
  fun x => ⟨xs.getD (e x).val 0 % (m+1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem encode_mem {X : Type*} {n m : Nat} (e : X ≃ Fin n) (f : X → Fin m) :
    encode e f ∈ FiniteSearch.tables m n := FiniteSearch.ofFn_mem_tables _

theorem eval_encode {X : Type*} {n m : Nat} (e : X ≃ Fin n) (f : X → Fin m) (x : X) :
    (encode e f).getD (e x).val 0 = (f x).val := by
  rw [List.getD_eq_getElem _ _ (by simpa [encode] using (e x).isLt)]
  simp [encode]

@[simp] theorem decode_encode {X : Type*} {n m : Nat}
    (e : X ≃ Fin n) (f : X → Fin (m+1)) : decode e (encode e f) = f := by
  funext x
  apply Fin.ext
  simp only [decode, eval_encode, Nat.mod_eq_of_lt (f x).isLt]

end DistributedSynthesis.FiniteFunctionCodes
