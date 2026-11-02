/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Encoding
import DistributedSynthesis.Library.Computability.FiniteFunctionCoding
import DistributedSynthesis.Library.Computability.PrimrecFunProp
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Numeric labels for the existing full-MSO valuations

Node and set markers use the same finite Boolean-function tables. This only
encodes the finite alphabet at each tree node: set variables still range over
arbitrary subsets of the infinite tree.
-/
namespace DistributedSynthesis.MSO.Tree.NumericValuations

/-- Base alphabet maximum, number of individual variables, number of set variables. -/
abbrev Shape := Nat × Nat × Nat

def bits (n : Nat) := FiniteFunctionCoding.codes n 2
def count (s : Shape) := (s.1 + 1) * (bits s.2.1).length * (bits s.2.2).length

def base (s : Shape) (a : Nat) := a / (bits s.2.2).length / (bits s.2.1).length
def nodeBits (s : Shape) (a : Nat) :=
  (bits s.2.1).getD (a / (bits s.2.2).length % (bits s.2.1).length) []
def setBits (s : Shape) (a : Nat) := (bits s.2.2).getD (a % (bits s.2.2).length) []
def node (s : Shape) (a i : Nat) := (nodeBits s a).getD i 0
def set (s : Shape) (a i : Nat) := (setBits s a).getD i 0

@[fun_prop] theorem bits_primrec : Primrec bits :=
  FiniteFunctionCoding.codes_primrec.comp Primrec.id (Primrec.const 2)
@[fun_prop] theorem count_primrec : Primrec count := by unfold count; fun_prop
@[fun_prop] theorem base_primrec : Primrec (fun x : Shape × Nat => base x.1 x.2) := by unfold base; fun_prop
@[fun_prop] theorem nodeBits_primrec : Primrec (fun x : Shape × Nat => nodeBits x.1 x.2) := by
  unfold nodeBits; fun_prop
@[fun_prop] theorem setBits_primrec : Primrec (fun x : Shape × Nat => setBits x.1 x.2) := by
  unfold setBits; fun_prop
@[fun_prop] theorem node_primrec : Primrec (fun x : Shape × Nat × Nat => node x.1 x.2.1 x.2.2) := by
  unfold node; fun_prop
@[fun_prop] theorem set_primrec : Primrec (fun x : Shape × Nat × Nat => set x.1 x.2.1 x.2.2) := by
  unfold set; fun_prop

noncomputable def bitEquiv (n : Nat) : (Fin n → Bool) ≃ Fin (bits n).length :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans (FiniteFunctionCoding.equiv n 2)

theorem bits_pos (n : Nat) : 0 < (bits n).length := Nat.zero_lt_of_lt (bitEquiv n (fun _ => false)).isLt

theorem count_pos (s : Shape) : 0 < count s :=
  Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (bits_pos _)) (bits_pos _)

noncomputable def equiv (s : Shape) : ValuationLabel (Fin (s.1 + 1)) s.2.1 s.2.2 ≃ Fin (count s) :=
  (((Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (bitEquiv s.2.1) (bitEquiv s.2.2))).trans
      (Equiv.prodAssoc _ _ _).symm).trans
    (Equiv.prodCongr finProdFinEquiv (Equiv.refl _))).trans finProdFinEquiv

theorem equiv_val (s : Shape) (a : ValuationLabel (Fin (s.1 + 1)) s.2.1 s.2.2) :
    (equiv s a).val = (bitEquiv s.2.2 a.2.2).val + (bits s.2.2).length *
      ((bitEquiv s.2.1 a.2.1).val + (bits s.2.1).length * a.1.val) := rfl

theorem bit_lookup {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    ((bits n).getD (bitEquiv n f).val []).getD i.val 0 = if f i then 1 else 0 := by
  change ((FiniteFunctionCoding.codes n 2).getD
    (FiniteFunctionCoding.equiv n 2 (fun i => finTwoEquiv.symm (f i))).val []).getD i.val 0 = _
  rw [FiniteFunctionCoding.get_equiv, FiniteFunctionCoding.lookup_encode]
  cases f i <;> rfl

theorem base_encode (s : Shape) (a : ValuationLabel (Fin (s.1 + 1)) s.2.1 s.2.2) :
    base s (equiv s a).val = a.1.val := by
  rw [base, equiv_val, Nat.add_mul_div_left _ _ (bits_pos _),
    Nat.div_eq_of_lt (bitEquiv s.2.2 a.2.2).isLt, Nat.zero_add,
    Nat.add_mul_div_left _ _ (bits_pos _), Nat.div_eq_of_lt (bitEquiv s.2.1 a.2.1).isLt, Nat.zero_add]

theorem node_encode (s : Shape) (a : ValuationLabel (Fin (s.1 + 1)) s.2.1 s.2.2) (i : Fin s.2.1) :
    node s (equiv s a).val i.val = if a.2.1 i then 1 else 0 := by
  rw [node, nodeBits, equiv_val, Nat.add_mul_div_left _ _ (bits_pos _),
    Nat.div_eq_of_lt (bitEquiv s.2.2 a.2.2).isLt, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (bitEquiv s.2.1 a.2.1).isLt]
  exact bit_lookup _ i

theorem set_encode (s : Shape) (a : ValuationLabel (Fin (s.1 + 1)) s.2.1 s.2.2) (i : Fin s.2.2) :
    set s (equiv s a).val i.val = if a.2.2 i then 1 else 0 := by
  rw [set, setBits, equiv_val, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (bitEquiv s.2.2 a.2.2).isLt]
  exact bit_lookup _ i

/-- The same numbering with the positive-size convention of numeric automata. -/
noncomputable def number (s : Shape) : ValuationLabel (Fin (s.1 + 1)) s.2.1 s.2.2 ≃
    Fin (count s - 1 + 1) :=
  (equiv s).trans (finCongr (Nat.sub_add_cancel (count_pos s)).symm)

theorem number_val (s : Shape) (a : ValuationLabel (Fin (s.1 + 1)) s.2.1 s.2.2) :
    (number s a).val = (equiv s a).val := rfl

end DistributedSynthesis.MSO.Tree.NumericValuations
