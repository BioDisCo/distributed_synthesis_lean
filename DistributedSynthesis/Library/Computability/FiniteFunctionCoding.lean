/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.FiniteCodeNumbering

/-! # Numbering finite functions by the existing table enumeration

This is an interface to `FiniteSearch.tables` and `FiniteCodeNumbering`, not a
new representation of finite sets. Both empty domains and empty codomains are
included.
-/
namespace DistributedSynthesis.FiniteFunctionCoding

def encode {m n : Nat} (f : Fin m → Fin n) : List Nat := List.ofFn (fun i => (f i).val)

theorem encode_injective {m n : Nat} : Function.Injective (encode (m := m) (n := n)) := by
  intro f g h
  funext i
  apply Fin.ext
  have he := congrArg (fun xs : List Nat => xs[i.val]?) h
  simpa only [encode, List.getElem?_ofFn, dif_pos i.isLt, Fin.eta, Option.some.injEq] using he

def codes (m n : Nat) : List (List Nat) := FiniteCodeNumbering.unique (FiniteSearch.tables n m)
def name (m n : Nat) (xs : List Nat) : Nat := FiniteCodeNumbering.name (FiniteSearch.tables n m) xs

theorem codes_primrec : Primrec₂ codes :=
  FiniteCodeNumbering.unique_primrec.comp (FiniteSearch.tables_primrec.comp Primrec.snd Primrec.fst)

theorem name_primrec : Primrec (fun x : (Nat × Nat) × List Nat => name x.1.1 x.1.2 x.2) :=
  FiniteCodeNumbering.name_primrec.comp
    (FiniteSearch.tables_primrec.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst))
    Primrec.snd

noncomputable def equiv (m n : Nat) : (Fin m → Fin n) ≃ Fin (codes m n).length :=
  FiniteCodeNumbering.equiv (FiniteSearch.tables n m) encode encode_injective
    FiniteSearch.ofFn_mem_tables (fun _ h => FiniteSearch.mem_tables_iff_policy _ |>.mp h)

theorem equiv_val {m n : Nat} (f : Fin m → Fin n) :
    (equiv m n f).val = name m n (encode f) := rfl

theorem get_name {m n : Nat} (f : Fin m → Fin n) :
    (codes m n).getD (name m n (encode f)) [] = encode f := by
  have h := FiniteCodeNumbering.get_name (FiniteSearch.tables n m) encode
    FiniteSearch.ofFn_mem_tables f
  change ((codes m n)[name m n (encode f)]?).getD [] = _
  simpa only [codes, name, h, Option.getD_some]

theorem get_equiv {m n : Nat} (f : Fin m → Fin n) :
    (codes m n).getD (equiv m n f).val [] = encode f := get_name f

theorem lookup_encode {m n : Nat} (f : Fin m → Fin n) (i : Fin m) :
    (encode f).getD i.val 0 = (f i).val := by
  rw [List.getD_eq_getElem _ _ (by simpa only [encode, List.length_ofFn] using i.isLt)]
  simp only [encode, List.getElem_ofFn, Fin.eta]

end DistributedSynthesis.FiniteFunctionCoding
