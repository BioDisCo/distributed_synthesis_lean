/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.NumericValuations
import DistributedSynthesis.Library.Logic.MSO.Recognizability

/-! # Numeric maps between MSO valuation alphabets

The same operation supports variable renaming and projection of the last bound
variable. It rearranges finite marker bits; it does not enumerate set values.
-/
namespace DistributedSynthesis.MSO.Tree.NumericRenaming
open NumericValuations

abbrev Input := Shape × Shape × List Nat × List Nat

def join (s : Shape) (a : Nat) (ns ss : List Nat) : Nat :=
  FiniteFunctionCoding.name s.2.2 2 ss + (bits s.2.2).length *
    (FiniteFunctionCoding.name s.2.1 2 ns + (bits s.2.1).length * a)

def mapLabel (x : Input) (a : Nat) : Nat :=
  join x.1 (base x.2.1 a)
    ((List.range x.1.2.1).map (fun i => node x.2.1 a (x.2.2.1.getD i 0)))
    ((List.range x.1.2.2).map (fun i => set x.2.1 a (x.2.2.2.getD i 0)))

def table (x : Input) : List Nat := (List.range (count x.2.1)).map (mapLabel x)

attribute [local fun_prop] FiniteFunctionCoding.name_primrec

@[fun_prop] theorem join_primrec :
    Primrec (fun x : Shape × Nat × List Nat × List Nat => join x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have hn : Primrec (fun x : Shape × Nat × List Nat × List Nat =>
      FiniteFunctionCoding.name x.1.2.1 2 x.2.2.1) :=
    FiniteFunctionCoding.name_primrec.comp
      (show Primrec (fun x : Shape × Nat × List Nat × List Nat => ((x.1.2.1, 2), x.2.2.1)) by fun_prop)
  have hs : Primrec (fun x : Shape × Nat × List Nat × List Nat =>
      FiniteFunctionCoding.name x.1.2.2 2 x.2.2.2) :=
    FiniteFunctionCoding.name_primrec.comp
      (show Primrec (fun x : Shape × Nat × List Nat × List Nat => ((x.1.2.2, 2), x.2.2.2)) by fun_prop)
  unfold join
  exact Primrec.nat_add.comp hs (Primrec.nat_mul.comp (by fun_prop)
    (Primrec.nat_add.comp hn (Primrec.nat_mul.comp (by fun_prop) (by fun_prop))))
@[fun_prop] theorem mapLabel_primrec : Primrec (fun x : Input × Nat => mapLabel x.1 x.2) := by
  unfold mapLabel
  fun_prop
@[fun_prop] theorem table_primrec : Primrec table := by unfold table; fun_prop

theorem join_encode (s : Shape) (a : ValuationLabel (Fin (s.1 + 1)) s.2.1 s.2.2) :
    join s a.1.val
      (FiniteFunctionCoding.encode (fun i => finTwoEquiv.symm (a.2.1 i)))
      (FiniteFunctionCoding.encode (fun i => finTwoEquiv.symm (a.2.2 i))) = (equiv s a).val := rfl

variable {a n m k l : Nat} (f : Fin n → Fin k) (g : Fin m → Fin l)

def input : Input := ((a,n,m), (a,k,l), FiniteFunctionCoding.encode f, FiniteFunctionCoding.encode g)

theorem mapLabel_correct (label : ValuationLabel (Fin (a+1)) k l) :
    mapLabel (input (a := a) f g) (equiv (a,k,l) label).val =
      (equiv (a,n,m) (renameMarkers f g label)).val := by
  have hn : (List.range n).map (fun i =>
      node (a,k,l) (equiv (a,k,l) label).val ((FiniteFunctionCoding.encode f).getD i 0)) =
      FiniteFunctionCoding.encode (fun i => finTwoEquiv.symm (label.2.1 (f i))) := by
    apply FiniteSearch.tabulate_eq_ofFn
    intro i
    rw [FiniteFunctionCoding.lookup_encode, node_encode]
    dsimp only
    cases label.2.1 (f i) <;> rfl
  have hs : (List.range m).map (fun i =>
      set (a,k,l) (equiv (a,k,l) label).val ((FiniteFunctionCoding.encode g).getD i 0)) =
      FiniteFunctionCoding.encode (fun i => finTwoEquiv.symm (label.2.2 (g i))) := by
    apply FiniteSearch.tabulate_eq_ofFn
    intro i
    rw [FiniteFunctionCoding.lookup_encode, set_encode]
    dsimp only
    cases label.2.2 (g i) <;> rfl
  change join (a,n,m) (base (a,k,l) (equiv (a,k,l) label).val) _ _ = _
  dsimp only [input]
  rw [base_encode, hn, hs]
  exact join_encode (a,n,m) (renameMarkers f g label)

theorem table_correct (label : ValuationLabel (Fin (a+1)) k l) :
    (table (input (a := a) f g)).getD (number (a,k,l) label).val 0 =
      (number (a,n,m) (renameMarkers f g label)).val := by
  change ((List.range (count (a,k,l))).map (mapLabel (input f g))).getD (equiv (a,k,l) label).val 0 = _
  rw [List.getD_eq_getElem _ _ (by
    simpa only [List.length_map, List.length_range] using (equiv (a,k,l) label).isLt)]
  simp only [List.getElem_map, List.getElem_range]
  exact mapLabel_correct f g label

end DistributedSynthesis.MSO.Tree.NumericRenaming
