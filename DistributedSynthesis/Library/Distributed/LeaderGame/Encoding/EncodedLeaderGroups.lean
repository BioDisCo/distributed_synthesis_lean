/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.FiniteCodeNumbering
import DistributedSynthesis.Library.Computability.FiniteFunctionCodes

/-! Effective leader groups are precisely distinct observation-matrix rows.
One table entry is communicated per group, then read consistently by all
roots belonging to that group. -/
namespace Characterisation.EncodedLeaderGroups
open DistributedSynthesis
attribute [local irreducible] Primrec

abbrev Data := Nat × List Nat
def roots (d : Data) := d.1
def matrix (d : Data) := d.2
def row (d : Data) (h : Nat) := (List.range (roots d)).map (fun k => (matrix d).getD (k+roots d*h) 0)
def rows (d : Data) := (List.range (roots d)).map (row d)
def groups (d : Data) := FiniteCodeNumbering.unique (rows d)
def count (d : Data) := (groups d).length
def name (d : Data) (h : Nat) := FiniteCodeNumbering.name (rows d) (row d h)
def assignment (d : Data) := (List.range (roots d)).map (name d)
def outputs (d : Data) (table : List Nat) := (List.range (roots d)).map (fun h => table.getD (name d h) 0)

theorem roots_primrec : Primrec roots := Primrec.fst
theorem matrix_primrec : Primrec matrix := Primrec.snd
theorem row_primrec : Primrec₂ row :=
  Primrec.list_map (Primrec.list_range.comp (roots_primrec.comp Primrec.fst))
    ((Primrec.list_getD 0).comp (matrix_primrec.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.nat_add.comp Primrec.snd (Primrec.nat_mul.comp
        (roots_primrec.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst)))).to₂
theorem rows_primrec : Primrec rows := Primrec.list_map (Primrec.list_range.comp roots_primrec) row_primrec.to₂
theorem groups_primrec : Primrec groups := FiniteCodeNumbering.unique_primrec.comp rows_primrec
theorem count_primrec : Primrec count := Primrec.list_length.comp groups_primrec
theorem name_primrec : Primrec₂ name := FiniteCodeNumbering.name_primrec.comp (rows_primrec.comp Primrec.fst) row_primrec
theorem assignment_primrec : Primrec assignment := Primrec.list_map (Primrec.list_range.comp roots_primrec) name_primrec.to₂
theorem outputs_primrec : Primrec₂ outputs :=
  Primrec.list_map (Primrec.list_range.comp (roots_primrec.comp Primrec.fst))
    ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst)
      (name_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂

end Characterisation.EncodedLeaderGroups
