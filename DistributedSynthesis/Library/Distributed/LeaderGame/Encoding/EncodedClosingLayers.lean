/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.FiniteCodeNumbering
import DistributedSynthesis.Library.Computability.FiniteFunctionCodes

/-! Uniform numbering of every hypothetical closing layer, including depth
zero. A slot contains one source root and the complete environment word. -/
namespace Characterisation.EncodedClosingLayers
open DistributedSynthesis
attribute [local irreducible] Primrec

abbrev Context := Nat × Nat × Nat
abbrev Slot := Nat × List Nat
def raw (c : Context) := (List.range c.1).product (FiniteSearch.tables c.2.1 c.2.2)
@[irreducible] def slots (c : Context) := FiniteCodeNumbering.unique (raw c)
def name (c : Context) (s : Slot) := FiniteCodeNumbering.name (raw c) s
def count (c : Context) := (slots c).length
theorem raw_primrec : Primrec raw := FiniteSearch.product_primrec.comp
  (Primrec.list_range.comp Primrec.fst)
  (FiniteSearch.tables_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
theorem slots_primrec : Primrec slots := by
  unfold slots
  exact FiniteCodeNumbering.unique_primrec.comp raw_primrec
theorem name_primrec : Primrec₂ name := FiniteCodeNumbering.name_primrec.comp (raw_primrec.comp Primrec.fst) Primrec.snd
theorem count_primrec : Primrec count := Primrec.list_length.comp slots_primrec

end Characterisation.EncodedClosingLayers
