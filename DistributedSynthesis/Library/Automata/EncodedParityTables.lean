/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.Compilers
import DistributedSynthesis.Library.Computability.FiniteSearch

/-! # Numeric deterministic parity word automata

The four fields are the maximum state index, initial state index, priorities,
and letter-major transition rows. The alphabet is the row index set. Missing
state entries default to zero; initial and successor indices are reduced
modulo the positive state count. All priorities use the min-even convention.
-/

namespace DistributedSynthesis.EncodedParityTables
abbrev Data := Nat × Nat × List Nat × List (List Nat)
def size (d : Data) : Nat := d.1 + 1
def initial (d : Data) : Nat := d.2.1
def priorities (d : Data) : List Nat := d.2.2.1
def rows (d : Data) : List (List Nat) := d.2.2.2
def next (d : Data) (q a : Nat) : Nat := ((rows d).getD a []).getD q 0 % size d
def priority (d : Data) (q : Nat) : Nat := (priorities d).getD q 0

theorem size_primrec : Primrec size := Primrec.succ.comp Primrec.fst
theorem initial_primrec : Primrec initial := Primrec.fst.comp Primrec.snd
theorem priorities_primrec : Primrec priorities := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem rows_primrec : Primrec rows := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
theorem next_primrec : Primrec (fun x : Data × Nat × Nat => next x.1 x.2.1 x.2.2) :=
  Primrec.nat_mod.comp ((Primrec.list_getD 0).comp
    ((Primrec.list_getD []).comp (rows_primrec.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp Primrec.snd)) (size_primrec.comp Primrec.fst)
theorem priority_primrec : Primrec₂ priority :=
  (Primrec.list_getD 0).comp (priorities_primrec.comp Primrec.fst) Primrec.snd

def automaton (d : Data) : DetParityAutomaton (Fin (rows d).length) where
  State := Fin (size d)
  stateFinite := inferInstance
  initial := ⟨initial d % size d, Nat.mod_lt _ (Nat.succ_pos _)⟩
  step q a := ⟨next d q.val a.val, Nat.mod_lt _ (Nat.succ_pos _)⟩
  priority q := priority d q.val

end DistributedSynthesis.EncodedParityTables
