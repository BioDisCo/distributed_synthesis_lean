/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingPlans
import DistributedSynthesis.Library.Automata.EncodedParityTables

/-! Bounded physical replay of a closing plan. Each transition reads the
output promised for the exact prefix ending at that round. The state table
may carry graph state, objective state, and a segment minimum together. -/
namespace Characterisation.EncodedClosingReplay
open DistributedSynthesis
open EncodedClosingPlans
attribute [local irreducible] Primrec

/-- Scenario context, output count, plan, and environment word. -/
abbrev Input := Context × Nat × Plan × List Nat
def letters (x : Input) : List Nat := (List.range x.2.2.2.length).map (fun i =>
  x.2.2.2.getD i 0 * x.2.1 + entry x.1 x.2.2.1 (x.2.2.2.take (i+1)))
def replay (d : EncodedParityTables.Data) (start : Nat) (x : Input) : Nat :=
  (letters x).foldl (EncodedParityTables.next d) start

theorem letters_primrec : Primrec letters := by
  apply Primrec.list_map (Primrec.list_range.comp
    (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hx : Primrec (fun x : Input × Nat => x.1) := Primrec.fst
  have hw : Primrec (fun x : Input × Nat => x.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hx))
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp ((Primrec.list_getD 0).comp hw Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp hx)))
    (entry_primrec.comp ((Primrec.fst.comp hx).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hx))).pair
        (Primrec.list_take.comp (Primrec.succ.comp Primrec.snd) hw))))

theorem replay_primrec : Primrec (fun x : EncodedParityTables.Data × Nat × Input => replay x.1 x.2.1 x.2.2) :=
  Primrec.list_foldl (letters_primrec.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp Primrec.snd)
    (EncodedParityTables.next_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

end Characterisation.EncodedClosingReplay
