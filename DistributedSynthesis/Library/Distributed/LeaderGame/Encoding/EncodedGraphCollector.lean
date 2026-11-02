/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingRestriction

/-! Generate the full graph-coupled closing collector: retain the active
source roots, enumerate every checked graph scan, and collect every complete
closing choice in its scheduled first-exit layers. -/
namespace Characterisation.EncodedGraphCollector
open DistributedSynthesis
attribute [local irreducible] Primrec

abbrev Data := EncodedScheduledCollector.Data × List Bool
def roots (d : Data) := EncodedClosingBanks.roots (EncodedScheduledCollector.bankData d.1.1)
def raw (d : Data) := (List.range (roots d)).filter (fun i => d.2.getD i false)
@[irreducible] def keep (d : Data) := FiniteCodeNumbering.unique (raw d)
def withScan (d : EncodedScheduledCollector.Data) (table : List Nat) : EncodedScheduledCollector.Data :=
  (d.1,EncodedScheduledCollector.parents d,EncodedScheduledCollector.minima d,
    EncodedScheduledCollector.graphData d,table,EncodedScheduledCollector.firstWindow d,EncodedScheduledCollector.width d)
def collect (d : Data) :=
  (EncodedClosingScans.scans (EncodedScheduledCollector.graphData d.1)).flatMap (fun table =>
    EncodedScheduledCollector.collect (EncodedClosingRestriction.apply (withScan d.1 table) (keep d)))

theorem roots_primrec : Primrec roots := EncodedClosingBanks.roots_primrec.comp
  (EncodedScheduledCollector.bankData_primrec.comp (Primrec.fst.comp Primrec.fst))
theorem raw_primrec : Primrec raw := by
  have h : PrimrecRel (fun d : Data => fun i => d.2.getD i false = true) :=
    Primrec.eq.comp ((Primrec.list_getD false).comp (Primrec.snd.comp Primrec.fst) Primrec.snd) (Primrec.const true)
  exact (h.swap.listFilter.comp (Primrec.list_range.comp roots_primrec) Primrec.id).of_eq
    (fun _ => by simp [raw,Function.swap])
theorem keep_primrec : Primrec keep := by
  unfold keep
  exact FiniteCodeNumbering.unique_primrec.comp raw_primrec
theorem withScan_primrec : Primrec₂ withScan :=
  (Primrec.fst.comp Primrec.fst).pair
    ((EncodedScheduledCollector.parents_primrec.comp Primrec.fst).pair
      ((EncodedScheduledCollector.minima_primrec.comp Primrec.fst).pair
        ((EncodedScheduledCollector.graphData_primrec.comp Primrec.fst).pair
          (Primrec.snd.pair ((EncodedScheduledCollector.firstWindow_primrec.comp Primrec.fst).pair
            (EncodedScheduledCollector.width_primrec.comp Primrec.fst))))))
theorem collect_primrec : Primrec collect :=
  Primrec.list_flatMap (EncodedClosingScans.scans_primrec.comp
    (EncodedScheduledCollector.graphData_primrec.comp Primrec.fst))
    (EncodedScheduledCollector.collect_primrec.comp
      (EncodedClosingRestriction.apply_primrec.comp
        (withScan_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (keep_primrec.comp Primrec.fst))).to₂

end Characterisation.EncodedGraphCollector
