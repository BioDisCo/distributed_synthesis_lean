/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedScheduledCollector

/-! Restrict all collector data along one list of source roots. The same
selection is applied to observations, promises, labels, graph states, and
predecessor slots. Hypothetical words and physical depths are unchanged. -/
namespace Characterisation.EncodedClosingRestriction
open DistributedSynthesis
open EncodedClosingLayers (Slot)
attribute [local irreducible] Primrec

def gather {α : Type} (fallback : α) (xs : List α) (keep : List Nat) :=
  keep.map (fun i => xs.getD i fallback)
def mapSlot (keep : List Nat) (s : Slot) : Slot := (keep.getD s.1 0,s.2)
def matrix (d : EncodedClosingBanks.Data) (keep : List Nat) :=
  (List.range (keep.length*keep.length)).map (fun i =>
    (EncodedClosingBanks.matrix d).getD
      (keep.getD (i%keep.length) 0 + EncodedClosingBanks.roots d*keep.getD (i/keep.length) 0) (false,false))
def bankData (d : EncodedClosingBanks.Data) (keep : List Nat) : EncodedClosingBanks.Data :=
  (keep.length,EncodedClosingBanks.context d,EncodedClosingBanks.roundTable d,
    EncodedClosingBanks.outputTable d,matrix d keep)
def replayData (d : EncodedScheduledCollector.ReplayData) (keep : List Nat) : EncodedScheduledCollector.ReplayData :=
  (bankData d.1 keep,gather [] (EncodedScheduledCollector.bank d) keep,
    EncodedScheduledCollector.outputs d,EncodedScheduledCollector.monitor d,
    gather 0 (EncodedScheduledCollector.initial d) keep)
def context (c : EncodedClosingLayers.Context) (keep : List Nat) : EncodedClosingLayers.Context :=
  (keep.length,c.2)
def graphData (d : EncodedClosingScans.Data) (keep : List Nat) : EncodedClosingScans.Data :=
  (context d.1 keep,EncodedClosingScans.rules d,EncodedClosingScans.graphs d,
    gather 0 (EncodedClosingScans.source d) keep)
def scan (c : EncodedClosingLayers.Context) (table keep : List Nat) :=
  (EncodedClosingScans.domain (context c keep)).map (fun s =>
    EncodedClosingScans.entry c table (mapSlot keep s))
def apply (d : EncodedScheduledCollector.Data) (keep : List Nat) : EncodedScheduledCollector.Data :=
  (replayData d.1 keep,gather 0 (EncodedScheduledCollector.parents d) keep,
    EncodedScheduledCollector.minima d,graphData (EncodedScheduledCollector.graphData d) keep,
    scan (EncodedScheduledCollector.graphData d).1 (EncodedScheduledCollector.scan d) keep,
    EncodedScheduledCollector.firstWindow d,EncodedScheduledCollector.width d)

theorem gather_primrec {α : Type} [Primcodable α] (fallback : α) : Primrec₂ (gather fallback) :=
  Primrec.list_map Primrec.snd ((Primrec.list_getD fallback).comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
theorem mapSlot_primrec : Primrec₂ mapSlot :=
  ((Primrec.list_getD 0).comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)
theorem matrix_primrec : Primrec₂ matrix := by
  have len : Primrec (fun x : EncodedClosingBanks.Data × List Nat => x.2.length) := Primrec.list_length.comp Primrec.snd
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp len len))
  have hd : Primrec (fun x : (EncodedClosingBanks.Data × List Nat) × Nat => x.1.1) := Primrec.fst.comp Primrec.fst
  have hk : Primrec (fun x : (EncodedClosingBanks.Data × List Nat) × Nat => x.1.2) := Primrec.snd.comp Primrec.fst
  have hl := Primrec.list_length.comp hk
  exact (Primrec.list_getD (false,false)).comp (EncodedClosingBanks.matrix_primrec.comp hd)
    (Primrec.nat_add.comp ((Primrec.list_getD 0).comp hk (Primrec.nat_mod.comp Primrec.snd hl))
      (Primrec.nat_mul.comp (EncodedClosingBanks.roots_primrec.comp hd)
        ((Primrec.list_getD 0).comp hk (Primrec.nat_div.comp Primrec.snd hl))))
theorem bankData_primrec : Primrec₂ bankData :=
  (Primrec.list_length.comp Primrec.snd).pair
    ((EncodedClosingBanks.context_primrec.comp Primrec.fst).pair
      ((EncodedClosingBanks.roundTable_primrec.comp Primrec.fst).pair
        ((EncodedClosingBanks.outputTable_primrec.comp Primrec.fst).pair matrix_primrec)))
theorem replayData_primrec : Primrec₂ replayData :=
  (bankData_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
    ((gather_primrec []).comp (EncodedScheduledCollector.bank_primrec.comp Primrec.fst) Primrec.snd |>.pair
      ((EncodedScheduledCollector.outputs_primrec.comp Primrec.fst).pair
        ((EncodedScheduledCollector.monitor_primrec.comp Primrec.fst).pair
          ((gather_primrec 0).comp (EncodedScheduledCollector.initial_primrec.comp Primrec.fst) Primrec.snd))))
theorem context_primrec : Primrec₂ context := (Primrec.list_length.comp Primrec.snd).pair (Primrec.snd.comp Primrec.fst)
theorem graphData_primrec : Primrec₂ graphData :=
  (context_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
    ((EncodedClosingScans.rules_primrec.comp Primrec.fst).pair
      ((EncodedClosingScans.graphs_primrec.comp Primrec.fst).pair
        ((gather_primrec 0).comp (EncodedClosingScans.source_primrec.comp Primrec.fst) Primrec.snd)))
theorem scan_primrec : Primrec (fun x : EncodedClosingLayers.Context × List Nat × List Nat => scan x.1 x.2.1 x.2.2) :=
  Primrec.list_map (EncodedClosingScans.domain_primrec.comp (context_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))
    (EncodedClosingScans.entry_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        (mapSlot_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)))).to₂
theorem apply_primrec : Primrec₂ apply :=
  (replayData_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
    (((gather_primrec 0).comp (EncodedScheduledCollector.parents_primrec.comp Primrec.fst) Primrec.snd).pair
      ((EncodedScheduledCollector.minima_primrec.comp Primrec.fst).pair
        ((graphData_primrec.comp (EncodedScheduledCollector.graphData_primrec.comp Primrec.fst) Primrec.snd).pair
          ((scan_primrec.comp
            ((Primrec.fst.comp (EncodedScheduledCollector.graphData_primrec.comp Primrec.fst)).pair
              ((EncodedScheduledCollector.scan_primrec.comp Primrec.fst).pair Primrec.snd))).pair
            ((EncodedScheduledCollector.firstWindow_primrec.comp Primrec.fst).pair
              (EncodedScheduledCollector.width_primrec.comp Primrec.fst))))))

end Characterisation.EncodedClosingRestriction
