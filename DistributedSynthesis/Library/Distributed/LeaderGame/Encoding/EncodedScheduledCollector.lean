/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingBanks
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingReplay
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingSchedule
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingLayerOffers

/-! Generate the complete scheduled collector from source banks and a graph
scan. Layer matrices, replayed labels, predecessor slots, and minima are
computed here, rather than supplied as precomputed layer tables. -/
namespace Characterisation.EncodedScheduledCollector
open DistributedSynthesis
open EncodedClosingLayers (Slot)
attribute [local irreducible] Primrec

/-- Bank decoding data, promised outputs, output alphabet size, replay
transition table, and initial replay states. -/
abbrev ReplayData := EncodedClosingBanks.Data × EncodedClosingBanks.Bank × Nat × EncodedParityTables.Data × List Nat
def bankData (d : ReplayData) := d.1
def bank (d : ReplayData) := d.2.1
def outputs (d : ReplayData) := d.2.2.1
def monitor (d : ReplayData) := d.2.2.2.1
def initial (d : ReplayData) := d.2.2.2.2
def label (d : ReplayData) (s : Slot) := EncodedClosingReplay.replay (monitor d)
  ((initial d).getD s.1 0)
  (EncodedClosingBanks.context (bankData d),outputs d,(bank d).getD s.1 [],s.2)

/-- Replay data, predecessor slots, state minima, graph data, graph scan,
initial-window flag, and target-width bound. -/
abbrev Data := ReplayData × List Nat × List Nat × EncodedClosingScans.Data × List Nat × Bool × Nat
def replayData (d : Data) := d.1
def parents (d : Data) := d.2.1
def minima (d : Data) := d.2.2.1
def graphData (d : Data) := d.2.2.2.1
def scan (d : Data) := d.2.2.2.2.1
def firstWindow (d : Data) := d.2.2.2.2.2.1
def width (d : Data) := d.2.2.2.2.2.2
def layerContext (d : Data) (n : Nat) : EncodedClosingLayers.Context :=
  (EncodedClosingBanks.roots (bankData d.1),(EncodedClosingBanks.context (bankData d.1)).1,n)
def slots (d : Data) (n : Nat) := EncodedClosingLayers.slots (layerContext d n)
def views (d : Data) (n : Nat) : List EncodedClosingObservations.Views :=
  let layer := slots d n
  (List.range (layer.length*layer.length)).map (fun i =>
    EncodedClosingBanks.observed (bankData d.1)
      (layer.getD (i/layer.length) (0,[])) (layer.getD (i%layer.length) (0,[])))
def layer (d : Data) (n : Nat) : EncodedClosingLayerOffers.Data :=
  let xs := slots d n
  ((xs.length,views d n,xs.map (EncodedClosingScans.live (graphData d) (scan d))),width d,
    xs.map (EncodedClosingScans.eligible (graphData d) (scan d) (firstWindow d)),
    xs.map (label d.1),xs.map (fun s => (parents d).getD s.1 0),
    xs.map (fun s => (minima d).getD (label d.1 s) 0))
def layerData (d : Data) : Bool × List EncodedClosingLayerOffers.Data :=
  (EncodedClosingBanks.coherent (bankData d.1) (bank d.1),
    (List.range (EncodedClosingBanks.context (bankData d.1)).2).map (fun n => layer d (n+1)))
def collect (d : Data) := EncodedClosingLayerOffers.collect (layerData d)

theorem bankData_primrec : Primrec bankData := Primrec.fst
theorem bank_primrec : Primrec bank := Primrec.fst.comp Primrec.snd
theorem outputs_primrec : Primrec outputs := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem monitor_primrec : Primrec monitor := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem initial_primrec : Primrec initial := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem label_primrec : Primrec₂ label := EncodedClosingReplay.replay_primrec.comp
  ((monitor_primrec.comp Primrec.fst).pair
    (((Primrec.list_getD 0).comp (initial_primrec.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      ((EncodedClosingBanks.context_primrec.comp (bankData_primrec.comp Primrec.fst)).pair
        ((outputs_primrec.comp Primrec.fst).pair
          (((Primrec.list_getD []).comp (bank_primrec.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
            (Primrec.snd.comp Primrec.snd))))))
theorem parents_primrec : Primrec parents := Primrec.fst.comp Primrec.snd
theorem minima_primrec : Primrec minima := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem graphData_primrec : Primrec graphData := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem scan_primrec : Primrec scan := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
theorem firstWindow_primrec : Primrec firstWindow := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
theorem width_primrec : Primrec width := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
theorem layerContext_primrec : Primrec₂ layerContext :=
  (EncodedClosingBanks.roots_primrec.comp (bankData_primrec.comp (Primrec.fst.comp Primrec.fst))).pair
    ((Primrec.fst.comp (EncodedClosingBanks.context_primrec.comp (bankData_primrec.comp (Primrec.fst.comp Primrec.fst)))).pair Primrec.snd)
theorem slots_primrec : Primrec₂ slots := EncodedClosingLayers.slots_primrec.comp layerContext_primrec
theorem views_primrec : Primrec₂ views := by
  have length := Primrec.list_length.comp slots_primrec
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp length length))
  have xs : Primrec (fun x : (Data × Nat) × Nat => slots x.1.1 x.1.2) :=
    slots_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have len := Primrec.list_length.comp xs
  exact EncodedClosingBanks.observed_primrec.comp
    ((bankData_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
      (((Primrec.list_getD (0,[])).comp xs (Primrec.nat_div.comp Primrec.snd len)).pair
        ((Primrec.list_getD (0,[])).comp xs (Primrec.nat_mod.comp Primrec.snd len))))
theorem layer_primrec : Primrec₂ layer := by
  have hd : Primrec (fun x : Data × Nat => x.1) := Primrec.fst
  have hg := graphData_primrec.comp hd
  have hs := scan_primrec.comp hd
  have xs : Primrec (fun x : Data × Nat => slots x.1 x.2) := slots_primrec
  have hv : Primrec (fun x : Data × Nat => views x.1 x.2) := views_primrec
  have alive := Primrec.list_map xs
    (EncodedClosingScans.live_primrec.comp ((hg.comp Primrec.fst).pair
      ((hs.comp Primrec.fst).pair Primrec.snd))).to₂
  have exits := Primrec.list_map xs
    (EncodedClosingScans.eligible_primrec.comp ((hg.comp Primrec.fst).pair
      ((hs.comp Primrec.fst).pair
        ((firstWindow_primrec.comp (hd.comp Primrec.fst)).pair Primrec.snd)))).to₂
  have labels := Primrec.list_map xs
    (label_primrec.comp (Primrec.fst.comp (hd.comp Primrec.fst)) Primrec.snd).to₂
  have parent := Primrec.list_map xs
    ((Primrec.list_getD 0).comp (parents_primrec.comp (hd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)).to₂
  have minimum := Primrec.list_map xs
    ((Primrec.list_getD 0).comp (minima_primrec.comp (hd.comp Primrec.fst))
      (label_primrec.comp (Primrec.fst.comp (hd.comp Primrec.fst)) Primrec.snd)).to₂
  exact ((Primrec.list_length.comp xs).pair (hv.pair alive)).pair
    ((width_primrec.comp hd).pair (exits.pair (labels.pair (parent.pair minimum))))
theorem layerData_primrec : Primrec layerData :=
  (EncodedClosingBanks.coherent_primrec.comp (bankData_primrec.comp Primrec.fst) (bank_primrec.comp Primrec.fst)).pair
    (Primrec.list_map (Primrec.list_range.comp
      (Primrec.snd.comp (EncodedClosingBanks.context_primrec.comp (bankData_primrec.comp Primrec.fst))))
      (layer_primrec.comp Primrec.fst (Primrec.succ.comp Primrec.snd)).to₂)
theorem collect_primrec : Primrec collect := EncodedClosingLayerOffers.collect_primrec.comp layerData_primrec

end Characterisation.EncodedScheduledCollector
