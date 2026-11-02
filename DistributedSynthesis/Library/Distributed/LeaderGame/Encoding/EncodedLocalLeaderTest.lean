/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedThreadStream
import DistributedSynthesis.Library.Automata.EncodedTreeNonemptiness
import DistributedSynthesis.Library.Computability.FiniteCodeNumbering
import DistributedSynthesis.Library.Computability.FiniteFunctionCodes

/-! Generate the entire local leader test from numeric physical-monitor data.
Narrowed labels contain the leader response and every state-indexed follower
response. The existing thread compiler and tree solver are reused unchanged. -/
namespace Characterisation.EncodedLocalLeaderTest
open DistributedSynthesis
attribute [local irreducible] Primrec

abbrev Data := EncodedParityTables.Data × Nat × Nat × Nat × Nat
abbrev Label := List Nat × List Nat
def monitorData (d : Data) := d.1
def receiverInputs (d : Data) := d.2.1
def senderInputs (d : Data) := d.2.2.1
def receiverOutputs (d : Data) := d.2.2.2.1
def senderOutputs (d : Data) := d.2.2.2.2
def physicalSize (d : Data) := receiverInputs d * senderInputs d * (receiverOutputs d * senderOutputs d)
def states (d : Data) := EncodedParityTables.size (monitorData d)
def responseSize (d : Data) := states d * (receiverInputs d * senderInputs d)
def rawLabels (d : Data) : List Label :=
  (FiniteSearch.tables (senderOutputs d) (senderInputs d)).product
    (FiniteSearch.tables (receiverOutputs d) (responseSize d))
def labels (d : Data) := FiniteCodeNumbering.unique (rawLabels d)
def responseIndex (d : Data) (q r s : Nat) := s + senderInputs d*r + (receiverInputs d*senderInputs d)*q
def physicalIndex (d : Data) (r s u v : Nat) :=
  v+senderOutputs d*u+(receiverOutputs d*senderOutputs d)*(s+senderInputs d*r)
def next (d : Data) (q : Nat) (label : Label) (r s : Nat) :=
  EncodedParityTables.next (monitorData d) q
    (physicalIndex d r s (label.2.getD (responseIndex d q r s) 0) (label.1.getD s 0))
def edges (d : Data) (label : Label) (s : Nat) : EncodedThreadBuchi.Edges :=
  (List.range (states d)).flatMap (fun q => (List.range (receiverInputs d)).map (fun r => (q,next d q label r s)))
def priorities (d : Data) := (List.range (states d)).map (EncodedParityTables.priority (monitorData d))
def config (d : Data) : EncodedThreadStream.Config :=
  (states d,EncodedParityTables.initial (monitorData d) % states d,priorities d)
def checkerStates (d : Data) := EncodedThreadStream.size (config d)
def transitions (d : Data) := (List.range (checkerStates d)).flatMap (fun q => (labels d).flatMap
  (fun l => (List.range (senderInputs d)).map (fun s => EncodedThreadStream.next (config d,edges d l s,q))))
def compile (d : Data) : EncodedTreeNonemptiness.Data :=
  (checkerStates d-1,(labels d).length,senderInputs d,transitions d,
    (List.range (checkerStates d)).map (EncodedThreadStream.priority (config d)),EncodedThreadStream.initial (config d))
def solve (d : Data) := EncodedTreeNonemptiness.solve (compile d)

theorem monitorData_primrec : Primrec monitorData := Primrec.fst
theorem receiverInputs_primrec : Primrec receiverInputs := Primrec.fst.comp Primrec.snd
theorem senderInputs_primrec : Primrec senderInputs := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem receiverOutputs_primrec : Primrec receiverOutputs := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem senderOutputs_primrec : Primrec senderOutputs := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem physicalSize_primrec : Primrec physicalSize := Primrec.nat_mul.comp
  (Primrec.nat_mul.comp receiverInputs_primrec senderInputs_primrec)
  (Primrec.nat_mul.comp receiverOutputs_primrec senderOutputs_primrec)
theorem states_primrec : Primrec states := EncodedParityTables.size_primrec.comp monitorData_primrec
theorem responseSize_primrec : Primrec responseSize := Primrec.nat_mul.comp states_primrec
  (Primrec.nat_mul.comp receiverInputs_primrec senderInputs_primrec)
theorem rawLabels_primrec : Primrec rawLabels := FiniteSearch.product_primrec.comp
  (FiniteSearch.tables_primrec.comp senderOutputs_primrec senderInputs_primrec)
  (FiniteSearch.tables_primrec.comp receiverOutputs_primrec responseSize_primrec)
theorem labels_primrec : Primrec labels := FiniteCodeNumbering.unique_primrec.comp rawLabels_primrec

section Composition
variable {X : Type*} [Primcodable X] {d : X → Data} {q r s u v : X → Nat} {l : X → Label}
theorem responseIndex_comp (hd : Primrec d) (hq : Primrec q) (hr : Primrec r) (hs : Primrec s) :
    Primrec (fun x => responseIndex (d x) (q x) (r x) (s x)) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp hs (Primrec.nat_mul.comp (senderInputs_primrec.comp hd) hr))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (receiverInputs_primrec.comp hd) (senderInputs_primrec.comp hd)) hq)
theorem physicalIndex_comp (hd : Primrec d) (hr : Primrec r) (hs : Primrec s) (hu : Primrec u) (hv : Primrec v) :
    Primrec (fun x => physicalIndex (d x) (r x) (s x) (u x) (v x)) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp hv (Primrec.nat_mul.comp (senderOutputs_primrec.comp hd) hu))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (receiverOutputs_primrec.comp hd) (senderOutputs_primrec.comp hd))
      (Primrec.nat_add.comp hs (Primrec.nat_mul.comp (senderInputs_primrec.comp hd) hr)))
theorem next_comp (hd : Primrec d) (hq : Primrec q) (hl : Primrec l) (hr : Primrec r) (hs : Primrec s) :
    Primrec (fun x => next (d x) (q x) (l x) (r x) (s x)) :=
  EncodedParityTables.next_primrec.comp ((monitorData_primrec.comp hd).pair (hq.pair
    (physicalIndex_comp hd hr hs
      ((Primrec.list_getD 0).comp (Primrec.snd.comp hl) (responseIndex_comp hd hq hr hs))
      ((Primrec.list_getD 0).comp (Primrec.fst.comp hl) hs))))
end Composition

theorem edges_primrec : Primrec (fun x : Data × Label × Nat => edges x.1 x.2.1 x.2.2) :=
  Primrec.list_flatMap (Primrec.list_range.comp (states_primrec.comp Primrec.fst))
    (Primrec.list_map (Primrec.list_range.comp (receiverInputs_primrec.comp (Primrec.fst.comp Primrec.fst)))
      ((Primrec.snd.comp Primrec.fst).pair (next_comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))).to₂).to₂
theorem priorities_primrec : Primrec priorities := Primrec.list_map (Primrec.list_range.comp states_primrec)
  (EncodedParityTables.priority_primrec.comp (monitorData_primrec.comp Primrec.fst) Primrec.snd).to₂
theorem config_primrec : Primrec config := states_primrec.pair
  ((Primrec.nat_mod.comp (EncodedParityTables.initial_primrec.comp monitorData_primrec) states_primrec).pair priorities_primrec)
theorem checkerStates_primrec : Primrec checkerStates := EncodedThreadStream.size_primrec.comp config_primrec
theorem transitions_primrec : Primrec transitions := by
  have entry : Primrec (fun x : ((Data × Nat) × Label) × Nat =>
      EncodedThreadStream.next (config x.1.1.1,edges x.1.1.1 x.1.2 x.2,x.1.1.2)) :=
    EncodedThreadStream.next_primrec.comp
      ((config_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
        ((edges_primrec.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
  have row := Primrec.list_map
    (Primrec.list_range.comp (senderInputs_primrec.comp (Primrec.fst.comp Primrec.fst))) entry.to₂
  have layers := Primrec.list_flatMap (labels_primrec.comp Primrec.fst) row.to₂
  exact Primrec.list_flatMap (Primrec.list_range.comp checkerStates_primrec) layers.to₂
theorem compile_primrec : Primrec compile :=
  (Primrec.nat_sub.comp checkerStates_primrec (Primrec.const 1)).pair
    ((Primrec.list_length.comp labels_primrec).pair (senderInputs_primrec.pair
      (transitions_primrec.pair ((Primrec.list_map (Primrec.list_range.comp checkerStates_primrec)
        (EncodedThreadStream.priority_primrec.comp (config_primrec.comp Primrec.fst) Primrec.snd).to₂).pair
        (EncodedThreadStream.initial_primrec.comp config_primrec)))))
theorem solve_primrec : Primrec solve := EncodedTreeNonemptiness.solve_primrec.comp compile_primrec

end Characterisation.EncodedLocalLeaderTest
