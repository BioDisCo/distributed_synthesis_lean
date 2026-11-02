/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedJournalTransitions
import DistributedSynthesis.Library.Automata.EncodedTreeNonemptiness

/-! # Uniform numeric journal tables

The lists enumerate all finite states, labels, and branches. State names use
duplicate-safe list numbering. The correctness connection to the semantic
journal is proved separately; no semantic strategy is used to construct data.
-/
namespace DistributedSynthesis.EncodedJournalTables
open EncodedRoundObjectives EncodedJournalMachines EncodedJournalTransitions

def ordinaryStates (d : Data) :=
  (List.range (ordinarySize d)).product (FiniteSetCodes.codes (EncodedChainThreads.atomCount d))
def chainStates (d : Data) := (List.range (chainSize d)).product
  ((FiniteSetCodes.codes (EncodedChainThreads.chainCount d)).product (FiniteSetCodes.codes (EncodedChainThreads.chainCount d)))
def rawStates (d : Data) : List State :=
  (List.range (EncodedChainThreads.atomCount d)).map (fun q => (0,q,[],[])) ++
  (ordinaryStates d).map (fun q => (1,q.1,q.2,[])) ++
  (ordinaryStates d).map (fun q => (2,q.1,q.2,[])) ++
  (chainStates d).map (fun q => (3,q.1,q.2.1,q.2.2)) ++
  (chainStates d).map (fun q => (4,q.1,q.2.1,q.2.2)) ++ [sink]
@[irreducible] def states (d : Data) := FiniteCodeNumbering.unique (rawStates d)
def name (d : Data) (q : State) := FiniteCodeNumbering.name (rawStates d) q
@[irreducible] def labels (d : Data) := EncodedJournalLabels.allCodes
  (stateCount d,inputOne d,inputTwo d,outputOne d,outputTwo d)
def branches (d : Data) : List Branch :=
  (List.range (EncodedChainThreads.atomCount d)).map (fun q => (0,q)) ++
  (List.range (inputTwo d)).map (fun j => (1,j)) ++ (List.range (inputOne d)).map (fun i => (2,i))
def transitions (d : Data) := (states d).flatMap (fun q => (labels d).flatMap
  (fun c => (branches d).map (fun b => name d (step (d,q,c,b)))))
def compile (d : Data) : EncodedTreeNonemptiness.Data :=
  ((states d).length-1,(labels d).length,(branches d).length,transitions d,
    (states d).map (priority d),name d (initial d))

theorem ordinaryStates_primrec : Primrec ordinaryStates := FiniteSearch.product_primrec.comp
  (Primrec.list_range.comp ordinarySize_primrec) (FiniteSetCodes.codes_primrec.comp EncodedChainThreads.atomCount_primrec)
theorem chainStates_primrec : Primrec chainStates := FiniteSearch.product_primrec.comp
  (Primrec.list_range.comp chainSize_primrec) (FiniteSearch.product_primrec.comp
    (FiniteSetCodes.codes_primrec.comp EncodedChainThreads.chainCount_primrec)
    (FiniteSetCodes.codes_primrec.comp EncodedChainThreads.chainCount_primrec))
theorem rawStates_primrec : Primrec rawStates := by
  have ha : Primrec (fun d => (List.range (EncodedChainThreads.atomCount d)).map
      (fun q => (0,q,[],[]) : Nat → State)) := Primrec.list_map
    (Primrec.list_range.comp EncodedChainThreads.atomCount_primrec)
    ((Primrec.const 0).pair (Primrec.snd.pair ((Primrec.const []).pair (Primrec.const [])))).to₂
  have ho (tag : Nat) : Primrec (fun d => (ordinaryStates d).map (fun q => (tag,q.1,q.2,[]) : Nat × List Nat → State)) :=
    Primrec.list_map ordinaryStates_primrec ((Primrec.const tag).pair
      ((Primrec.fst.comp Primrec.snd).pair ((Primrec.snd.comp Primrec.snd).pair (Primrec.const [])))).to₂
  have hc (tag : Nat) : Primrec (fun d => (chainStates d).map (fun q => (tag,q.1,q.2.1,q.2.2) : Nat × List Nat × List Nat → State)) :=
    Primrec.list_map chainStates_primrec ((Primrec.const tag).pair Primrec.snd).to₂
  exact Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp
    (Primrec.list_append.comp (Primrec.list_append.comp ha (ho 1)) (ho 2)) (hc 3)) (hc 4)) (Primrec.const [sink])
theorem states_primrec : Primrec states := by
  unfold states
  exact FiniteCodeNumbering.unique_primrec.comp rawStates_primrec
theorem name_primrec : Primrec₂ name := FiniteCodeNumbering.name_primrec.comp
  (rawStates_primrec.comp Primrec.fst) Primrec.snd
theorem labels_primrec : Primrec labels := by
  unfold labels
  exact EncodedJournalLabels.allCodes_primrec.comp (stateCount_primrec.pair
    (inputOne_primrec.pair (inputTwo_primrec.pair (outputOne_primrec.pair outputTwo_primrec))))
theorem branches_primrec : Primrec branches := by
  have hm {f : Data → Nat} (hf : Primrec f) (tag : Nat) :
      Primrec (fun d => (List.range (f d)).map (fun q => (tag,q))) :=
    Primrec.list_map (Primrec.list_range.comp hf) ((Primrec.const tag).pair Primrec.snd).to₂
  exact Primrec.list_append.comp (Primrec.list_append.comp
    (hm EncodedChainThreads.atomCount_primrec 0) (hm inputTwo_primrec 1)) (hm inputOne_primrec 2)
theorem transitions_primrec : Primrec transitions := by
  apply Primrec.list_flatMap states_primrec
  change Primrec (fun x : Data × State => (labels x.1).flatMap
    (fun c => (branches x.1).map (fun b => name x.1 (step (x.1,x.2,c,b)))))
  apply Primrec.list_flatMap (labels_primrec.comp Primrec.fst)
  change Primrec (fun x : (Data × State) × EncodedJournalLabels.Code => (branches x.1.1).map
    (fun b => name x.1.1 (step (x.1.1,x.1.2,x.2,b))))
  apply Primrec.list_map (branches_primrec.comp (Primrec.fst.comp Primrec.fst))
  have hd : Primrec (fun x : ((Data × State) × EncodedJournalLabels.Code) × Branch => x.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  exact (name_primrec.comp hd (step_primrec.comp (hd.pair
    ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))))).to₂
theorem compile_primrec : Primrec compile :=
  (Primrec.nat_sub.comp (Primrec.list_length.comp states_primrec) (Primrec.const 1)).pair
    ((Primrec.list_length.comp labels_primrec).pair ((Primrec.list_length.comp branches_primrec).pair
      (transitions_primrec.pair ((Primrec.list_map states_primrec priority_primrec).pair
        (name_primrec.comp Primrec.id initial_primrec)))))
end DistributedSynthesis.EncodedJournalTables
