/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphCollector
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderMemory

/-! Concrete joint graph memory. The collector template stores the fixed
bank alphabet, graph rules, annotation transition table, source slots, and
width. Graph rules, successor and stopping tables are fixed adversary data.
Every memory update and closing restriction is generated from these data. -/
namespace Characterisation.EncodedGraphMemory
open DistributedSynthesis
attribute [local irreducible] Primrec

abbrev Data := EncodedScheduledCollector.Data × List Nat × List Bool × Nat
abbrev State := (List Nat × List Bool × List Nat) × EncodedClosingBanks.Bank × Bool
abbrev Letter := Nat × List Nat × EncodedClosingBanks.Bank
local instance : Primcodable Data := inferInstance
local instance : Primcodable State := inferInstance
local instance : Primcodable Letter := inferInstance
local instance numericLetterBEq : BEq Letter := instBEqOfDecidableEq
def template (d : Data) := d.1
def successors (d : Data) := d.2.1
def stops (d : Data) := d.2.2.1
def maxPriority (d : Data) := d.2.2.2
def bankData (d : Data) := EncodedScheduledCollector.bankData (template d).1
def roots (d : Data) := EncodedClosingBanks.roots (bankData d)
def outputs (d : Data) := EncodedScheduledCollector.outputs (template d).1
def annotation (d : Data) := EncodedScheduledCollector.monitor (template d).1
def graphData (d : Data) := EncodedScheduledCollector.graphData (template d)
def outcomeContext (d : Data) : EncodedLeaderAlphabet.Context :=
  (EncodedScheduledCollector.width (template d),EncodedParityTables.size (annotation d),maxPriority d)
def refined (b : EncodedClosingBanks.Data) : EncodedClosingBanks.Data :=
  (b.1,b.2.1,b.2.2.1,b.2.2.2.1,(EncodedClosingBanks.matrix b).map (fun v => (v.1,v.2 && v.1)))
def currentBankData (d : Data) (first : Bool) := if first then bankData d else refined (bankData d)
def initial (d : Data) : State :=
  ((EncodedClosingScans.source (graphData d),(List.range (roots d)).map (fun _ => true),
    EncodedScheduledCollector.initial (template d).1),EncodedScheduledCollector.bank (template d).1,true)
def rawStates (d : Data) : List State :=
  ((FiniteSearch.tables (EncodedClosingScans.rules (graphData d)).1 (roots d)).product
    ((FiniteSearch.words [false,true] (roots d)).product
      (FiniteSearch.tables (EncodedParityTables.size (annotation d)) (roots d)))).product
    ((EncodedClosingBanks.banks (bankData d) (outputs d)).product [false,true])
def states (d : Data) := FiniteCodeNumbering.unique (rawStates d)
def name (d : Data) (q : State) := FiniteCodeNumbering.name (rawStates d) q
def letters (d : Data) : List Letter :=
  (List.range (EncodedClosingBanks.context (bankData d)).1).product
    ((FiniteSearch.tables (outputs d) (roots d)).product (EncodedClosingBanks.banks (bankData d) (outputs d)))
def next (d : Data) (q : State) (a : Letter) : State :=
  (((q.1.1).map (fun g => (successors d).getD g 0),
    (List.range (roots d)).map (fun h => (q.1.2.1).getD h false && !(stops d).getD ((q.1.1).getD h 0) false),
    (List.range (roots d)).map (fun h => EncodedParityTables.next (annotation d) ((q.1.2.2).getD h 0)
      (a.1*outputs d+(a.2.1).getD h 0))),a.2.2,false)
def collector (d : Data) (q : State) : EncodedGraphCollector.Data :=
  (((currentBankData d q.2.2,q.2.1,outputs d,annotation d,q.1.2.2),
    EncodedScheduledCollector.parents (template d),EncodedScheduledCollector.minima (template d),
    ((graphData d).1,EncodedClosingScans.rules (graphData d),EncodedClosingScans.graphs (graphData d),q.1.1),
    [],q.2.2,EncodedScheduledCollector.width (template d)),q.1.2.1)
def rolling (d : Data) (q : State) (a : Letter) :=
  EncodedLeaderMemory.check (currentBankData d q.2.2,refined (bankData d))
    (q.2.1,a.2.2,a.1,(a.2.1).map (fun o => (EncodedClosingBanks.outputTable (bankData d)).getD o (0,0)))
/-- Test every complete numbered outcome. This requires only the existing
membership correctness theorem for the collector. -/
def Restricted (d : Data) (allowed : List EncodedLeaderAlphabet.Outcome) (q : State) : Prop :=
  ∀ o ∈ EncodedLeaderAlphabet.rawOutcomes (outcomeContext d),
    o ∉ EncodedGraphCollector.collect (collector d q) ∨ o ∈ allowed
instance (d : Data) (allowed : List EncodedLeaderAlphabet.Outcome) (q : State) :
    Decidable (Restricted d allowed q) := by unfold Restricted; infer_instance
def valid (d : Data) (allowed : List EncodedLeaderAlphabet.Outcome) (q : State) (a : Letter) :=
  rolling d q a && decide (Restricted d allowed q)
def updates (d : Data) := (letters d).map (fun a => (states d).map (fun q => name d (next d q a)))
def checks (d : Data) (allowed : List EncodedLeaderAlphabet.Outcome) :=
  (letters d).map (fun a => (states d).map (fun q => valid d allowed q a))
def start (d : Data) := name d (initial d)
def readNext (d : Data) (q : Nat) (a : Letter) :=
  ((updates d).getD ((letters d).idxOf a) []).getD q 0 % (states d).length
def readCheck (d : Data) (allowed : List EncodedLeaderAlphabet.Outcome) (q : Nat) (a : Letter) :=
  ((checks d allowed).getD ((letters d).idxOf a) []).getD q false

theorem template_primrec : Primrec template := Primrec.fst
theorem successors_primrec : Primrec successors := Primrec.fst.comp Primrec.snd
theorem stops_primrec : Primrec stops := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem maxPriority_primrec : Primrec maxPriority := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
theorem bankData_primrec : Primrec bankData := EncodedScheduledCollector.bankData_primrec.comp
  (Primrec.fst.comp template_primrec)
theorem roots_primrec : Primrec roots := EncodedClosingBanks.roots_primrec.comp bankData_primrec
theorem outputs_primrec : Primrec outputs := EncodedScheduledCollector.outputs_primrec.comp
  (Primrec.fst.comp template_primrec)
theorem annotation_primrec : Primrec annotation := EncodedScheduledCollector.monitor_primrec.comp
  (Primrec.fst.comp template_primrec)
theorem graphData_primrec : Primrec graphData := EncodedScheduledCollector.graphData_primrec.comp template_primrec
theorem outcomeContext_primrec : Primrec outcomeContext :=
  (EncodedScheduledCollector.width_primrec.comp template_primrec).pair
    ((EncodedParityTables.size_primrec.comp annotation_primrec).pair maxPriority_primrec)
theorem refined_primrec : Primrec refined := Primrec.fst.pair
  ((Primrec.fst.comp Primrec.snd).pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).pair
      (Primrec.list_map EncodedClosingBanks.matrix_primrec
        ((Primrec.dom_finite (fun v : Bool × Bool => (v.1,v.2 && v.1))).comp Primrec.snd).to₂))))
theorem currentBankData_primrec : Primrec₂ currentBankData :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const true))
    (bankData_primrec.comp Primrec.fst) (refined_primrec.comp (bankData_primrec.comp Primrec.fst))
theorem initial_primrec : Primrec initial :=
  ((EncodedClosingScans.source_primrec.comp graphData_primrec).pair
    ((Primrec.list_map (Primrec.list_range.comp roots_primrec) (Primrec.const true).to₂).pair
      (EncodedScheduledCollector.initial_primrec.comp (Primrec.fst.comp template_primrec)))).pair
    ((EncodedScheduledCollector.bank_primrec.comp (Primrec.fst.comp template_primrec)).pair (Primrec.const true))
theorem rawStates_primrec : Primrec rawStates := FiniteSearch.product_primrec.comp
  (FiniteSearch.product_primrec.comp
    (FiniteSearch.tables_primrec.comp (Primrec.fst.comp (EncodedClosingScans.rules_primrec.comp graphData_primrec)) roots_primrec)
    (FiniteSearch.product_primrec.comp (FiniteSearch.words_primrec.comp (Primrec.const [false,true]) roots_primrec)
      (FiniteSearch.tables_primrec.comp (EncodedParityTables.size_primrec.comp annotation_primrec) roots_primrec)))
  (FiniteSearch.product_primrec.comp (EncodedClosingBanks.banks_primrec.comp bankData_primrec outputs_primrec)
    (Primrec.const [false,true]))
theorem states_primrec : Primrec states := FiniteCodeNumbering.unique_primrec.comp rawStates_primrec
theorem name_primrec : Primrec₂ name := FiniteCodeNumbering.name_primrec.comp (rawStates_primrec.comp Primrec.fst) Primrec.snd
theorem letters_primrec : Primrec letters := FiniteSearch.product_primrec.comp
  (Primrec.list_range.comp (Primrec.fst.comp (EncodedClosingBanks.context_primrec.comp bankData_primrec)))
  (FiniteSearch.product_primrec.comp (FiniteSearch.tables_primrec.comp outputs_primrec roots_primrec)
    (EncodedClosingBanks.banks_primrec.comp bankData_primrec outputs_primrec))

theorem next_primrec : Primrec (fun x : Data × State × Letter => next x.1 x.2.1 x.2.2) := by
  have hd : Primrec (fun x : Data × State × Letter => x.1) := Primrec.fst
  have hq : Primrec (fun x : Data × State × Letter => x.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun x : Data × State × Letter => x.2.2) := Primrec.snd.comp Primrec.snd
  have graph := Primrec.fst.comp (Primrec.fst.comp hq)
  have active := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp hq))
  have labels := Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp hq))
  have gd := Primrec.list_map graph ((Primrec.list_getD 0).comp
    (successors_primrec.comp (hd.comp Primrec.fst)) Primrec.snd).to₂
  have ac := Primrec.list_map (Primrec.list_range.comp (roots_primrec.comp hd))
    ((Primrec.dom_finite (fun b : Bool × Bool => b.1 && !b.2)).comp
      (((Primrec.list_getD false).comp (active.comp Primrec.fst) Primrec.snd).pair
        ((Primrec.list_getD false).comp (stops_primrec.comp (hd.comp Primrec.fst))
          ((Primrec.list_getD 0).comp (graph.comp Primrec.fst) Primrec.snd)))).to₂
  have an := Primrec.list_map (Primrec.list_range.comp (roots_primrec.comp hd))
    (EncodedParityTables.next_primrec.comp
      ((annotation_primrec.comp (hd.comp Primrec.fst)).pair
        (((Primrec.list_getD 0).comp (labels.comp Primrec.fst) Primrec.snd).pair
          (Primrec.nat_add.comp
            (Primrec.nat_mul.comp (Primrec.fst.comp (ha.comp Primrec.fst)) (outputs_primrec.comp (hd.comp Primrec.fst)))
            ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp (ha.comp Primrec.fst))) Primrec.snd))))).to₂
  exact (gd.pair (ac.pair an)).pair ((Primrec.snd.comp (Primrec.snd.comp ha)).pair (Primrec.const false))

theorem collector_primrec : Primrec₂ collector := by
  have hd : Primrec (fun x : Data × State => x.1) := Primrec.fst
  have hq : Primrec (fun x : Data × State => x.2) := Primrec.snd
  have ht := template_primrec.comp hd
  have first := Primrec.snd.comp (Primrec.snd.comp hq)
  have replay := (currentBankData_primrec.comp hd first).pair
    ((Primrec.fst.comp (Primrec.snd.comp hq)).pair ((outputs_primrec.comp hd).pair
      ((annotation_primrec.comp hd).pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp hq))))))
  have graph := ((Primrec.fst.comp (graphData_primrec.comp hd)).pair
    ((EncodedClosingScans.rules_primrec.comp (graphData_primrec.comp hd)).pair
      ((EncodedClosingScans.graphs_primrec.comp (graphData_primrec.comp hd)).pair
        (Primrec.fst.comp (Primrec.fst.comp hq)))))
  exact (replay.pair ((EncodedScheduledCollector.parents_primrec.comp ht).pair
    ((EncodedScheduledCollector.minima_primrec.comp ht).pair
      (graph.pair ((Primrec.const []).pair (first.pair (EncodedScheduledCollector.width_primrec.comp ht))))))).pair
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp hq)))

theorem rolling_primrec : Primrec (fun x : Data × State × Letter => rolling x.1 x.2.1 x.2.2) := by
  have hd : Primrec (fun x : Data × State × Letter => x.1) := Primrec.fst
  have hq : Primrec (fun x : Data × State × Letter => x.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun x : Data × State × Letter => x.2.2) := Primrec.snd.comp Primrec.snd
  exact EncodedLeaderMemory.check_primrec.comp
    ((currentBankData_primrec.comp hd (Primrec.snd.comp (Primrec.snd.comp hq))).pair
      (refined_primrec.comp (bankData_primrec.comp hd)))
    ((Primrec.fst.comp (Primrec.snd.comp hq)).pair
      ((Primrec.snd.comp (Primrec.snd.comp ha)).pair ((Primrec.fst.comp ha).pair
        (Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp ha))
          ((Primrec.list_getD (0,0)).comp (EncodedClosingBanks.outputTable_primrec.comp
            (bankData_primrec.comp (hd.comp Primrec.fst))) Primrec.snd).to₂))))

theorem restricted_primrec : PrimrecPred (fun x : Data × List EncodedLeaderAlphabet.Outcome × State =>
    Restricted x.1 x.2.1 x.2.2) := by
  unfold Restricted
  apply FiniteSearch.forall_mem (EncodedLeaderAlphabet.rawOutcomes_primrec.comp (outcomeContext_primrec.comp Primrec.fst))
  have hd : Primrec (fun x : (Data × List EncodedLeaderAlphabet.Outcome × State) × EncodedLeaderAlphabet.Outcome => x.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hq : Primrec (fun x : (Data × List EncodedLeaderAlphabet.Outcome × State) × EncodedLeaderAlphabet.Outcome => x.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have allowed : Primrec (fun x : (Data × List EncodedLeaderAlphabet.Outcome × State) × EncodedLeaderAlphabet.Outcome => x.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have mem : PrimrecRel (fun o (xs : List EncodedLeaderAlphabet.Outcome) => o ∈ xs) :=
    (Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)).swap
  exact ((mem.comp Primrec.snd (EncodedGraphCollector.collect_primrec.comp
    (collector_primrec.comp hd hq))).not.or (mem.comp Primrec.snd allowed)).primrecRel

theorem valid_primrec : Primrec (fun x : Data × List EncodedLeaderAlphabet.Outcome × State × Letter =>
    valid x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  (Primrec.dom_finite (fun b : Bool × Bool => b.1 && b.2)).comp
    ((rolling_primrec.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))).pair
      (restricted_primrec.decide.comp (Primrec.fst.pair
        ((Primrec.fst.comp Primrec.snd).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))))
theorem updates_primrec : Primrec updates := Primrec.list_map letters_primrec
  (Primrec.list_map (states_primrec.comp Primrec.fst)
    (name_primrec.comp (Primrec.fst.comp Primrec.fst)
      (next_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))))).to₂).to₂
theorem checks_primrec : Primrec₂ checks := Primrec.list_map (letters_primrec.comp Primrec.fst)
  (Primrec.list_map (states_primrec.comp (Primrec.fst.comp Primrec.fst))
    (valid_primrec.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))))).to₂).to₂

theorem start_primrec : Primrec start := name_primrec.comp Primrec.id initial_primrec
theorem readNext_primrec : Primrec (fun x : Data × Nat × Letter => readNext x.1 x.2.1 x.2.2) :=
  Primrec.nat_mod.comp ((Primrec.list_getD 0).comp
    ((Primrec.list_getD []).comp (updates_primrec.comp Primrec.fst)
      (Primrec.list_idxOf.comp (Primrec.snd.comp Primrec.snd) (letters_primrec.comp Primrec.fst)))
    (Primrec.fst.comp Primrec.snd)) (Primrec.list_length.comp (states_primrec.comp Primrec.fst))
theorem readCheck_primrec : Primrec (fun x : Data × List EncodedLeaderAlphabet.Outcome × Nat × Letter =>
    readCheck x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  (Primrec.list_getD false).comp
    ((Primrec.list_getD []).comp (checks_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.list_idxOf.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (letters_primrec.comp Primrec.fst)))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))

end Characterisation.EncodedGraphMemory
