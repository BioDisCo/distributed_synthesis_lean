/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphMemory
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedBankRoleExchange

/-! Left-leader memory reuses the existing state enumeration, transition
algorithm and rolling checks. Only bank interpretation and stopping flags
change; the original graph-scan context is retained. The collector converts
local bank metadata back to the original process order. -/
namespace Characterisation.EncodedLeftGraphMemory
open DistributedSynthesis
attribute [local irreducible] Primrec
abbrev Data := EncodedGraphMemory.Data
abbrev State := EncodedGraphMemory.State
abbrev Letter := EncodedGraphMemory.Letter
local instance : Primcodable Data := inferInstance
local instance : Primcodable State := inferInstance
local instance : Primcodable Letter := inferInstance
local instance leftMemoryLetterBEq : BEq Letter := instBEqOfDecidableEq

def prepare (d : Data) (stops : List Bool) : Data :=
  (((EncodedBankRoleExchange.bankData d.1.1.1,d.1.1.2),d.1.2),d.2.1,stops,d.2.2.2)
def collector (d : Data) (q : State) : EncodedGraphCollector.Data :=
  let c := EncodedGraphMemory.collector d q
  (((EncodedBankRoleExchange.bankData c.1.1.1,c.1.1.2),c.1.2),c.2)
def Restricted (d : Data) (allowed : List EncodedLeaderAlphabet.Outcome) (q : State) : Prop :=
  ∀ o ∈ EncodedLeaderAlphabet.rawOutcomes (EncodedGraphMemory.outcomeContext d),
    o ∉ EncodedGraphCollector.collect (collector d q) ∨ o ∈ allowed
instance (d : Data) (allowed : List EncodedLeaderAlphabet.Outcome) (q : State) :
    Decidable (Restricted d allowed q) := by unfold Restricted; infer_instance
def valid (d : Data) (allowed : List EncodedLeaderAlphabet.Outcome) (q : State) (a : Letter) :=
  EncodedGraphMemory.rolling d q a && decide (Restricted d allowed q)
def checks (d : Data) (allowed : List EncodedLeaderAlphabet.Outcome) :=
  (EncodedGraphMemory.letters d).map (fun a => (EncodedGraphMemory.states d).map (fun q => valid d allowed q a))
def readCheck (d : Data) (allowed : List EncodedLeaderAlphabet.Outcome) (q : Nat) (a : Letter) :=
  ((checks d allowed).getD ((EncodedGraphMemory.letters d).idxOf a) []).getD q false

theorem prepare_primrec : Primrec₂ prepare := by
  have hd : Primrec (fun x : Data × List Bool => x.1) := Primrec.fst
  have ht := Primrec.fst.comp hd
  have replay := Primrec.fst.comp ht
  exact (((EncodedBankRoleExchange.bankData_primrec.comp (Primrec.fst.comp replay)).pair
    (Primrec.snd.comp replay)).pair (Primrec.snd.comp ht)).pair
    ((Primrec.fst.comp (Primrec.snd.comp hd)).pair (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hd)))))
theorem collector_primrec : Primrec₂ collector := by
  have c : Primrec (fun x : Data × State => EncodedGraphMemory.collector x.1 x.2) := EncodedGraphMemory.collector_primrec
  have t := Primrec.fst.comp c
  have r := Primrec.fst.comp t
  exact (((EncodedBankRoleExchange.bankData_primrec.comp (Primrec.fst.comp r)).pair
    (Primrec.snd.comp r)).pair (Primrec.snd.comp t)).pair (Primrec.snd.comp c)
theorem restricted_primrec : PrimrecPred (fun x : Data × List EncodedLeaderAlphabet.Outcome × State =>
    Restricted x.1 x.2.1 x.2.2) := by
  unfold Restricted
  apply FiniteSearch.forall_mem (EncodedLeaderAlphabet.rawOutcomes_primrec.comp
    (EncodedGraphMemory.outcomeContext_primrec.comp Primrec.fst))
  have hd : Primrec (fun x : (Data × List EncodedLeaderAlphabet.Outcome × State) × EncodedLeaderAlphabet.Outcome => x.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hq : Primrec (fun x : (Data × List EncodedLeaderAlphabet.Outcome × State) × EncodedLeaderAlphabet.Outcome => x.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have ha : Primrec (fun x : (Data × List EncodedLeaderAlphabet.Outcome × State) × EncodedLeaderAlphabet.Outcome => x.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have mem : PrimrecRel (fun o (xs : List EncodedLeaderAlphabet.Outcome) => o ∈ xs) :=
    (Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)).swap
  exact ((mem.comp Primrec.snd (EncodedGraphCollector.collect_primrec.comp
    (collector_primrec.comp hd hq))).not.or (mem.comp Primrec.snd ha)).primrecRel

theorem valid_primrec : Primrec (fun x : Data × List EncodedLeaderAlphabet.Outcome × State × Letter =>
    valid x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  (Primrec.dom_finite (fun b : Bool × Bool => b.1 && b.2)).comp
    ((EncodedGraphMemory.rolling_primrec.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))).pair
      (restricted_primrec.decide.comp (Primrec.fst.pair
        ((Primrec.fst.comp Primrec.snd).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))))
theorem checks_primrec : Primrec₂ checks := Primrec.list_map (EncodedGraphMemory.letters_primrec.comp Primrec.fst)
  (Primrec.list_map (EncodedGraphMemory.states_primrec.comp (Primrec.fst.comp Primrec.fst))
    (valid_primrec.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))))).to₂).to₂
theorem readCheck_primrec : Primrec (fun x : Data × List EncodedLeaderAlphabet.Outcome × Nat × Letter =>
    readCheck x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  (Primrec.list_getD false).comp
    ((Primrec.list_getD []).comp (checks_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.list_idxOf.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (EncodedGraphMemory.letters_primrec.comp Primrec.fst)))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))

/-- Bank metadata and stop flags do not affect the enumeration of states. -/
theorem rawStates_prepare (d : Data) (stops : List Bool) :
    EncodedGraphMemory.rawStates (prepare d stops) = EncodedGraphMemory.rawStates d := rfl
theorem initial_prepare (d : Data) (stops : List Bool) :
    EncodedGraphMemory.initial (prepare d stops) = EncodedGraphMemory.initial d := rfl
theorem letters_prepare (d : Data) (stops : List Bool) :
    EncodedGraphMemory.letters (prepare d stops) = EncodedGraphMemory.letters d := rfl

end Characterisation.EncodedLeftGraphMemory
