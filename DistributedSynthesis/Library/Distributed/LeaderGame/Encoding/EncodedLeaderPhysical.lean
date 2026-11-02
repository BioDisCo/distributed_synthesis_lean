/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderPhase
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphMemory
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderSafety

/-! Generate the physical alphabet shared by the phase objective and the
concrete graph memory. The leader chooses a group-indexed output table.
The receiver chooses root-indexed outputs and a complete new promised bank.
Neither translation changes the number of physical rounds. -/
namespace Characterisation.EncodedLeaderPhysical
open DistributedSynthesis
attribute [local irreducible] Primrec

abbrev Data := EncodedLeaderPhase.Data × EncodedGraphMemory.Data × List EncodedLeaderAlphabet.Outcome
abbrev Receiver := List Nat × EncodedClosingBanks.Bank
abbrev Round := (Nat × Nat) × Nat × Nat
local instance : Primcodable EncodedGraphMemory.Data := inferInstance
local instance : Primcodable Data := inferInstance
local instance physicalPhaseBEq : BEq EncodedJointPhaseObjective.Letter := instBEqOfDecidableEq
local instance physicalMemoryBEq : BEq EncodedGraphMemory.Letter := instBEqOfDecidableEq
local instance physicalOutputBEq : BEq (Nat × Nat) := instBEqOfDecidableEq
local instance physicalEnvBEq : BEq EncodedClosingObservations.Round := instBEqOfDecidableEq
local instance physicalReceiverBEq : BEq Receiver := instBEqOfDecidableEq

def phase (d : Data) := EncodedLeaderPhase.phaseData d.1
def memory (d : Data) := d.2.1
def allowed (d : Data) := d.2.2
def senders (d : Data) := FiniteCodeNumbering.unique
  (FiniteSearch.tables (EncodedRoundObjectives.outputOne (phase d).1) (EncodedJointPhaseObjective.groups (phase d)))
def rawReceivers (d : Data) : List Receiver :=
  (FiniteSearch.tables (EncodedRoundObjectives.outputTwo (phase d).1) (EncodedJointPhaseObjective.roots (phase d))).product
    (EncodedClosingBanks.banks (EncodedGraphMemory.bankData (memory d)) (EncodedGraphMemory.outputs (memory d)))
def receivers (d : Data) := FiniteCodeNumbering.unique (rawReceivers d)
/-- Only the four alphabet sizes of this datum are used. -/
def layout (d : Data) : EncodedLocalLeaderTest.Data :=
  ((0,0,[0],[]),EncodedRoundObjectives.inputTwo (phase d).1,EncodedRoundObjectives.inputOne (phase d).1,
    (receivers d).length,(senders d).length)
def alphabet (d : Data) := EncodedLocalLeaderTest.physicalSize (layout d)
def decode (d : Data) (a : Nat) : Round :=
  let outputs := (receivers d).length * (senders d).length
  ((a / outputs / EncodedRoundObjectives.inputOne (phase d).1,
    a / outputs % EncodedRoundObjectives.inputOne (phase d).1),
    a % outputs / (senders d).length,a % outputs % (senders d).length)
def receiver (d : Data) (a : Round) := (receivers d).getD a.2.1 ([],[])
def sender (d : Data) (a : Round) := (senders d).getD a.2.2 []
def phaseLetter (d : Data) (a : Round) : EncodedJointPhaseObjective.Letter :=
  (a.1,(receiver d a).1,sender d a)
def phaseIndex (d : Data) (a : Nat) :=
  (EncodedJointPhaseObjective.letters (phase d)).idxOf (phaseLetter d (decode d a))
/-- The bank's decoding tables determine the memory codes. In particular,
right is code zero here, independently of the objective's graph numbering. -/
def memoryLetter (d : Data) (a : Round) : EncodedGraphMemory.Letter :=
  ((EncodedClosingBanks.roundTable (EncodedGraphMemory.bankData (memory d))).idxOf (a.1.2,a.1.1,0),
    (List.range (EncodedJointPhaseObjective.roots (phase d))).map (fun h =>
      (EncodedClosingBanks.outputTable (EncodedGraphMemory.bankData (memory d))).idxOf
        ((sender d a).getD ((EncodedJointPhaseObjective.assignment (phase d)).getD h 0) 0,
          (receiver d a).1.getD h 0)),(receiver d a).2)
def memoryIndex (d : Data) (a : Nat) :=
  (EncodedGraphMemory.letters (memory d)).idxOf (memoryLetter d (decode d a))
def objective (d : Data) : EncodedParityTables.Data :=
  let p := EncodedLeaderPhase.compile d.1
  (p.1,EncodedParityTables.initial p,EncodedParityTables.priorities p,
    (List.range (alphabet d)).map (fun a => (EncodedParityTables.rows p).getD (phaseIndex d a) []))
def base (d : Data) : EncodedLocalLeaderTest.Data := (objective d,(layout d).2)
def updates (d : Data) := (List.range (alphabet d)).map
  (fun a => (EncodedGraphMemory.updates (memory d)).getD (memoryIndex d a) [])
def checks (d : Data) := (List.range (alphabet d)).map
  (fun a => (EncodedGraphMemory.checks (memory d) (allowed d)).getD (memoryIndex d a) [])
def safetyData (d : Data) : EncodedLeaderSafety.Data :=
  (base d,(EncodedGraphMemory.states (memory d)).length-1,EncodedGraphMemory.start (memory d),updates d,checks d)
def compile (d : Data) := EncodedLeaderSafety.compile (safetyData d)
def solve (d : Data) := EncodedLeaderSafety.solve (safetyData d)

theorem phase_primrec : Primrec phase := EncodedLeaderPhase.phaseData_primrec.comp Primrec.fst
theorem memory_primrec : Primrec memory := Primrec.fst.comp Primrec.snd
theorem allowed_primrec : Primrec allowed := Primrec.snd.comp Primrec.snd
theorem senders_primrec : Primrec senders := FiniteCodeNumbering.unique_primrec.comp
  (FiniteSearch.tables_primrec.comp (EncodedRoundObjectives.outputOne_primrec.comp (Primrec.fst.comp phase_primrec))
    (EncodedJointPhaseObjective.groups_primrec.comp phase_primrec))
theorem rawReceivers_primrec : Primrec rawReceivers := FiniteSearch.product_primrec.comp
  (FiniteSearch.tables_primrec.comp (EncodedRoundObjectives.outputTwo_primrec.comp (Primrec.fst.comp phase_primrec))
    (EncodedJointPhaseObjective.roots_primrec.comp phase_primrec))
  (EncodedClosingBanks.banks_primrec.comp (EncodedGraphMemory.bankData_primrec.comp memory_primrec)
    (EncodedGraphMemory.outputs_primrec.comp memory_primrec))
theorem receivers_primrec : Primrec receivers := FiniteCodeNumbering.unique_primrec.comp rawReceivers_primrec
theorem layout_primrec : Primrec layout := (Primrec.const (0,0,[0],[])).pair
  ((EncodedRoundObjectives.inputTwo_primrec.comp (Primrec.fst.comp phase_primrec)).pair
    ((EncodedRoundObjectives.inputOne_primrec.comp (Primrec.fst.comp phase_primrec)).pair
      ((Primrec.list_length.comp receivers_primrec).pair (Primrec.list_length.comp senders_primrec))))
theorem alphabet_primrec : Primrec alphabet := EncodedLocalLeaderTest.physicalSize_primrec.comp layout_primrec
theorem decode_primrec : Primrec₂ decode := by
  have hd : Primrec (fun x : Data × Nat => x.1) := Primrec.fst
  have ns := Primrec.list_length.comp (senders_primrec.comp hd)
  have no := Primrec.nat_mul.comp (Primrec.list_length.comp (receivers_primrec.comp hd)) ns
  have ni := EncodedRoundObjectives.inputOne_primrec.comp (Primrec.fst.comp (phase_primrec.comp hd))
  have inputs := Primrec.nat_div.comp Primrec.snd no
  have outputs := Primrec.nat_mod.comp Primrec.snd no
  exact ((Primrec.nat_div.comp inputs ni).pair (Primrec.nat_mod.comp inputs ni)).pair
    ((Primrec.nat_div.comp outputs ns).pair (Primrec.nat_mod.comp outputs ns))
theorem receiver_primrec : Primrec₂ receiver := (Primrec.list_getD ([],[])).comp
  (receivers_primrec.comp Primrec.fst) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
theorem sender_primrec : Primrec₂ sender := (Primrec.list_getD []).comp
  (senders_primrec.comp Primrec.fst) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem phaseLetter_primrec : Primrec₂ phaseLetter := (Primrec.fst.comp Primrec.snd).pair
  ((Primrec.fst.comp receiver_primrec).pair sender_primrec)
theorem phaseIndex_primrec : Primrec₂ phaseIndex := Primrec.list_idxOf.comp
  (phaseLetter_primrec.comp Primrec.fst decode_primrec)
  (EncodedJointPhaseObjective.letters_primrec.comp (phase_primrec.comp Primrec.fst))
theorem memoryLetter_primrec : Primrec₂ memoryLetter := by
  have hd : Primrec (fun x : Data × Round => x.1) := Primrec.fst
  have ha : Primrec (fun x : Data × Round => x.2) := Primrec.snd
  have bank := EncodedGraphMemory.bankData_primrec.comp (memory_primrec.comp hd)
  have env := Primrec.list_idxOf.comp
    ((Primrec.snd.comp (Primrec.fst.comp ha)).pair ((Primrec.fst.comp (Primrec.fst.comp ha)).pair (Primrec.const 0)))
    (EncodedClosingBanks.roundTable_primrec.comp bank)
  have pairs : Primrec (fun x : (Data × Round) × Nat =>
      ((sender x.1.1 x.1.2).getD ((EncodedJointPhaseObjective.assignment (phase x.1.1)).getD x.2 0) 0,
        (receiver x.1.1 x.1.2).1.getD x.2 0)) :=
    ((Primrec.list_getD 0).comp (sender_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
      ((Primrec.list_getD 0).comp (EncodedJointPhaseObjective.assignment_primrec.comp
        (phase_primrec.comp (hd.comp Primrec.fst))) Primrec.snd)).pair
      ((Primrec.list_getD 0).comp (Primrec.fst.comp (receiver_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))) Primrec.snd)
  exact env.pair ((Primrec.list_map (Primrec.list_range.comp
    (EncodedJointPhaseObjective.roots_primrec.comp (phase_primrec.comp hd)))
    (Primrec.list_idxOf.comp pairs (EncodedClosingBanks.outputTable_primrec.comp (bank.comp Primrec.fst))).to₂).pair
      (Primrec.snd.comp receiver_primrec))
theorem memoryIndex_primrec : Primrec₂ memoryIndex := Primrec.list_idxOf.comp
  (memoryLetter_primrec.comp Primrec.fst decode_primrec)
  (EncodedGraphMemory.letters_primrec.comp (memory_primrec.comp Primrec.fst))
theorem objective_primrec : Primrec objective := by
  have p := EncodedLeaderPhase.compile_primrec.comp (Primrec.fst : Primrec (fun d : Data => d.1))
  exact (Primrec.fst.comp p).pair ((EncodedParityTables.initial_primrec.comp p).pair
    ((EncodedParityTables.priorities_primrec.comp p).pair
      (Primrec.list_map (Primrec.list_range.comp alphabet_primrec)
        ((Primrec.list_getD []).comp (EncodedParityTables.rows_primrec.comp (p.comp Primrec.fst)) phaseIndex_primrec).to₂)))
theorem base_primrec : Primrec base := objective_primrec.pair (Primrec.snd.comp layout_primrec)
theorem updates_primrec : Primrec updates := Primrec.list_map (Primrec.list_range.comp alphabet_primrec)
  ((Primrec.list_getD []).comp (EncodedGraphMemory.updates_primrec.comp (memory_primrec.comp Primrec.fst)) memoryIndex_primrec).to₂
theorem checks_primrec : Primrec checks := Primrec.list_map (Primrec.list_range.comp alphabet_primrec)
  ((Primrec.list_getD []).comp (EncodedGraphMemory.checks_primrec.comp
    (memory_primrec.comp Primrec.fst) (allowed_primrec.comp Primrec.fst)) memoryIndex_primrec).to₂
theorem safetyData_primrec : Primrec safetyData := base_primrec.pair
  ((Primrec.nat_sub.comp (Primrec.list_length.comp (EncodedGraphMemory.states_primrec.comp memory_primrec)) (Primrec.const 1)).pair
    ((EncodedGraphMemory.start_primrec.comp memory_primrec).pair (updates_primrec.pair checks_primrec)))
theorem compile_primrec : Primrec compile := EncodedLeaderSafety.compile_primrec.comp safetyData_primrec
theorem solve_primrec : Primrec solve := EncodedLeaderSafety.solve_primrec.comp safetyData_primrec

end Characterisation.EncodedLeaderPhysical
