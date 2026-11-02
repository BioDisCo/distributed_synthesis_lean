/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderPhysical
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderSafetyLocal
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphMemoryRun

/-! Exact physical execution of the assembled local compiler. Every table
lookup is tied to the generated leader/receiver alphabet, and the parity and
memory components advance together at each original round. -/
namespace Characterisation.EncodedLeaderPhysical
open DistributedSynthesis
local instance correctPhaseBEq : BEq EncodedJointPhaseObjective.Letter := instBEqOfDecidableEq
local instance correctMemoryBEq : BEq EncodedGraphMemory.Letter := instBEqOfDecidableEq
local instance correctReceiverBEq : BEq Receiver := instBEqOfDecidableEq

variable (d : Data)
abbrev PhysicalRound := EncodedLocalLeaderTest.PhysicalRound (layout d)
def roundCode (a : PhysicalRound d) : Round := ((a.1.1.val,a.1.2.val),a.2.1.val,a.2.2.val)
theorem decode_fin (a : Fin (alphabet d)) : decode d a.val =
    roundCode d ((EncodedLocalLeaderTest.physicalNumber (layout d)).symm a) := rfl

theorem decode_number (a : PhysicalRound d) :
    decode d (EncodedLocalLeaderTest.physicalNumber (layout d) a).val = roundCode d a := by
  rw [decode_fin,Equiv.symm_apply_apply]

private theorem lookup_mem {A : Type} (xs : List A) (fallback : A) (i : Fin xs.length) :
    xs.getD i.val fallback ∈ xs := by
  rw [List.getD_eq_getElem _ _ i.isLt]
  exact List.getElem_mem i.isLt

theorem phaseLetter_mem (a : PhysicalRound d) :
    phaseLetter d (roundCode d a) ∈ EncodedJointPhaseObjective.rawLetters (phase d) := by
  have hr := (FiniteCodeNumbering.mem_unique (rawReceivers d) _).mp
    (lookup_mem (receivers d) ([],[]) a.2.1)
  have hs := (FiniteCodeNumbering.mem_unique _ _).mp
    (lookup_mem (senders d) [] a.2.2)
  exact List.mem_product.mpr ⟨List.mem_product.mpr
    ⟨List.mem_range.mpr a.1.1.isLt,List.mem_range.mpr a.1.2.isLt⟩,
    List.mem_product.mpr ⟨(List.mem_product.mp hr).1,hs⟩⟩

theorem phaseIndex_lt (a : Fin (alphabet d)) :
    phaseIndex d a.val < (EncodedJointPhaseObjective.letters (phase d)).length := by
  apply List.idxOf_lt_length_iff.mpr
  apply (FiniteCodeNumbering.mem_unique _ _).mpr
  rw [decode_fin]
  exact phaseLetter_mem d _

def phaseNumber (a : Fin (alphabet d)) : Fin (EncodedJointPhaseObjective.letters (phase d)).length :=
  ⟨phaseIndex d a.val,phaseIndex_lt d a⟩

theorem objective_alphabet : (EncodedParityTables.rows (objective d)).length = alphabet d := by
  simp [objective,EncodedParityTables.rows]

private theorem map_range_lookup {A : Type} (N : Nat) (f : Nat → A) (fallback : A) (a : Fin N) :
    ((List.range N).map f).getD a.val fallback = f a.val := by
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map,List.length_range] using a.isLt)]
  simp only [List.getElem_map,List.getElem_range]

theorem objective_next (q : Nat) (a : Fin (alphabet d)) :
    EncodedParityTables.next (objective d) q a.val =
      EncodedParityTables.next (EncodedLeaderPhase.compile d.1) q (phaseIndex d a.val) := by
  have row := map_range_lookup (alphabet d)
    (fun a => (EncodedParityTables.rows (EncodedLeaderPhase.compile d.1)).getD (phaseIndex d a) []) [] a
  change (((List.range (alphabet d)).map _).getD a.val []).getD q 0 % _ = _
  rw [row]
  rfl

theorem objective_run (word : OmegaWord (Fin (alphabet d))) (n : Nat) :
    (EncodedParityConjunction.read (objective d) (alphabet d)).run word n =
      (EncodedParityConjunction.read (EncodedLeaderPhase.compile d.1)
        (EncodedJointPhaseObjective.letters (phase d)).length).run (fun n => phaseNumber d (word n)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Fin.ext
    change EncodedParityTables.next (objective d)
      ((EncodedParityConjunction.read (objective d) (alphabet d)).run word n).val (word n).val = _
    rw [ih,objective_next]
    rfl

theorem objective_accepts_iff (word : OmegaWord (Fin (alphabet d))) :
    (EncodedParityConjunction.read (objective d) (alphabet d)).Accepts word ↔
      (EncodedParityConjunction.read (EncodedLeaderPhase.compile d.1)
        (EncodedJointPhaseObjective.letters (phase d)).length).Accepts (fun n => phaseNumber d (word n)) := by
  rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity,DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
  simp only [objective_run]
  rfl

variable (startBound : EncodedGraphMemory.start (memory d) < (EncodedGraphMemory.states (memory d)).length)
include startBound in
theorem memorySize_eq : EncodedLeaderSafety.memorySize (safetyData d) =
    (EncodedGraphMemory.states (memory d)).length := by
  change _ - 1 + 1 = _
  omega

include startBound in
theorem initialMemory_eq : EncodedLeaderSafety.initialMemory (safetyData d) =
    EncodedGraphMemory.start (memory d) := by
  unfold EncodedLeaderSafety.initialMemory
  rw [memorySize_eq d startBound]
  exact Nat.mod_eq_of_lt startBound

include startBound in
theorem memoryNext_eq (q : Nat) (a : Fin (alphabet d)) :
    EncodedLeaderSafety.memoryNext (safetyData d) q a.val =
      EncodedGraphMemory.readNext (memory d) q (memoryLetter d (decode d a.val)) := by
  have row := map_range_lookup (alphabet d)
    (fun a => (EncodedGraphMemory.updates (memory d)).getD (memoryIndex d a) []) [] a
  unfold EncodedLeaderSafety.memoryNext
  rw [memorySize_eq d startBound]
  change ((updates d).getD a.val []).getD q 0 % _ = _
  rw [show (updates d).getD a.val [] = _ from row]
  rfl

theorem valid_eq (q : Nat) (a : Fin (alphabet d)) :
    EncodedLeaderSafety.valid (safetyData d) q a.val =
      EncodedGraphMemory.readCheck (memory d) (allowed d) q (memoryLetter d (decode d a.val)) := by
  have row := map_range_lookup (alphabet d)
    (fun a => (EncodedGraphMemory.checks (memory d) (allowed d)).getD (memoryIndex d a) []) [] a
  change ((checks d).getD a.val []).getD q false = _
  rw [show (checks d).getD a.val [] = _ from row]
  rfl

include startBound in
theorem memoryRun_eq (word : OmegaWord (Fin (alphabet d))) (n : Nat) :
    EncodedLeaderSafety.memoryRun (safetyData d) word n =
      phaseMemoryRun (EncodedGraphMemory.start (memory d)) (EncodedGraphMemory.readNext (memory d))
        (fun n => memoryLetter d (decode d (word n).val)) n := by
  induction n with
  | zero => exact initialMemory_eq d startBound
  | succ n ih =>
    change EncodedLeaderSafety.memoryNext (safetyData d)
      (EncodedLeaderSafety.memoryRun (safetyData d) word n) (word n).val = _
    rw [memoryNext_eq d startBound,ih]
    rfl

include startBound in
/-- The generated local monitor checks the original phase word and every
promised bank along the actual unbounded memory execution. -/
theorem compile_wins_iff (play : Nat → PhysicalRound d) :
    (EncodedLocalLeaderTest.monitor (compile d)).WinsPlay play ↔
      (EncodedParityConjunction.read (EncodedLeaderPhase.compile d.1)
        (EncodedJointPhaseObjective.letters (phase d)).length).Accepts
        (fun n => phaseNumber d (EncodedLocalLeaderTest.physicalNumber (layout d) (play n))) ∧
      ∀ n, EncodedGraphMemory.readCheck (memory d) (allowed d)
        (phaseMemoryRun (EncodedGraphMemory.start (memory d)) (EncodedGraphMemory.readNext (memory d))
          (fun n => memoryLetter d (roundCode d (play n))) n)
        (memoryLetter d (roundCode d (play n))) = true := by
  rw [EncodedLocalLeaderTest.winsPlay_iff_accepts]
  change (EncodedParityConjunction.read
    (EncodedLocalLeaderTest.monitorData (EncodedLeaderSafety.compile (safetyData d)))
    (EncodedLocalLeaderTest.physicalSize (EncodedLeaderSafety.base (safetyData d)))).Accepts
    (fun n => EncodedLocalLeaderTest.physicalNumber (layout d) (play n)) ↔ _
  rw [EncodedLeaderSafety.compile_accepts_iff (safetyData d) (objective_alphabet d)]
  change (EncodedParityConjunction.read (objective d) (alphabet d)).Accepts _ ∧ _ ↔ _
  rw [objective_accepts_iff]
  simp only [memoryRun_eq d startBound,valid_eq,decode_number]

variable [Inhabited (Fin (EncodedLocalLeaderTest.receiverInputs (layout d)))]
variable [Inhabited (Fin (EncodedLocalLeaderTest.senderInputs (layout d)))]
variable [Inhabited (Fin (EncodedLocalLeaderTest.receiverOutputs (layout d)))]
local instance : Inhabited (Fin (EncodedLocalLeaderTest.receiverInputs (compile d))) :=
  inferInstanceAs (Inhabited (Fin (EncodedLocalLeaderTest.receiverInputs (layout d))))
local instance : Inhabited (Fin (EncodedLocalLeaderTest.senderInputs (compile d))) :=
  inferInstanceAs (Inhabited (Fin (EncodedLocalLeaderTest.senderInputs (layout d))))
local instance : Inhabited (Fin (EncodedLocalLeaderTest.receiverOutputs (compile d))) :=
  inferInstanceAs (Inhabited (Fin (EncodedLocalLeaderTest.receiverOutputs (layout d))))
local instance : DecidableEq (EncodedLocalLeaderTest.monitor (compile d)).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedLocalLeaderTest.states (compile d))))

include startBound in
/-- A complete Boolean test for strategies over the generated physical
alphabet. Its data contain neither local update tables nor a local solver. -/
theorem solve_iff_strategies : solve d = true ↔
    ∃ (receiverStrategy : ReceiverBlockStrategy
        (Fin (EncodedLocalLeaderTest.receiverInputs (layout d)))
        (Fin (EncodedLocalLeaderTest.senderInputs (layout d)))
        (Fin (EncodedLocalLeaderTest.receiverOutputs (layout d))))
      (leaderStrategy : SenderBlockStrategy
        (Fin (EncodedLocalLeaderTest.senderInputs (layout d)))
        (Fin (EncodedLocalLeaderTest.senderOutputs (layout d)))),
      ∀ env,
        (EncodedParityConjunction.read (EncodedLeaderPhase.compile d.1)
          (EncodedJointPhaseObjective.letters (phase d)).length).Accepts
          (fun n => phaseNumber d (EncodedLocalLeaderTest.physicalNumber (layout d)
            (pairPlay receiverStrategy leaderStrategy env n))) ∧
        ∀ n, EncodedGraphMemory.readCheck (memory d) (allowed d)
          (phaseMemoryRun (EncodedGraphMemory.start (memory d)) (EncodedGraphMemory.readNext (memory d))
            (fun n => memoryLetter d (roundCode d (pairPlay receiverStrategy leaderStrategy env n))) n)
          (memoryLetter d (roundCode d (pairPlay receiverStrategy leaderStrategy env n))) = true := by
  change EncodedLocalLeaderTest.solve (compile d) = true ↔ _
  rw [EncodedLocalLeaderTest.solve_eq_leaderThreadTest,leaderThreadTest_iff_strategies]
  apply exists_congr
  intro receiverStrategy
  apply exists_congr
  intro leaderStrategy
  exact forall_congr' (fun env => compile_wins_iff d startBound _)

end Characterisation.EncodedLeaderPhysical
