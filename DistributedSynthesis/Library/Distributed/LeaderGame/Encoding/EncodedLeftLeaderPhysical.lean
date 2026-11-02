/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderPhysicalCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeftGraphMemory

/-! Reuse the physical alphabet, objective, and memory transitions for left
leadership. Only the closing-check rows use the original left collector. -/
namespace Characterisation.EncodedLeftLeaderPhysical
open DistributedSynthesis
open EncodedLeaderPhysical
attribute [local irreducible] Primrec
local instance leftPhysicalMemoryCode : Primcodable EncodedGraphMemory.Data := inferInstance
local instance leftPhysicalDataCode : Primcodable Data := inferInstance
local instance leftPhysicalMemoryBEq : BEq EncodedGraphMemory.Letter := instBEqOfDecidableEq

def checks (d : Data) := (List.range (alphabet d)).map
  (fun a => (EncodedLeftGraphMemory.checks (memory d) (allowed d)).getD (memoryIndex d a) [])
def safetyData (d : Data) : EncodedLeaderSafety.Data :=
  (base d,(EncodedGraphMemory.states (memory d)).length-1,EncodedGraphMemory.start (memory d),updates d,checks d)
def compile (d : Data) := EncodedLeaderSafety.compile (safetyData d)
def solve (d : Data) := EncodedLeaderSafety.solve (safetyData d)

theorem checks_primrec : Primrec checks := Primrec.list_map (Primrec.list_range.comp alphabet_primrec)
  ((Primrec.list_getD []).comp (EncodedLeftGraphMemory.checks_primrec.comp
    (memory_primrec.comp Primrec.fst) (allowed_primrec.comp Primrec.fst)) memoryIndex_primrec).to₂
theorem safetyData_primrec : Primrec safetyData := base_primrec.pair
  ((Primrec.nat_sub.comp (Primrec.list_length.comp (EncodedGraphMemory.states_primrec.comp memory_primrec)) (Primrec.const 1)).pair
    ((EncodedGraphMemory.start_primrec.comp memory_primrec).pair (updates_primrec.pair checks_primrec)))
theorem compile_primrec : Primrec compile := EncodedLeaderSafety.compile_primrec.comp safetyData_primrec
theorem solve_primrec : Primrec solve := EncodedLeaderSafety.solve_primrec.comp safetyData_primrec

attribute [local irreducible] checks EncodedLeaderPhysical.checks
  EncodedLeaderPhysical.objective EncodedLeaderPhysical.updates

variable (d : Data)
theorem memoryRun_shared (word : OmegaWord (Fin (alphabet d))) (n : Nat) :
    EncodedLeaderSafety.memoryRun (safetyData d) word n =
      EncodedLeaderSafety.memoryRun (EncodedLeaderPhysical.safetyData d) word n := by
  simp only [EncodedLeaderSafety.memoryRun,EncodedLeaderSafety.initialMemory,
    EncodedLeaderSafety.memoryNext,EncodedLeaderSafety.memorySize,EncodedLeaderSafety.updates,
    safetyData,EncodedLeaderPhysical.safetyData]

theorem valid_eq (q : Nat) (a : Fin (alphabet d)) :
    EncodedLeaderSafety.valid (safetyData d) q a.val =
      EncodedLeftGraphMemory.readCheck (memory d) (allowed d) q (memoryLetter d (decode d a.val)) := by
  have row : (checks d).getD a.val [] =
      (EncodedLeftGraphMemory.checks (memory d) (allowed d)).getD (memoryIndex d a.val) [] := by
    unfold checks
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map,List.length_range] using a.isLt)]
    simp only [List.getElem_map,List.getElem_range]
  change ((checks d).getD a.val []).getD q false = _
  rw [row]
  rfl

/-- Both components advance at each original physical round; no phase is
shortened by this compilation. -/
theorem compile_wins_iff
    (startBound : EncodedGraphMemory.start (memory d) < (EncodedGraphMemory.states (memory d)).length)
    (play : Nat → PhysicalRound d) :
    (EncodedLocalLeaderTest.monitor (compile d)).WinsPlay play ↔
      (EncodedParityConjunction.read (EncodedLeaderPhase.compile d.1)
        (EncodedJointPhaseObjective.letters (phase d)).length).Accepts
        (fun n => phaseNumber d (EncodedLocalLeaderTest.physicalNumber (layout d) (play n))) ∧
      ∀ n, EncodedLeftGraphMemory.readCheck (memory d) (allowed d)
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
  simp only [memoryRun_shared,EncodedLeaderPhysical.memoryRun_eq d startBound,valid_eq,decode_number]

end Characterisation.EncodedLeftLeaderPhysical
