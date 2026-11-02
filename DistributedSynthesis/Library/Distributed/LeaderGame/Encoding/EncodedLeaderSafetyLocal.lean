/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderSafetyCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLocalLeaderPhysical
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLocalLeaderTestCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.LocalLeaderLanguage

/-! Complete local leader solving for a physical objective coupled to
finite memory tables. Model-specific generation of those memory tables is
a separate obligation; it is not assumed computable by this theorem. -/
namespace Characterisation.EncodedLeaderSafety
open DistributedSynthesis

variable (d : Data)
abbrev PhysicalRound := EncodedLocalLeaderTest.PhysicalRound (base d)
def memoryStep (m : Fin (memorySize d)) (a : PhysicalRound d) : Fin (memorySize d) :=
  ⟨memoryNext d m.val (EncodedLocalLeaderTest.physicalNumber (base d) a).val,Nat.mod_lt _ (Nat.succ_pos _)⟩
def memoryCheck (m : Fin (memorySize d)) (a : PhysicalRound d) :=
  valid d m.val (EncodedLocalLeaderTest.physicalNumber (base d) a).val
def guard := leaderMemoryMonitor (EncodedLocalLeaderTest.monitor (base d)) id
  (⟨initialMemory d,Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (memorySize d)) (memoryStep d) (memoryCheck d)

theorem memoryRun_val (play : Nat → PhysicalRound d) (n : Nat) :
    (phaseMemoryRun (⟨initialMemory d,Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (memorySize d))
      (memoryStep d) play n).val =
      memoryRun d (fun n => EncodedLocalLeaderTest.physicalNumber (base d) (play n)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change memoryNext d _ _ = _
    rw [ih]
    rfl

theorem guard_wins_iff (play : Nat → PhysicalRound d) : (guard d).WinsPlay play ↔
    (EncodedLocalLeaderTest.monitor (base d)).WinsPlay play ∧
    ∀ n, valid d (memoryRun d (fun n => EncodedLocalLeaderTest.physicalNumber (base d) (play n)) n)
      (EncodedLocalLeaderTest.physicalNumber (base d) (play n)).val = true := by
  have projected : phasePhysicalPlay id play = play := by funext n; rfl
  simp only [guard,leaderMemoryMonitor_wins_iff,projected,memoryCheck,memoryRun_val]

variable (alphabet : (EncodedParityTables.rows (EncodedLocalLeaderTest.monitorData (base d))).length =
  EncodedLocalLeaderTest.physicalSize (base d))

include alphabet in
theorem compile_wins_iff (play : Nat → PhysicalRound d) :
    (EncodedLocalLeaderTest.monitor (compile d)).WinsPlay play ↔ (guard d).WinsPlay play := by
  rw [EncodedLocalLeaderTest.winsPlay_iff_accepts,guard_wins_iff,
    EncodedLocalLeaderTest.winsPlay_iff_accepts]
  exact compile_accepts_iff d alphabet _

variable [Inhabited (Fin (EncodedLocalLeaderTest.receiverInputs (base d)))]
variable [Inhabited (Fin (EncodedLocalLeaderTest.senderInputs (base d)))]
variable [Inhabited (Fin (EncodedLocalLeaderTest.receiverOutputs (base d)))]

local instance : Inhabited (Fin (EncodedLocalLeaderTest.receiverInputs (compile d))) :=
  inferInstanceAs (Inhabited (Fin (EncodedLocalLeaderTest.receiverInputs (base d))))
local instance : Inhabited (Fin (EncodedLocalLeaderTest.senderInputs (compile d))) :=
  inferInstanceAs (Inhabited (Fin (EncodedLocalLeaderTest.senderInputs (base d))))
local instance : Inhabited (Fin (EncodedLocalLeaderTest.receiverOutputs (compile d))) :=
  inferInstanceAs (Inhabited (Fin (EncodedLocalLeaderTest.receiverOutputs (base d))))

local instance : DecidableEq (EncodedLocalLeaderTest.monitor (compile d)).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedLocalLeaderTest.states (compile d))))
local instance : DecidableEq (guard d).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedLocalLeaderTest.states (base d)) × Fin (memorySize d) × Bool))

include alphabet in
/-- The generated Boolean solver decides the original finite-memory leader
test, including all hidden receiver inputs and arbitrary phase duration. -/
theorem solve_eq_guardTest : solve d = leaderThreadTest (guard d) := by
  rw [solve,EncodedLocalLeaderTest.solve_eq_leaderThreadTest]
  exact leaderThreadTest_language_congr _ _ (compile_wins_iff d alphabet)

end Characterisation.EncodedLeaderSafety
