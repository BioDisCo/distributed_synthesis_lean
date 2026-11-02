/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphMemoryChecks

/-! The generated memory machine follows the original joint graph memory
at every physical round. No bound is placed on the duration of the phase. -/
namespace Characterisation.EncodedGraphMemory
open DistributedSynthesis
local instance runLetterBEq : BEq Letter := instBEqOfDecidableEq

variable {H G GQ Q I₁ I₂ O₁ O₂ : Type} {R E V N₁ N₂ P₁ P₂ J S B C d K : Nat}
variable [Fintype H] [Fintype GQ] [Fintype Q]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq H] [DecidableEq GQ] [DecidableEq Q]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
variable (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (output : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (number : Q ≃ Fin J) (shape : InputShape H)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (graphs : GraphRootState GQ d K ≃ Fin S)
variable (advance : GraphRootState GQ d K → GraphRootState GQ d K)
variable (source : H → GraphRootState GQ d K) (start : H → Q)
variable (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ d) (transitions : EncodedParityTables.Data)
variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))


local notation "input" => dataEncode root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum
local notation "encode" => stateEncode root env output number graphs
local notation "Memory" => GraphLeaderMemory H GQ Q I₁ I₂ O₁ O₂ d K
variable (size : EncodedParityTables.size transitions = J)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (transition : ∀ q r o, EncodedParityTables.next transitions (number q).val
  ((env r).val*V+(output o).val) = (number (step q r o)).val)
variable (group : H → G)

include size transition in
omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem readNext_encode (q : Memory)
    (a : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    readNext input (name input (encode q)) (letterEncode root env output group a) =
      name input (encode (jointGraphLeaderNext group recognizer step advance q a)) := by
  unfold readNext
  rw [updates_entry root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size step transition]
  exact Nat.mod_eq_of_lt (stateNumber root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size
    (jointGraphLeaderNext group recognizer step advance q a)).isLt

include size transition in
omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem run_encode
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) (n : Nat) :
    phaseMemoryRun (EncodedGraphMemory.start input) (readNext input)
      (fun n => letterEncode root env output group (play n)) n =
      name input (encode (phaseMemoryRun ((source,(fun _ => true),start),bank,true)
        (jointGraphLeaderNext group recognizer step advance) play n)) := by
  induction n with
  | zero =>
    change name input (initial input) = _
    rw [initial_encode]
    rfl
  | succ n ih =>
    rw [phaseMemoryRun,ih]
    exact readNext_encode root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size step transition group _ _

include size transition in
theorem checks_run (allowed : Finset (LeaderHandover Q B C))
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    (∀ n, readCheck input (allowedEncode number allowed)
      (phaseMemoryRun (EncodedGraphMemory.start input) (readNext input)
        (fun n => letterEncode root env output group (play n)) n)
      (letterEncode root env output group (play n)) = true) ↔
      ∀ n, jointLeaderCheck group shape
        (phaseMemoryRun ((source,(fun _ => true),start),bank,true)
          (jointGraphLeaderNext group recognizer step advance) play n).2 (play n) = true ∧
        jointGraphLeaderCollect recognizer step shape slot minimum
          (phaseMemoryRun ((source,(fun _ => true),start),bank,true)
            (jointGraphLeaderNext group recognizer step advance) play n) (play n) ⊆ allowed := by
  apply forall_congr'
  intro n
  rw [run_encode root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size step transition]
  exact checks_entry root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size step transition group allowed _ _

variable [Fintype G] [DecidableEq G]
include size transition in
omit [Fintype G] [DecidableEq G] in
/-- Generated checks coupled to any physical phase objective are exactly
its original fused graph guard. This equivalence holds on each whole play. -/
theorem guard_wins_iff (allowed : Finset (LeaderHandover Q B C))
    (phase : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H → O₂) (G → O₁))
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    (jointGraphGuard group shape recognizer step advance source start bank slot minimum allowed phase).WinsPlay play ↔
      phase.WinsPlay (phasePhysicalPlay Prod.fst play) ∧
      ∀ n, readCheck input (allowedEncode number allowed)
        (phaseMemoryRun (EncodedGraphMemory.start input) (readNext input)
          (fun n => letterEncode root env output group (play n)) n)
        (letterEncode root env output group (play n)) = true := by
  rw [checks_run root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size step transition]
  simp only [jointGraphGuard,leaderMemoryMonitor_wins_iff,Bool.and_eq_true,decide_eq_true_eq]

end Characterisation.EncodedGraphMemory
