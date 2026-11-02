/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeftGraphMemoryCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphMemoryChecks

/-! Reuse the complete original memory enumeration. Role exchange is a
bijection on semantic banks and leaves their numeric codes unchanged. -/
namespace Characterisation.EncodedLeftGraphMemory
open DistributedSynthesis
local instance leftNumberStateBEq : BEq State := instBEqOfDecidableEq
local instance leftNumberLetterBEq : BEq Letter := instBEqOfDecidableEq

variable {H G GQ Q I₁ I₂ O₁ O₂ : Type} {R E V N₁ N₂ P₁ P₂ J S B C d K : Nat}
variable [Fintype H] [Fintype GQ] [Fintype Q]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq H] [DecidableEq GQ] [DecidableEq Q]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
variable (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (out : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (number : Q ≃ Fin J) (shape : InputShape H)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (graphs : GraphRootState GQ d K ≃ Fin S)
variable (advance : GraphRootState GQ d K → GraphRootState GQ d K)
variable (source : H → GraphRootState GQ d K) (start : H → Q)
variable (bank : ClosingPlanBank H I₂ I₁ O₂ O₁ d) (transitions : EncodedParityTables.Data)
variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))

local notation "swappedEnv" => EncodedBankRoleExchange.environment env
local notation "swappedOut" => EncodedBankRoleExchange.output out
local notation "Memory" => GraphLeaderMemory H GQ Q I₂ I₁ O₂ O₁ d K
local notation "encode" => EncodedGraphMemory.stateEncode root swappedEnv swappedOut number graphs


local notation "input" => dataEncode root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum
local notation "original" => EncodedGraphMemory.dataEncode root env one two out outOne outTwo number shape recognizer graphs
  advance source start (fun h => exchangePlan (bank h)) transitions slot minimum
variable (size : EncodedParityTables.size transitions = J)

noncomputable def memoryExchange : Memory ≃ GraphLeaderMemory H GQ Q I₁ I₂ O₁ O₂ d K where
  toFun q := (q.1,(fun h => exchangePlan (q.2.1 h)),q.2.2)
  invFun q := (q.1,(fun h => exchangePlan (q.2.1 h)),q.2.2)
  left_inv q := by simp only [exchangePlan_twice,Prod.eta]
  right_inv q := by simp only [exchangePlan_twice,Prod.eta]

noncomputable def stateNumber : Memory ≃ Fin (EncodedGraphMemory.states input).length :=
  memoryExchange.trans (EncodedGraphMemory.stateNumber root env one two out outOne outTwo number shape recognizer graphs
    advance source start (fun h => exchangePlan (bank h)) transitions slot minimum size)

omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem stateNumber_val (q : Memory) :
    (stateNumber root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size q).val =
      EncodedGraphMemory.name input (encode q) := by
  change EncodedGraphMemory.name input
    (EncodedGraphMemory.stateEncode root env out number graphs (q.1,(fun h => exchangePlan (q.2.1 h)),q.2.2)) = _
  unfold EncodedGraphMemory.stateEncode
  rw [EncodedBankRoleExchange.bankEncode_unexchange]

include size in
omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem stateEncode_mem (q : Memory) : encode q ∈ EncodedGraphMemory.rawStates input := by
  have member := EncodedGraphMemory.stateEncode_mem root env one two out outOne outTwo number shape recognizer graphs
    advance source start (fun h => exchangePlan (bank h)) transitions slot minimum size (memoryExchange q)
  change EncodedGraphMemory.stateEncode root env out number graphs
    (q.1,(fun h => exchangePlan (q.2.1 h)),q.2.2) ∈ EncodedGraphMemory.rawStates input at member
  simpa only [EncodedGraphMemory.stateEncode,EncodedBankRoleExchange.bankEncode_unexchange] using member

omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem initial_encode : EncodedGraphMemory.initial input = encode ((source,(fun _ => true),start),bank,true) := by
  change EncodedGraphMemory.initial original = _
  rw [EncodedGraphMemory.initial_encode]
  unfold EncodedGraphMemory.stateEncode
  rw [EncodedBankRoleExchange.bankEncode_unexchange]

omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem letterEncode_mem (group : H → G)
    (a : RealizedBlockRound I₁ I₂ (RollingReceiverOutput H I₂ I₁ O₂ O₁ d) (G → O₂)) :
    EncodedGraphMemory.letterEncode root swappedEnv swappedOut group a ∈ EncodedGraphMemory.letters input :=
  EncodedGraphMemory.letterEncode_mem root swappedEnv two one swappedOut outTwo outOne number (exchangeShape shape)
    recognizer graphs advance source start bank transitions slot minimum group a

end Characterisation.EncodedLeftGraphMemory
