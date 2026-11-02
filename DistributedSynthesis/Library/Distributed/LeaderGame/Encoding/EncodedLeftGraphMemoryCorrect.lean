/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeftGraphMemory
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphMemoryCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.LeftGraphGuard

/-! The reused numeric memory follows original leftward graph steps.
Collector equality is with the original recognizer and the unexchanged
closing bank, not with a mirrored recognizer or independent target choices. -/
namespace Characterisation.EncodedLeftGraphMemory
open DistributedSynthesis

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

noncomputable def dataEncode : Data :=
  prepare (EncodedGraphMemory.dataEncode root env one two out outOne outTwo number shape recognizer graphs
    advance source start (fun h => exchangePlan (bank h)) transitions slot minimum)
    (List.ofFn (fun i => graphRootStop recognizer (graphs.symm i) .left))
local notation "input" => dataEncode root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum

section
omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂]

theorem bankData_encode : EncodedGraphMemory.bankData input =
    EncodedClosingBanks.dataEncode root swappedEnv two one swappedOut outTwo outOne (exchangeShape shape) (d+1) :=
  EncodedBankRoleExchange.bankData_encode root env one two out outOne outTwo shape

theorem currentBankData_encode (first : Bool) : EncodedGraphMemory.currentBankData input first =
    EncodedClosingBanks.dataEncode root swappedEnv two one swappedOut outTwo outOne
      (jointLeaderShape (exchangeShape shape) first) (d+1) := by
  unfold EncodedGraphMemory.currentBankData
  rw [bankData_encode]
  cases first with
  | false => exact EncodedGraphMemory.refined_encode root swappedEnv two one swappedOut outTwo outOne (exchangeShape shape)
  | true => rfl

theorem collector_encode (q : Memory) : collector input (encode q) =
    EncodedGraphCollector.dataEncode root env one two out outOne outTwo number
      (exchangeShape (jointLeaderShape (exchangeShape shape) q.2.2)) (fun h => exchangePlan (q.2.1 h))
      q.1.2.2 transitions recognizer graphs q.1.1 q.2.2 slot minimum q.1.2.1 := by
  unfold collector EncodedGraphMemory.collector
  rw [currentBankData_encode]
  dsimp only
  rw [EncodedBankRoleExchange.bankData_encode,
    EncodedBankRoleExchange.environment_twice,EncodedBankRoleExchange.output_twice]
  change (((_,EncodedClosingBanks.bankEncode root swappedEnv swappedOut q.2.1,_,_,_),_,_,_,_,_,_),_) = _
  rw [← EncodedBankRoleExchange.bankEncode_unexchange root env out q.2.1]
  rfl

end

omit [Fintype Q] [Fintype O₁] [Fintype O₂] [DecidableEq H] [DecidableEq Q] in
theorem rolling_encode (group : H → G) (q : Memory)
    (a : RealizedBlockRound I₁ I₂ (RollingReceiverOutput H I₂ I₁ O₂ O₁ d) (G → O₂)) :
    EncodedGraphMemory.rolling input (encode q) (EncodedGraphMemory.letterEncode root swappedEnv swappedOut group a) =
      jointLeaderCheck group (exchangeShape shape) q.2 a := by
  have metadata := bankData_encode root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum
  have expected : ((EncodedGraphMemory.letterEncode root swappedEnv swappedOut group a).2.1).map
      (fun o => (EncodedClosingBanks.outputTable (EncodedGraphMemory.bankData input)).getD o (0,0)) =
      List.ofFn (fun i => ((outTwo (a.2.2 (group (root.symm i)))).val,(outOne (a.2.1.1 (root.symm i))).val)) := by
    rw [metadata]
    simp only [EncodedGraphMemory.letterEncode,FiniteFunctionCodes.encode,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact EncodedClosingBanks.table_eval swappedOut
      (fun o => ((outTwo o.1).val,(outOne o.2).val)) (0,0) _
  unfold EncodedGraphMemory.rolling
  rw [currentBankData_encode,expected,metadata,
    EncodedGraphMemory.refined_encode root swappedEnv two one swappedOut outTwo outOne (exchangeShape shape)]
  exact EncodedLeaderMemory.jointLeaderCheck_encode root swappedEnv two one swappedOut outTwo outOne group (exchangeShape shape) q.2 a

variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (transition : ∀ q r o, EncodedParityTables.next transitions (number q).val
  ((env r).val*V+(out o).val) = (number (step q r o)).val)

include transition in
omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem next_encode (group : H → G) (q : Memory)
    (a : RealizedBlockRound I₁ I₂ (RollingReceiverOutput H I₂ I₁ O₂ O₁ d) (G → O₂)) :
    EncodedGraphMemory.next input (encode q) (EncodedGraphMemory.letterEncode root swappedEnv swappedOut group a) =
      encode (leftGraphLeaderNext group recognizer step advance q a) := by
  apply Prod.ext
  · apply Prod.ext
    · change (FiniteFunctionCodes.encode root (graphs ∘ q.1.1)).map
          (fun g => (FiniteFunctionCodes.encode graphs (fun q => graphs (advance q))).getD g 0) = _
      simp only [FiniteFunctionCodes.encode,List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      exact FiniteFunctionCodes.eval_encode graphs (fun q => graphs (advance q)) _
    · apply Prod.ext
      · apply FiniteSearch.tabulate_eq_ofFn
        intro i
        let h := root.symm i
        have hi : (root h).val = i.val := by simp [h]
        change ((List.ofFn (fun i => q.1.2.1 (root.symm i))).getD i.val false &&
          !((List.ofFn (fun i => graphRootStop recognizer (graphs.symm i) .left)).getD
            ((FiniteFunctionCodes.encode root (graphs ∘ q.1.1)).getD i.val 0) false)) = _
        rw [← hi,EncodedClosingBanks.table_eval root q.1.2.1 false h,FiniteFunctionCodes.eval_encode]
        simp only [Function.comp_apply]
        rw [EncodedClosingBanks.table_eval graphs (fun g => graphRootStop recognizer g .left) false]
        rfl
      · apply FiniteSearch.tabulate_eq_ofFn
        intro i
        let h := root.symm i
        have hi : (root h).val = i.val := by simp [h]
        change EncodedParityTables.next transitions
          ((FiniteFunctionCodes.encode root (number ∘ q.1.2.2)).getD i.val 0)
          ((env (a.1.1,a.1.2,.left)).val*V+
            (FiniteFunctionCodes.encode root (fun h => out (a.2.1.1 h,a.2.2 (group h)))).getD i.val 0) = _
        rw [← hi,FiniteFunctionCodes.eval_encode,FiniteFunctionCodes.eval_encode]
        simp only [Function.comp_apply]
        rw [transition]
        rfl
  · rfl

include transition in
theorem collect_member_encode (q : Memory) (outcome : LeaderHandover Q B C) :
    EncodedLeaderAlphabet.outcomeEncode number outcome ∈ EncodedGraphCollector.collect (collector input (encode q)) ↔
      outcome ∈ graphClosingOffers recognizer q.1.1 q.1.2.1
        (exchangeShape (jointLeaderShape (exchangeShape shape) q.2.2)) q.2.2
        step q.1.2.2 (closingPolicyOfBank (fun h => exchangePlan (q.2.1 h))) slot minimum := by
  rw [collector_encode]
  exact EncodedGraphCollector.collect_encode root env one two out outOne outTwo number _ _ _ _
    recognizer graphs _ _ slot minimum _ step transition outcome

end Characterisation.EncodedLeftGraphMemory
