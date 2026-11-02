/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphMemory
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphCollectorCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderMemoryCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.JointGraphGuard

/-! The generated memory is the existing joint graph memory, with the same
physical annotation updates, persistent activity, promised bank, and complete
closing collector. Numberings are proof-side interfaces to finite codes. -/
namespace Characterisation.EncodedGraphMemory
open DistributedSynthesis

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

noncomputable def dataEncode : Data :=
  ((EncodedGraphCollector.dataEncode root env one two output outOne outTwo number shape bank start transitions
    recognizer graphs source true slot minimum (fun _ => true)).1,
    FiniteFunctionCodes.encode graphs (fun q => graphs (advance q)),
    List.ofFn (fun i => graphRootStop recognizer (graphs.symm i) .right),C)

abbrev SemanticState := GraphLeaderMemory H GQ Q I₁ I₂ O₁ O₂ d K

noncomputable def stateEncode (q : SemanticState (H:=H) (GQ:=GQ) (Q:=Q) (I₁:=I₁) (I₂:=I₂) (O₁:=O₁) (O₂:=O₂) (d:=d) (K:=K)) : State :=
  ((FiniteFunctionCodes.encode root (graphs ∘ q.1.1),List.ofFn (fun i => q.1.2.1 (root.symm i)),
    FiniteFunctionCodes.encode root (number ∘ q.1.2.2)),EncodedClosingBanks.bankEncode root env output q.2.1,q.2.2)

noncomputable def letterEncode (group : H → G)
    (a : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) : Letter :=
  ((env (a.1.2,a.1.1,.right)).val,
    FiniteFunctionCodes.encode root (fun h => output (a.2.2 (group h),a.2.1.1 h)),
    EncodedClosingBanks.bankEncode root env output a.2.1.2)

local notation "input" => dataEncode root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum
local notation "encode" => stateEncode root env output number graphs

omit [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [DecidableEq H]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] in
theorem refined_encode : refined (EncodedClosingBanks.dataEncode root env one two output outOne outTwo shape (d+1)) =
    EncodedClosingBanks.dataEncode root env one two output outOne outTwo (rightRefinedShape shape) (d+1) := by
  simp only [refined,EncodedClosingBanks.dataEncode,EncodedClosingBanks.matrix,List.map_ofFn,rightRefinedShape]
  rfl

omit [Fintype Q] [DecidableEq Q] [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁]
    [Fintype O₂] [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem currentBankData_encode (first : Bool) : currentBankData input first =
    EncodedClosingBanks.dataEncode root env one two output outOne outTwo (jointLeaderShape shape first) (d+1) := by
  cases first with
  | false => exact refined_encode root env one two output outOne outTwo shape
  | true => rfl

omit [Fintype Q] [DecidableEq Q] [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁]
    [Fintype O₂] [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem collector_encode (q : SemanticState (H:=H) (GQ:=GQ) (Q:=Q) (I₁:=I₁) (I₂:=I₂) (O₁:=O₁) (O₂:=O₂) (d:=d) (K:=K)) :
    collector input (encode q) =
      EncodedGraphCollector.dataEncode root env one two output outOne outTwo number
        (jointLeaderShape shape q.2.2) q.2.1 q.1.2.2 transitions recognizer graphs q.1.1 q.2.2 slot minimum q.1.2.1 := by
  unfold collector
  rw [currentBankData_encode]
  rfl

omit [Fintype Q] [DecidableEq Q] [Fintype O₁] [Fintype O₂] [DecidableEq H] in
theorem rolling_encode (group : H → G)
    (q : SemanticState (H:=H) (GQ:=GQ) (Q:=Q) (I₁:=I₁) (I₂:=I₂) (O₁:=O₁) (O₂:=O₂) (d:=d) (K:=K))
    (a : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    rolling input (encode q) (letterEncode root env output group a) = jointLeaderCheck group shape q.2 a := by
  have expected : ((letterEncode root env output group a).2.1).map
      (fun o => (EncodedClosingBanks.outputTable (bankData input)).getD o (0,0)) =
      List.ofFn (fun i => ((outOne (a.2.2 (group (root.symm i)))).val,(outTwo (a.2.1.1 (root.symm i))).val)) := by
    simp only [letterEncode,FiniteFunctionCodes.encode,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact EncodedClosingBanks.table_eval output
      (fun o => ((outOne o.1).val,(outTwo o.2).val)) (0,0) _
  unfold rolling
  rw [currentBankData_encode,expected]
  have refinedData : refined (bankData input) =
      EncodedClosingBanks.dataEncode root env one two output outOne outTwo (rightRefinedShape shape) (d+1) :=
    refined_encode root env one two output outOne outTwo shape
  rw [refinedData]
  exact EncodedLeaderMemory.jointLeaderCheck_encode root env one two output outOne outTwo group shape q.2 a

variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (transition : ∀ q r o, EncodedParityTables.next transitions (number q).val
  ((env r).val*V+(output o).val) = (number (step q r o)).val)

include transition in
omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] in
theorem next_encode (group : H → G)
    (q : SemanticState (H:=H) (GQ:=GQ) (Q:=Q) (I₁:=I₁) (I₂:=I₂) (O₁:=O₁) (O₂:=O₂) (d:=d) (K:=K))
    (a : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    next input (encode q) (letterEncode root env output group a) =
      encode (jointGraphLeaderNext group recognizer step advance q a) := by
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
          !((List.ofFn (fun i => graphRootStop recognizer (graphs.symm i) .right)).getD
            ((FiniteFunctionCodes.encode root (graphs ∘ q.1.1)).getD i.val 0) false)) = _
        rw [← hi,EncodedClosingBanks.table_eval root q.1.2.1 false h,
          FiniteFunctionCodes.eval_encode]
        simp only [Function.comp_apply]
        rw [
          EncodedClosingBanks.table_eval graphs (fun g => graphRootStop recognizer g .right) false]
        rfl
      · apply FiniteSearch.tabulate_eq_ofFn
        intro i
        let h := root.symm i
        have hi : (root h).val = i.val := by simp [h]
        change EncodedParityTables.next transitions
          ((FiniteFunctionCodes.encode root (number ∘ q.1.2.2)).getD i.val 0)
          ((env (a.1.2,a.1.1,.right)).val*V+
            (FiniteFunctionCodes.encode root (fun h => output (a.2.2 (group h),a.2.1.1 h))).getD i.val 0) = _
        rw [← hi,FiniteFunctionCodes.eval_encode,FiniteFunctionCodes.eval_encode]
        simp only [Function.comp_apply]
        rw [transition]
        rfl
  · rfl

include transition in
theorem collect_member_encode
    (q : SemanticState (H:=H) (GQ:=GQ) (Q:=Q) (I₁:=I₁) (I₂:=I₂) (O₁:=O₁) (O₂:=O₂) (d:=d) (K:=K))
    (outcome : LeaderHandover Q B C) :
    EncodedLeaderAlphabet.outcomeEncode number outcome ∈ EncodedGraphCollector.collect (collector input (encode q)) ↔
      outcome ∈ graphClosingOffers recognizer q.1.1 q.1.2.1 (jointLeaderShape shape q.2.2) q.2.2
        step q.1.2.2 (closingPolicyOfBank q.2.1) slot minimum := by
  rw [collector_encode]
  exact EncodedGraphCollector.collect_encode root env one two output outOne outTwo number _ _ _ _
    recognizer graphs _ _ slot minimum _ step transition outcome

end Characterisation.EncodedGraphMemory
