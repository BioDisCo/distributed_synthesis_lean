/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RollingPhaseReadback

/-! The finite monitor's winning condition supplies every hypothesis of
the whole-phase local readback theorem. The resulting strategy reproduces
the closing plans and the physical outputs of the checked leader table. -/
namespace Characterisation
open DistributedSynthesis

def receiverClosingBank {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (initial : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D))
    (node : List (I₂ × I₁)) : ClosingPlanBank H I₁ I₂ O₁ O₂ D :=
  match node.getLast? with
  | none => initial
  | some r => (receiver node.dropLast r).2

@[simp] theorem receiverClosingBank_snoc {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (initial : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D))
    (node : List (I₂ × I₁)) (r : I₂ × I₁) :
    receiverClosingBank initial receiver (node++[r]) = (receiver node r).2 := by
  simp only [receiverClosingBank,List.getLast?_concat,List.dropLast_concat]

theorem receiverClosingBank_memory {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (initial : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D))
    (leader : SenderBlockStrategy I₁ O₁) (env : Nat → I₂ × I₁) (n : Nat) :
    phaseMemoryRun initial rollingLeaderNext (pairPlay receiver leader env) n =
      receiverClosingBank initial receiver (branchNode env n) := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [branchNode,receiverClosingBank_snoc]
    rfl

/-- A finite input node and its next input occur on an infinite thread. -/
theorem rollingBranch_realizes_step {B : Type} [Inhabited B] (node : List B) (r : B) :
    ∃ env : Nat → B, branchNode env node.length = node ∧ env node.length = r := by
  let env : Nat → B := fun n => (node++[r]).getD n default
  have old : branchNode env node.length = node := by
    simpa only [List.take_left] using rollingBranch_take (node++[r]) node.length (by simp)
  have full : branchNode env (node.length+1) = node++[r] := by
    have eq := rollingBranch_take (node++[r]) (node.length+1) (by simp)
    rw [List.take_of_length_le (show (node++[r]).length ≤ node.length+1 by simp)] at eq
    exact eq
  rw [branchNode,old] at full
  exact ⟨env,old,List.singleton_inj.mp (List.append_cancel_left full)⟩

section Checked
variable {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
variable [Fintype H] [DecidableEq H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Inhabited I₁] [Inhabited I₂] [Nonempty O₁] [Nonempty O₂]
variable (M : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H → O₂) O₁)
variable (shape : InputShape H) (initial : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
variable (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D))
variable (leader : SenderBlockStrategy I₁ O₁)
variable (wins : ∀ env, (coherentRollingMonitor M shape initial).WinsPlay (pairPlay receiver leader env))

include wins in
omit [Nonempty O₁] [Nonempty O₂] in
/-- Winning on every infinite input thread enforces the finite checks at
every finite node. No extra cross-thread assumption is added. -/
theorem checkedReceiverBank_step (node : List (I₂ × I₁)) (r : I₂ × I₁) :
    ClosingBankCoherent shape (receiverClosingBank initial receiver node) ∧
      ∀ h, RollingClosingOverlap (receiverClosingBank initial receiver node h)
          (receiverClosingBank initial receiver (node++[r]) h) (r.2,r.1,.right) ∧
        closingPlanEntry (receiverClosingBank initial receiver node h)
            (fun _ => (r.2,r.1,.right)) ⟨0,by omega⟩ =
          (leader (senderWord node) r.2,(receiver node r).1 h) := by
  obtain ⟨env,old,fresh⟩ := rollingBranch_realizes_step node r
  have correct := (coherentRollingMonitor_correct M shape initial _).mp (wins env)
  have coherent := correct.2 node.length
  rw [receiverClosingBank_memory,old] at coherent
  have checks := ((rollingLeaderMonitor_correct M initial _).mp correct.1).2 node.length
  have letter : pairPlay receiver leader env node.length =
      (r,receiver node r,leader (senderWord node) r.2) := by
    simp only [pairPlay,treePlay,treeOfPair,blockLabelApply,old,fresh]
  simp only [receiverClosingBank_memory,branchNode,old,fresh,letter] at checks
  exact ⟨coherent,checks⟩

include wins in
/-- Read back an all-thread winner into one actual local strategy. It
implements all carried closing plans and every physical rightward output. -/
theorem checked_leader_phase_readback
    (past : H → EnvHistory I₁ I₂) (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (leaders : ∀ h k, currentView .one (past h) = currentView .one (past k)) :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      (∀ node h, closingPlanOfStrategy σ (rollingSourceHistory past node h) (D+1) =
        receiverClosingBank initial receiver node h) ∧
      (∀ node r h,
        σ.one (currentView .one (rollingSourceHistory past (node++[r]) h)) =
            leader (senderWord node) r.2 ∧
        σ.two (currentView .two (rollingSourceHistory past (node++[r]) h)) =
            (receiver node r).1 h) ∧
      (∀ env, M.WinsPlay (phasePhysicalPlay Prod.fst (pairPlay receiver leader env))) := by
  have step := checkedReceiverBank_step M shape initial receiver leader wins
  obtain ⟨σ,plans⟩ := rollingBanks_phase_plans past shape rep L depth leaders
    (receiverClosingBank initial receiver) leader
    (fun node r h => ((step node r).2 h).1)
    (fun node => (step node default).1)
    (fun node r h => congrArg Prod.fst ((step node r).2 h).2)
  refine ⟨σ,plans,?_,?_⟩
  · intro node r h
    have output := ((step node r).2 h).2
    rw [← plans node h,closingPlanOfStrategy_first] at output
    rw [rollingSourceHistory_snoc]
    exact ⟨congrArg Prod.fst output,congrArg Prod.snd output⟩
  · intro env
    have rolling := ((coherentRollingMonitor_correct M shape initial _).mp (wins env)).1
    exact ((rollingLeaderMonitor_correct M initial _).mp rolling).1

end Checked
end Characterisation
