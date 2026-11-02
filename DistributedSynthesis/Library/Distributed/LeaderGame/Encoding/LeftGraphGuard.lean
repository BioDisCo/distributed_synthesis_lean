/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeftLeader
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.JointGraphGuard

/-! One memory for left-leader promises and complete closing offers. Local
roles are exchanged, while graph states, stop tests and the closing
collector remain those of the original recognizer. -/
namespace Characterisation
open DistributedSynthesis

section
variable {H G GQ Q I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype H] [DecidableEq H] [Fintype G] [DecidableEq G]
variable [Fintype GQ] [DecidableEq GQ] [Fintype Q] [DecidableEq Q]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (group : H → G) (shape : InputShape H)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (advance : GraphRootState GQ d K → GraphRootState GQ d K)
variable (source : H → GraphRootState GQ d K) (initial : H → Q)
variable (bank : ClosingPlanBank H I₂ I₁ O₂ O₁ d)
variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
variable (permitted : Finset (LeaderHandover Q B C))
variable (phase : BlockRecordMonitor.{0,0,0,0,0} I₁ I₂ (H → O₁) (G → O₂))

noncomputable def leftGraphLeaderNext
    (q : GraphLeaderMemory H GQ Q I₂ I₁ O₂ O₁ d K)
    (a : RealizedBlockRound I₁ I₂ (RollingReceiverOutput H I₂ I₁ O₂ O₁ d) (G → O₂)) :
    GraphLeaderMemory H GQ Q I₂ I₁ O₂ O₁ d K :=
  (coupledRootNext recognizer step q.1
    ((fun _ => ⟨a.1.1,a.1.2,.left,(),()⟩),
      (fun h => (a.2.1.1 h,a.2.2 (group h))),fun h => advance (q.1.1 h)),a.2.1.2,false)

noncomputable def leftGraphLeaderCollect
    (q : GraphLeaderMemory H GQ Q I₂ I₁ O₂ O₁ d K)
    (_a : RealizedBlockRound I₁ I₂ (RollingReceiverOutput H I₂ I₁ O₂ O₁ d) (G → O₂)) :
    Finset (LeaderHandover Q B C) :=
  graphClosingOffers recognizer q.1.1 q.1.2.1
    (exchangeShape (jointLeaderShape (exchangeShape shape) q.2.2)) q.2.2
    step q.1.2.2 (closingPolicyOfBank (fun h => exchangePlan (q.2.1 h))) slot minimum

noncomputable def leftGraphGuard : BlockRecordMonitor.{0,0,0,0,0} I₁ I₂
    (RollingReceiverOutput H I₂ I₁ O₂ O₁ d) (G → O₂) :=
  leaderMemoryMonitor phase Prod.fst ((source,(fun _ => true),initial),bank,true)
    (leftGraphLeaderNext group recognizer step advance)
    (fun q a => jointLeaderCheck group (exchangeShape shape) q.2 a &&
      decide (leftGraphLeaderCollect shape recognizer step slot minimum q a ⊆ permitted))

omit [Fintype H] [DecidableEq H] [Fintype G] [DecidableEq G] [Fintype GQ] [DecidableEq GQ]
    [Fintype Q] [DecidableEq Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] in
theorem leftGraphLeaderMemory_bank
    (play : Nat → RealizedBlockRound I₁ I₂ (RollingReceiverOutput H I₂ I₁ O₂ O₁ d) (G → O₂)) (n : Nat) :
    (phaseMemoryRun ((source,(fun _ => true),initial),bank,true)
      (leftGraphLeaderNext group recognizer step advance) play n).2 =
        phaseMemoryRun (bank,true) jointLeaderNext play n := by
  cases n <;> rfl

omit [Fintype G] [DecidableEq G] in
theorem leftGraphGuard_wins_iff
    (play : Nat → RealizedBlockRound I₁ I₂ (RollingReceiverOutput H I₂ I₁ O₂ O₁ d) (G → O₂)) :
    (leftGraphGuard group shape recognizer step advance source initial bank slot minimum permitted phase).WinsPlay play ↔
      phase.WinsPlay (phasePhysicalPlay Prod.fst play) ∧
      (∀ n, jointLeaderCheck group (exchangeShape shape)
        (phaseMemoryRun (bank,true) jointLeaderNext play n) (play n) = true) ∧
      ∀ n, leftGraphLeaderCollect shape recognizer step slot minimum
        (phaseMemoryRun ((source,(fun _ => true),initial),bank,true)
          (leftGraphLeaderNext group recognizer step advance) play n) (play n) ⊆ permitted := by
  simp only [leftGraphGuard,leaderMemoryMonitor_wins_iff,Bool.and_eq_true,decide_eq_true_eq,
    leftGraphLeaderMemory_bank,forall_and]

omit [Fintype G] [DecidableEq G] in
theorem leftGraphGuard_wins_iff_nested
    (play : Nat → RealizedBlockRound I₁ I₂ (RollingReceiverOutput H I₂ I₁ O₂ O₁ d) (G → O₂)) :
    (leftGraphGuard group shape recognizer step advance source initial bank slot minimum permitted phase).WinsPlay play ↔
      (phaseOfferMonitor (jointLeaderMonitor group (exchangeShape shape) phase bank) id
        ((source,(fun _ => true),initial),bank,true)
        (leftGraphLeaderNext group recognizer step advance)
        (leftGraphLeaderCollect shape recognizer step slot minimum) permitted).WinsPlay play := by
  rw [leftGraphGuard_wins_iff,phaseOfferMonitor_wins_iff]
  have projected : phasePhysicalPlay id play = play := by funext n; rfl
  rw [projected,jointLeaderMonitor_wins_iff]
  exact and_assoc.symm

end

section Numbered
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable [DecidableEq objective.State] (rank : objective.State → Fin (C+1))
variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
variable (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))
variable (bank : ClosingPlanBank (Fin header.1.val) I₂ I₁ O₂ O₁ d)

theorem numberedLeftGuard_wins_iff_fused (play : Nat → NumberedLeftLetter objective header) :
    (numberedLeftGuard recognizer objective rank header permitted bank).WinsPlay play ↔
      (leftGraphGuard (shapeLeaderGroup header.2.1 .two) header.2.1 recognizer
        (leaderAnnotationStep recognizer objective rank) (fun q => chooseGraphRootNext recognizer q .left)
        (fun i => (header.2.2 i).1.1) (fun i => resetLeaderMinimum objective (header.2.2 i)) bank
        (numberedLeaderSlot objective header) (fun q => q.2 ()) permitted
        (jointPhaseObjective (objective.comap exchangeLetter) (fun i => (header.2.2 i).1.2)
          (shapeLeaderGroup header.2.1 .two))).WinsPlay play :=
  (leftGraphGuard_wins_iff_nested (shapeLeaderGroup header.2.1 .two) header.2.1 recognizer
    (leaderAnnotationStep recognizer objective rank) (fun q => chooseGraphRootNext recognizer q .left)
    (fun i => (header.2.2 i).1.1) (fun i => resetLeaderMinimum objective (header.2.2 i)) bank
    (numberedLeaderSlot objective header) (fun q => q.2 ()) permitted
    (jointPhaseObjective (objective.comap exchangeLetter) (fun i => (header.2.2 i).1.2)
      (shapeLeaderGroup header.2.1 .two)) play).symm

end Numbered
end Characterisation
