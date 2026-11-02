/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.JointLeaderCompression
import DistributedSynthesis.Library.Distributed.LeaderPhases.GraphLeaderCollectorReadback

/-! The concrete graph collector for a joint phase table. All initial
leader-view groups share the same finite memory and offer restriction.
Each root's physical output is selected from its observable group entry. -/
namespace Characterisation
open DistributedSynthesis

section
variable {H G GQ Q I₁ I₂ O₁ O₂ : Type} {d K : Nat}
variable (group : H → G)

def jointGraphRound
    (letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    H → RoundRecord I₁ I₂ Graph Unit Unit := fun _ => ⟨letter.1.2,letter.1.1,.right,(),()⟩

def jointGraphOutput
    (letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    H → O₁ × O₂ := fun h => (letter.2.2 (group h),letter.2.1.1 h)

variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (advance : GraphRootState GQ d K → GraphRootState GQ d K)

def jointGraphLeaderNext (state : GraphLeaderMemory H GQ Q I₁ I₂ O₁ O₂ d K)
    (letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    GraphLeaderMemory H GQ Q I₁ I₂ O₁ O₂ d K :=
  (coupledRootNext M step state.1 (jointGraphRound letter,jointGraphOutput group letter,
    fun h => advance (state.1.1 h)),letter.2.1.2,false)

theorem jointGraphLeaderMemory_run
    (source : H → GraphRootState GQ d K) (initial : H → Q)
    (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ d)
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) (n : Nat) :
    phaseMemoryRun ((source,(fun _ => true),initial),bank,true) (jointGraphLeaderNext group M step advance) play n =
      ((graphLeaderBankRun advance source n,
        rootActivityRun (fun i h => graphRootStop M (graphLeaderBankRun advance source i h) .right) n,
        rootMonitorRun step initial (fun i => jointGraphRound (play i)) (fun i => jointGraphOutput group (play i)) n),
        (phaseMemoryRun (bank,true) jointLeaderNext play n).1,decide (n = 0)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [phaseMemoryRun,ih]; rfl

variable [Fintype H] [DecidableEq H] [Fintype GQ] [DecidableEq GQ] [Fintype Q] [DecidableEq Q]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]

def jointGraphLeaderCollect {B C : Nat} (shape : InputShape H)
    (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
    (state : GraphLeaderMemory H GQ Q I₁ I₂ O₁ O₂ d K)
    (_letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    Finset (LeaderHandover Q B C) :=
  graphClosingOffers M state.1.1 state.1.2.1 (jointLeaderShape shape state.2.2) state.2.2 step state.1.2.2
    (closingPolicyOfBank state.2.1) slot minimum

theorem jointGraphLeaderCollect_at_cut {B C : Nat} (shape : InputShape H)
    (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
    (source : H → GraphRootState GQ d K) (initial : H → Q)
    (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ d)
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) (n : Nat) :
    jointGraphLeaderCollect M step shape slot minimum
      (phaseMemoryRun ((source,(fun _ => true),initial),bank,true) (jointGraphLeaderNext group M step advance) play n) (play n) =
      graphClosingOffers M (graphLeaderBankRun advance source n)
        (rootActivityRun (fun i h => graphRootStop M (graphLeaderBankRun advance source i h) .right) n)
        (jointLeaderShape shape (decide (n = 0))) (decide (n = 0)) step
        (rootMonitorRun step initial (fun i => jointGraphRound (play i)) (fun i => jointGraphOutput group (play i)) n)
        (closingPolicyOfBank (phaseMemoryRun (bank,true) jointLeaderNext play n).1) slot minimum := by
  rw [jointGraphLeaderMemory_run]
  rfl

end
end Characterisation
