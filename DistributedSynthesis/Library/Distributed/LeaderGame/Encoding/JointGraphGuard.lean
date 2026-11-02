/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.LocalLeaderLanguage

/-! One memory suffices for promised tables and graph-coupled closing
offers. The graph memory already carries the current bank and first-round
bit. The fused guard checks both obligations before advancing that memory;
its accepting plays are exactly those of the original nested guard. -/
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
variable (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ d)
variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
variable (permitted : Finset (LeaderHandover Q B C))
variable (phase : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H → O₂) (G → O₁))

def jointGraphGuard : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁
    (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁) :=
  leaderMemoryMonitor phase Prod.fst ((source,(fun _ => true),initial),bank,true)
    (jointGraphLeaderNext group recognizer step advance)
    (fun state letter => jointLeaderCheck group shape state.2 letter &&
      decide (jointGraphLeaderCollect recognizer step shape slot minimum state letter ⊆ permitted))

omit [Fintype H] [DecidableEq H] [Fintype G] [DecidableEq G] [Fintype GQ] [DecidableEq GQ]
    [Fintype Q] [DecidableEq Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] in
theorem jointGraphLeaderMemory_bank
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) (n : Nat) :
    (phaseMemoryRun ((source,(fun _ => true),initial),bank,true)
      (jointGraphLeaderNext group recognizer step advance) play n).2 =
        phaseMemoryRun (bank,true) jointLeaderNext play n := by
  cases n <;> rfl

omit [Fintype G] [DecidableEq G] in
/-- The complete local obligation, with no bound on the phase duration.
The collector is evaluated on the current bank, before the new round. -/
theorem jointGraphGuard_wins_iff
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    (jointGraphGuard group shape recognizer step advance source initial bank slot minimum permitted phase).WinsPlay play ↔
      phase.WinsPlay (phasePhysicalPlay Prod.fst play) ∧
      (∀ n, jointLeaderCheck group shape (phaseMemoryRun (bank,true) jointLeaderNext play n) (play n) = true) ∧
      ∀ n, jointGraphLeaderCollect recognizer step shape slot minimum
        (phaseMemoryRun ((source,(fun _ => true),initial),bank,true)
          (jointGraphLeaderNext group recognizer step advance) play n) (play n) ⊆ permitted := by
  simp only [jointGraphGuard,leaderMemoryMonitor_wins_iff,Bool.and_eq_true,decide_eq_true_eq,
    jointGraphLeaderMemory_bank,forall_and]

omit [Fintype G] [DecidableEq G] in
theorem jointGraphGuard_wins_iff_nested
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    (jointGraphGuard group shape recognizer step advance source initial bank slot minimum permitted phase).WinsPlay play ↔
      (phaseOfferMonitor (jointLeaderMonitor group shape phase bank) id
        ((source,(fun _ => true),initial),bank,true)
        (jointGraphLeaderNext group recognizer step advance)
        (jointGraphLeaderCollect recognizer step shape slot minimum) permitted).WinsPlay play := by
  rw [jointGraphGuard_wins_iff,phaseOfferMonitor_wins_iff]
  have projected : phasePhysicalPlay id play = play := by
    funext n
    rfl
  rw [projected,jointLeaderMonitor_wins_iff]
  exact and_assoc.symm

variable (phase' : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H → O₂) (G → O₁))

omit [Fintype G] [DecidableEq G] in
/-- Replacing the all-root phase objective changes neither the promised
tables nor the permitted complete closing choices. -/
theorem jointGraphGuard_language_congr
    (same : ∀ play, phase.WinsPlay play ↔ phase'.WinsPlay play)
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    (jointGraphGuard group shape recognizer step advance source initial bank slot minimum permitted phase).WinsPlay play ↔
      (jointGraphGuard group shape recognizer step advance source initial bank slot minimum permitted phase').WinsPlay play := by
  rw [jointGraphGuard_wins_iff,jointGraphGuard_wins_iff]
  exact and_congr_left (fun _ => same _)

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
variable (bank : ClosingPlanBank (Fin header.1.val) I₁ I₂ O₁ O₂ d)

/-- Specialization to the actual numbered right-leader guard. The source
graph states, reset minima, root slots, and permitted outcomes are unchanged. -/
theorem numberedRightGuard_wins_iff_fused
    (play : Nat → RealizedBlockRound I₂ I₁
      (RollingReceiverOutput (Fin header.1.val) I₁ I₂ O₁ O₂ d)
      (ShapeLeaderGroup header.2.1 .one → O₁)) :
    (numberedRightGuard recognizer objective rank header permitted bank).WinsPlay play ↔
      (jointGraphGuard (shapeLeaderGroup header.2.1 .one) header.2.1 recognizer
        (leaderAnnotationStep recognizer objective rank)
        (fun st => chooseGraphRootNext recognizer st .right)
        (fun i => (header.2.2 i).1.1) (fun i => resetLeaderMinimum objective (header.2.2 i)) bank
        (numberedLeaderSlot objective header) (fun q => q.2 ()) permitted
        (jointPhaseObjective objective (fun i => (header.2.2 i).1.2)
          (shapeLeaderGroup header.2.1 .one))).WinsPlay play :=
  (jointGraphGuard_wins_iff_nested _ _ _ _ _ _ _ _ _ _ _ _ play).symm

end Numbered
end Characterisation
