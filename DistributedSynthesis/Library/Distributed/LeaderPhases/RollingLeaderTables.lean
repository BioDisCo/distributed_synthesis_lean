/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderMemoryCompression

/-! One leader table carries a finite bank of closing promises along an
arbitrarily long rightward phase. The receiver has a row for each hidden
root; the sender has one output depending only on its own input history.
Local coherence within hypothetical closing branches and selection of the
next global boundary remain additional obligations. -/
namespace Characterisation
open DistributedSynthesis

abbrev ClosingPlanBank (H I₁ I₂ O₁ O₂ : Type) (D : Nat) :=
  H → LeaderClosingPlan I₁ I₂ O₁ O₂ (D+1)

instance closingPlanBank_fintype {H I₁ I₂ O₁ O₂ : Type}
    [Fintype H] [DecidableEq H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq I₁] [DecidableEq I₂] (D : Nat) :
    Fintype (ClosingPlanBank H I₁ I₂ O₁ O₂ D) := by
  letI : Fintype (ClosingScenario I₁ I₂ (D+1)) := by
    unfold ClosingScenario WindowScenario
    infer_instance
  letI : DecidableEq (ClosingScenario I₁ I₂ (D+1)) := by
    unfold ClosingScenario WindowScenario
    infer_instance
  letI : Fintype (LeaderClosingPlan I₁ I₂ O₁ O₂ (D+1)) := by
    unfold LeaderClosingPlan
    infer_instance
  unfold ClosingPlanBank
  infer_instance

abbrev RollingReceiverOutput (H I₁ I₂ O₁ O₂ : Type) (D : Nat) :=
  (H → O₂) × ClosingPlanBank H I₁ I₂ O₁ O₂ D

def rollingLeaderNext {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (_ : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) O₁) :
    ClosingPlanBank H I₁ I₂ O₁ O₂ D := letter.2.1.2

def rollingLeaderCheck {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    [Fintype H] [Fintype I₁] [Fintype I₂] [DecidableEq O₁] [DecidableEq O₂]
    (old : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) O₁) : Bool :=
  decide (∀ h,
    RollingClosingOverlap (old h) (letter.2.1.2 h) (letter.1.2,letter.1.1,.right) ∧
    closingPlanEntry (old h) (fun _ => (letter.1.2,letter.1.1,.right)) ⟨0,by omega⟩ =
      (letter.2.2,letter.2.1.1 h))

section Monitor
variable {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
variable [Fintype H] [DecidableEq H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (M : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H → O₂) O₁)
variable (initial : ClosingPlanBank H I₁ I₂ O₁ O₂ D)

def rollingLeaderMonitor :
    BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) O₁ :=
  leaderMemoryMonitor M Prod.fst initial rollingLeaderNext rollingLeaderCheck

/-- The monitored state remembers the last emitted bank, including the
initial bank before the first round. -/
theorem rollingLeaderMonitor_correct
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) O₁) :
    (rollingLeaderMonitor M initial).WinsPlay play ↔
      M.WinsPlay (phasePhysicalPlay Prod.fst play) ∧
      ∀ n h,
        RollingClosingOverlap (phaseMemoryRun initial rollingLeaderNext play n h)
          (phaseMemoryRun initial rollingLeaderNext play (n+1) h)
          ((play n).1.2,(play n).1.1,.right) ∧
        closingPlanEntry (phaseMemoryRun initial rollingLeaderNext play n h)
          (fun _ => ((play n).1.2,(play n).1.1,.right)) ⟨0,by omega⟩ =
            ((play n).2.2,(play n).2.1.1 h) := by
  rw [rollingLeaderMonitor,leaderMemoryMonitor_wins_iff]
  simp only [rollingLeaderCheck,decide_eq_true_eq,phaseMemoryRun,rollingLeaderNext]

/-- Every earlier promise is honored by the actual later outputs. This
holds at every starting time in an unbounded phase and for every hidden root.
The bank is replenished every round without shortening future obligations. -/
theorem rollingLeaderMonitor_promises
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) O₁)
    (wins : (rollingLeaderMonitor M initial).WinsPlay play)
    (a t : Nat) (within : t < D+1) (h : H) :
    closingPlanEntry (phaseMemoryRun initial rollingLeaderNext play a h)
      (fun n => ((play (a+n)).1.2,(play (a+n)).1.1,.right)) ⟨t,within⟩ =
        ((play (a+t)).2.2,(play (a+t)).2.1.1 h) := by
  have checks := ((rollingLeaderMonitor_correct M initial play).mp wins).2
  have preserved := rollingClosingPlans_preserve_promises
    (fun n => phaseMemoryRun initial rollingLeaderNext play n h)
    (fun n => ((play n).1.2,(play n).1.1,.right))
    (fun n => (checks n h).1) a t within
  rw [preserved,closingPlanEntry_zero]
  exact (checks (a+t) h).2

variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]

/-- A winning one-way strategy with compatible rolling promises can be
replaced by a member of one fixed finite leader-table alphabet. The physical
parity condition and all promises are imposed together before narrowing. -/
theorem rollingLeader_finite_table
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D))
    (leader : SenderBlockStrategy I₁ O₁)
    (physical : ∀ env, M.WinsPlay (phasePhysicalPlay Prod.fst (pairPlay receiver leader env)))
    (checks : ∀ env n,
      rollingLeaderCheck (phaseMemoryRun initial rollingLeaderNext (pairPlay receiver leader env) n)
        (pairPlay receiver leader env n) = true) :
    ∃ table : FiniteRootFamilyTable (fun _ : Unit => rollingLeaderMonitor M initial),
      NarrowedAllThreadsWin (rollingLeaderMonitor M initial)
        (finiteRootMemberController (fun _ : Unit => rollingLeaderMonitor M initial)
          table.toTransitionRationalTree ()).labeledTree :=
  leaderMemory_finite_table M Prod.fst initial rollingLeaderNext rollingLeaderCheck
    receiver leader physical checks

end Monitor
end Characterisation
