/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingBankCoherence

/-! Narrow an entire unbounded one-way phase while preserving locally
implementable closing banks, their rolling overlap, and one supplied parity
objective. The cross-phase game and its observation-correct readback are not
assumed to follow from this phase theorem. -/
namespace Characterisation
open DistributedSynthesis

section
variable {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
variable [Fintype H] [DecidableEq H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (M : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H → O₂) O₁)
variable (shape : InputShape H) (initial : ClosingPlanBank H I₁ I₂ O₁ O₂ D)

def coherentRollingCheck (old : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) O₁) : Bool :=
  rollingLeaderCheck old letter && decide (ClosingBankCoherent shape old) &&
    decide (ClosingBankCoherent shape letter.2.1.2)

def coherentRollingMonitor :
    BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) O₁ :=
  leaderMemoryMonitor M Prod.fst initial rollingLeaderNext (coherentRollingCheck shape)

/-- Include the initial bank in the move alphabet, so the alphabet itself
does not depend on the strategy from which that bank was extracted. -/
abbrev CoherentLeaderPhaseMove :=
  Σ bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D,
    FiniteRootFamilyTable (fun _ : Unit => coherentRollingMonitor M shape bank)

instance coherentLeaderPhaseMove_finite [Nonempty I₁] : Finite (CoherentLeaderPhaseMove (D:=D) M shape) := by
  classical
  letI : Fintype (ClosingPlanBank H I₁ I₂ O₁ O₂ D) := closingPlanBank_fintype D
  letI : Fintype (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) := inferInstance
  letI : ∀ bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D,
      Fintype (FiniteRootFamilyTable (fun _ : Unit => coherentRollingMonitor M shape bank)) :=
    fun _ => by unfold FiniteRootFamilyTable; infer_instance
  unfold CoherentLeaderPhaseMove
  infer_instance

/-- The stronger monitor preserves all earlier rolling guarantees and adds
local implementability of the closing bank at every time. -/
theorem coherentRollingMonitor_correct
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) O₁) :
    (coherentRollingMonitor M shape initial).WinsPlay play ↔
      (rollingLeaderMonitor M initial).WinsPlay play ∧
      ∀ n, ClosingBankCoherent shape (phaseMemoryRun initial rollingLeaderNext play n) := by
  rw [coherentRollingMonitor,leaderMemoryMonitor_wins_iff,
    rollingLeaderMonitor,leaderMemoryMonitor_wins_iff]
  simp only [coherentRollingCheck,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨physical,checks⟩
    exact ⟨⟨physical,fun n => (checks n).1.1⟩,fun n => (checks n).1.2⟩
  · rintro ⟨⟨physical,rolling⟩,coherent⟩
    exact ⟨physical,fun n => ⟨⟨rolling n,coherent n⟩,coherent (n+1)⟩⟩

variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]

/-- No rolling or bank-coherence hypothesis is imposed on the original
strategy: both are proved by extraction. Only the supplied physical parity
objective's winning condition is assumed. The original strategy may use
unbounded memory. The result belongs to a fixed finite leader-table type. -/
theorem finite_coherent_leader_table_of_strategy
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (rep : RepresentsInputShape past shape)
    (base : View I₁ I₂ .one) (same : ∀ h, currentView .one (past h) = base)
    (physical : ∀ env, M.WinsPlay (phasePhysicalPlay Prod.fst
      (pairPlay (rollingOriginalReceiver σ past D) (rollingOriginalLeader σ base) env))) :
    ∃ table : FiniteRootFamilyTable (fun _ : Unit =>
        coherentRollingMonitor M shape (rollingOriginalBank σ past D [])),
      NarrowedAllThreadsWin (coherentRollingMonitor M shape (rollingOriginalBank σ past D []))
        (finiteRootMemberController (fun _ : Unit =>
          coherentRollingMonitor M shape (rollingOriginalBank σ past D []))
          table.toTransitionRationalTree ()).labeledTree := by
  apply leaderMemory_finite_table M Prod.fst (rollingOriginalBank σ past D [])
    rollingLeaderNext (coherentRollingCheck shape)
    (rollingOriginalReceiver σ past D) (rollingOriginalLeader σ base) physical
  intro env n
  simp only [coherentRollingCheck,Bool.and_eq_true,decide_eq_true_eq]
  have common : ∀ h k, currentView .one (past h) = currentView .one (past k) :=
    fun h k => (same h).trans (same k).symm
  refine ⟨⟨rollingOriginal_checks σ past D base same env n,?_⟩,?_⟩
  · rw [rollingOriginal_memory]
    exact rollingOriginalBank_coherent σ past shape rep common _
  · exact rollingOriginalBank_coherent σ past shape rep common (branchNode env n ++ [env n])

/-- The uniform finite alphabet depends on the finite monitor, source
observation matrix, alphabets, root slots, and horizon, but not on σ or the
length of the one-way phase. -/
theorem finite_coherent_leader_phase_move
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (rep : RepresentsInputShape past shape)
    (base : View I₁ I₂ .one) (same : ∀ h, currentView .one (past h) = base)
    (physical : ∀ env, M.WinsPlay (phasePhysicalPlay Prod.fst
      (pairPlay (rollingOriginalReceiver σ past D) (rollingOriginalLeader σ base) env))) :
    ∃ move : CoherentLeaderPhaseMove (D:=D) M shape,
      move.1 = rollingOriginalBank σ past D [] ∧
      NarrowedAllThreadsWin (coherentRollingMonitor M shape move.1)
        (finiteRootMemberController (fun _ : Unit => coherentRollingMonitor M shape move.1)
          move.2.toTransitionRationalTree ()).labeledTree := by
  obtain ⟨table,wins⟩ := finite_coherent_leader_table_of_strategy M shape σ past rep base same physical
  exact ⟨⟨rollingOriginalBank σ past D [],table⟩,rfl,wins⟩

end
end Characterisation
