/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.CheckedPhaseReadback

/-! A finite leader phase move has one actual local implementation for its
entire unbounded phase and all carried closing plans. This reuses the
original narrowing readback and keeps the supplied physical parity monitor. -/
namespace Characterisation
open DistributedSynthesis

/-- Exact agreement with the carried plans and the physical output row
at every source word and root. Root indices are not additional observations. -/
def ImplementsLeaderPhase {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (initial : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D))
    (leader : SenderBlockStrategy I₁ O₁) : Prop :=
  (∀ node h, closingPlanOfStrategy σ (rollingSourceHistory past node h) (D+1) =
    receiverClosingBank initial receiver node h) ∧
  (∀ node r h,
    σ.one (currentView .one (rollingSourceHistory past (node++[r]) h)) =
        leader (senderWord node) r.2 ∧
    σ.two (currentView .two (rollingSourceHistory past (node++[r]) h)) =
        (receiver node r).1 h)

section FiniteMove
variable {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
variable [Fintype H] [DecidableEq H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (M : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H → O₂) O₁)
variable (shape : InputShape H)

noncomputable def coherentMoveTree (move : CoherentLeaderPhaseMove (D:=D) M shape) :
    LabeledTree (I₂ × I₁) (BlockLambdaLabel I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) O₁) :=
  narrowedInducedTree (coherentRollingMonitor M shape move.1)
    (finiteRootMemberController (fun _ : Unit => coherentRollingMonitor M shape move.1)
      move.2.toTransitionRationalTree ()).labeledTree

noncomputable def coherentMoveReceiver (move : CoherentLeaderPhaseMove (D:=D) M shape) :
    ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) :=
  receiverOfTree (coherentMoveTree M shape move)

variable [Inhabited I₂]

noncomputable def coherentMoveLeader (move : CoherentLeaderPhaseMove (D:=D) M shape) :
    SenderBlockStrategy I₁ O₁ := senderOfTree (coherentMoveTree M shape move)

/-- The parent narrowing readback reproduces the complete strategy tree,
so every physical letter and every emitted bank are retained. -/
theorem coherentMove_pair_wins (move : CoherentLeaderPhaseMove (D:=D) M shape)
    (wins : NarrowedAllThreadsWin (coherentRollingMonitor M shape move.1)
      (finiteRootMemberController (fun _ : Unit => coherentRollingMonitor M shape move.1)
        move.2.toTransitionRationalTree ()).labeledTree) :
    ∀ env, (coherentRollingMonitor M shape move.1).WinsPlay
      (pairPlay (coherentMoveReceiver M shape move) (coherentMoveLeader M shape move) env) := by
  letI : Fintype (ClosingPlanBank H I₁ I₂ O₁ O₂ D) := closingPlanBank_fintype D
  letI : Fintype (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) := inferInstance
  have oblivious := senderOblivious_narrowedInducedTree (coherentRollingMonitor M shape move.1)
    (finiteRootMemberController (fun _ : Unit => coherentRollingMonitor M shape move.1)
      move.2.toTransitionRationalTree ()).labeledTree
  have winning := narrowedInducedTree_winningTree_of_allThreadsWin
    (coherentRollingMonitor M shape move.1) wins
  intro env
  rw [coherentMoveReceiver,coherentMoveLeader,pairPlay,coherentMoveTree,treeOfPair_ofTree oblivious]
  exact ((coherentRollingMonitor M shape move.1).lift_winningTree_iff _).mp winning env

variable [Inhabited I₁] [Nonempty O₁] [Nonempty O₂]

/-- Every winning finite phase move admits a single local strategy that
implements all its closing banks and physical outputs on all input threads. -/
theorem finite_leader_move_readback
    (past : H → EnvHistory I₁ I₂) (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (leaders : ∀ h k, currentView .one (past h) = currentView .one (past k))
    (move : CoherentLeaderPhaseMove (D:=D) M shape)
    (wins : NarrowedAllThreadsWin (coherentRollingMonitor M shape move.1)
      (finiteRootMemberController (fun _ : Unit => coherentRollingMonitor M shape move.1)
        move.2.toTransitionRationalTree ()).labeledTree) :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      ImplementsLeaderPhase σ past move.1 (coherentMoveReceiver M shape move) (coherentMoveLeader M shape move) ∧
      ∀ env, M.WinsPlay (phasePhysicalPlay Prod.fst
        (pairPlay (coherentMoveReceiver M shape move) (coherentMoveLeader M shape move) env)) := by
  obtain ⟨σ,plans,outputs,physical⟩ := checked_leader_phase_readback M shape move.1
    (coherentMoveReceiver M shape move) (coherentMoveLeader M shape move)
    (coherentMove_pair_wins M shape move wins) past rep L depth leaders
  exact ⟨σ,⟨plans,outputs⟩,physical⟩

variable [Inhabited O₁] [Inhabited O₂]

/-- Compression and readback together. Starting from any original local
strategy winning the supplied one-way parity monitor, select one move from
the fixed finite alphabet and implement all of its unbounded-phase and
closing-window prescriptions by one local strategy pair. -/
theorem finite_implementable_leader_phase
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (rep : RepresentsInputShape past shape) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (base : View I₁ I₂ .one) (same : ∀ h, currentView .one (past h) = base)
    (physical : ∀ env, M.WinsPlay (phasePhysicalPlay Prod.fst
      (pairPlay (rollingOriginalReceiver σ past D) (rollingOriginalLeader σ base) env))) :
    ∃ move : CoherentLeaderPhaseMove (D:=D) M shape,
      move.1 = rollingOriginalBank σ past D [] ∧
      NarrowedAllThreadsWin (coherentRollingMonitor M shape move.1)
        (finiteRootMemberController (fun _ : Unit => coherentRollingMonitor M shape move.1)
          move.2.toTransitionRationalTree ()).labeledTree ∧
      ∃ τ : StrategyPair I₁ I₂ O₁ O₂,
        ImplementsLeaderPhase τ past move.1 (coherentMoveReceiver M shape move) (coherentMoveLeader M shape move) ∧
        ∀ env, M.WinsPlay (phasePhysicalPlay Prod.fst
          (pairPlay (coherentMoveReceiver M shape move) (coherentMoveLeader M shape move) env)) := by
  obtain ⟨move,initial,wins⟩ := finite_coherent_leader_phase_move M shape σ past rep base same physical
  have leaders : ∀ h k, currentView .one (past h) = currentView .one (past k) :=
    fun h k => (same h).trans (same k).symm
  exact ⟨move,initial,wins,finite_leader_move_readback M shape past rep L depth leaders move wins⟩

end FiniteMove
end Characterisation
