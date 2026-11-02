/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.JointLeaderOriginal

/-! Preserve one joint handover restriction across all initial leader-view
groups. The original narrowing is applied once to the full vector of group
responses, and the joint readback gives one physical strategy. -/
namespace Characterisation
open DistributedSynthesis

section
variable {H G I₁ I₂ O₁ O₂ Memory Outcome : Type} {D : Nat}
variable [Fintype H] [DecidableEq H] [Fintype G] [DecidableEq G]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]
variable [Fintype Memory] [DecidableEq Outcome]
variable (M : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H → O₂) (G → O₁))
variable (shape : InputShape H) (group : H → G)
variable (initial : Memory)
variable (next : Memory → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) (G → O₁) → Memory)
variable (collect : Memory → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) (G → O₁) → Finset Outcome)
variable (allowed : Finset Outcome)

/-- The phase alphabet ranges over all allowed sets and initial closing
banks. Its size is independent of the strategy and of phase duration. -/
abbrev JointLeaderPhaseMove :=
  Σ permitted : Finset Outcome, Σ bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D,
    FiniteRootFamilyTable (fun _ : Unit => phaseOfferMonitor
      (jointLeaderMonitor group shape M bank) id initial next collect permitted)

instance jointLeaderPhaseMove_finite [Fintype Outcome] :
    Finite (JointLeaderPhaseMove M shape group initial next collect) := by
  classical
  letI : Fintype (ClosingPlanBank H I₁ I₂ O₁ O₂ D) := closingPlanBank_fintype D
  letI : Fintype (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) := inferInstance
  letI : ∀ permitted : Finset Outcome, ∀ bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D,
      Fintype (FiniteRootFamilyTable (fun _ : Unit => phaseOfferMonitor
        (jointLeaderMonitor group shape M bank) id initial next collect permitted)) :=
    fun _ _ => by unfold FiniteRootFamilyTable; infer_instance
  unfold JointLeaderPhaseMove
  infer_instance

/-- One finite table handles all initial groups jointly. Its offer set is
computed from that same table, so target entries from independently chosen
group controllers are never combined. No coherence or rolling-check premise
is added to the original strategy. -/
theorem finite_joint_leader_phase
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (rep : RepresentsInputShape past shape) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (base : G → View I₁ I₂ .one) (distinct : Function.Injective base)
    (same : ∀ h, currentView .one (past h) = base (group h))
    (physical : ∀ env, M.WinsPlay (phasePhysicalPlay Prod.fst
      (pairPlay (rollingOriginalReceiver σ past D) (jointOriginalLeader σ base) env)))
    (restricted : ∀ env n, collect
      (phaseMemoryRun initial next (pairPlay (rollingOriginalReceiver σ past D) (jointOriginalLeader σ base) env) n)
      (pairPlay (rollingOriginalReceiver σ past D) (jointOriginalLeader σ base) env n) ⊆ allowed) :
    ∃ table : FiniteRootFamilyTable (fun _ : Unit => phaseOfferMonitor
        (jointLeaderMonitor group shape M (rollingOriginalBank σ past D [])) id initial next collect allowed),
      let guard := phaseOfferMonitor (jointLeaderMonitor group shape M (rollingOriginalBank σ past D [])) id initial next collect allowed
      let T := finiteRootMemberController (fun _ : Unit => guard) table.toTransitionRationalTree ()
      let tree := narrowedInducedTree guard T.labeledTree
      NarrowedAllThreadsWin guard T.labeledTree ∧
      narrowedPhaseOffers guard T (fun q letter => collect q.2.1 letter) ⊆ allowed ∧
      (∀ env, M.WinsPlay (phasePhysicalPlay Prod.fst (treePlay tree env))) ∧
      ∃ τ : StrategyPair I₁ I₂ O₁ O₂,
        (∀ node h, closingPlanOfStrategy τ (rollingSourceHistory past node h) (D+1) =
          receiverClosingBank (rollingOriginalBank σ past D []) (receiverOfTree tree) node h) ∧
        ∀ node r h,
          τ.one (currentView .one (rollingSourceHistory past (node++[r]) h)) =
            senderOfTree tree (senderWord node) r.2 (group h) ∧
          τ.two (currentView .two (rollingSourceHistory past (node++[r]) h)) = (receiverOfTree tree node r).1 h := by
  letI : Fintype (ClosingPlanBank H I₁ I₂ O₁ O₂ D) := closingPlanBank_fintype D
  letI : Fintype (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) := inferInstance
  have original := jointOriginal_monitor_wins σ past shape rep group base same M physical
  obtain ⟨table,wins,subset,guarded⟩ := finite_phase_preserving_offers
    (jointLeaderMonitor group shape M (rollingOriginalBank σ past D [])) id initial next collect allowed
    (rollingOriginalReceiver σ past D) (jointOriginalLeader σ base)
    (by simpa only [phasePhysicalPlay,id_eq,Prod.eta] using original) restricted
  let guard := phaseOfferMonitor (jointLeaderMonitor group shape M (rollingOriginalBank σ past D [])) id initial next collect allowed
  let T := finiteRootMemberController (fun _ : Unit => guard) table.toTransitionRationalTree ()
  let tree := narrowedInducedTree guard T.labeledTree
  have treeWinning : ∀ env, (jointLeaderMonitor group shape M (rollingOriginalBank σ past D [])).WinsPlay (treePlay tree env) := by
    intro env
    simpa only [phasePhysicalPlay,id_eq,Prod.eta] using guarded env
  have oblivious := senderOblivious_narrowedInducedTree guard T.labeledTree
  have pairWinning : ∀ env, (jointLeaderMonitor group shape M (rollingOriginalBank σ past D [])).WinsPlay
      (pairPlay (receiverOfTree tree) (senderOfTree tree) env) := by
    intro env
    rw [pairPlay,treeOfPair_ofTree oblivious]
    exact treeWinning env
  have groupExact : ∀ h k, group h = group k ↔ currentView .one (past h) = currentView .one (past k) := by
    intro h k
    rw [same,same]
    exact distinct.eq_iff.symm
  refine ⟨table,wins,subset,?_,?_⟩
  · intro env
    exact ((jointLeaderMonitor_wins_iff group shape M _ _).mp (treeWinning env)).1
  · exact jointLeaderMonitor_readback group shape M (rollingOriginalBank σ past D [])
      past rep L depth groupExact (receiverOfTree tree) (senderOfTree tree) pairWinning

end
end Characterisation
