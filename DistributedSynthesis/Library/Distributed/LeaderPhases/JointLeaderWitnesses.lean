/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.JointGraphLeaderReadback

/-! Every offer of a compressed joint phase has one witness under the
original strategy and its current whole source family. The witness set is
used only in the existence proof; it is not claimed to be computable from
an arbitrary infinite strategy. -/
namespace Characterisation
open DistributedSynthesis

noncomputable def semanticPhaseOffers {Input Letter Memory Outcome : Type}
    [Fintype Outcome] (initial : Memory) (next : Memory → Letter → Memory)
    (collect : Memory → Letter → Finset Outcome) (plays : (Nat → Input) → Nat → Letter) :
    Finset Outcome := by
  classical
  exact Finset.univ.filter fun outcome =>
    ∃ env n, outcome ∈ collect (phaseMemoryRun initial next (plays env) n) (plays env n)

theorem mem_semanticPhaseOffers_iff {Input Letter Memory Outcome : Type}
    [Fintype Outcome] (initial : Memory) (next : Memory → Letter → Memory)
    (collect : Memory → Letter → Finset Outcome) (plays : (Nat → Input) → Nat → Letter)
    (outcome : Outcome) :
    outcome ∈ semanticPhaseOffers initial next collect plays ↔
      ∃ env n, outcome ∈ collect (phaseMemoryRun initial next (plays env) n) (plays env n) := by
  classical
  simp only [semanticPhaseOffers, Finset.mem_filter, Finset.mem_univ, true_and]

section
variable {H G I₁ I₂ O₁ O₂ Memory Outcome : Type} {D : Nat}
variable [Fintype H] [DecidableEq H] [Fintype G] [DecidableEq G]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]
variable [Fintype Memory] [Fintype Outcome] [DecidableEq Outcome]
variable (M : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H → O₂) (G → O₁))
variable (shape : InputShape H) (group : H → G) (initial : Memory)
variable (next : Memory → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) (G → O₁) → Memory)
variable (collect : Memory → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) (G → O₁) → Finset Outcome)

-- The naming linter normalizes the nested finite-controller type and exceeds
-- its own heartbeat limit. Kernel checking and the axiom audit remain enabled.
set_option maxHeartbeats 800000 in
set_option linter.constructorNameAsVariable false in
/-- No offer restriction is a premise. Every advertised whole outcome has
one original private-input word and one physical cut witnessing it. The
compressed table may remove offers, but introduces none outside this finite
advertised set. It has a joint local readback and winning infinite plays. -/
theorem finite_joint_leader_phase_witnesses
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (rep : RepresentsInputShape past shape) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (base : G → View I₁ I₂ .one) (distinct : Function.Injective base)
    (same : ∀ h, currentView .one (past h) = base (group h))
    (physical : ∀ env, M.WinsPlay (phasePhysicalPlay Prod.fst
      (pairPlay (rollingOriginalReceiver σ past D) (jointOriginalLeader σ base) env))) :
    ∃ permitted : Finset Outcome, ∃ table : FiniteRootFamilyTable (fun _ : Unit => phaseOfferMonitor
        (jointLeaderMonitor group shape M (rollingOriginalBank σ past D [])) id initial next collect permitted),
      let guard := phaseOfferMonitor (jointLeaderMonitor group shape M (rollingOriginalBank σ past D [])) id initial next collect permitted
      let T := finiteRootMemberController (fun _ : Unit => guard) table.toTransitionRationalTree ()
      let tree := narrowedInducedTree guard T.labeledTree
      NarrowedAllThreadsWin guard T.labeledTree ∧
      (∀ outcome, outcome ∈ permitted →
        ∃ env n, outcome ∈ collect
          (phaseMemoryRun initial next
            (pairPlay (rollingOriginalReceiver σ past D) (jointOriginalLeader σ base) env) n)
          (pairPlay (rollingOriginalReceiver σ past D) (jointOriginalLeader σ base) env n)) ∧
      narrowedPhaseOffers guard T (fun q letter => collect q.2.1 letter) ⊆ permitted ∧
      (∀ outcome, outcome ∈ narrowedPhaseOffers guard T (fun q letter => collect q.2.1 letter) →
        ∃ env n, outcome ∈ collect
          (phaseMemoryRun initial next
            (pairPlay (rollingOriginalReceiver σ past D) (jointOriginalLeader σ base) env) n)
          (pairPlay (rollingOriginalReceiver σ past D) (jointOriginalLeader σ base) env n)) ∧
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
  let original := pairPlay (rollingOriginalReceiver σ past D) (jointOriginalLeader σ base)
  let permitted := semanticPhaseOffers initial next collect original
  have restricted : ∀ env n,
      collect (phaseMemoryRun initial next (original env) n) (original env n) ⊆ permitted := by
    intro env n outcome member
    exact (mem_semanticPhaseOffers_iff initial next collect original outcome).mpr ⟨env, n, member⟩
  obtain ⟨table, wins, subset, parity, readback⟩ :=
    finite_joint_leader_phase M shape group initial next collect permitted σ past rep L depth
      base distinct same physical restricted
  refine ⟨permitted, table, wins, ?_, subset, ?_, parity, readback⟩
  · intro outcome member
    exact (mem_semanticPhaseOffers_iff initial next collect original outcome).mp member
  · intro outcome member
    exact (mem_semanticPhaseOffers_iff initial next collect original outcome).mp (subset member)

end
end Characterisation
