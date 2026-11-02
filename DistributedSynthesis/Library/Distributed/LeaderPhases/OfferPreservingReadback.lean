/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.OfferPreservingCompression

/-! Tie the offer-preserving compression to the existing local leader
readback. The selected finite table has one local implementation for its
whole one-way phase and all carried closing plans. -/
namespace Characterisation
open DistributedSynthesis

section
variable {H I₁ I₂ O₁ O₂ Memory Outcome : Type} {D : Nat}
variable [Fintype H] [DecidableEq H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]
variable [Fintype Memory] [DecidableEq Outcome]
variable (M : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H → O₂) O₁)
variable (shape : InputShape H) (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
variable (initial : Memory)
variable (next : Memory → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) O₁ → Memory)
variable (collect : Memory → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) O₁ → Finset Outcome)
variable (allowed : Finset Outcome)

/-- The finite offer restriction is retained together with local closing
compatibility and infinite-phase parity. The source roots have one agreed
leader view; they are not made observable to that leader. -/
theorem finite_offer_preserving_leader_phase
    (past : H → EnvHistory I₁ I₂) (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (leaders : ∀ h k, currentView .one (past h) = currentView .one (past k))
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D))
    (leader : SenderBlockStrategy I₁ O₁)
    (coherent : ∀ env, (coherentRollingMonitor M shape bank).WinsPlay (pairPlay receiver leader env))
    (restricted : ∀ env n,
      collect (phaseMemoryRun initial next (pairPlay receiver leader env) n)
        (pairPlay receiver leader env n) ⊆ allowed) :
    ∃ table : FiniteRootFamilyTable (fun _ : Unit =>
        phaseOfferMonitor (coherentRollingMonitor M shape bank) id initial next collect allowed),
      let G := phaseOfferMonitor (coherentRollingMonitor M shape bank) id initial next collect allowed
      let T := finiteRootMemberController (fun _ : Unit => G) table.toTransitionRationalTree ()
      let tree := narrowedInducedTree G T.labeledTree
      NarrowedAllThreadsWin G T.labeledTree ∧
      narrowedPhaseOffers G T (fun q letter => collect q.2.1 letter) ⊆ allowed ∧
      ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
        ImplementsLeaderPhase σ past bank (receiverOfTree tree) (senderOfTree tree) ∧
        ∀ env, M.WinsPlay (phasePhysicalPlay Prod.fst
          (pairPlay (receiverOfTree tree) (senderOfTree tree) env)) := by
  letI : Fintype (ClosingPlanBank H I₁ I₂ O₁ O₂ D) := closingPlanBank_fintype D
  letI : Fintype (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) := inferInstance
  obtain ⟨table, wins, subset, physical⟩ := finite_phase_preserving_offers
    (coherentRollingMonitor M shape bank) id initial next collect allowed receiver leader
    (by simpa only [phasePhysicalPlay, id_eq, Prod.eta] using coherent) restricted
  refine ⟨table, wins, subset, ?_⟩
  let G := phaseOfferMonitor (coherentRollingMonitor M shape bank) id initial next collect allowed
  let T := finiteRootMemberController (fun _ : Unit => G) table.toTransitionRationalTree ()
  let tree := narrowedInducedTree G T.labeledTree
  have oblivious : SenderOblivious tree := senderOblivious_narrowedInducedTree G T.labeledTree
  have pairWinning : ∀ env, (coherentRollingMonitor M shape bank).WinsPlay
      (pairPlay (receiverOfTree tree) (senderOfTree tree) env) := by
    intro env
    rw [pairPlay, treeOfPair_ofTree oblivious]
    simpa only [phasePhysicalPlay, id_eq, Prod.eta] using physical env
  obtain ⟨σ, plans, outputs, winning⟩ := checked_leader_phase_readback M shape bank
    (receiverOfTree tree) (senderOfTree tree) pairWinning past rep L depth leaders
  exact ⟨σ, ⟨plans, outputs⟩, winning⟩

end
end Characterisation
