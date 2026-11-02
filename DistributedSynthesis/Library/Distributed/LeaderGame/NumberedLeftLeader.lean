/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.RoleExchange

/-! Leftward numbered moves reuse joint leader compression after exchanging
local strategy roles. Their graph memory and closing collector still refer
to the original recognizer and its original canonical boundary rule. -/
namespace Characterisation
open DistributedSynthesis

section
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable [DecidableEq objective.State] (rank : objective.State → Fin (C+1))
variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)

abbrev NumberedLeftMemory := GraphLeaderMemory (Fin header.1.val) GQ
  (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) I₂ I₁ O₂ O₁ d K

abbrev NumberedLeftLetter := RealizedBlockRound I₁ I₂
  (RollingReceiverOutput (Fin header.1.val) I₂ I₁ O₂ O₁ d) (ShapeLeaderGroup header.2.1 .two → O₂)

noncomputable def numberedLeftNext (state : NumberedLeftMemory objective header)
    (letter : NumberedLeftLetter objective header) : NumberedLeftMemory objective header :=
  (coupledRootNext M (leaderAnnotationStep M objective rank) state.1
    ((fun _ => ⟨letter.1.1,letter.1.2,.left,(),()⟩),
      (fun h => (letter.2.1.1 h,letter.2.2 (shapeLeaderGroup header.2.1 .two h))),
      (fun h => chooseGraphRootNext M (state.1.1 h) .left)),letter.2.1.2,false)

/-- Unexchange only the closing bank. In particular, M is not replaced by
a mirrored recognizer, and the graph-root boundary test is unchanged. -/
noncomputable def numberedLeftCollect (state : NumberedLeftMemory objective header)
    (_letter : NumberedLeftLetter objective header) :
    Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) :=
  graphClosingOffers M state.1.1 state.1.2.1
    (exchangeShape (jointLeaderShape (exchangeShape header.2.1) state.2.2)) state.2.2
    (leaderAnnotationStep M objective rank) state.1.2.2
    (closingPolicyOfBank (fun h => exchangePlan (state.2.1 h)))
    (numberedLeaderSlot objective header) (fun q => q.2 ())

noncomputable def numberedLeftGuard
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))
    (bank : ClosingPlanBank (Fin header.1.val) I₂ I₁ O₂ O₁ d) :
    BlockRecordMonitor I₁ I₂ (RollingReceiverOutput (Fin header.1.val) I₂ I₁ O₂ O₁ d)
      (ShapeLeaderGroup header.2.1 .two → O₂) :=
  phaseOfferMonitor (jointLeaderMonitor (shapeLeaderGroup header.2.1 .two) (exchangeShape header.2.1)
    (jointPhaseObjective (objective.comap exchangeLetter) (fun i => (header.2.2 i).1.2)
      (shapeLeaderGroup header.2.1 .two)) bank) id
    (((fun i => (header.2.2 i).1.1),(fun _ => true),
      (fun i => resetLeaderMinimum objective (header.2.2 i))),bank,true)
    (numberedLeftNext M objective rank header) (numberedLeftCollect M objective rank header) permitted

abbrev NumberedLeftTable
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)) :=
  Σ bank : ClosingPlanBank (Fin header.1.val) I₂ I₁ O₂ O₁ d,
    RunParityTreeAutomaton.StateControlledTreeTable
      (numberedLeftGuard M objective rank header permitted bank).threadBlockMonitor.toRunAutomaton

instance numberedLeftTable_finite
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)) :
    Finite (NumberedLeftTable M objective rank header permitted) := by
  classical
  letI : Fintype (ClosingPlanBank (Fin header.1.val) I₂ I₁ O₂ O₁ d) := closingPlanBank_fintype d
  letI : ∀ bank : ClosingPlanBank (Fin header.1.val) I₂ I₁ O₂ O₁ d,
      Fintype (RunParityTreeAutomaton.StateControlledTreeTable
        (numberedLeftGuard M objective rank header permitted bank).threadBlockMonitor.toRunAutomaton) :=
    fun _ => inferInstance
  unfold NumberedLeftTable
  infer_instance

noncomputable def numberedLeftLegal
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)) : Bool := by
  classical
  letI : Fintype (ClosingPlanBank (Fin header.1.val) I₂ I₁ O₂ O₁ d) := closingPlanBank_fintype d
  exact decide (∃ bank, leaderThreadTest (numberedLeftGuard M objective rank header permitted bank) = true)

theorem numberedLeftLegal_correct
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)) :
    numberedLeftLegal M objective rank header permitted = true ↔
      ∃ bank tree, NarrowedAllThreadsWin (numberedLeftGuard M objective rank header permitted bank) tree := by
  classical
  simp only [numberedLeftLegal,decide_eq_true_eq,leaderThreadTest_correct]

variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]

omit [Inhabited I₁] [Inhabited O₁] [Inhabited O₂] in
theorem numberedLeftLegal_iff_table
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)) :
    numberedLeftLegal M objective rank header permitted = true ↔
      ∃ table : NumberedLeftTable M objective rank header permitted,
        NarrowedAllThreadsWin (numberedLeftGuard M objective rank header permitted table.1)
          table.2.toTransitionRationalTree.labeledTree := by
  rw [numberedLeftLegal_correct]
  constructor
  · rintro ⟨bank,tree,winning⟩
    let guard := numberedLeftGuard M objective rank header permitted bank
    have accepted := (guard.threadBlockMonitor.acceptsTree_iff_winningTree tree).mpr
      ((guard.threadBlockMonitor_winningTree_iff tree).mpr winning)
    letI := guard.threadBlockMonitor.alphabetFinite
    obtain ⟨table,correct⟩ := guard.threadBlockMonitor.toRunAutomaton.exists_stateControlledTreeTable_accepted
      ⟨tree,accepted⟩
    exact ⟨⟨bank,table⟩,(guard.threadBlockMonitor_winningTree_iff _).mp
      ((guard.threadBlockMonitor.acceptsTree_iff_winningTree _).mp correct)⟩
  · rintro ⟨table,winning⟩
    exact ⟨table.1,table.2.toTransitionRationalTree.labeledTree,winning⟩

/-- Both the physical closing plans and the endless leftward objective
are read from the same local strategy. No leader-rule equivariance is used. -/
theorem numberedLeftTable_readback
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))
    (table : NumberedLeftTable M objective rank header permitted)
    (winning : NarrowedAllThreadsWin (numberedLeftGuard M objective rank header permitted table.1)
      table.2.toTransitionRationalTree.labeledTree)
    (past : Fin header.1.val → EnvHistory I₁ I₂)
    (shape : RepresentsInputShape past header.2.1)
    (L : Nat) (depth : ∀ h, List.length (past h) = L) :
    let tree := narrowedInducedTree (numberedLeftGuard M objective rank header permitted table.1)
      table.2.toTransitionRationalTree.labeledTree
    let receiver := receiverOfTree tree
    let leader := senderOfTree tree
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      (∀ node h, closingPlanOfStrategy σ (leftSourceHistory past node h) (d+1) =
        exchangePlan (receiverClosingBank table.1 receiver node h)) ∧
      (∀ node r h,
        σ.one (currentView .one (leftSourceHistory past (node++[r]) h)) = (receiver node r).1 h ∧
        σ.two (currentView .two (leftSourceHistory past (node++[r]) h)) =
          leader (senderWord node) r.2 (shapeLeaderGroup header.2.1 .two h)) ∧
      ∀ h (env : Nat → I₁ × I₂), objective.AcceptsFrom (header.2.2 h).1.2
        (continuationTrace (strategyContinuationPolicy σ past) h
          (fun n => ((env n).1,(env n).2,.left))) := by
  let guard := numberedLeftGuard M objective rank header permitted table.1
  let tree := narrowedInducedTree guard table.2.toTransitionRationalTree.labeledTree
  let group := shapeLeaderGroup header.2.1 .two
  let physical := jointPhaseObjective (objective.comap exchangeLetter) (fun i => (header.2.2 i).1.2) group
  let monitor := jointLeaderMonitor group (exchangeShape header.2.1) physical table.1
  have guarded : ∀ env, guard.WinsPlay (pairPlay (receiverOfTree tree) (senderOfTree tree) env) := by
    intro env
    rw [pairPlay,treeOfPair_ofTree (senderOblivious_narrowedInducedTree guard _)]
    exact (guard.lift_winningTree_iff tree).mp
      (narrowedInducedTree_winningTree_of_allThreadsWin guard winning) env
  have checked : ∀ env, monitor.WinsPlay (pairPlay (receiverOfTree tree) (senderOfTree tree) env) := by
    intro env
    have parts := (phaseOfferMonitor_wins_iff _ _ _ _ _ _ _).mp (guarded env)
    simpa only [phasePhysicalPlay,id_eq,Prod.eta] using parts.1
  have exchangedShape := exchangeShape_exact past header.2.1 shape
  obtain ⟨τ,plans,outputs⟩ := jointLeaderMonitor_readback group (exchangeShape header.2.1) physical table.1
    (exchangeHistory ∘ past) exchangedShape L (fun h => (exchangeHistory_length _).trans (depth h))
    (shapeLeaderGroup_exact (exchangeHistory ∘ past) (exchangeShape header.2.1) exchangedShape .one)
    (receiverOfTree tree) (senderOfTree tree) checked
  have original := exchange_left_readback past group table.1 (receiverOfTree tree) (senderOfTree tree) τ plans outputs
  refine ⟨exchangeStrategy τ,original.1,original.2,?_⟩
  have physicalWins := jointPhaseObjective_readback (objective.comap exchangeLetter)
    (fun i => (header.2.2 i).1.2) (exchangeHistory ∘ past) group
    (receiverOfTree tree) (senderOfTree tree) τ outputs
    (fun env => ((jointLeaderMonitor_wins_iff group (exchangeShape header.2.1) physical table.1 _).mp
      (checked env)).1)
  intro h env
  have result := (DetParityAutomaton.comap_acceptsFrom_iff objective exchangeLetter _ _).mp (physicalWins h env)
  have trace := exchange_continuation_trace τ (exchangeHistory ∘ past) h
    (fun n => ((env n).2,(env n).1,.right))
  simp only [Function.comp_def,exchangeHistory_twice] at trace
  change continuationTrace (strategyContinuationPolicy (exchangeStrategy τ) past) h
      (fun n => ((env n).1,(env n).2,.left)) = _ at trace
  rw [trace]
  exact result

end
end Characterisation
