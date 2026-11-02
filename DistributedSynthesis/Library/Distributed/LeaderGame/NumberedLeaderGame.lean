/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeftSuccessors
import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedPhaseSuccessors
import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderTreeAssembly

/-! One concrete finite public game for both agreed leaders. Its move tests
are the proved rightward and leftward local table tests; its parity condition
is the existing compatible-hidden-history monitor. The semantic equivalence with physical distributed realizability is proved
in NumberedGameEquivalence; uniform numeric compilation remains separate. -/
namespace Characterisation
open DistributedSynthesis FullViewPath

def graphRootLeader {Q : Type} {d K : Nat} : GraphRootState Q d K → Proc
  | none => .one
  | some st => finiteGraphLeader (fun _ => true) (fun i => (st.1.2.2 i).age)

theorem graphRootLeader_exact {Q : Type} {d K : Nat} (P : List Graph → Prop)
    (M : Recognizer Graph Q) (g : List Graph) (live : P g) (state : GraphRootState Q d K)
    (rep : GraphRootRep P M g state) : graphRootLeader state = componentLeader P d g := by
  cases state with
  | none => exact False.elim (rep live)
  | some st =>
    obtain ⟨_,past,data,_⟩ := rep
    apply finiteGraphLeader_exact P d g past (fun _ => true)
      (fun i => ⟨fun _ => (data.2.1 _).mpr ⟨i,rfl⟩,fun _ => rfl⟩)
      (fun k connected => (data.2.1 k).mp connected)
    intro i p
    rw [data.2.2.2]
    simpa only [graphReceptionLabel,graphHistory_graphSequence,graphHistory_view] using
      cappedReceptionRun_exact d (graphHistory (past i)) p

section
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable [DecidableEq objective.State] (rank : objective.State → Fin (C+1))

abbrev NumberedLeaderMove := Proc × Finset
  (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)

instance numberedLeaderMove_fintype :
    Fintype (NumberedLeaderMove (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) := by
  unfold NumberedLeaderMove NumberedLeaderOutcome LeaderAnnotation
  infer_instance

def numberedLeaderOffers
    (move : NumberedLeaderMove (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (outcome : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) : Bool :=
  decide (outcome ∈ move.2)

/-- The elected leader is checked against every source graph component.
The process name in a move is not an extra controllable leader election. -/
noncomputable def numberedLeaderLegal
    (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (move : NumberedLeaderMove (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) : Bool :=
  decide (∀ h, graphRootLeader (header.2.2 h).1.1 = move.1) &&
    match move.1 with
    | .one => numberedRightLegal M objective rank header move.2
    | .two => numberedLeftLegal M objective rank header move.2

variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]

/-- At an actual boundary, the same globally chosen leader is a legal
public move whenever the current original strategy wins its residual objective.
Only the permitted whole-outcome set is selected by the strategy. -/
theorem numberedLeaderLegal_of_strategy
    (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (P : List Graph → Prop) (u : EnvHistory I₁ I₂) (live : P (History.graphSequence u))
    (e : Fin header.1.val ≃ InputHistoryComponent P u)
    (rep : RepresentsInputShape (fun h => (e h).val) header.2.1)
    (graphs : ∀ h, GraphRootRep P M (History.graphSequence (e h).val) (header.2.2 h).1.1)
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (winning : ContinuationWins objective.AcceptsFrom (fun i => (header.2.2 i).1.2)
      (strategyContinuationPolicy σ (fun h => (e h).val))) :
    ∃ permitted, numberedLeaderLegal M objective rank header
      (componentLeader P d (History.graphSequence u),permitted) = true := by
  have leaders : ∀ h, graphRootLeader (header.2.2 h).1.1 = componentLeader P d (History.graphSequence u) := by
    intro h
    rw [graphRootLeader_exact P M _ (inputConnected_live P live (e h).property) _ (graphs h)]
    exact (componentLeader_component_invariant P d (inputConnected_projects P (e h).property)).symm
  cases selected : componentLeader P d (History.graphSequence u) with
  | one =>
    obtain ⟨_,_,_,permitted,legal,_⟩ := numbered_right_of_strategy M objective rank header
      (fun h => (e h).val) rep (List.length u)
      (fun h => (inputConnected_length P (e h).property).symm) σ winning
    refine ⟨permitted,?_⟩
    have agree : ∀ h, graphRootLeader (header.2.2 h).1.1 = .one := by
      intro h
      rw [leaders,selected]
    simpa only [numberedLeaderLegal,selected,agree,implies_true,decide_true,Bool.true_and] using legal
  | two =>
    obtain ⟨_,_,_,permitted,legal,_⟩ := numbered_left_of_strategy M objective rank header
      (fun h => (e h).val) rep (List.length u)
      (fun h => (inputConnected_length P (e h).property).symm) σ winning
    refine ⟨permitted,?_⟩
    have agree : ∀ h, graphRootLeader (header.2.2 h).1.1 = .two := by
      intro h
      rw [leaders,selected]
    simpa only [numberedLeaderLegal,selected,agree,implies_true,decide_true,Bool.true_and] using legal

section
omit [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]

noncomputable def numberedLeaderGame
    (initial : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (code : HandoverCode B C) := by
  letI : Inhabited (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) := ⟨initial⟩
  exact supportedLeaderProgressMonitor (numberedLeaderOffers objective) code initial
    (fun header move => numberedLeaderLegal M objective rank header move = true)

/-- This typed finite test inherits noncomputable automaton data. Its
correctness theorem concerns this public game, not the synthesis predicate. -/
noncomputable def numberedLeaderGameTest
    (initial : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (code : HandoverCode B C) : Bool := by
  classical
  exact TreeNonemptiness.nonempty (numberedLeaderGame M objective rank initial code)

/-- The concrete finite test checks legality at every supported public
node and parity along every compatible hidden predecessor thread. -/
theorem numberedLeaderGameTest_correct
    (initial : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (code : HandoverCode B C) :
    numberedLeaderGameTest M objective rank initial code = true ↔
      ∃ tree : LabeledTree
        (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
        (NumberedLeaderMove (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective),
        SupportedMovesValid (numberedLeaderOffers objective) initial
          (fun family move => numberedLeaderLegal M objective rank family.1 move = true) tree ∧
        ∀ branch, ∀ thread : HiddenCodeContinuityThread code
          (OfferedHandoverEdge (numberedLeaderOffers objective)) (observableThreadWord tree branch),
          NatSeqMinEvenParity (fun n => (thread.code (n+1)).2.val) := by
  classical
  letI : Inhabited (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) := ⟨initial⟩
  rw [numberedLeaderGameTest,TreeNonemptiness.nonempty_correct]
  apply exists_congr
  intro tree
  exact ((numberedLeaderGame M objective rank initial code).acceptsTree_iff_winningTree tree).trans
    (supportedLeaderProgress_winning_iff (numberedLeaderOffers objective) code initial
      (fun header move => numberedLeaderLegal M objective rank header move = true) tree)

end

end
end Characterisation
