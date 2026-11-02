/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.PhysicalContinuation

/-! Connect the finite phase collector to complete successor components on
the actual private-input tree. The source is the whole current boundary
component. A collected outcome uses one common branch and one closing
certificate for all its slots. -/
namespace Characterisation
open DistributedSynthesis

section
variable {G GQ Q I₁ I₂ O₁ O₂ : Type} {B C K : Nat}
variable [Fintype G] [DecidableEq G] [Fintype GQ] [DecidableEq GQ]
variable [Fintype Q] [DecidableEq Q]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept) (d : Nat)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (u : EnvHistory I₁ I₂) (liveU : P (History.graphSequence u))
variable (startU : leaderBoundary P d u = true)
variable [Fintype (InputHistoryComponent P u)] [DecidableEq (InputHistoryComponent P u)]
variable (shape : InputShape (InputHistoryComponent P u))
variable (rep : RepresentsInputShape (fun h : InputHistoryComponent P u => h.val) shape)
variable (source : InputHistoryComponent P u → GraphRootState GQ d K)
variable (sourceExact : ∀ h, GraphRootRep P M (History.graphSequence h.val) (source h))
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (initial : InputHistoryComponent P u → Q)
variable (group : InputHistoryComponent P u → G)
variable (bank : ClosingPlanBank (InputHistoryComponent P u) I₁ I₂ O₁ O₂ d)
variable (slot : InputHistoryComponent P u → Fin (B+1)) (minimum : Q → Fin (C+1))

/-- The concrete finite state and collector used throughout the phase. -/
noncomputable abbrev graphPhaseRun
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput (InputHistoryComponent P u) I₁ I₂ O₁ O₂ d))
    (leader : SenderBlockStrategy I₁ (G → O₁)) (env : Nat → I₂ × I₁) (n : Nat) :=
  phaseMemoryRun ((source,(fun _ => true),initial),bank,true)
    (jointGraphLeaderNext group M step (fun st => chooseGraphRootNext M st .right))
    (pairPlay receiver leader env) n

/-- A complete successor at a single physical cut. The target histories,
their observation shape, carried labels, and predecessor links all come
from the same checked certificate. -/
def GraphPhaseSuccessor
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput (InputHistoryComponent P u) I₁ I₂ O₁ O₂ d))
    (leader : SenderBlockStrategy I₁ (G → O₁)) (env : Nat → I₂ × I₁) (n : Nat)
    (outcome : LeaderHandover Q B C) : Prop :=
  let state := graphPhaseRun M P d u source step initial group bank receiver leader env n
  let past := rollingSourceHistory (fun h : InputHistoryComponent P u => h.val) (branchNode env n)
  ∃ (t : Fin (d+1)) (root : ClosingLayer (ActiveClosingRoots state.1.2.1) I₁ I₂ (t.val+1))
    (move : ClosingBoundaryCertificate (ActiveClosingRoots state.1.2.1) I₁ I₂ O₁ O₂ Q B (d+1) (t.val+1)),
    certificateHandover (slot ∘ Subtype.val) minimum move = outcome ∧
    ClosingOfferRealizes P (past ∘ Subtype.val) step (state.1.2.2 ∘ Subtype.val)
      (restrictClosingPolicy Subtype.val (closingPolicyOfBank state.2.1)) (by omega) root move ∧
    ∀ i, ConsecutiveLeaderBoundaries P d
      (closingLayerHistory (past ∘ Subtype.val) (t.val+1) (move.2.2.1 i)) u.length

include closed recognizes recent bounded liveU startU rep sourceExact in
omit [Fintype G] [DecidableEq G] [Inhabited I₁] [Inhabited I₂] in
/-- Soundness of the actual finite-memory collector on every common input
branch. No target-coverage assumption is required. -/
theorem graphPhaseRun_offer_realizes
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput (InputHistoryComponent P u) I₁ I₂ O₁ O₂ d))
    (leader : SenderBlockStrategy I₁ (G → O₁)) (env : Nat → I₂ × I₁) (n : Nat)
    (outcome : LeaderHandover Q B C)
    (offered : outcome ∈ jointGraphLeaderCollect M step shape slot minimum
      (graphPhaseRun M P d u source step initial group bank receiver leader env n)
      (pairPlay receiver leader env n)) :
    GraphPhaseSuccessor M P d u source step initial group bank slot minimum receiver leader env n outcome := by
  let past := fun h : InputHistoryComponent P u => h.val
  let node := branchNode env n
  let word := rightInputHistory node
  let state := graphPhaseRun M P d u source step initial group bank receiver leader env n
  have depth : ∀ h : InputHistoryComponent P u, (past h).length = u.length :=
    fun h => (inputConnected_length P h.property).symm
  have allLengths : ∀ m, (branchNode env m).length = m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simpa only [branchNode, List.length_append, List.length_singleton] using congrArg Nat.succ ih
  have nodeLength : node.length = n := allLengths n
  have wordLength : word.length = n := by
    simpa only [word, rightInputHistory, History.length, List.length_map] using nodeLength
  have nodeEmpty : (node = []) ↔ n = 0 := by
    rw [← List.length_eq_zero_iff, nodeLength]
  have current := jointGraphLeaderMemory_rolling_sources M P closed recognizes bounded
    past u.length depth source sourceExact step initial group bank receiver leader env n
  have currentShape : RepresentsInputShape (carriedBoundarySources P u word)
      (jointLeaderShape shape (decide (n = 0))) := by
    simpa only [nodeEmpty] using jointLeaderShape_exact past shape rep node
  have flag : state.2.2 = decide (word.length = 0) := by
    rw [wordLength]
    exact current.2.2.2
  change outcome ∈ graphClosingOffers M state.1.1 state.1.2.1
    (jointLeaderShape shape state.2.2) state.2.2 step state.1.2.2
    (closingPolicyOfBank state.2.1) slot minimum at offered
  rw [flag, wordLength] at offered
  have activity : SourceActivityOnLive P d u.length (u.length + word.length)
      (carriedBoundarySources P u word) state.1.2.1 := by
    rw [wordLength]
    exact current.2.1
  have offered' : outcome ∈ graphClosingOffers M state.1.1 state.1.2.1
      (jointLeaderShape shape (decide (n = 0))) (decide (word.length = 0)) step state.1.2.2
      (closingPolicyOfBank state.2.1) slot minimum := by
    simpa only [wordLength] using offered
  exact graphClosingOffers_realizes M P closed recognizes d recent u word liveU startU
    _ currentShape state.1.2.1 activity state.1.1 current.1 step state.1.2.2
    (closingPolicyOfBank state.2.1) slot minimum outcome offered'

noncomputable def graphPhaseGuard
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (incoming : InputHistoryComponent P u → objective.State)
    (permitted : Finset (LeaderHandover Q B C)) :=
  phaseOfferMonitor (jointLeaderMonitor group shape
    (jointPhaseObjective objective incoming group) bank) id
    ((source,(fun _ => true),initial),bank,true)
    (jointGraphLeaderNext group M step (fun st => chooseGraphRootNext M st .right))
    (jointGraphLeaderCollect M step shape slot minimum) permitted

include closed recognizes recent bounded liveU startU rep sourceExact in
set_option maxHeartbeats 800000 in
set_option linter.constructorNameAsVariable false in
/-- A globally winning strategy gives one finite joint leader table and a
finite advertised set whose every outcome has a complete successor under
that same original strategy. The table's computed offers lie in this set.
The extracted table also has one local implementation, accepting every
infinite rightward continuation from the original residual states. Neither
target coverage nor infinite-phase acceptance is assumed separately. -/
theorem finite_graph_phase_with_complete_successors
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (winning : ∀ env, objective.Accepts (fun n => recordContinuationLetter (execution σ env n)))
    (base : G → View I₁ I₂ .one) (distinct : Function.Injective base)
    (same : ∀ h : InputHistoryComponent P u, currentView .one h.val = base (group h)) :
    let past := fun h : InputHistoryComponent P u => h.val
    let incoming := fun h : InputHistoryComponent P u => strategyHistoryLabel σ
      (fun q input output => objective.step q (input,output)) objective.initial h.val
    let oldBank := rollingOriginalBank σ past d []
    ∃ permitted : Finset (LeaderHandover Q B C),
    ∃ table : FiniteRootFamilyTable (fun _ : Unit =>
      graphPhaseGuard M P d u shape source step initial group oldBank slot minimum objective incoming permitted),
      let guard := graphPhaseGuard M P d u shape source step initial group oldBank slot minimum objective incoming permitted
      let T := finiteRootMemberController (fun _ : Unit => guard) table.toTransitionRationalTree ()
      let tree := narrowedInducedTree guard T.labeledTree
      NarrowedAllThreadsWin guard T.labeledTree ∧
      (∀ outcome, outcome ∈ permitted →
        ∃ env n, GraphPhaseSuccessor M P d u source step initial group oldBank slot minimum
          (rollingOriginalReceiver σ past d) (jointOriginalLeader σ base) env n outcome) ∧
      narrowedPhaseOffers guard T
        (fun q letter => jointGraphLeaderCollect M step shape slot minimum q.2.1 letter) ⊆ permitted ∧
      (∀ outcome, outcome ∈ narrowedPhaseOffers guard T
        (fun q letter => jointGraphLeaderCollect M step shape slot minimum q.2.1 letter) →
        ∃ env n, GraphPhaseSuccessor M P d u source step initial group oldBank slot minimum
          (rollingOriginalReceiver σ past d) (jointOriginalLeader σ base) env n outcome) ∧
      ∃ τ : StrategyPair I₁ I₂ O₁ O₂,
        (∀ node h, closingPlanOfStrategy τ (rollingSourceHistory past node h) (d+1) =
          receiverClosingBank oldBank (receiverOfTree tree) node h) ∧
        (∀ node r h,
          τ.one (currentView .one (rollingSourceHistory past (node++[r]) h)) =
            senderOfTree tree (senderWord node) r.2 (group h) ∧
          τ.two (currentView .two (rollingSourceHistory past (node++[r]) h)) =
            (receiverOfTree tree node r).1 h) ∧
        ∀ h (env : Nat → I₂ × I₁), objective.AcceptsFrom (incoming h)
          (continuationTrace (strategyContinuationPolicy τ past) h
            (fun n => ((env n).2,(env n).1,.right))) := by
  let past := fun h : InputHistoryComponent P u => h.val
  let incoming := fun h : InputHistoryComponent P u => strategyHistoryLabel σ
    (fun q input output => objective.step q (input,output)) objective.initial h.val
  let oldBank := rollingOriginalBank σ past d []
  let physical := jointPhaseObjective objective incoming group
  let start : GraphLeaderMemory (InputHistoryComponent P u) GQ Q I₁ I₂ O₁ O₂ d K :=
    ((source,(fun _ => true),initial),oldBank,true)
  let next := jointGraphLeaderNext (d := d) (K := K) group M step (fun st => chooseGraphRootNext M st .right)
  let collect := jointGraphLeaderCollect (G := G) (d := d) (K := K) M step shape slot minimum
  have depth : ∀ h : InputHistoryComponent P u, (past h).length = u.length :=
    fun h => (inputConnected_length P h.property).symm
  obtain ⟨permitted,table,accepted,advertised,subset,witnesses,parity,τ,plans,outputs⟩ :=
    finite_joint_leader_phase_witnesses physical shape group start next collect σ past rep
      u.length depth base distinct same
      (jointPhaseObjective_of_global_winning objective σ winning past group base same d)
  let guard := graphPhaseGuard M P d u shape source step initial group oldBank slot minimum objective incoming permitted
  let T := finiteRootMemberController (fun _ : Unit => guard) table.toTransitionRationalTree ()
  let tree := narrowedInducedTree guard T.labeledTree
  refine ⟨permitted,table,accepted,?_,subset,?_,τ,plans,outputs,?_⟩
  · intro outcome member
    obtain ⟨env,n,offered⟩ := advertised outcome member
    exact ⟨env,n,graphPhaseRun_offer_realizes M P closed recognizes d recent bounded u liveU startU
      shape rep source sourceExact step initial group oldBank slot minimum
      (rollingOriginalReceiver σ past d) (jointOriginalLeader σ base) env n outcome offered⟩
  · intro outcome member
    obtain ⟨env,n,offered⟩ := witnesses outcome member
    exact ⟨env,n,graphPhaseRun_offer_realizes M P closed recognizes d recent bounded u liveU startU
      shape rep source sourceExact step initial group oldBank slot minimum
      (rollingOriginalReceiver σ past d) (jointOriginalLeader σ base) env n outcome offered⟩
  · apply jointPhaseObjective_readback objective incoming past group
      (receiverOfTree tree) (senderOfTree tree) τ outputs
    intro env
    rw [pairPlay, treeOfPair_ofTree (senderOblivious_narrowedInducedTree guard T.labeledTree)]
    exact parity env

end
end Characterisation
