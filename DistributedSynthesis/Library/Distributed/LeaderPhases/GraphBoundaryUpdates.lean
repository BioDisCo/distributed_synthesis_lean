/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.FiniteGraphLeader

/-! One-round graph-component expansion computes live flags, the agreed
leader and boundary flags from finite data. The observation update and
component reachability algorithm are reused unchanged. -/
namespace Characterisation
open DistributedSynthesis FullViewPath

structure GraphReceptionLabel (Q : Type) (d : Nat) where
  state : Q
  age : CappedReceptionAge d
  memory : ReceptionMemory d
  deriving Fintype, DecidableEq

def graphReceptionLabel {Q : Type} (M : Recognizer Graph Q) (d : Nat) (g : List Graph) : GraphReceptionLabel Q d :=
  ⟨M.eval g,cappedReceptionRun d g,receptionMemoryRun d g⟩

def graphReceptionStep {Q : Type} {d : Nat} (step : Q → Graph → Q)
    (label : GraphReceptionLabel Q d) (g : Graph) : GraphReceptionLabel Q d :=
  ⟨step label.state g,cappedReceptionStep label.age g,receptionMemoryStep label.memory g⟩

theorem graphReceptionLabel_append {Q : Type} (M : Recognizer Graph Q) (d : Nat) (g : List Graph) (r : Graph) :
    graphReceptionLabel M d (g++[r]) = graphReceptionStep M.step (graphReceptionLabel M d g) r := by
  simp only [graphReceptionLabel,graphReceptionStep,cappedReceptionRun_append,receptionMemoryRun_append]
  congr 1
  simp [Recognizer.eval,Recognizer.evalFrom]

def graphChildLabels {S Q : Type} {d : Nat} (step : Q → Graph → Q)
    (label : S → GraphReceptionLabel Q d) (s : GraphChild S) : GraphReceptionLabel Q d :=
  graphReceptionStep step (label s.1) s.2

def graphChildLive {S Q : Type} {d : Nat} (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (label : S → GraphReceptionLabel Q d) (s : GraphChild S) : Bool :=
  decide ((graphChildLabels M.step label s).state ∈ M.accept)

def graphStepBoundary {S Q : Type} [Fintype S] [DecidableEq S] {d : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)] (shape : InputShape S)
    (label : S → GraphReceptionLabel Q d) (root : GraphChild S) : Bool :=
  let next := graphChildLabels M.step label
  finiteGraphBoundary (closingComponentMask (graphChildShape shape) (graphChildLive M label) root)
    (fun s => (next s).age) (fun s => (next s).memory) root
    (finiteGraphLeader (fun _ : S => true) (fun s => (label s).age))

/-- Child annotations and liveness are determined by the previous finite
annotations and recognizer transition; no semantic boundary oracle is used. -/
theorem graphChildLabels_exact {S Q : Type} (M : Recognizer Graph Q) (d : Nat)
    (past : S → List Graph) (label : S → GraphReceptionLabel Q d)
    (exactLabels : ∀ s, label s = graphReceptionLabel M d (past s)) (s : GraphChild S) :
    graphChildLabels M.step label s = graphReceptionLabel M d (graphChildHistory past s) := by
  simp only [graphChildLabels,exactLabels,graphChildHistory,graphReceptionLabel_append]

theorem graphChildLive_exact {S Q : Type} (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (d : Nat) (P : List Graph → Prop) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
    (past : S → List Graph) (label : S → GraphReceptionLabel Q d)
    (exactLabels : ∀ s, label s = graphReceptionLabel M d (past s)) (s : GraphChild S) :
    graphChildLive M label s = true ↔ P (graphChildHistory past s) := by
  simp only [graphChildLive,graphChildLabels_exact M d past label exactLabels,
    graphReceptionLabel,decide_eq_true_eq,recognizes]

/-- From a complete single source graph component, the executable expansion
computes the original boundary predicate for every live next history, with
arbitrary private inputs. No truthfulness premise for boundary flags remains. -/
theorem graphStepBoundary_exact {S Q I₁ I₂ : Type} [Fintype S] [DecidableEq S]
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept) (d : Nat)
    (past : S → List Graph) (shape : InputShape S)
    (rep : RepresentsInputShape (graphHistory ∘ past) shape)
    (sameComponent : ∀ s t, Connected P (past s) (past t))
    (covers : ∀ s k, Connected P (past s) k → ∃ t, past t = k)
    (label : S → GraphReceptionLabel Q d)
    (exactLabels : ∀ s, label s = graphReceptionLabel M d (past s))
    (root : GraphChild S) (h : EnvHistory I₁ I₂)
    (graphs : History.graphSequence h = graphChildHistory past root)
    (live : P (History.graphSequence h)) :
    graphStepBoundary M shape label root = leaderBoundary P d h := by
  let next := graphChildLabels M.step label
  have nextExact := graphChildLabels_exact M d past label exactLabels
  have coverage : ∀ k, Connected P (History.graphSequence h) k → ∃ s, graphChildHistory past s = k := by
    intro k conn
    rw [graphs] at conn
    exact graphChild_component_coverage P closed past covers root k conn
  have liveExact := graphChildLive_exact M d P recognizes past label exactLabels
  have maskExact : ∀ s, closingComponentMask (graphChildShape shape) (graphChildLive M label) root s = true ↔
      Connected P (History.graphSequence h) (graphChildHistory past s) := by
    intro s
    rw [graphs]
    exact graphComponentMask_exact P (graphChildHistory past) (graphChildShape shape)
      (graphChildShape_exact past shape rep) (graphChildLive M label) liveExact root
      (by rwa [← graphs]) (fun k conn => coverage k (by rwa [graphs])) s
  have oldAges : ∀ s p, ((label s).age p).val = min d (silentAge (graphView p (past s))) := by
    intro s p
    rw [exactLabels]
    simpa only [graphReceptionLabel,graphHistory_graphSequence,graphHistory_view] using
      cappedReceptionRun_exact d (graphHistory (past s)) p
  have newAges : ∀ s p, ((next s).age p).val = min d (silentAge (graphView p (graphChildHistory past s))) := by
    intro s p
    change ((graphChildLabels M.step label s).age p).val = _
    rw [nextExact]
    simpa only [graphReceptionLabel,graphHistory_graphSequence,graphHistory_view] using
      cappedReceptionRun_exact d (graphHistory (graphChildHistory past s)) p
  have oldLeader := finiteGraphLeader_exact P d (past root.1) past (fun _ => true)
    (fun s => ⟨fun _ => sameComponent root.1 s,fun _ => rfl⟩) (covers root.1) (fun s => (label s).age) oldAges
  apply finiteGraphBoundary_exact P d h (graphChildHistory past) _ maskExact coverage
    (fun s => (next s).age) newAges (fun s => (next s).memory) root
  · change (graphChildLabels M.step label root).memory = _
    rw [nextExact,graphs]
    rfl
  · rw [oldLeader,graphSequence_dropLast,graphs]
    simp only [graphChildHistory,List.dropLast_concat]

/-- The computed bits agree with the existing local boundary strategies.
Scenario enumeration therefore adds no graph observation to either process. -/
theorem graphStepBoundary_local {S Q I₁ I₂ : Type} [Fintype S] [DecidableEq S]
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (past : S → List Graph) (shape : InputShape S)
    (rep : RepresentsInputShape (graphHistory ∘ past) shape)
    (sameComponent : ∀ s t, Connected P (past s) (past t))
    (covers : ∀ s k, Connected P (past s) k → ∃ t, past t = k)
    (label : S → GraphReceptionLabel Q d)
    (exactLabels : ∀ s, label s = graphReceptionLabel M d (past s)) :
    ∃ test : StrategyPair I₁ I₂ Bool Bool, ∀ root (h : EnvHistory I₁ I₂),
      History.graphSequence h = graphChildHistory past root → P (History.graphSequence h) →
      test.one (currentView .one h) = graphStepBoundary M shape label root ∧
      test.two (currentView .two h) = graphStepBoundary M shape label root := by
  obtain ⟨test,correct⟩ := leaderBoundary_local (I₁:=I₁) (I₂:=I₂) P closed d recent
  refine ⟨test,fun root h graphs live => ?_⟩
  rw [graphStepBoundary_exact M P closed recognizes d past shape rep sameComponent covers label exactLabels root h graphs live]
  exact correct h live

/-- Bounded graph components and finite annotations have a common finite
interface type, reusing the existing bounded observation representation. -/
theorem bounded_graph_reception_interfaces {Q : Type} (M : Recognizer Graph Q) (d K : Nat)
    (P : List Graph → Prop)
    (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K) :
    ∀ g, P g → ∃ summary : SwitchInterface (GraphReceptionLabel Q d) K,
      ∃ e : Fin summary.1.val ≃ HistoryComponent P g,
        RepresentsInputShape (fun i => graphHistory (e i).val) summary.2.1 ∧
        ∀ i, summary.2.2 i = graphReceptionLabel M d (e i).val := by
  intro g live
  letI : Finite (HistoryComponent P g) := (bounded g live).1
  exact finite_switch_interface K (bounded g live).2
    (fun s : HistoryComponent P g => graphHistory s.val) (fun s => graphReceptionLabel M d s.val)

end Characterisation
