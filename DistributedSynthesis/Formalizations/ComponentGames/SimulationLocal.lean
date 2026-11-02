/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.GameEmbeddings

/- Lemma replacement-game-equivalence, forward direction, following the
manuscript's Sim_n construction. No rank choice, new winning strategy, or
alternative decision theorem is substituted for the simulation argument. -/
namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

/-- Exactly the induction invariant (sim-views), (sim-states), and equal phases. -/
structure Simulation (P R : Position I₁ I₂ Q D) where
  map : P.Root → R.Root
  phase : P.phase = R.phase
  views : ∀ p h k, currentView p h.val = currentView p k.val →
    currentView p (map h).val = currentView p (map k).val
  graph : ∀ h, M.eval (History.graphSequence h.val) = M.eval (History.graphSequence (map h).val)
  state : ∀ h, P.state h = R.state (map h)

section Map
variable {H K : Type} (past : H → EnvHistory I₁ I₂) (other : K → EnvHistory I₁ I₂)
variable (f : H → K)
variable (views : ∀ p h k, currentView p (past h) = currentView p (past k) →
    currentView p (other (f h)) = currentView p (other (f k)))

include views in
theorem simulation_layer_views (n : Nat) (p : Proc) (s t : ClosingLayer H I₁ I₂ n)
    (same : currentView p (closingLayerHistory past n s) = currentView p (closingLayerHistory past n t)) :
    currentView p (closingLayerHistory other n (mapClosingLayer f n s)) =
      currentView p (closingLayerHistory other n (mapClosingLayer f n t)) := by
  rw [← closingLayerHistory_map,← closingLayerHistory_map,scenarioWord_history,scenarioWord_history]
  apply append_preserves_views _ _ _ _ (fun p eq => views p _ _ eq)
    _ _ ((scenarioWord n s).property.trans (scenarioWord n t).property.symm) p
  simpa only [scenarioWord_history] using same

include views in
theorem simulation_rule_coherent {E : Nat} (out : ClosingPolicy K I₁ I₂ O₁ O₂ E)
    (distributed : ClosingPolicyCoherent (extractInputShape other) out) :
    ClosingPolicyCoherent (extractInputShape past) (restrictClosingPolicy f out) := by
  intro n
  have first := closingLayerShape_exact past _ (extractInputShape_exact past) (n.val+1)
  have second := closingLayerShape_exact other _ (extractInputShape_exact other) (n.val+1)
  constructor
  · intro s t same
    exact (distributed n).1 _ _ ((second .one _ _).mpr
      (simulation_layer_views past other f views _ .one s t ((first .one s t).mp same)))
  · intro s t same
    exact (distributed n).2 _ _ ((second .two _ _).mpr
      (simulation_layer_views past other f views _ .two s t ((first .two s t).mp same)))
end Map

variable {P : Position I₁ I₂ Q D} (m : Move I₁ I₂ O₁ O₂ Q D)
variable (sim : Simulation M P m.source)

def pullMove : Move I₁ I₂ O₁ O₂ Q D :=
  ⟨P,restrictClosingPolicy sim.map m.rule,id⟩

theorem pullMove_legal (legal : Legal M step .replacement m.source m) :
    Legal M step .component P (pullMove M m sim) :=
  ⟨rfl,simulation_rule_coherent P.past m.source.past sim.map sim.views m.rule legal.2.1,rfl⟩

/-- The two runs agree at EVERY prefix, before applying the simulated replacement. -/
theorem simulation_prefix_state (n : Nat) (bound : n ≤ D) (e : ClosingLayer P.Root I₁ I₂ n) :
    closingLayerLabels step P.state (pullMove M m sim).rule n bound e =
      closingLayerLabels step m.source.state m.rule n bound (mapClosingLayer sim.map n e) := by
  have eq : m.source.state ∘ sim.map = P.state := funext (fun h => (sim.state h).symm)
  simpa only [eq,pullMove] using closingLayerLabels_restrict sim.map step m.source.state m.rule n bound e

theorem simulation_prefix_graph (n : Nat) (e : ClosingLayer P.Root I₁ I₂ n) :
    M.eval (History.graphSequence (closingLayerHistory P.past n e)) =
      M.eval (History.graphSequence (closingLayerHistory m.source.past n (mapClosingLayer sim.map n e))) := by
  rw [← closingLayerHistory_map,scenarioWord_history,scenarioWord_history]
  exact graph_recognizer_replay M _ _ _ (sim.graph _)

/-- Sim_{n+1}(hw) = rhat(Sim_n(h))w, exactly as in the manuscript. -/
def simulationEnd (e : P.End) : m.source.End :=
  mapClosingLayer m.replacement D (mapClosingLayer sim.map D e)

theorem simulationEnd_history (e : P.End) :
    m.source.history (simulationEnd M m sim e) =
      (m.replacement (sim.map (closingLayerRoot D e))).val ++ (scenarioWord D e).val := by
  rw [Position.history,simulationEnd,← closingLayerHistory_map,← closingLayerHistory_map,scenarioWord_history]
  rfl

theorem replacement_prefix_graph (legal : Legal M step .replacement m.source m)
    (n : Nat) (bound : n ≤ D) (e : ClosingLayer m.source.Root I₁ I₂ n) :
    M.eval (History.graphSequence (closingLayerHistory m.source.past n e)) =
      M.eval (History.graphSequence (closingLayerHistory m.source.past n (mapClosingLayer m.replacement n e))) := by
  have equal := (legal.2.2.2 ⟨n,by omega⟩ e).1
  have replay (z : ClosingLayer m.source.Root I₁ I₂ n) :=
    closingLayerLabels_recognizer M m.source.past (fun h => M.eval (History.graphSequence h.val))
      (fun _ => rfl) m.rule n bound z
  exact (replay e).symm.trans (equal.trans (replay _))

theorem simulationEnd_live (legal : Legal M step .replacement m.source m)
    (e : P.End) (live : extensionLive M (pullMove M m sim) e = true) :
    extensionLive M m (simulationEnd M m sim e) = true := by
  apply decide_eq_true
  constructor
  · change closingLayerRoot D (mapClosingLayer _ D (mapClosingLayer _ D e)) ∈ _
    rw [closingLayerRoot_map,closingLayerRoot_map]
    exact Finset.mem_image.mpr ⟨sim.map (closingLayerRoot D e),Finset.mem_univ _,rfl⟩
  · have original := (of_decide_eq_true live).2
    have equal := (simulation_prefix_graph M m sim D e).trans
      (replacement_prefix_graph M step m legal D (Nat.le_refl _) (mapClosingLayer sim.map D e))
    exact equal ▸ original

theorem simulationEnd_views (legal : Legal M step .replacement m.source m)
    (p : Proc) (e f : P.End) (same : closingLayerShape P.shape D p e f = true) :
    closingLayerShape m.source.shape D p (simulationEnd M m sim e) (simulationEnd M m sim f) = true := by
  apply legal.2.2.1 p
  have first := closingLayerShape_exact P.past _ (extractInputShape_exact P.past) D
  have second := closingLayerShape_exact m.source.past _ (extractInputShape_exact m.source.past) D
  exact (second p _ _).mpr
    (simulation_layer_views P.past m.source.past sim.map sim.views D p e f ((first p e f).mp same))

theorem simulationEnd_state (legal : Legal M step .replacement m.source m) (e : P.End) :
    closingLayerLabels step P.state (pullMove M m sim).rule D (Nat.le_refl _) e =
      closingLayerLabels step m.source.state m.rule D (Nat.le_refl _) (simulationEnd M m sim e) :=
  (simulation_prefix_state M step m sim D (Nat.le_refl _) e).trans
    (legal.2.2.2 ⟨D,by omega⟩ (mapClosingLayer sim.map D e)).2

/-- A connected component maps INTO one simulated component. The map may
collapse vertices, so the proof uses reachability, not an injective graph map. -/
theorem simulation_component (legal : Legal M step .replacement m.source m)
    (K : Finset P.End) (component : IsComponent M (pullMove M m sim) K) :
    ∃ L : Finset m.source.End, IsComponent M m L ∧
      ∀ e ∈ K, simulationEnd M m sim e ∈ L := by
  classical
  obtain ⟨anchor,alive,mask⟩ := component
  let first := closingObservationGraph (closingLayerShape P.shape D)
    (extensionLive M (pullMove M m sim))
  let second := closingObservationGraph (closingLayerShape m.source.shape D) (extensionLive M m)
  have mapEdge (e f : P.End) (edge : first.Adj e f) :
      second.Reachable (simulationEnd M m sim e) (simulationEnd M m sim f) := by
    by_cases equal : simulationEnd M m sim e = simulationEnd M m sim f
    · rw [equal]
    · apply SimpleGraph.Adj.reachable
      refine ⟨equal,simulationEnd_live M step m sim legal e edge.2.1,
        simulationEnd_live M step m sim legal f edge.2.2.1,?_⟩
      obtain ⟨p,eq | eq⟩ := edge.2.2.2
      · exact ⟨p,Or.inl (simulationEnd_views M step m sim legal p e f eq)⟩
      · exact ⟨p,Or.inr (simulationEnd_views M step m sim legal p f e eq)⟩
  have mapPath (e f : P.End) (reach : first.Reachable e f) :
      second.Reachable (simulationEnd M m sim e) (simulationEnd M m sim f) := by
    have path := (first.reachable_iff_reflTransGen e f).mp reach
    clear reach
    induction path with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b c _ edge ih => exact ih.trans (mapEdge b c edge)
  let L := Finset.univ.filter (fun e => closingComponentMask
    (closingLayerShape m.source.shape D) (extensionLive M m) (simulationEnd M m sim anchor) e = true)
  refine ⟨L,⟨simulationEnd M m sim anchor,simulationEnd_live M step m sim legal anchor alive,
    fun e => by simp only [L,Finset.mem_filter,Finset.mem_univ,true_and]⟩,?_⟩
  intro e he
  have inside := (mask e).mp he
  simp only [closingComponentMask,Bool.and_eq_true,decide_eq_true_eq] at inside
  simp only [L,Finset.mem_filter,Finset.mem_univ,true_and,
    closingComponentMask,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨simulationEnd_live M step m sim legal e inside.1,mapPath anchor e inside.2⟩

/-- Expose the exact component used when constructing its successor position. -/
theorem next_component_data (L : Finset m.source.End) (component : IsComponent M m L) :
    ∃ R : Position I₁ I₂ Q D, R.phase = m.source.phase+1 ∧
      R.histories = L.image m.source.history ∧
      ∀ (h : R.Root) (e : m.source.End), e ∈ L → h.val = m.source.history e →
        R.state h = closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) e := by
  classical
  obtain ⟨a,alive,mask⟩ := component
  have inside : a ∈ L := (mask a).mpr (by
    simp only [closingComponentMask,alive,Bool.true_and,decide_eq_true_eq]
    exact SimpleGraph.Reachable.refl a)
  let histories := L.image m.source.history
  have witnesses (h : histories) : ∃ e, e ∈ L ∧ m.source.history e = h.val :=
    Finset.mem_image.mp h.property
  let pick (h : histories) := (witnesses h).choose
  let R : Position I₁ I₂ Q D :=
    { phase := m.source.phase+1
      histories := histories
      nonempty := ⟨m.source.history a,Finset.mem_image.mpr ⟨a,inside,rfl⟩⟩
      lengths := by
        intro h mem
        obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp mem
        exact m.source.history_length e
      state := fun h => closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) (pick h) }
  refine ⟨R,rfl,rfl,?_⟩
  intro h e _ eq
  have chosen : m.source.history (pick h) = h.val := (witnesses h).choose_spec.2
  have same : pick h = e := m.source.history_injective (chosen.trans eq)
  change closingLayerLabels step m.source.state m.rule D _ (pick h) = _
  rw [same]

/-- The complete induction step on arbitrary environment choices, including
all invariants and the explicit formula needed to map compatible runs. -/
theorem simulation_next (legal : Legal M step .replacement m.source m)
    (R : Position I₁ I₂ Q D) (next : Next M step (pullMove M m sim) R) :
    ∃ T : Position I₁ I₂ Q D, Next M step m T ∧
      ∃ nextSim : Simulation M R T, ∀ (h : R.Root) (a : P.Root)
        (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D),
        h.val = a.val ++ w.val →
        (nextSim.map h).val = (m.replacement (sim.map a)).val ++ w.val := by
  classical
  obtain ⟨phase,K,component,histories,labels⟩ := next
  change R.histories = K.image P.history at histories
  obtain ⟨L,targetComponent,inside⟩ := simulation_component M step m sim legal K component
  obtain ⟨T,targetPhase,targetHistories,targetLabels⟩ := next_component_data M step m L targetComponent
  have witnesses (h : R.Root) : ∃ e : P.End, e ∈ K ∧ P.history e = h.val := by
    have mem : h.val ∈ K.image P.history := by rw [← histories]; exact h.property
    exact Finset.mem_image.mp mem
  let pick (h : R.Root) : P.End := (witnesses h).choose
  have pickMem (h : R.Root) : pick h ∈ K := (witnesses h).choose_spec.1
  have pickHistory (h : R.Root) : P.history (pick h) = h.val := (witnesses h).choose_spec.2
  let f (h : R.Root) : T.Root := ⟨m.source.history (simulationEnd M m sim (pick h)),by
    change _ ∈ T.histories
    rw [targetHistories]
    exact Finset.mem_image.mpr ⟨simulationEnd M m sim (pick h),inside _ (pickMem h),rfl⟩⟩
  have first := closingLayerShape_exact P.past _ (extractInputShape_exact P.past) D
  have second := closingLayerShape_exact m.source.past _ (extractInputShape_exact m.source.past) D
  let nextSim : Simulation M R T :=
    { map := f
      phase := by rw [phase,targetPhase]; exact congrArg (· + 1) sim.phase
      views := by
        intro p h k same
        apply (second p _ _).mp
        apply simulationEnd_views M step m sim legal
        apply (first p _ _).mpr
        simpa only [← pickHistory h,← pickHistory k] using same
      graph := by
        intro h
        rw [← pickHistory h]
        exact (simulation_prefix_graph M m sim D (pick h)).trans
          (replacement_prefix_graph M step m legal D (Nat.le_refl _) _)
      state := by
        intro h
        rw [labels h (pick h) (pickMem h) (pickHistory h).symm,
          targetLabels (f h) _ (inside _ (pickMem h)) rfl]
        exact simulationEnd_state M step m sim legal (pick h) }
  refine ⟨T,⟨targetPhase,L,targetComponent,targetHistories,targetLabels⟩,nextSim,?_⟩
  intro h a w eq
  have picked : pick h = wordScenario a w := P.history_injective (by
    rw [pickHistory,eq]
    exact (wordScenario_history P.past a w).symm)
  change m.source.history (simulationEnd M m sim (pick h)) = _
  rw [simulationEnd_history,picked,wordScenario_root,scenarioWord_wordScenario]

end
end Characterisation.ComponentGames.HistoryGame

