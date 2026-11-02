/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.Trees
import DistributedSynthesis.Formalizations.ComponentGames.ComponentReadback

/-! The induction step in the reverse bounded-representation proof.
Maps may collapse vertices. Allowed extensions follow from the constructed
block automaton's liveness specification and state reachability.
-/
namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {I₁ I₂ O₁ O₂ G : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]

/-- The manuscript's T_w invariant, with no extra graph-state hypothesis. -/
structure PositionSimulation (P R : Position I₁ I₂ B.State D) where
  map : ViewComplexMap P.past R.past
  phase : P.phase = R.phase
  states : ∀ h, P.state h = R.state (map.edge h)

namespace PositionSimulation
variable {B M} {P R S : Position I₁ I₂ B.State D}
def castTarget (sim : PositionSimulation B P R) (eq : R = S) : PositionSimulation B P S := eq ▸ sim
@[simp] theorem castTarget_edge (sim : PositionSimulation B P R) (eq : R = S) (h : P.Root) :
    ((sim.castTarget eq).map.edge h).val = (sim.map.edge h).val := by cases eq; rfl
end PositionSimulation

/-- Every offered full child inherits the position conditions. -/
theorem ComponentSuccessor.valid {m : Move I₁ I₂ O₁ O₂ B.State D}
    {P : Position I₁ I₂ B.State D} (next : ComponentSuccessor B M m P)
    (valid : PositionValid B M m.source) : PositionValid B M P := by
  obtain ⟨C, component, _, histories, labels⟩ := next
  let e := componentEquiv m C P histories
  have hist (x : C) : P.past (e x) = m.source.history x.val := rfl
  have back (h : P.Root) : m.source.history (e.symm h).val = h.val := by
    change P.past (e (e.symm h)) = _
    rw [e.apply_symm_apply]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [← back h]
    exact component_alive M m C component (e.symm h)
  · intro h k
    have path : Relation.ReflTransGen
        (fun x y : P.Root => ∃ p, currentView p x.val = currentView p y.val)
        (e (e.symm h)) (e (e.symm k)) := Relation.ReflTransGen.lift e (fun _ _ edge => edge)
      (component_connected M m C component (e.symm h) (e.symm k))
    simpa only [e.apply_symm_apply] using path
  · intro h
    rw [labels h (e.symm h) (back h).symm, ← back h]
    exact blockSuccessor_reachable B m.source m.rule valid.2.2 (e.symm h).val

variable {bound : Nat} (N : CompressedNode B M bound)
variable (P : Position I₁ I₂ B.State D) (valid : PositionValid B M P)
variable (sim : PositionSimulation B P N.position)

def pullNode : UncompressedNode B M where
  position := P
  valid := valid
  rule := restrictClosingPolicy (N.reduction.imageProjection N.position ∘ sim.map.edge) N.rule
  distributed := (N.copied_rule P.past sim.map P.state sim.states).1

def simulationEndpoint : P.End → N.extensionMove.source.End :=
  mapClosingLayer (N.reduction.imageProjection N.position ∘ sim.map.edge) D

theorem simulationEndpoint_history (e : P.End) :
    N.extensionMove.source.history (simulationEndpoint B M N P sim e) =
      (N.reduction.map.edge (sim.map.edge (closingLayerRoot D e))).val ++ (scenarioWord D e).val := by
  exact ((N.reduction.imageMap N.position).comp sim.map).extend_history D e

theorem simulationEndpoint_views (p : Proc) (e f : P.End)
    (same : currentView p (P.history e) = currentView p (P.history f)) :
    currentView p (N.extensionMove.source.history (simulationEndpoint B M N P sim e)) =
      currentView p (N.extensionMove.source.history (simulationEndpoint B M N P sim f)) :=
  (((N.reduction.imageMap N.position).comp sim.map).extend D).preserves_views p e f same

theorem simulationEndpoint_state (e : P.End) :
    blockSuccessor B P.state (pullNode B M N P valid sim).rule e =
      blockSuccessor B N.extensionMove.source.state N.rule (simulationEndpoint B M N P sim e) :=
  (N.copied_rule P.past sim.map P.state sim.states).2 e

theorem simulationEndpoint_live (liveness : StateLiveness B M) (e : P.End)
    (alive : extensionLive M (pullNode B M N P valid sim).move e = true) :
    extensionLive M N.extensionMove (simulationEndpoint B M N P sim e) = true := by
  have first := blockSuccessor_reachable B P (pullNode B M N P valid sim).rule valid.2.2 e
  have second := blockSuccessor_reachable B N.extensionMove.source N.rule
    (N.reduction.imagePosition_valid B M N.position N.valid).2.2 (simulationEndpoint B M N P sim e)
  have equal := liveness.equal_states first second (simulationEndpoint_state B M N P valid sim e)
  have sourceLive := (of_decide_eq_true alive).2
  have targetLive := equal.mp sourceLive
  simpa only [CompressedNode.extensionMove, extensionLive_identity] using (decide_eq_true targetLive)

/-- The image of a full real component lies inside one full simulated
component. The proof follows shared-vertex paths and allows collapsed edges. -/
theorem simulation_component (liveness : StateLiveness B M)
    (C : Finset P.End) (component : IsComponent M (pullNode B M N P valid sim).move C) :
    ∃ L : Finset N.extensionMove.source.End, IsComponent M N.extensionMove L ∧
      ∀ e ∈ C, simulationEndpoint B M N P sim e ∈ L := by
  obtain ⟨a, ha⟩ := component_nonempty M (pullNode B M N P valid sim).move C component
  let F := simulationEndpoint B M N P sim
  have alive (e : C) : extensionLive M N.extensionMove (F e.val) = true :=
    simulationEndpoint_live B M N P valid sim liveness e.val (component_member_live M (pullNode B M N P valid sim).move C component e.val e.property)
  let graph := closingObservationGraph (closingLayerShape N.extensionMove.source.shape D)
    (extensionLive M N.extensionMove)
  have mapEdge (e f : C)
      (same : ∃ p, currentView p (P.history e.val) = currentView p (P.history f.val)) :
      graph.Reachable (F e.val) (F f.val) := by
    by_cases eq : F e.val = F f.val
    · rw [eq]
    apply SimpleGraph.Adj.reachable
    refine ⟨eq, alive e, alive f, ?_⟩
    obtain ⟨p, same⟩ := same
    have shape := closingLayerShape_exact N.extensionMove.source.past _
      (extractInputShape_exact N.extensionMove.source.past) D
    exact ⟨p, Or.inl ((shape p _ _).mpr (simulationEndpoint_views B M N P sim p e.val f.val same))⟩
  have reach (e : C) : graph.Reachable (F a) (F e.val) := by
    have path := component_connected M (pullNode B M N P valid sim).move C component ⟨a, ha⟩ e
    induction path with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b c _ edge ih => exact ih.trans (mapEdge b c edge)
  let L := Finset.univ.filter (fun e => closingComponentMask
    (closingLayerShape N.extensionMove.source.shape D) (extensionLive M N.extensionMove) (F a) e = true)
  refine ⟨L, ⟨F a, alive ⟨a, ha⟩, fun e => by simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]⟩, ?_⟩
  intro e he
  simp only [L, Finset.mem_filter, Finset.mem_univ, true_and,
    closingComponentMask, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨alive ⟨e, he⟩, reach ⟨e, he⟩⟩

/-- The complete induction step: next full component, next simulation, and
its exact edge equation. No folding is applied at the target of this block. -/
theorem simulation_next (liveness : StateLiveness B M)
    (R : Position I₁ I₂ B.State D)
    (next : (pullNode B M N P valid sim).Successor R) :
    ∃ S : Position I₁ I₂ B.State D, N.Successor S ∧
      ∃ nextSim : PositionSimulation B R S,
        ∀ (h : R.Root) (a : P.Root) (u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D),
          h.val = a.val ++ u.val →
          (nextSim.map.edge h).val = (N.reduction.map.edge (sim.map.edge a)).val ++ u.val := by
  obtain ⟨C, component, phase, histories, labels⟩ := next
  obtain ⟨L, targetComponent, inside⟩ := simulation_component B M N P valid sim liveness C component
  obtain ⟨S, targetPhase, targetHistories, _, targetLabels⟩ := component_position M B N.extensionMove L
    (N.reduction.imagePosition_valid B M N.position N.valid) targetComponent
  let e := componentEquiv (pullNode B M N P valid sim).move C R histories
  let pick (h : R.Root) := (e.symm h).val
  have pickMem h : pick h ∈ C := (e.symm h).property
  have pickHist h : P.history (pick h) = h.val := by
    change (e (e.symm h)).val = h.val
    rw [e.apply_symm_apply]
  let f (h : R.Root) : S.Root := ⟨N.extensionMove.source.history (simulationEndpoint B M N P sim (pick h)), by
    change _ ∈ S.histories
    rw [targetHistories]
    exact Finset.mem_image.mpr ⟨_, inside _ (pickMem h), rfl⟩⟩
  let nextSim : PositionSimulation B R S :=
    { map := ViewComplexMap.ofEdge f (by
        intro p h k same
        apply simulationEndpoint_views B M N P sim p (pick h) (pick k)
        simpa only [pickHist] using same)
      phase := by rw [phase, targetPhase]; exact congrArg (· + 1) sim.phase
      states := by
        intro h
        change R.state h = S.state (f h)
        rw [labels h (e.symm h) (pickHist h).symm,
          targetLabels (f h) ⟨_, inside _ (pickMem h)⟩ rfl]
        exact simulationEndpoint_state B M N P valid sim (pick h) }
  refine ⟨S, ⟨L, targetComponent, targetPhase, targetHistories, targetLabels⟩, nextSim, ?_⟩
  intro h a u eq
  have picked : pick h = wordScenario a u := P.history_injective
    ((pickHist h).trans (eq.trans (wordScenario_history P.past a u).symm))
  change N.extensionMove.source.history (simulationEndpoint B M N P sim (pick h)) = _
  rw [simulationEndpoint_history, picked, wordScenario_root, scenarioWord_wordScenario]

end
end Characterisation.ComponentTrees
