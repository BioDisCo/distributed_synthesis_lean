/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.Positions
import DistributedSynthesis.Formalizations.ComponentTrees.Reductions
import DistributedSynthesis.Formalizations.ComponentTrees.CommonView

/-! Local steps of the compressed trees in `main.tex`.
A node keeps its FULL component. Its reduction image is the source of the
next block; the next position is the FULL selected successor component.
-/

namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {I₁ I₂ O₁ O₂ Q G : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (m : Move I₁ I₂ O₁ O₂ Q D) (C : Finset m.source.End)

theorem component_nonempty (component : IsComponent M m C) : C.Nonempty := by
  obtain ⟨a, alive, mask⟩ := component
  refine ⟨a, (mask a).mpr ?_⟩
  simp only [closingComponentMask, alive, Bool.true_and, decide_eq_true_eq]
  exact SimpleGraph.Reachable.refl a

theorem component_alive (component : IsComponent M m C) (e : C) :
    M.eval (History.graphSequence (m.source.history e.val)) ∈ M.accept := by
  obtain ⟨_, _, mask⟩ := component
  have inside := (mask e.val).mp e.property
  simp only [closingComponentMask, Bool.and_eq_true] at inside
  exact (of_decide_eq_true inside.1).2

/-- Connectivity inside C, rather than in a larger ambient complex. -/
theorem component_connected (component : IsComponent M m C) (e f : C) :
    Relation.ReflTransGen
      (fun x y : C => ∃ p, currentView p (m.source.history x.val) =
        currentView p (m.source.history y.val)) e f := by
  obtain ⟨anchor, alive, mask⟩ := component
  have ee := (mask e.val).mp e.property
  have ff := (mask f.val).mp f.property
  simp only [closingComponentMask, Bool.and_eq_true, decide_eq_true_eq] at ee ff
  let graph := closingObservationGraph (closingLayerShape m.source.shape D) (extensionLive M m)
  have path := (graph.reachable_iff_reflTransGen e.val f.val).mp (ee.2.symm.trans ff.2)
  have go : ∀ z, Relation.ReflTransGen graph.Adj e.val z → ∀ hz : z ∈ C,
      Relation.ReflTransGen
        (fun x y : C => ∃ p, currentView p (m.source.history x.val) =
          currentView p (m.source.history y.val)) e ⟨z, hz⟩ := by
    intro z path
    induction path with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | @tail b c path edge ih =>
      have hb : b ∈ C := (mask b).mpr (by
        simp only [closingComponentMask, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨edge.2.1, ee.2.trans ((graph.reachable_iff_reflTransGen _ _).mpr path)⟩)
      intro hc
      apply (ih hb).tail
      have shape := closingLayerShape_exact m.source.past m.source.shape
        (extractInputShape_exact m.source.past) D
      obtain ⟨p, same | same⟩ := edge.2.2.2
      · exact ⟨p, (shape p b c).mp same⟩
      · exact ⟨p, ((shape p c b).mp same).symm⟩
  exact go f.val path f.property

/-- The new broadcaster proof supplies the common vertex used in compression. -/
theorem participating_common_of_consensus {V : Type} [Nontrivial V]
    (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
      Consensus.SolvesBy σ (Residual A u) D)
    (component : IsComponent M m C) :
    ∃ p, ∀ h k : participatingRoots m C, currentView p h.val.val = currentView p k.val.val := by
  have ne : Nonempty C := ⟨⟨(component_nonempty M m C component).choose,
    (component_nonempty M m C component).choose_spec⟩⟩
  obtain ⟨p, common⟩ := broadcaster_common_roots A D positive consensus
    (fun e : C => (closingLayerRoot D e.val).val)
    (fun e : C => (scenarioWord D e.val).val) (m.source.phase * D)
    (fun e => m.source.lengths _ (closingLayerRoot D e.val).property)
    (fun e => (scenarioWord D e.val).property)
    (fun e => (recognizes _).mpr (by
      simpa only [Position.history, scenarioWord_history, Position.past] using component_alive M m C component e))
    ne (by simpa only [Position.history, scenarioWord_history, Position.past] using component_connected M m C component)
  refine ⟨p, fun h k => ?_⟩
  obtain ⟨e, he, eqe⟩ := Finset.mem_image.mp h.property
  obtain ⟨f, hf, eqf⟩ := Finset.mem_image.mp k.property
  rw [← eqe, ← eqf]
  exact common ⟨e, he⟩ ⟨f, hf⟩

/-- `lem:tree-compression` as an actual idempotent vertex map on C.
The only geometric premise is the manuscript's repeated bounded consensus.
Its proof follows the broadcaster, common vertex, extension, restriction,
and table-counting arguments, in that order. -/
theorem compression_reduction {S V : Type} [Fintype S] [Nontrivial V]
    (label : m.source.End → S)
    (rep : participatingRoots m C → participatingRoots m C)
    (preserves : ∀ h, endpointTable m C label (rep h) = endpointTable m C label h)
    (constant : ∀ h k, endpointTable m C label h = endpointTable m C label k → rep h = rep k)
    (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
      Consensus.SolvesBy σ (Residual A u) D)
    (component : IsComponent M m C) :
    ∃ r : Reduction (fun e : C => m.source.history e.val) (fun e : C => label e.val),
      (∀ e, m.source.history (r.map.edge e).val =
        (rep (rootOf m C e)).val.val ++ (scenarioWord D e.val).val) ∧
      (Finset.univ.image r.map.edge).card ≤
        (1 + Nat.card S) ^ (Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D) *
          Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  obtain ⟨p, common⟩ := participating_common_of_consensus M m C A recognizes positive consensus component
  exact ⟨endpointReduction m C label rep preserves constant p common,
    endpointFold_history m C label rep preserves,
    endpointFold_image_bound m C label rep preserves constant⟩

variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))

/-- The FULL selected component with its actual successor states. This
replaces use of `folded_position` as the child-position construction. -/
theorem component_position (m : Move I₁ I₂ O₁ O₂ B.State D)
    (C : Finset m.source.End) (valid : PositionValid B M m.source)
    (component : IsComponent M m C) :
    ∃ P : Position I₁ I₂ B.State D,
      P.phase = m.source.phase + 1 ∧
      P.histories = C.image m.source.history ∧ PositionValid B M P ∧
      ∀ (h : P.Root) (e : C), h.val = m.source.history e.val →
        P.state h = blockSuccessor B m.source.state m.rule e.val := by
  let histories := C.image m.source.history
  have witness (h : histories) : ∃ e, e ∈ C ∧ m.source.history e = h.val := Finset.mem_image.mp h.property
  let pick (h : histories) : C := ⟨(witness h).choose, (witness h).choose_spec.1⟩
  have pickHist h : m.source.history (pick h).val = h.val := (witness h).choose_spec.2
  let P : Position I₁ I₂ B.State D :=
    { phase := m.source.phase + 1
      histories := histories
      nonempty := (component_nonempty M m C component).image _
      lengths := by
        intro h hh
        obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hh
        exact m.source.history_length e
      state := fun h => blockSuccessor B m.source.state m.rule (pick h).val }
  let toHist (e : C) : P.Root := ⟨m.source.history e.val, Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩⟩
  have pickEq h : toHist (pick h) = h := Subtype.ext (pickHist h)
  refine ⟨P, rfl, rfl, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro h
    simpa only [pickHist] using component_alive M m C component (pick h)
  · intro h k
    rw [← pickEq h, ← pickEq k]
    exact Relation.ReflTransGen.lift toHist (fun _ _ edge => edge)
      (component_connected M m C component (pick h) (pick k))
  · intro h
    rw [← pickHist h]
    exact blockSuccessor_reachable B m.source m.rule valid.2.2 (pick h).val
  · intro h e eq
    have chosen : pick h = e := Subtype.ext (m.source.history_injective ((pickHist h).trans eq))
    change blockSuccessor B m.source.state m.rule (pick h).val = _
    rw [chosen]

/-- Full child position together with its bounded reduction, with actual
block states and their reachability witnesses. This joins the local results
without replacing C by the reduction image or adding a hypothesis on C. -/
theorem component_position_with_reduction {V : Type} [Nontrivial V]
    (m : Move I₁ I₂ O₁ O₂ B.State D) (C : Finset m.source.End)
    (valid : PositionValid B M m.source)
    (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
      Consensus.SolvesBy σ (Residual A u) D)
    (component : IsComponent M m C)
    (rep : participatingRoots m C → participatingRoots m C)
    (preserves : ∀ h, endpointTable m C (blockSuccessor B m.source.state m.rule) (rep h) =
      endpointTable m C (blockSuccessor B m.source.state m.rule) h)
    (constant : ∀ h k, endpointTable m C (blockSuccessor B m.source.state m.rule) h =
      endpointTable m C (blockSuccessor B m.source.state m.rule) k → rep h = rep k) :
    ∃ P : Position I₁ I₂ B.State D, P.phase = m.source.phase + 1 ∧
      P.histories = C.image m.source.history ∧ PositionValid B M P ∧
      (∀ (h : P.Root) (e : C), h.val = m.source.history e.val →
        P.state h = blockSuccessor B m.source.state m.rule e.val) ∧
      ∃ r : Reduction P.past P.state,
        (∀ (h : P.Root) (e : C), h.val = m.source.history e.val →
          (r.map.edge h).val = (rep (rootOf m C e)).val.val ++ (scenarioWord D e.val).val) ∧
        (Finset.univ.image r.map.edge).card ≤
          (1 + Nat.card B.State) ^ (Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D) *
            Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  obtain ⟨P, phase, histories, validP, states⟩ := component_position M B m C valid component
  obtain ⟨r, action, small⟩ := compression_reduction M m C
    (blockSuccessor B m.source.state m.rule) rep preserves constant A recognizes positive consensus component
  let e := componentEquiv m C P histories
  have hist h : P.past (e h) = m.source.history h.val := rfl
  have labels h : P.state (e h) = blockSuccessor B m.source.state m.rule h.val := states _ h rfl
  let transported := r.reindex e P.past P.state hist labels
  refine ⟨P, phase, histories, validP, states, transported, ?_, ?_⟩
  · intro h c eq
    have original : e.symm h = c := e.injective (by
      rw [e.apply_symm_apply]
      exact Subtype.ext eq)
    change P.past (e (r.map.edge (e.symm h))) = _
    rw [hist, original]
    exact action c
  · exact (r.reindex_image_card e P.past P.state hist labels).trans_le small

/-- Size of a full successor component, distinct from the smaller image bound. -/
theorem component_position_bound (m : Move I₁ I₂ O₁ O₂ Q D)
    (C : Finset m.source.End) (component : IsComponent M m C)
    (bound : Nat) (small : m.source.histories.card ≤ bound) :
    (C.image m.source.history).card ≤ bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  apply le_trans (Finset.card_le_card (show C.image m.source.history ⊆ extensions M m from ?_))
    (live_endpoints_bound m M bound small)
  intro h hh
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨_, _, mask⟩ := component
  have inside := (mask e).mp he
  simp only [closingComponentMask, Bool.and_eq_true] at inside
  exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, inside.1⟩, rfl⟩

end
end Characterisation.ComponentTrees
