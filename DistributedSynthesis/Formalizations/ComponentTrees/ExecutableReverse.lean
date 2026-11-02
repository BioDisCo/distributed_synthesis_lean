/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.ReverseTree
import DistributedSynthesis.Formalizations.ComponentGames.ExecutableComponents

/-! Finite-search implementation of the reverse tree construction.
These definitions are deliberately outside a `noncomputable section`.
The supplied tree and automata are inputs; all additional choices are
finite searches, and the result is proved equal to the semantic tree.
-/
namespace Characterisation.ComponentTrees.ExecutableReverse
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration
open scoped Characterisation.ComponentGames.Representation.FiniteArena DistributedSynthesis.DecidableViews
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

variable {I₁ I₂ O₁ O₂ G : Type} {D bound : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable [DecidableEq B.State]

instance vertexFintype {H : Type} [Fintype H] (past : H → EnvHistory I₁ I₂) (p : Proc) :
    Fintype (ViewVertex past p) :=
  Fintype.ofFinset (Finset.univ.image (fun h => currentView p (past h))) (by
    intro v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rfl)

/-- Finite search for the unique target vertex; incident source edges need
not be unique, so no injectivity or arbitrary choice is smuggled in. -/
def finiteViewMap {H K : Type} [Fintype H] [Fintype K]
    (past : H → EnvHistory I₁ I₂) (other : K → EnvHistory I₁ I₂) (f : H → K)
    (views : ∀ p h k, currentView p (past h) = currentView p (past k) →
      currentView p (other (f h)) = currentView p (other (f k))) : ViewComplexMap past other := by
  let pred p (v : ViewVertex past p) (w : ViewVertex other p) : Prop :=
    ∀ h, currentView p (past h) = v.val → currentView p (other (f h)) = w.val
  have unique p (v : ViewVertex past p) : ∃! w, pred p v w := by
    obtain ⟨h, hv⟩ := v.property
    refine ⟨viewEndpoint other p (f h), ?_, ?_⟩
    · intro k hk
      exact views p k h (hk.trans hv.symm)
    · intro w hw
      exact Subtype.ext (hw h hv).symm
  exact
    { edge := f
      vertex p v := Fintype.choose (pred p v) (unique p v)
      incident p h := Subtype.ext
        ((Fintype.choose_spec (pred p (viewEndpoint past p h)) (unique p _)) h rfl).symm }

instance successorDecidable
    (m : Move I₁ I₂ O₁ O₂ B.State D) (P : Position I₁ I₂ B.State D) :
    Decidable (ComponentSuccessor B M m P) := by
  unfold ComponentSuccessor
  infer_instance

/-- Full component plus labels determines its child position uniquely. -/
theorem successor_unique (m : Move I₁ I₂ O₁ O₂ B.State D)
    (P R : Position I₁ I₂ B.State D)
    (first : ComponentSuccessor B M m P) (second : ComponentSuccessor B M m R)
    (h : P.Root) (k : R.Root) (same : h.val = k.val) : P = R := by
  classical
  obtain ⟨C, cc, pc, hc, sc⟩ := first
  obtain ⟨L, cl, pl, hl, sl⟩ := second
  have hm : h.val ∈ C.image m.source.history := by rw [← hc]; exact h.property
  have km : k.val ∈ L.image m.source.history := by rw [← hl]; exact k.property
  obtain ⟨e, he, eh⟩ := Finset.mem_image.mp hm
  obtain ⟨f, hf, fk⟩ := Finset.mem_image.mp km
  have ef : e = f := m.source.history_injective (eh.trans (same.trans fk.symm))
  have eq : C = L := ExecutableHistories.components_eq_of_common M m C L cc cl e he (ef.symm ▸ hf)
  subst L
  apply position_ext P R (pc.trans pl.symm) (hc.trans hl.symm)
  intro x y xy
  have inside : x.val ∈ C.image m.source.history := by rw [← hc]; exact x.property
  obtain ⟨e, he, eh⟩ := Finset.mem_image.mp inside
  exact (sc x ⟨e, he⟩ eh.symm).trans (sl y ⟨e, he⟩ (xy.symm.trans eh.symm)).symm

/-- Recover the full component by its uniquely determined history image. -/
def recoverComponent (m : Move I₁ I₂ O₁ O₂ B.State D) (P : Position I₁ I₂ B.State D)
    (next : ComponentSuccessor B M m P) : Finset m.source.End :=
  Fintype.choose (fun C : Finset m.source.End => P.histories = C.image m.source.history) (by
    obtain ⟨C, _, _, histories, _⟩ := next
    exact ⟨C, histories, fun L eq => Finset.image_injective m.source.history_injective (eq.symm.trans histories)⟩)

theorem recoverComponent_spec (m : Move I₁ I₂ O₁ O₂ B.State D) (P : Position I₁ I₂ B.State D)
    (next : ComponentSuccessor B M m P) :
    P.histories = (recoverComponent B M m P next).image m.source.history := by
  unfold recoverComponent
  exact Fintype.choose_spec (fun C : Finset m.source.End => P.histories = C.image m.source.history) _

theorem recoverComponent_eq (m : Move I₁ I₂ O₁ O₂ B.State D) (P : Position I₁ I₂ B.State D)
    (next : ComponentSuccessor B M m P) : recoverComponent B M m P next = next.choose :=
  Finset.image_injective m.source.history_injective
    ((recoverComponent_spec B M m P next).symm.trans next.choose_spec.2.2.1)

/-- Reuse the library's finite preimage search; only the state labeling
changes from per-round game states to the actual block successor. -/
def componentPosition (m : Move I₁ I₂ O₁ O₂ B.State D) (C : Finset m.source.End)
    (component : IsComponent M m C) : Position I₁ I₂ B.State D where
  phase := m.source.phase + 1
  histories := C.image m.source.history
  nonempty := (ComponentTrees.component_nonempty M m C component).image _
  lengths := by
    intro h hh
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hh
    exact m.source.history_length e
  state h := blockSuccessor B m.source.state m.rule (ExecutableHistories.preimage m C h)

theorem componentPosition_states (m : Move I₁ I₂ O₁ O₂ B.State D) (C : Finset m.source.End)
    (component : IsComponent M m C)
    (h : (componentPosition B M m C component).Root) (e : C)
    (eq : h.val = m.source.history e.val) :
    (componentPosition B M m C component).state h = blockSuccessor B m.source.state m.rule e.val := by
  have same := m.source.history_injective ((ExecutableHistories.preimage_spec m C h).trans eq)
  change blockSuccessor B m.source.state m.rule _ = _
  rw [same]

theorem componentPosition_successor (m : Move I₁ I₂ O₁ O₂ B.State D) (C : Finset m.source.End)
    (component : IsComponent M m C) : ComponentSuccessor B M m (componentPosition B M m C component) :=
  ⟨C, component, rfl, rfl, componentPosition_states B M m C component⟩



variable (liveness : StateLiveness B M)
variable (hat : CompressedTree B M bound) (hatValid : hat.Valid)
open ReverseConstruction

def mappedComponent (st : ReverseConstruction.State B M hat)
    (C : Finset st.real.End) (component : IsComponent M (action B M hat st).move C) :
    {L : Finset (hat st.node).extensionMove.source.End //
      IsComponent M (hat st.node).extensionMove L ∧
      ∀ e ∈ C, simulationEndpoint B M (hat st.node) st.real st.sim e ∈ L} := by
  exact Fintype.chooseX (fun L => IsComponent M (hat st.node).extensionMove L ∧
    ∀ e ∈ C, simulationEndpoint B M (hat st.node) st.real st.sim e ∈ L) (by
      obtain ⟨L, comp, inside⟩ := simulation_component B M (hat st.node) st.real st.valid st.sim liveness C component
      obtain ⟨a, ha⟩ := ComponentTrees.component_nonempty M (action B M hat st).move C component
      exact ⟨L, ⟨comp, inside⟩, fun J hj => ExecutableHistories.components_eq_of_common M
        (hat st.node).extensionMove J L hj.1 comp _ (hj.2 a ha) (inside a ha)⟩)

def advanceData (st : ReverseConstruction.State B M hat) (R : Position I₁ I₂ B.State D)
    (next : (action B M hat st).Successor R) : ReverseConstruction.AdvanceData B M hat st R := by
  let N := hat st.node
  let P := st.real
  let m := (action B M hat st).move
  let C := recoverComponent B M m R next
  have ceq : C = next.choose := recoverComponent_eq B M m R next
  have component : IsComponent M m C := by rw [ceq]; exact next.choose_spec.1
  have histories : R.histories = C.image P.history := recoverComponent_spec B M m R next
  have labels : ∀ (h : R.Root) (e : C), h.val = P.history e.val →
      R.state h = blockSuccessor B P.state m.rule e.val := by
    rw [ceq]
    exact next.choose_spec.2.2.2
  let mapped := mappedComponent B M liveness hat st C component
  let L := mapped.val
  have targetComponent := mapped.property.1
  have inside := mapped.property.2
  let S := componentPosition B M N.extensionMove L targetComponent
  let pick (h : R.Root) : P.End := ExecutableHistories.preimage m C
    ⟨h.val, by change _ ∈ C.image P.history; rw [← histories]; exact h.property⟩
  have pickMem h : pick h ∈ C := ExecutableHistories.preimage_mem m C _
  have pickHist h : P.history (pick h) = h.val := ExecutableHistories.preimage_spec m C _
  let f (h : R.Root) : S.Root := ⟨N.extensionMove.source.history (simulationEndpoint B M N P st.sim (pick h)),
    Finset.mem_image.mpr ⟨_, inside _ (pickMem h), rfl⟩⟩
  let nextSim : PositionSimulation B R S :=
    { map := finiteViewMap R.past S.past f (by
        intro p h k same
        apply simulationEndpoint_views B M N P st.sim p (pick h) (pick k)
        simpa only [pickHist] using same)
      phase := by
        change R.phase = N.position.phase + 1
        rw [next.choose_spec.2.1]
        exact congrArg (· + 1) st.sim.phase
      states := by
        intro h
        change R.state h = S.state (f h)
        rw [labels h ⟨pick h, pickMem h⟩ (pickHist h).symm,
          componentPosition_states B M N.extensionMove L targetComponent (f h) ⟨_, inside _ (pickMem h)⟩ rfl]
        exact simulationEndpoint_state B M N P st.valid st.sim (pick h) }
  refine ⟨S, componentPosition_successor B M N.extensionMove L targetComponent, nextSim, ?_⟩
  intro h a u eq
  have picked : pick h = wordScenario a u := P.history_injective
    ((pickHist h).trans (eq.trans (wordScenario_history P.past a u).symm))
  change N.extensionMove.source.history (simulationEndpoint B M N P st.sim (pick h)) = _
  rw [simulationEndpoint_history, picked, wordScenario_root, scenarioWord_wordScenario]

theorem advanceData_unique (st : ReverseConstruction.State B M hat) (P : Position I₁ I₂ B.State D)
    (next : (action B M hat st).Successor P)
    (x y : ReverseConstruction.AdvanceData B M hat st P) : x = y := by
  classical
  have equalMap (h : P.Root) : (x.sim.map.edge h).val = (y.sim.map.edge h).val := by
    obtain ⟨C, _, _, histories, _⟩ := next
    have mem : h.val ∈ C.image st.real.history := by
      change h.val ∈ C.image (action B M hat st).move.source.history
      rw [← histories]
      exact h.property
    obtain ⟨e, _, eh⟩ := Finset.mem_image.mp mem
    have trace : h.val = (closingLayerRoot D e).val ++ (scenarioWord D e).val :=
      eh.symm.trans (scenarioWord_history st.real.past D e)
    exact (x.trace h _ _ trace).trans (y.trace h _ _ trace).symm
  obtain ⟨h, hh⟩ := P.nonempty
  have targetEq := successor_unique B M (hat st.node).extensionMove x.target y.target x.next y.next
    (x.sim.map.edge ⟨h, hh⟩) (y.sim.map.edge ⟨h, hh⟩) (equalMap ⟨h, hh⟩)
  cases x with | mk X nx sx tx =>
    cases y with | mk Y ny sy ty =>
      dsimp only at targetEq
      subst Y
      have mapEq : sx.map = sy.map := ViewComplexMap.ext (funext (fun h => Subtype.ext (equalMap h)))
      cases sx
      cases sy
      dsimp only at mapEq
      cases mapEq
      rfl

theorem advanceData_eq (st : ReverseConstruction.State B M hat) (P : Position I₁ I₂ B.State D)
    (next : (action B M hat st).Successor P) :
    advanceData B M liveness hat st P next = ReverseConstruction.advanceData B M liveness hat st P next :=
  advanceData_unique B M hat st P next _ _

def buildAdvance (st : ReverseConstruction.State B M hat) (P : Position I₁ I₂ B.State D)
    (next : (action B M hat st).Successor P)
    (data : ReverseConstruction.AdvanceData B M hat st P) : ReverseConstruction.State B M hat := by
  have support : publicSupport CompressedNode.offers hat (st.node ++ [data.target]) = true := by
    rw [publicSupport_append, st.supported, Bool.true_and]
    exact @decide_eq_true _ (Classical.propDecidable _) data.next
  have source : (hat (st.node ++ [data.target])).position = data.target := by
    have eq := hatValid _ support
    simpa only [observableAt, List.getLast?_concat, Option.getD_some] using eq
  exact ⟨P, ComponentSuccessor.valid B M next st.valid,
    st.node ++ [data.target], support, data.sim.castTarget source.symm⟩

def advanceState (st : ReverseConstruction.State B M hat) (P : Position I₁ I₂ B.State D)
    (next : (action B M hat st).Successor P) : ReverseConstruction.State B M hat :=
  buildAdvance B M hat hatValid st P next (advanceData B M liveness hat st P next)

theorem advanceState_eq (st : ReverseConstruction.State B M hat) (P : Position I₁ I₂ B.State D)
    (next : (action B M hat st).Successor P) :
    advanceState B M liveness hat hatValid st P next = ReverseConstruction.advanceState B M liveness hat hatValid st P next :=
  congrArg (buildAdvance B M hat hatValid st P next) (advanceData_eq B M liveness hat st P next)

def stepState (st : ReverseConstruction.State B M hat) (P : Position I₁ I₂ B.State D) : ReverseConstruction.State B M hat :=
  if next : ComponentSuccessor B M (action B M hat st).move P then
    advanceState B M liveness hat hatValid st P next else st

theorem stepState_eq : stepState B M liveness hat hatValid = ReverseConstruction.stepState B M liveness hat hatValid := by
  funext st P
  by_cases next : ComponentSuccessor B M (action B M hat st).move P
  · simp only [stepState, ReverseConstruction.stepState, UncompressedNode.Successor, dif_pos next, advanceState_eq]
  · simp only [stepState, ReverseConstruction.stepState, UncompressedNode.Successor, dif_neg next]

/-- Executable transformation of an effectively supplied compressed tree.
It computes each requested finite address by finite searches and a fold. -/
def tree : UncompressedTree B M := fun node => action B M hat
  (node.foldl (stepState B M liveness hat hatValid) (initialState B M hat hatValid))

theorem tree_eq : tree B M liveness hat hatValid = ReverseConstruction.tree B M liveness hat hatValid := by
  unfold tree ReverseConstruction.tree ReverseConstruction.atState
  rw [stepState_eq]

theorem tree_accepting (accepting : hat.Accepting) : (tree B M liveness hat hatValid).Accepting := by
  rw [tree_eq]
  exact ReverseConstruction.tree_accepting B M liveness hat hatValid accepting

end Characterisation.ComponentTrees.ExecutableReverse
