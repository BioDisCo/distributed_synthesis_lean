/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ExecutableComponents
namespace Characterisation.ComponentGames.ExecutableSimulation
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration Characterisation.ComponentGames.Representation.FiniteArena
open scoped DistributedSynthesis.DecidableViews
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open HistoryGame ExecutableHistories
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (hat : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D))
variable (q₀ : Q)
variable (hatLegal : SupportedMovesValid (HistoryGame.offers M step) (Position.initial q₀)
    (Legal M step .replacement) hat)

def advanceData (st : SimState M step hat) (R : Position I₁ I₂ Q D)
    (next : Next M step (stateAction M step hat st) R) : AdvanceData M step hat st R := by
  let P := st.real
  let m := hat st.node
  let sim := st.sim
  have legal : Legal M step .replacement m.source m := ⟨rfl,(hatLegal st.node st.supported).2⟩
  let K := recoverComponent M step (stateAction M step hat st) R next
  have keq : K = next.2.choose := recoverComponent_eq M step (stateAction M step hat st) R next
  have component : IsComponent M (pullMove M m sim) K := by rw [keq]; exact next.2.choose_spec.1
  have histories : R.histories = K.image P.history := by rw [keq]; exact next.2.choose_spec.2.1
  have labels : ∀ (h : R.Root) (e : P.End), e ∈ K → h.val = P.history e →
      R.state h = closingLayerLabels step P.state (pullMove M m sim).rule D (Nat.le_refl D) e := by
    rw [keq]; exact next.2.choose_spec.2.2
  have phase := next.1
  let mapped := mappedComponent M step m sim legal K component
  let L := mapped.val
  have targetComponent := mapped.property.1
  have inside := mapped.property.2
  let T := componentPosition M step m L targetComponent
  have targetPhase : T.phase = m.source.phase+1 := rfl
  have targetLabels := componentPosition_states M step m L targetComponent
  let pick (h : R.Root) : P.End := preimage (pullMove M m sim) K ⟨h.val,by change h.val ∈ K.image P.history; rw [← histories]; exact h.property⟩
  have pickMem (h : R.Root) : pick h ∈ K := preimage_mem _ K _
  have pickHistory (h : R.Root) : P.history (pick h) = h.val := preimage_spec _ K _
  let f (h : R.Root) : T.Root := ⟨m.source.history (simulationEnd M m sim (pick h)),
    Finset.mem_image.mpr ⟨simulationEnd M m sim (pick h),inside _ (pickMem h),rfl⟩⟩
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
  refine ⟨T,componentPosition_next M step m L targetComponent,nextSim,?_⟩
  intro h a w eq
  have picked : pick h = wordScenario a w := P.history_injective (by
    rw [pickHistory,eq]
    exact (wordScenario_history P.past a w).symm)
  change m.source.history (simulationEnd M m sim (pick h)) = _
  rw [simulationEnd_history,picked,wordScenario_root,scenarioWord_wordScenario]


theorem advanceData_unique (st : SimState M step hat) (P : Position I₁ I₂ Q D)
    (next : Next M step (stateAction M step hat st) P)
    (x y : AdvanceData M step hat st P) : x = y := by
  classical
  have equalMap (h : P.Root) : (x.sim.map h).val = (y.sim.map h).val := by
    obtain ⟨⟨a,w⟩,⟨_,eq⟩,_⟩ := previous_phase_extensions M step _ P next h
    exact (x.trace h a w eq).trans (y.trace h a w eq).symm
  obtain ⟨h,mem⟩ := P.nonempty
  have targetEq := next_unique_of_view M step (hat st.node) x.target y.target x.next y.next
    (x.sim.map ⟨h,mem⟩) (y.sim.map ⟨h,mem⟩) .one (congrArg (currentView .one) (equalMap ⟨h,mem⟩))
  cases x with | mk T nx sx tx =>
    cases y with | mk U ny sy ty =>
      dsimp only at targetEq
      subst U
      have mapEq : sx.map = sy.map := funext (fun h => Subtype.ext (equalMap h))
      cases sx
      cases sy
      dsimp only at mapEq
      cases mapEq
      rfl

theorem advanceData_eq (st : SimState M step hat) (P : Position I₁ I₂ Q D)
    (next : Next M step (stateAction M step hat st) P) :
    advanceData M step hat q₀ hatLegal st P next = HistoryGame.advanceData M step hat q₀ hatLegal st P next :=
  advanceData_unique M step hat st P next _ _
def buildAdvance (st : SimState M step hat) (P : Position I₁ I₂ Q D)
    (data : AdvanceData M step hat st P) : SimState M step hat := by
  have support : publicSupport (HistoryGame.offers M step) hat (st.node ++ [data.target]) = true := by
    rw [publicSupport_append,st.supported,Bool.true_and]
    exact @decide_eq_true _ (Classical.propDecidable _) data.next
  have source : (hat (st.node ++ [data.target])).source = data.target := by
    have h := (hatLegal _ support).1
    simpa only [observableAt,List.getLast?_concat,Option.getD_some] using h
  exact ⟨P,st.node ++ [data.target],support,data.sim.castTarget M source.symm⟩

def advanceState (st : SimState M step hat) (P : Position I₁ I₂ Q D)
    (next : Next M step (stateAction M step hat st) P) : SimState M step hat :=
  buildAdvance M step hat q₀ hatLegal st P (advanceData M step hat q₀ hatLegal st P next)

theorem advanceState_eq (st : SimState M step hat) (P : Position I₁ I₂ Q D)
    (next : Next M step (stateAction M step hat st) P) :
    advanceState M step hat q₀ hatLegal st P next = HistoryGame.advanceState M step hat q₀ hatLegal st P next :=
  congrArg (buildAdvance M step hat q₀ hatLegal st P) (advanceData_eq M step hat q₀ hatLegal st P next)

def stepState (st : SimState M step hat) (P : Position I₁ I₂ Q D) : SimState M step hat :=
  if next : Next M step (stateAction M step hat st) P then advanceState M step hat q₀ hatLegal st P next else st

theorem stepState_eq : stepState M step hat q₀ hatLegal = HistoryGame.stepState M step hat q₀ hatLegal := by
  funext st P
  by_cases next : Next M step (stateAction M step hat st) P
  · simp only [stepState,HistoryGame.stepState,dif_pos next,advanceState_eq]
  · simp only [stepState,HistoryGame.stepState,dif_neg next]

def tree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D) :=
  fun node => stateAction M step hat (node.foldl (stepState M step hat q₀ hatLegal)
    (initialSimState M step hat q₀ hatLegal))

theorem tree_eq : tree M step hat q₀ hatLegal = simulationTree M step hat q₀ hatLegal := by
  unfold tree simulationTree atState
  rw [stepState_eq]

end Characterisation.ComponentGames.ExecutableSimulation
