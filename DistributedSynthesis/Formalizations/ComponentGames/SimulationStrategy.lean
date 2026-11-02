/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.SimulationLocal

/- Assemble the manuscript's Sim_n induction along complete strategies and
infinite plays. Finite component containment alone is not an equivalence. -/
namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

namespace Simulation
variable {P R T : Position I₁ I₂ Q D}
def castTarget (sim : Simulation M P R) (eq : R = T) : Simulation M P T := eq ▸ sim
@[simp] theorem castTarget_val (sim : Simulation M P R) (eq : R = T) (h : P.Root) :
    ((sim.castTarget M eq).map h).val = (sim.map h).val := by cases eq; rfl
end Simulation

variable (hat : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D))
variable (q₀ : Q)
variable (hatLegal : SupportedMovesValid (offers M step) (Position.initial q₀)
    (Legal M step .replacement) hat)

structure SimState where
  real : Position I₁ I₂ Q D
  node : List (Position I₁ I₂ Q D)
  supported : publicSupport (offers M step) hat node = true
  sim : Simulation M real (hat node).source

def stateAction (st : SimState M step hat) : Move I₁ I₂ O₁ O₂ Q D :=
  pullMove M (hat st.node) st.sim

def initialSimState : SimState M step hat := by
  have source := (hatLegal [] (publicSupport_nil _ _)).1
  change (hat []).source = Position.initial q₀ at source
  refine ⟨Position.initial q₀,[],publicSupport_nil _ _,?_⟩
  rw [source]
  exact ⟨id,rfl,fun _ _ _ same => same,fun _ => rfl,fun _ => rfl⟩

include hatLegal in
theorem stateAction_legal (st : SimState M step hat) :
    Legal M step .component st.real (stateAction M step hat st) :=
  pullMove_legal M step (hat st.node) st.sim ⟨rfl,(hatLegal st.node st.supported).2⟩

structure AdvanceData (st : SimState M step hat) (P : Position I₁ I₂ Q D) where
  target : Position I₁ I₂ Q D
  next : Next M step (hat st.node) target
  sim : Simulation M P target
  trace : ∀ (h : P.Root) (a : st.real.Root)
    (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D), h.val = a.val ++ w.val →
    (sim.map h).val = ((hat st.node).replacement (st.sim.map a)).val ++ w.val

def advanceData (st : SimState M step hat) (P : Position I₁ I₂ Q D)
    (next : Next M step (stateAction M step hat st) P) : AdvanceData M step hat st P := by
  have ex := simulation_next M step (hat st.node) st.sim
    ⟨rfl,(hatLegal st.node st.supported).2⟩ P next
  exact ⟨ex.choose,ex.choose_spec.1,ex.choose_spec.2.choose,ex.choose_spec.2.choose_spec⟩

def advanceState (st : SimState M step hat) (P : Position I₁ I₂ Q D)
    (next : Next M step (stateAction M step hat st) P) : SimState M step hat := by
  let data := advanceData M step hat q₀ hatLegal st P next
  have support : publicSupport (offers M step) hat (st.node ++ [data.target]) = true := by
    rw [publicSupport_append,st.supported,Bool.true_and]
    exact decide_eq_true data.next
  have source : (hat (st.node ++ [data.target])).source = data.target := by
    have h := (hatLegal _ support).1
    simpa only [observableAt,List.getLast?_concat,Option.getD_some] using h
  exact ⟨P,st.node ++ [data.target],support,data.sim.castTarget M source.symm⟩

@[simp] theorem advanceState_real (st : SimState M step hat) (P : Position I₁ I₂ Q D)
    (next : Next M step (stateAction M step hat st) P) :
    (advanceState M step hat q₀ hatLegal st P next).real = P := rfl

@[simp] theorem advanceState_node (st : SimState M step hat) (P : Position I₁ I₂ Q D)
    (next : Next M step (stateAction M step hat st) P) :
    (advanceState M step hat q₀ hatLegal st P next).node =
      st.node ++ [(advanceData M step hat q₀ hatLegal st P next).target] := rfl

theorem advanceState_trace (st : SimState M step hat) (P : Position I₁ I₂ Q D)
    (next : Next M step (stateAction M step hat st) P)
    (h : P.Root) (a : st.real.Root) (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D)
    (eq : h.val = a.val ++ w.val) :
    ((advanceState M step hat q₀ hatLegal st P next).sim.map h).val =
      ((hat st.node).replacement (st.sim.map a)).val ++ w.val := by
  change (((advanceData M step hat q₀ hatLegal st P next).sim.castTarget M _).map h).val = _
  rw [Simulation.castTarget_val]
  exact (advanceData M step hat q₀ hatLegal st P next).trace h a w eq

def stepState (st : SimState M step hat) (P : Position I₁ I₂ Q D) : SimState M step hat :=
  if next : Next M step (stateAction M step hat st) P then
    advanceState M step hat q₀ hatLegal st P next else st

def atState (node : List (Position I₁ I₂ Q D)) : SimState M step hat :=
  node.foldl (stepState M step hat q₀ hatLegal) (initialSimState M step hat q₀ hatLegal)

def simulationTree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D) :=
  fun node => stateAction M step hat (atState M step hat q₀ hatLegal node)

@[simp] theorem atState_nil : (atState M step hat q₀ hatLegal []).real = Position.initial q₀ := rfl

@[simp] theorem atState_append (node : List (Position I₁ I₂ Q D)) (P : Position I₁ I₂ Q D) :
    atState M step hat q₀ hatLegal (node ++ [P]) =
      stepState M step hat q₀ hatLegal (atState M step hat q₀ hatLegal node) P := by
  simp only [atState,List.foldl_append,List.foldl_cons,List.foldl_nil]

@[simp] theorem stepState_of_next (st : SimState M step hat) (P : Position I₁ I₂ Q D)
    (next : Next M step (stateAction M step hat st) P) :
    stepState M step hat q₀ hatLegal st P = advanceState M step hat q₀ hatLegal st P next := by
  simp only [stepState,dif_pos next]

theorem atState_real (node : List (Position I₁ I₂ Q D))
    (supported : publicSupport (offers M step) (simulationTree M step hat q₀ hatLegal) node = true) :
    (atState M step hat q₀ hatLegal node).real = observableAt (Position.initial q₀) node := by
  cases node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node P =>
    have both : publicSupport (offers M step) (simulationTree M step hat q₀ hatLegal) node = true ∧
        offers M step (simulationTree M step hat q₀ hatLegal node) P = true := by
      simpa only [publicSupport_append,Bool.and_eq_true] using supported
    have next : Next M step (stateAction M step hat (atState M step hat q₀ hatLegal node)) P :=
      of_decide_eq_true both.2
    rw [atState_append,stepState_of_next M step hat q₀ hatLegal _ _ next,advanceState_real]
    simp [observableAt]

theorem simulationTree_legal :
    SupportedMovesValid (offers M step) (Position.initial q₀) (Legal M step .component)
      (simulationTree M step hat q₀ hatLegal) := by
  intro node supported
  rw [← atState_real M step hat q₀ hatLegal node supported]
  exact stateAction_legal M step hat q₀ hatLegal _

end
end Characterisation.ComponentGames.HistoryGame
