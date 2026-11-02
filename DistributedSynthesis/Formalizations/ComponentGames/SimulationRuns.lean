/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.SimulationStrategy

namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

theorem mapClosingLayer_fromWord {H K : Type} (f : H → K) (h : H) (n : Nat)
    (word : Fin n → I₁ × I₂ × Graph) :
    mapClosingLayer f n (closingLayerFromWord h n word) = closingLayerFromWord (f h) n word := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [closingLayerFromWord,mapClosingLayer,ih]

theorem mapClosingLayer_wordScenario {H K : Type} (f : H → K) (h : H) (n : Nat)
    (word : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) n) :
    mapClosingLayer f n (wordScenario h word) = wordScenario (f h) word :=
  mapClosingLayer_fromWord f h n _

theorem simulation_stateAt (real target : Move I₁ I₂ O₁ O₂ Q D)
    (sim : Simulation M real.source target.source)
    (rule : real.rule = restrictClosingPolicy sim.map target.rule)
    (h : real.source.Root) (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D) (t : Nat) :
    stateAt step real h w t = stateAt step target (sim.map h) w t := by
  have initial : target.source.state ∘ sim.map = real.source.state := funext (fun h => (sim.state h).symm)
  unfold stateAt
  rw [rule]
  have replay := closingLayerLabels_restrict sim.map step target.source.state target.rule
    (min t D) (Nat.min_le_right _ _) (wordScenario h ⟨w.val.take t,by simp [w.property]⟩)
  simpa only [initial,mapClosingLayer_wordScenario] using replay

/-- The final paragraph of the paper's simulation proof. Each actual
compatible run maps to one persistent simulated run, with equal phase minima. -/
theorem simulated_run_wins
    (real hat : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D))
    (branch targetBranch : Nat → Position I₁ I₂ Q D)
    (q₀ : Q) (χ : Q → Nat) (winning : Winning M step .replacement q₀ χ hat)
    (supported : ∀ n, publicSupport (offers M step) hat (branchNode targetBranch n) = true)
    (sim : ∀ n, Simulation M (real (branchNode branch n)).source (hat (branchNode targetBranch n)).source)
    (rule : ∀ n, (real (branchNode branch n)).rule =
      restrictClosingPolicy (sim n).map (hat (branchNode targetBranch n)).rule)
    (trace : ∀ n (h : (real (branchNode branch (n+1))).source.Root)
      (a : (real (branchNode branch n)).source.Root)
      (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D),
      h.val = ((real (branchNode branch n)).replacement a).val ++ w.val →
      ((sim (n+1)).map h).val = ((hat (branchNode targetBranch n)).replacement ((sim n).map a)).val ++ w.val)
    (run : CompatibleRun real branch) :
    NatSeqMinEvenParity (fun n => rangeMin
      (fun t => χ (stateAt step (real (branchNode branch n)) (run.history n) (run.word n) t)) 0 (D-1)) := by
  let mapped : CompatibleRun hat targetBranch :=
    { history := fun n => (sim n).map (run.history n)
      word := run.word
      initial := by
        have mem := ((sim 0).map (run.history 0)).property
        have start := (winning.1 [] (publicSupport_nil _ _)).1
        change (hat []).source = Position.initial q₀ at start
        change _ ∈ (hat []).source.histories at mem
        rw [start] at mem
        exact Finset.mem_singleton.mp mem
      next := fun n => trace n (run.history (n+1)) (run.history n) (run.word n) (run.next n) }
  have wins := winning.2 targetBranch supported mapped
  have priorities : ∀ n, rangeMin
      (fun t => χ (stateAt step (real (branchNode branch n)) (run.history n) (run.word n) t)) 0 (D-1) =
      rangeMin (fun t => χ (stateAt step (hat (branchNode targetBranch n)) (mapped.history n) (mapped.word n) t)) 0 (D-1) := by
    intro n
    apply rangeMin_congr
    intro t _
    simpa only [Nat.zero_add] using congrArg χ
      (simulation_stateAt M step _ _ (sim n) (rule n) (run.history n) (run.word n) t)
  simpa only [priorities] using wins

section BranchConstruction
variable (hat : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D))
variable (q₀ : Q)
variable (hatLegal : SupportedMovesValid (offers M step) (Position.initial q₀)
    (Legal M step .replacement) hat)

private theorem cast_rule {P : Position I₁ I₂ Q D} (old new : Move I₁ I₂ O₁ O₂ Q D)
    (eq : old = new) (sim : Simulation M P old.source) :
    restrictClosingPolicy (sim.castTarget M (congrArg Move.source eq)).map new.rule =
      restrictClosingPolicy sim.map old.rule := by cases eq; rfl

private theorem cast_replacement {P : Position I₁ I₂ Q D} (old new : Move I₁ I₂ O₁ O₂ Q D)
    (eq : old = new) (sim : Simulation M P old.source) (h : P.Root) :
    (new.replacement ((sim.castTarget M (congrArg Move.source eq)).map h)).val =
      (old.replacement (sim.map h)).val := by cases eq; rfl

private theorem advance_trace_eq (st after : SimState M step hat) (P : Position I₁ I₂ Q D)
    (next : Next M step (stateAction M step hat st) P)
    (eq : after = advanceState M step hat q₀ hatLegal st P next)
    (h : after.real.Root) (a : st.real.Root) (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D)
    (trace : h.val = a.val ++ w.val) :
    (after.sim.map h).val = ((hat st.node).replacement (st.sim.map a)).val ++ w.val := by
  subst after
  exact advanceState_trace M step hat q₀ hatLegal st P next h a w trace

/-- For EVERY supported infinite real play, construct the simulated play
and the Sim_n family, including the run relation and output pullback. -/
theorem simulation_branch
    (branch : Nat → Position I₁ I₂ Q D)
    (supported : ∀ n, publicSupport (offers M step)
      (simulationTree M step hat q₀ hatLegal) (branchNode branch n) = true) :
    ∃ targetBranch : Nat → Position I₁ I₂ Q D,
      (∀ n, publicSupport (offers M step) hat (branchNode targetBranch n) = true) ∧
      ∃ sim : ∀ n, Simulation M
        (simulationTree M step hat q₀ hatLegal (branchNode branch n)).source
        (hat (branchNode targetBranch n)).source,
      (∀ n, (simulationTree M step hat q₀ hatLegal (branchNode branch n)).rule =
        restrictClosingPolicy (sim n).map (hat (branchNode targetBranch n)).rule) ∧
      ∀ n (h : (simulationTree M step hat q₀ hatLegal (branchNode branch (n+1))).source.Root)
        (a : (simulationTree M step hat q₀ hatLegal (branchNode branch n)).source.Root)
        (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D),
        h.val = ((simulationTree M step hat q₀ hatLegal (branchNode branch n)).replacement a).val ++ w.val →
        ((sim (n+1)).map h).val =
          ((hat (branchNode targetBranch n)).replacement ((sim n).map a)).val ++ w.val := by
  let st (n : Nat) := atState M step hat q₀ hatLegal (branchNode branch n)
  have next (n : Nat) : Next M step (stateAction M step hat (st n)) (branch n) := by
    have both := supported (n+1)
    change publicSupport (offers M step) (simulationTree M step hat q₀ hatLegal)
      (branchNode branch n ++ [branch n]) = true at both
    rw [publicSupport_append,Bool.and_eq_true] at both
    exact of_decide_eq_true both.2
  have advance (n : Nat) : st (n+1) = advanceState M step hat q₀ hatLegal (st n) (branch n) (next n) := by
    change atState M step hat q₀ hatLegal (branchNode branch n ++ [branch n]) = _
    rw [atState_append,stepState_of_next M step hat q₀ hatLegal _ _ (next n)]
  let targetBranch (n : Nat) := (advanceData M step hat q₀ hatLegal (st n) (branch n) (next n)).target
  have nodes (n : Nat) : (st n).node = branchNode targetBranch n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [advance n,advanceState_node]
      change (st n).node ++ [targetBranch n] = branchNode targetBranch n ++ [targetBranch n]
      rw [ih]
  let sim (n : Nat) := (st n).sim.castTarget M (congrArg Move.source (congrArg hat (nodes n)))
  refine ⟨targetBranch,?_,sim,?_,?_⟩
  · intro n
    rw [← nodes n]
    exact (st n).supported
  · intro n
    exact (cast_rule M (hat (st n).node) (hat (branchNode targetBranch n)) (congrArg hat (nodes n)) (st n).sim).symm
  · intro n h a w eq
    change h.val = a.val ++ w.val at eq
    dsimp only [sim]
    rw [Simulation.castTarget_val,cast_replacement M _ _ (congrArg hat (nodes n)) (st n).sim a]
    exact advance_trace_eq M step hat q₀ hatLegal (st n) (st (n+1)) (branch n) (next n) (advance n) h a w eq

/-- The difficult direction of Lemma replacement-game-equivalence, using
precisely the manuscript's recursive simulation and compatible-run map. -/
theorem replacement_winning_component (χ : Q → Nat)
    (winning : Winning M step .replacement q₀ χ hat) :
    Winning M step .component q₀ χ (simulationTree M step hat q₀ winning.1) := by
  refine ⟨simulationTree_legal M step hat q₀ winning.1,?_⟩
  intro branch supported run
  obtain ⟨targetBranch,targetSupported,sim,rules,trace⟩ :=
    simulation_branch M step hat q₀ winning.1 branch supported
  exact simulated_run_wins M step _ hat branch targetBranch q₀ χ winning targetSupported sim rules trace run

/-- The full paper game equivalence, over the literal history-set games. -/
theorem replacement_game_equivalence (χ : Q → Nat) :
    (∃ tree, Winning (D:=D) M step .replacement q₀ χ tree) ↔
      ∃ tree, Winning (D:=D) M step .component q₀ χ tree := by
  constructor
  · rintro ⟨tree,winning⟩
    exact ⟨_,replacement_winning_component M step tree q₀ χ winning⟩
  · rintro ⟨tree,winning⟩
    exact ⟨tree,component_winning_replacement M step q₀ χ tree winning⟩

end BranchConstruction

end
end Characterisation.ComponentGames.HistoryGame

