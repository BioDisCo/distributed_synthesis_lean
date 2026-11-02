/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.ReverseLocal

/-! Recursive unfolding in the reverse bounded-representation proof.
Every supported real child gets a simulated child and a state-preserving
map. The construction is one tree for all runs, not a tree chosen per run.
-/
namespace Characterisation.ComponentTrees.ReverseConstruction
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {I₁ I₂ O₁ O₂ G : Type} {D bound : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (liveness : StateLiveness B M)
variable (hat : CompressedTree B M bound) (hatValid : hat.Valid)

structure State where
  real : Position I₁ I₂ B.State D
  valid : PositionValid B M real
  node : List (Position I₁ I₂ B.State D)
  supported : publicSupport CompressedNode.offers hat node = true
  sim : PositionSimulation B real (hat node).position

def action (st : State B M hat) : UncompressedNode B M :=
  pullNode B M (hat st.node) st.real st.valid st.sim

def initialState : State B M hat := by
  have source := hatValid [] (publicSupport_nil _ _)
  change (hat []).position = Position.initial B.initial at source
  refine ⟨Position.initial B.initial, ?_, [], publicSupport_nil _ _, ?_⟩
  · rw [← source]
    exact (hat []).valid
  · rw [source]
    exact ⟨ViewComplexMap.identity _, rfl, fun _ => rfl⟩

structure AdvanceData (st : State B M hat) (P : Position I₁ I₂ B.State D) where
  target : Position I₁ I₂ B.State D
  next : (hat st.node).Successor target
  sim : PositionSimulation B P target
  trace : ∀ (h : P.Root) (a : st.real.Root)
    (u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D), h.val = a.val ++ u.val →
    (sim.map.edge h).val = ((hat st.node).reduction.map.edge (st.sim.map.edge a)).val ++ u.val

def advanceData (st : State B M hat) (P : Position I₁ I₂ B.State D)
    (next : (action B M hat st).Successor P) : AdvanceData B M hat st P := by
  have ex := simulation_next B M (hat st.node) st.real st.valid st.sim liveness P next
  exact ⟨ex.choose, ex.choose_spec.1, ex.choose_spec.2.choose, ex.choose_spec.2.choose_spec⟩

def advanceState (st : State B M hat) (P : Position I₁ I₂ B.State D)
    (next : (action B M hat st).Successor P) : State B M hat := by
  let data := advanceData B M liveness hat st P next
  have support : publicSupport CompressedNode.offers hat (st.node ++ [data.target]) = true := by
    rw [publicSupport_append, st.supported, Bool.true_and]
    exact decide_eq_true data.next
  have source : (hat (st.node ++ [data.target])).position = data.target := by
    have eq := hatValid _ support
    simpa only [observableAt, List.getLast?_concat, Option.getD_some] using eq
  exact ⟨P, ComponentSuccessor.valid B M next st.valid,
    st.node ++ [data.target], support, data.sim.castTarget source.symm⟩

@[simp] theorem advanceState_real (st : State B M hat) (P : Position I₁ I₂ B.State D)
    (next : (action B M hat st).Successor P) :
    (advanceState B M liveness hat hatValid st P next).real = P := rfl

@[simp] theorem advanceState_node (st : State B M hat) (P : Position I₁ I₂ B.State D)
    (next : (action B M hat st).Successor P) :
    (advanceState B M liveness hat hatValid st P next).node =
      st.node ++ [(advanceData B M liveness hat st P next).target] := rfl

theorem advanceState_trace (st : State B M hat) (P : Position I₁ I₂ B.State D)
    (next : (action B M hat st).Successor P)
    (h : P.Root) (a : st.real.Root) (u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D)
    (eq : h.val = a.val ++ u.val) :
    ((advanceState B M liveness hat hatValid st P next).sim.map.edge h).val =
      ((hat st.node).reduction.map.edge (st.sim.map.edge a)).val ++ u.val := by
  change (((advanceData B M liveness hat st P next).sim.castTarget _).map.edge h).val = _
  rw [PositionSimulation.castTarget_edge]
  exact (advanceData B M liveness hat st P next).trace h a u eq

def stepState (st : State B M hat) (P : Position I₁ I₂ B.State D) : State B M hat :=
  if next : (action B M hat st).Successor P then
    advanceState B M liveness hat hatValid st P next else st

def atState (node : List (Position I₁ I₂ B.State D)) : State B M hat :=
  node.foldl (stepState B M liveness hat hatValid) (initialState B M hat hatValid)

def tree : UncompressedTree B M := fun node => action B M hat (atState B M liveness hat hatValid node)

@[simp] theorem atState_append (node : List (Position I₁ I₂ B.State D)) (P : Position I₁ I₂ B.State D) :
    atState B M liveness hat hatValid (node ++ [P]) =
      stepState B M liveness hat hatValid (atState B M liveness hat hatValid node) P := by
  simp only [atState, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp] theorem stepState_of_next (st : State B M hat) (P : Position I₁ I₂ B.State D)
    (next : (action B M hat st).Successor P) :
    stepState B M liveness hat hatValid st P = advanceState B M liveness hat hatValid st P next := by
  simp only [stepState, dif_pos next]

theorem atState_real (node : List (Position I₁ I₂ B.State D))
    (supported : publicSupport UncompressedNode.offers (tree B M liveness hat hatValid) node = true) :
    (atState B M liveness hat hatValid node).real = observableAt (Position.initial B.initial) node := by
  cases node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node P =>
    have both : publicSupport UncompressedNode.offers (tree B M liveness hat hatValid) node = true ∧
        UncompressedNode.offers (tree B M liveness hat hatValid node) P = true := by
      simpa only [publicSupport_append, Bool.and_eq_true] using supported
    have next : (action B M hat (atState B M liveness hat hatValid node)).Successor P := of_decide_eq_true both.2
    rw [atState_append, stepState_of_next B M liveness hat hatValid _ _ next, advanceState_real]
    simp [observableAt]

theorem tree_valid : (tree B M liveness hat hatValid).Valid := by
  intro node supported
  exact atState_real B M liveness hat hatValid node supported

private theorem cast_reduction (old new : CompressedNode B M bound) (eq : old = new)
    {P : Position I₁ I₂ B.State D} (sim : PositionSimulation B P old.position) (h : P.Root) :
    (new.reduction.map.edge ((sim.castTarget (congrArg CompressedNode.position eq)).map.edge h)).val =
      (old.reduction.map.edge (sim.map.edge h)).val := by cases eq; rfl

private theorem advance_trace_eq (st after : State B M hat) (P : Position I₁ I₂ B.State D)
    (next : (action B M hat st).Successor P)
    (eq : after = advanceState B M liveness hat hatValid st P next)
    (h : after.real.Root) (a : st.real.Root) (u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D)
    (trace : h.val = a.val ++ u.val) :
    (after.sim.map.edge h).val = ((hat st.node).reduction.map.edge (st.sim.map.edge a)).val ++ u.val := by
  subst after
  exact advanceState_trace B M liveness hat hatValid st P next h a u trace

/-- One persistent simulated branch and its maps, for every supported real
branch. All runs on this branch use these same maps and copied rules. -/
theorem simulation_branch (branch : Nat → Position I₁ I₂ B.State D)
    (supported : ∀ n, publicSupport UncompressedNode.offers
      (tree B M liveness hat hatValid) (branchNode branch n) = true) :
    ∃ targetBranch : Nat → Position I₁ I₂ B.State D,
      (∀ n, publicSupport CompressedNode.offers hat (branchNode targetBranch n) = true) ∧
      ∃ sim : ∀ n, PositionSimulation B
        (tree B M liveness hat hatValid (branchNode branch n)).position (hat (branchNode targetBranch n)).position,
      ∀ n (h : (tree B M liveness hat hatValid (branchNode branch (n+1))).position.Root)
        (a : (tree B M liveness hat hatValid (branchNode branch n)).position.Root)
        (u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D), h.val = a.val ++ u.val →
        ((sim (n+1)).map.edge h).val =
          ((hat (branchNode targetBranch n)).reduction.map.edge ((sim n).map.edge a)).val ++ u.val := by
  let st n := atState B M liveness hat hatValid (branchNode branch n)
  have next n : (action B M hat (st n)).Successor (branch n) := by
    have both := supported (n+1)
    change publicSupport UncompressedNode.offers (tree B M liveness hat hatValid)
      (branchNode branch n ++ [branch n]) = true at both
    rw [publicSupport_append, Bool.and_eq_true] at both
    exact of_decide_eq_true both.2
  have advance n : st (n+1) = advanceState B M liveness hat hatValid (st n) (branch n) (next n) := by
    change atState B M liveness hat hatValid (branchNode branch n ++ [branch n]) = _
    rw [atState_append, stepState_of_next B M liveness hat hatValid _ _ (next n)]
  let targetBranch n := (advanceData B M liveness hat (st n) (branch n) (next n)).target
  have nodes n : (st n).node = branchNode targetBranch n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [advance n, advanceState_node]
      change (st n).node ++ [targetBranch n] = branchNode targetBranch n ++ [targetBranch n]
      rw [ih]
  let sim n := (st n).sim.castTarget (congrArg CompressedNode.position (congrArg hat (nodes n)))
  refine ⟨targetBranch, ?_, sim, ?_⟩
  · intro n
    rw [← nodes n]
    exact (st n).supported
  · intro n h a u eq
    dsimp only [sim]
    rw [PositionSimulation.castTarget_edge,
      cast_reduction B M _ _ (congrArg hat (nodes n)) (st n).sim a]
    exact advance_trace_eq B M liveness hat hatValid (st n) (st (n+1)) (branch n) (next n) (advance n) h a u eq

/-- The reverse semantic implication of `thm:tree-bounded-representation`,
with all branches and all compatible runs quantified globally. -/
theorem tree_accepting (accepting : hat.Accepting) : (tree B M liveness hat hatValid).Accepting := by
  refine ⟨tree_valid B M liveness hat hatValid, ?_⟩
  intro branch supported run
  obtain ⟨targetBranch, targetSupported, sim, trace⟩ :=
    simulation_branch B M liveness hat hatValid branch supported
  let mapped : hat.Run targetBranch :=
    { history := fun n => (sim n).map.edge (run.history n)
      word := run.word
      initial := by
        have mem := ((sim 0).map.edge (run.history 0)).property
        have root := hatValid [] (publicSupport_nil _ _)
        change (hat []).position = Position.initial B.initial at root
        change _ ∈ (hat []).position.histories at mem
        rw [root] at mem
        exact Finset.mem_singleton.mp mem
      next := fun n => trace n (run.history (n+1)) (run.history n) (run.word n) (run.next n) }
  have accepted := accepting.2 targetBranch targetSupported mapped
  have colors n : B.priority ((tree B M liveness hat hatValid (branchNode branch n)).position.state (run.history n)) =
      B.priority ((hat (branchNode targetBranch n)).position.state (mapped.history n)) :=
    congrArg B.priority ((sim n).states (run.history n))
  simpa only [← colors] using accepted

end
end Characterisation.ComponentTrees.ReverseConstruction

namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
variable {I₁ I₂ O₁ O₂ G : Type} {D bound : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]

theorem compressed_to_uncompressed
    (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
    (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
    (liveness : StateLiveness B M) (hat : CompressedTree B M bound) (accepting : hat.Accepting) :
    ∃ tree : UncompressedTree B M, tree.Accepting :=
  ⟨_, ReverseConstruction.tree_accepting B M liveness hat accepting.1 accepting⟩

/-- The manuscript's constructed automaton discharges the liveness premise;
it is not an additional assumption on its compressed trees or reductions. -/
theorem block_compressed_to_uncompressed [Fintype G]
    (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
    (A : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (hat : CompressedTree (blockAutomaton (jointRecognizer M) A D) M bound) (accepting : hat.Accepting) :
    ∃ tree : UncompressedTree (blockAutomaton (jointRecognizer M) A D) M, tree.Accepting :=
  compressed_to_uncompressed _ M (blockAutomaton_stateLiveness M A) hat accepting

end
end Characterisation.ComponentTrees
