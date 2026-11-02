/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemDiagonalPairTreeRationalization
import DistributedSynthesis.Formalizations.Theorem.ThmDeterministicBlockAutomaton
import DistributedSynthesis.Formalizations.Theorem.ThmUniversalThreadDeterminization

/-!
# The exact-view uniform rationalization target

This file isolates the generic theorem that a one-tree alternating route would
have to provide.  Ordinary parity tree automata check one branch of one tree.
Exact local consistency is instead a finite synchronous two-node safety test:
the monitor follows two environment histories and compares the two labels
whenever the corresponding exact local views agree.

Both ingredients are finite and are instantiated below.  What is *not* proved
by the ordinary Rabin basis is that a tree satisfying both conditions can be
replaced by one transition-rational tree satisfying both.  Applying Rabin to
the synchronous square only returns an arbitrary rational pair tree; the
crossed-tree example in `LemDiagonalPairTreeRationalization` shows why that
does not recover one shared-origin tree.
-/

namespace DistributedSynthesis

universe u v w x y s

/-- A finite automaton that reads two branches of the same labeled tree in
lockstep and checks a relation between the two current node labels. -/
structure SynchronousPairSafetyMonitor
    (Branch : Type u) (Alphabet : Type v) where
  State : Type w
  stateFinite : Fintype State
  initial : State
  step : State -> Branch -> Branch -> State
  safe : State -> Alphabet -> Alphabet -> Prop

attribute [instance] SynchronousPairSafetyMonitor.stateFinite

namespace SynchronousPairSafetyMonitor

variable {Branch : Type u} {Alphabet : Type v}

/-- State after a synchronous pair of branch histories. -/
def control
    (M : SynchronousPairSafetyMonitor.{u, v, w} Branch Alphabet)
    (node : TreeNode (Branch × Branch)) : M.State :=
  node.foldl (fun state branch => M.step state branch.1 branch.2) M.initial

/-- The monitor accepts one tree when its pair law holds at every synchronous
pair of nodes. -/
def Accepts
    (M : SynchronousPairSafetyMonitor.{u, v, w} Branch Alphabet)
    (tree : LabeledTree Branch Alphabet) : Prop :=
  ∀ node : TreeNode (Branch × Branch),
    M.safe (M.control node)
      (tree (node.map Prod.fst)) (tree (node.map Prod.snd))

/-- The precise missing regular-basis principle: regularize one tree while
preserving both ordinary parity-tree acceptance and the synchronous pair
law on that same tree. -/
def RegularUniformizationBasis
    (global : RunParityTreeAutomaton.{u, v, x} Branch Alphabet)
    (pair : SynchronousPairSafetyMonitor.{u, v, w} Branch Alphabet) : Prop :=
  (∃ tree : LabeledTree Branch Alphabet,
      global.acceptsTree tree ∧ pair.Accepts tree) ->
    ∃ controller : TransitionRationalTree.{u, v, max w x} Branch Alphabet,
      global.acceptsTree controller.labeledTree ∧
        pair.Accepts controller.labeledTree

end SynchronousPairSafetyMonitor

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

variable [Inhabited In₁] [Inhabited In₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- The exact-view two-node monitor.  Its state is just the pair of exact-view
equality bits already proved correct in `ThmPairedProfiledExactViewTree`. -/
def exactViewPairSafetyMonitor :
    SynchronousPairSafetyMonitor
      (EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) where
  State := Bool × Bool
  stateFinite := inferInstance
  initial := (true, true)
  step := pairedViewEqualityStep
  safe := fun equal leftTable rightTable =>
    ∀ leftEnv rightEnv,
      let nextEqual := pairedViewEqualityStep equal leftEnv rightEnv
      (nextEqual.1 = true ->
          (leftTable leftEnv).1 = (rightTable rightEnv).1) ∧
        (nextEqual.2 = true ->
          (leftTable leftEnv).2 = (rightTable rightEnv).2)

@[simp] theorem exactViewPairSafetyMonitor_control
    (node : TreeNode
      (EnvironmentRound In₁ In₂ × EnvironmentRound In₁ In₂)) :
    (exactViewPairSafetyMonitor
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)).control
        node =
      pairedViewEqualityAfter node :=
  rfl

/-- The generic pair-monitor semantics is definitionally the exact local
consistency safety law on the self-product of one tree. -/
theorem exactViewPairSafetyMonitor_accepts_iff
    (tree : LabeledTree (EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) :
    (exactViewPairSafetyMonitor
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)).Accepts
        tree <->
      ExactViewGlobalSelfProductSafe (exactViewGlobalSelfProduct tree) :=
  Iff.rfl

/-- Deterministic one-tree monitor for universal DPA acceptance along every
environment branch. -/
noncomputable def exactViewGlobalParityMonitor :
    DeterministicBlockMonitor
      (EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  step := fun state table env =>
    A.step state
      { inputOne := env.inputOne
        inputTwo := env.inputTwo
        graph := env.graph
        outputOne := (table env).1
        outputTwo := (table env).2 }
  priority := A.priority

/-- The deterministic tree monitor state is exactly the original DPA state
after the corresponding finite environment prefix. -/
theorem exactViewGlobalParityMonitor_control_eq_run
    (tree : LabeledTree (EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (env : EnvironmentSequence In₁ In₂) : forall n,
    (exactViewGlobalParityMonitor A).control tree (branchNode env n) =
      A.run (exactViewGlobalTreeWord tree env) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode env (n + 1) =
          branchNode env n ++ [env n] from rfl,
        (exactViewGlobalParityMonitor A).control_append]
      change A.step _ (exactViewGlobalTreeWord tree env n) = _
      rw [ih]
      rfl

/-- Winning the ordinary deterministic tree monitor is exactly universal
acceptance of the original DPA on the one strategy tree. -/
theorem exactViewGlobalParityMonitor_winning_iff
    (tree : LabeledTree (EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) :
    (exactViewGlobalParityMonitor A).WinningTree tree <->
      ExactViewGlobalTreeWinning A tree := by
  constructor
  · intro hmonitor env
    rw [A.accepts_iff_natSeqMinEvenParity]
    have hbranch := hmonitor env
    have heq :
        (fun n => A.priority
          ((exactViewGlobalParityMonitor A).control tree
            (branchNode env n))) =
          fun n => A.priority (A.run (exactViewGlobalTreeWord tree env) n) := by
      funext n
      exact congrArg A.priority
        (exactViewGlobalParityMonitor_control_eq_run A tree env n)
    simpa only [exactViewGlobalParityMonitor] using (heq ▸ hbranch)
  · intro hglobal env
    have hbranch : NatSeqMinEvenParity
        (fun n => A.priority (A.run (exactViewGlobalTreeWord tree env) n)) :=
      (A.accepts_iff_natSeqMinEvenParity _).mp (hglobal env)
    have heq :
        (fun n => A.priority
          ((exactViewGlobalParityMonitor A).control tree
            (branchNode env n))) =
          fun n => A.priority (A.run (exactViewGlobalTreeWord tree env) n) := by
      funext n
      exact congrArg A.priority
        (exactViewGlobalParityMonitor_control_eq_run A tree env n)
    change NatSeqMinEvenParity
      (fun n => A.priority
        ((exactViewGlobalParityMonitor A).control tree (branchNode env n)))
    rw [heq]
    exact hbranch

/-- Exact specialization of the generic missing theorem. -/
def ExactViewRegularUniformizationBasis : Prop :=
  SynchronousPairSafetyMonitor.RegularUniformizationBasis
    (exactViewGlobalParityMonitor A).toRunAutomaton
    (exactViewPairSafetyMonitor
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))

/-- The smallest model-specific statement needed by the synthesis route.  It
does not assert a generic basis for arbitrary pair monitors or even for every
input tree: it starts only from existence of a winning distributed strategy
in this exact delay-one view model. -/
def DelayOneExactViewRegularization : Prop :=
  (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts (execution strategy env)) ->
    ∃ controller : TransitionRationalTree.{max u v, max u v x y, s}
        (EnvironmentRound In₁ In₂)
        (ExactViewGlobalActionTable
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)),
      ExactViewGlobalTreeWinning A controller.labeledTree ∧
        ExactViewGlobalSelfProductSafe
          (exactViewGlobalSelfProduct controller.labeledTree)

/-- A raw winning distributed strategy supplies the non-regular witness on
the left side of the uniformization target. -/
theorem exactViewUniformization_nonempty_of_winning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    ∃ tree : LabeledTree (EnvironmentRound In₁ In₂)
        (ExactViewGlobalActionTable
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)),
      (exactViewGlobalParityMonitor A).toRunAutomaton.acceptsTree tree ∧
        (exactViewPairSafetyMonitor
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)).Accepts
          tree := by
  let tree := exactViewGlobalActionTree strategy
  refine ⟨tree, ?_, ?_⟩
  · rw [(exactViewGlobalParityMonitor A).acceptsTree_iff_winningTree,
      exactViewGlobalParityMonitor_winning_iff]
    exact exactViewGlobalTreeWinning_actionTree A strategy hwin
  · rw [exactViewPairSafetyMonitor_accepts_iff]
    exact exactViewGlobalSelfProduct_safe tree
      (exactViewGlobalActionTree_locallyConsistent strategy)

/-- If the missing regular-uniformization basis is supplied, the exact-view
route immediately returns one finite shared-origin strategy tree. -/
theorem exists_transitionRational_exactViewTree_of_winning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (hbasis : ExactViewRegularUniformizationBasis A) :
    ∃ controller : TransitionRationalTree.{max u v, max u v x y, s}
        (EnvironmentRound In₁ In₂)
        (ExactViewGlobalActionTable
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)),
      ExactViewGlobalTreeWinning A controller.labeledTree ∧
        ExactViewGlobalSelfProductSafe
          (exactViewGlobalSelfProduct controller.labeledTree) := by
  rcases hbasis (exactViewUniformization_nonempty_of_winning A strategy hwin) with
    ⟨controller, hglobal, hpair⟩
  refine ⟨controller, ?_, ?_⟩
  · exact (exactViewGlobalParityMonitor_winning_iff A _).mp
      ((exactViewGlobalParityMonitor A).acceptsTree_iff_winningTree _ |>.mp
        hglobal)
  · exact (exactViewPairSafetyMonitor_accepts_iff _).mp hpair

/-- The generic uniformization target would discharge the strictly smaller
delay-one theorem, but the converse is intentionally not claimed. -/
theorem delayOneExactViewRegularization_of_uniformizationBasis
    (hbasis : ExactViewRegularUniformizationBasis A) :
    DelayOneExactViewRegularization A := by
  rintro ⟨strategy, hwin⟩
  exact exists_transitionRational_exactViewTree_of_winning A strategy hwin hbasis

end

end DetParityAutomaton

end DistributedSynthesis
