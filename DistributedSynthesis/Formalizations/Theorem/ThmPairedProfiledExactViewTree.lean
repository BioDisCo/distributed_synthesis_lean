/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRationalTree

/-!
# Exact-view local consistency before rationalization

This is the first brick of the exact-view route.  Nothing is quotiented by an
open root.  At a paired macro history we retain the genuine blind local view;
inside the following one-directional block we retain the blind process's own
input word.  These two pieces determine the complete finite action table for
the next blind round.

The table type is finite.  The proofs below show that two arbitrary semantic
macro histories with equal exact blind views choose the same table at every
equal own-input word.  Thus local consistency can be installed before the one
global parity rationalization, without a strict-leader bit or a representative
replacement.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

variable [Inhabited In₁] [Inhabited In₂]

/-- Finite action selected by the currently blind process for every possible
current own input.  The constructors are proof-side orientations; neither
constructor is delivered to a process. -/
inductive PairedBlindRoundTable where
  | sink
  | processOne (action : In₁ → Out₁)
  | processTwo (action : In₂ → Out₂)

noncomputable instance
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] :
    Fintype (PairedBlindRoundTable
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) := by
  classical
  let Rep := Unit ⊕ ((In₁ → Out₁) ⊕ (In₂ → Out₂))
  let e : PairedBlindRoundTable
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) ≃ Rep :=
    { toFun := fun table =>
        match table with
        | .sink => .inl ()
        | .processOne action => .inr (.inl action)
        | .processTwo action => .inr (.inr action)
      invFun := fun table =>
        match table with
        | .inl _ => .sink
        | .inr (.inl action) => .processOne action
        | .inr (.inr action) => .processTwo action
      left_inv := by intro table; cases table <;> rfl
      right_inv := by
        intro table
        rcases table with empty | (one | two)
        · cases empty; rfl
        · rfl
        · rfl }
  exact Fintype.ofEquiv Rep e.symm

/-- The exact blind view carried by semantic paired memory. -/
inductive PairedExactBlindView where
  | sink
  | processOne (view : View In₁ In₂ Proc.one)
  | processTwo (view : View In₁ In₂ Proc.two)

/-- Read the genuine local view, not a finite root representative. -/
def PairedStrategyMemory.exactBlindView
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂} :
    PairedStrategyMemory A strategy →
      PairedExactBlindView (In₁ := In₁) (In₂ := In₂)
  | .sink => .sink
  | .processOne entry _ => .processOne
      (currentView Proc.one entry.leftHistory)
  | .processTwo entry _ => .processTwo
      (currentView Proc.two entry.rightHistory)

/-- The finite next-round blind action table after an own-input word. -/
def PairedStrategyMemory.blindRoundTable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (memory : PairedStrategyMemory A strategy)
    (wordOne : List In₁) (wordTwo : List In₂) :
    PairedBlindRoundTable
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  match memory with
  | .sink => .sink
  | .processOne entry _ => .processOne
      (entry.lambdaOfStrategy.blind wordOne)
  | .processTwo entry _ => .processTwo
      (entry.lambdaOfStrategy.blind wordTwo)

/-- Exact process-one blind view after an interior own-input word. -/
def exactBlindViewOneAfter (view : View In₁ In₂ Proc.one)
    (word : List In₁) : View In₁ In₂ Proc.one :=
  word.foldl (fun current input => .noRecv current (.inl input)) view

/-- Process-two mirror. -/
def exactBlindViewTwoAfter (view : View In₁ In₂ Proc.two)
    (word : List In₂) : View In₁ In₂ Proc.two :=
  word.foldl (fun current input => .noRecv current (.inr input)) view

/-- Finite next-round table obtained directly from an exact process-one view,
with no semantic history representative. -/
def exactBlindRoundTableOne
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (view : View In₁ In₂ Proc.one) (word : List In₁) : In₁ → Out₁ :=
  fun input => strategy.one
    (.noRecv (exactBlindViewOneAfter view word) (.inl input))

/-- Process-two exact-view table. -/
def exactBlindRoundTableTwo
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (view : View In₁ In₂ Proc.two) (word : List In₂) : In₂ → Out₂ :=
  fun input => strategy.two
    (.noRecv (exactBlindViewTwoAfter view word) (.inr input))

/-! ## Finite synchronized equality monitor

The apparent infinitude of an exact recursive view is not needed when two
histories are compared round by round.  Equality of the two process-one views
and equality of the two process-two views form a two-bit invariant.  The next
two bits are computed from the old bits and the two current environment
rounds.  This is the finite pair test needed by an alternating strategy-tree
construction; it does not summarize either view in isolation.
-/

/-- The two equality bits for a pair of joint exact-view states. -/
noncomputable def pairedViewEquality
    (left right :
      View In₁ In₂ Proc.one × View In₁ In₂ Proc.two) : Bool × Bool :=
  by
    classical
    exact
      (if left.1 = right.1 then true else false,
        if left.2 = right.2 then true else false)

/-- Whether process one receives on a graph letter. -/
def processOneReceives : Graph → Bool
  | .left | .both => true
  | .right => false

/-- Whether process two receives on a graph letter. -/
def processTwoReceives : Graph → Bool
  | .right | .both => true
  | .left => false

/-- Update one equality bit.  A receive compares both predecessor views;
a no-receive step compares only the receiver's own predecessor view. -/
def pairedViewEqualityStepOne
    [DecidableEq In₁] [DecidableEq In₂]
    (equal : Bool × Bool)
    (left right : EnvironmentRound In₁ In₂) : Bool :=
  if processOneReceives left.graph != processOneReceives right.graph then
    false
  else if processOneReceives left.graph then
    equal.1 && equal.2 && decide (left.inputOne = right.inputOne) &&
      decide (left.inputTwo = right.inputTwo)
  else
    equal.1 && decide (left.inputOne = right.inputOne)

/-- Process-two mirror of the equality-bit update. -/
def pairedViewEqualityStepTwo
    [DecidableEq In₁] [DecidableEq In₂]
    (equal : Bool × Bool)
    (left right : EnvironmentRound In₁ In₂) : Bool :=
  if processTwoReceives left.graph != processTwoReceives right.graph then
    false
  else if processTwoReceives left.graph then
    equal.2 && equal.1 && decide (left.inputTwo = right.inputTwo) &&
      decide (left.inputOne = right.inputOne)
  else
    equal.2 && decide (left.inputTwo = right.inputTwo)

/-- The complete finite update of exact-view equality. -/
def pairedViewEqualityStep
    [DecidableEq In₁] [DecidableEq In₂]
    (equal : Bool × Bool)
    (left right : EnvironmentRound In₁ In₂) : Bool × Bool :=
  (pairedViewEqualityStepOne equal left right,
    pairedViewEqualityStepTwo equal left right)

omit [Inhabited In₁] [Inhabited In₂] in
/-- Kernel-checked pair test: the two-bit monitor computes exact equality of
the recursively updated views, including the `left`/`both` and `right`/`both`
indistinguishabilities. -/
theorem pairedViewEquality_advanceViewsWithEnvironment
    [DecidableEq In₁] [DecidableEq In₂]
    (left right :
      View In₁ In₂ Proc.one × View In₁ In₂ Proc.two)
    (leftRound rightRound : EnvironmentRound In₁ In₂) :
    pairedViewEquality
        (advanceViewsWithEnvironment left leftRound)
        (advanceViewsWithEnvironment right rightRound) =
      pairedViewEqualityStep (pairedViewEquality left right)
        leftRound rightRound := by
  cases leftRound with
  | mk leftOne leftTwo leftGraph =>
      cases rightRound with
      | mk rightOne rightTwo rightGraph =>
          cases leftGraph <;> cases rightGraph <;>
            all_goals
              by_cases hviewOne : left.1 = right.1 <;>
              by_cases hviewTwo : left.2 = right.2 <;>
              by_cases hinputOne : leftOne = rightOne <;>
              by_cases hinputTwo : leftTwo = rightTwo <;>
              simp [pairedViewEquality, pairedViewEqualityStep,
                pairedViewEqualityStepOne, pairedViewEqualityStepTwo,
                processOneReceives, processTwoReceives,
                advanceViewsWithEnvironment, hviewOne, hviewTwo,
                hinputOne, hinputTwo, Bool.and_assoc] <;>
              assumption

/-! ## The finite-branch global strategy tree

The pair monitor is most useful on the ordinary full environment tree.  A
node is a finite environment prefix.  Its finite label is the complete table
of joint outputs for the next environment round.  This presentation keeps a
single occurrence of every strategy choice; the local-uniformity law is a
synchronous two-node condition on that one tree.
-/

/-- Exact joint views generated by a finite environment prefix.  Outputs do
not occur because the view update is output-independent. -/
def exactViewsAfterEnvironmentPrefix
    (envs : List (EnvironmentRound In₁ In₂)) :
    View In₁ In₂ Proc.one × View In₁ In₂ Proc.two :=
  envs.foldl advanceViewsWithEnvironment
    (.empty Proc.one, .empty Proc.two)

section
omit [Inhabited In₁] [Inhabited In₂]

@[simp] theorem exactViewsAfterEnvironmentPrefix_nil :
    exactViewsAfterEnvironmentPrefix
        (In₁ := In₁) (In₂ := In₂) [] =
      (.empty Proc.one, .empty Proc.two) :=
  rfl

@[simp] theorem exactViewsAfterEnvironmentPrefix_snoc
    (envs : List (EnvironmentRound In₁ In₂))
    (env : EnvironmentRound In₁ In₂) :
    exactViewsAfterEnvironmentPrefix (envs ++ [env]) =
      advanceViewsWithEnvironment
        (exactViewsAfterEnvironmentPrefix envs) env := by
  simp [exactViewsAfterEnvironmentPrefix, List.foldl_append]

/-- The output-independent fold agrees with the exact views of the semantic
execution prefix generated by any strategy. -/
theorem viewPair_executionPrefixFromList_eq_exactViews
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    ∀ envs : List (EnvironmentRound In₁ In₂),
      viewPair (executionPrefixFromList strategy envs) =
        exactViewsAfterEnvironmentPrefix envs := by
  intro envs
  induction envs using List.reverseRecOn with
  | nil => rfl
  | append_singleton envs env ih =>
      rw [executionPrefixFromList_snoc, viewPair_append,
        exactViewsAfterEnvironmentPrefix_snoc, ih]
      cases hgraph : env.graph <;>
        simp [nextRound, advanceViews, advanceViewsWithEnvironment, hgraph]

end

/-- Exact joint views after one more environment round. -/
def exactNextViews
    (envs : List (EnvironmentRound In₁ In₂))
    (env : EnvironmentRound In₁ In₂) :
    View In₁ In₂ Proc.one × View In₁ In₂ Proc.two :=
  advanceViewsWithEnvironment (exactViewsAfterEnvironmentPrefix envs) env

/-- A finite node label: all joint outputs for the next environment move. -/
abbrev ExactViewGlobalActionTable :=
  EnvironmentRound In₁ In₂ → Out₁ × Out₂

noncomputable instance
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] :
    Fintype (ExactViewGlobalActionTable
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) := by
  classical
  infer_instance

/-- The one global action tree induced by a raw distributed strategy. -/
def exactViewGlobalActionTree
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    LabeledTree (EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :=
  fun envs env =>
    let round := nextRound strategy
      (executionPrefixFromList strategy envs) env
    (round.outputOne, round.outputTwo)

/-- Distributed local uniformity as a synchronous pair law on a single
finite-branch global strategy tree. -/
def ExactViewGlobalTreeLocallyConsistent
    (tree : LabeledTree (EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) : Prop :=
  (∀ left right leftEnv rightEnv,
      (exactNextViews left leftEnv).1 = (exactNextViews right rightEnv).1 →
        (tree left leftEnv).1 = (tree right rightEnv).1) ∧
  (∀ left right leftEnv rightEnv,
      (exactNextViews left leftEnv).2 = (exactNextViews right rightEnv).2 →
        (tree left leftEnv).2 = (tree right rightEnv).2)

omit [Inhabited In₁] [Inhabited In₂] in
/-- The global tree of a distributed strategy satisfies both synchronous
pair laws by construction. -/
theorem exactViewGlobalActionTree_locallyConsistent
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    ExactViewGlobalTreeLocallyConsistent
      (exactViewGlobalActionTree strategy) := by
  constructor
  · intro left right leftEnv rightEnv hview
    unfold exactViewGlobalActionTree
    simp only
    change strategy.one
        (nextView Proc.one (executionPrefixFromList strategy left) leftEnv) =
      strategy.one
        (nextView Proc.one (executionPrefixFromList strategy right) rightEnv)
    congr 1
    simpa [nextView, exactNextViews,
      viewPair_executionPrefixFromList_eq_exactViews strategy] using hview
  · intro left right leftEnv rightEnv hview
    unfold exactViewGlobalActionTree
    simp only
    change strategy.two
        (nextView Proc.two (executionPrefixFromList strategy left) leftEnv) =
      strategy.two
        (nextView Proc.two (executionPrefixFromList strategy right) rightEnv)
    congr 1
    simpa [nextView, exactNextViews,
      viewPair_executionPrefixFromList_eq_exactViews strategy] using hview

/-! ## Synchronous self-composition

The equality test becomes an ordinary finite-state safety test after taking
the synchronous self-product of the environment tree.  This is the positive
half of the alternating-automata route.  The self-product must still be kept
as the square of one shared strategy tree; forgetting that diagonal condition
would allow the two copies to choose unrelated outputs.
-/

/-- Equality-monitor state after a synchronous pair of finite environment
prefixes. -/
def pairedViewEqualityAfter
    [DecidableEq In₁] [DecidableEq In₂]
    (rounds : List
      (EnvironmentRound In₁ In₂ × EnvironmentRound In₁ In₂)) :
    Bool × Bool :=
  rounds.foldl
    (fun equal round => pairedViewEqualityStep equal round.1 round.2)
    (true, true)

section
omit [Inhabited In₁] [Inhabited In₂]

@[simp] theorem pairedViewEqualityAfter_nil
    [DecidableEq In₁] [DecidableEq In₂] :
    pairedViewEqualityAfter
        (In₁ := In₁) (In₂ := In₂) [] = (true, true) :=
  rfl

@[simp] theorem pairedViewEqualityAfter_snoc
    [DecidableEq In₁] [DecidableEq In₂]
    (rounds : List
      (EnvironmentRound In₁ In₂ × EnvironmentRound In₁ In₂))
    (round : EnvironmentRound In₁ In₂ ×
      EnvironmentRound In₁ In₂) :
    pairedViewEqualityAfter (rounds ++ [round]) =
      pairedViewEqualityStep (pairedViewEqualityAfter rounds)
        round.1 round.2 := by
  simp [pairedViewEqualityAfter, List.foldl_append]

/-- The finite synchronous monitor is extensionally the exact recursive-view
equality test on the two projected prefixes. -/
theorem pairedViewEqualityAfter_eq_exact
    [DecidableEq In₁] [DecidableEq In₂] :
    ∀ rounds : List
      (EnvironmentRound In₁ In₂ × EnvironmentRound In₁ In₂),
      pairedViewEqualityAfter rounds =
        pairedViewEquality
          (exactViewsAfterEnvironmentPrefix (rounds.map Prod.fst))
          (exactViewsAfterEnvironmentPrefix (rounds.map Prod.snd)) := by
  intro rounds
  induction rounds using List.reverseRecOn with
  | nil =>
      simp [pairedViewEquality, exactViewsAfterEnvironmentPrefix]
  | append_singleton rounds round ih =>
      rw [pairedViewEqualityAfter_snoc]
      simp only [List.map_append, List.map_singleton]
      rw [exactViewsAfterEnvironmentPrefix_snoc,
        exactViewsAfterEnvironmentPrefix_snoc, ih]
      exact (pairedViewEquality_advanceViewsWithEnvironment _ _ _ _).symm

end

/-- Synchronous square of one global strategy tree.  Both labels are read
from the same `tree`; this diagonal sharing is stronger than an arbitrary
tree whose labels happen to be pairs. -/
def exactViewGlobalSelfProduct
    (tree : LabeledTree (EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) :
    LabeledTree
      (EnvironmentRound In₁ In₂ × EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) ×
        ExactViewGlobalActionTable
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :=
  fun rounds =>
    (tree (rounds.map Prod.fst), tree (rounds.map Prod.snd))

/-- The exact finite node-local safety law checked on the synchronous square.
When the updated equality bit is true, the corresponding current outputs
must agree. -/
def ExactViewGlobalSelfProductSafe
    [DecidableEq In₁] [DecidableEq In₂]
    (productTree :
      LabeledTree
        (EnvironmentRound In₁ In₂ × EnvironmentRound In₁ In₂)
        (ExactViewGlobalActionTable
            (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) ×
          ExactViewGlobalActionTable
            (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) : Prop :=
  ∀ rounds leftEnv rightEnv,
    let equal := pairedViewEqualityStep (pairedViewEqualityAfter rounds)
      leftEnv rightEnv
    (equal.1 = true →
        ((productTree rounds).1 leftEnv).1 =
          ((productTree rounds).2 rightEnv).1) ∧
      (equal.2 = true →
        ((productTree rounds).1 leftEnv).2 =
          ((productTree rounds).2 rightEnv).2)

omit [Inhabited In₁] [Inhabited In₂] in
/-- Full exact-view local consistency implies the finite node-local safety
law of the synchronous self-product. -/
theorem exactViewGlobalSelfProduct_safe
    [DecidableEq In₁] [DecidableEq In₂]
    (tree : LabeledTree (EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (hlocal : ExactViewGlobalTreeLocallyConsistent tree) :
    ExactViewGlobalSelfProductSafe (exactViewGlobalSelfProduct tree) := by
  intro rounds leftEnv rightEnv
  rw [pairedViewEqualityAfter_eq_exact]
  constructor
  · intro hone
    have hview :
        (exactNextViews (rounds.map Prod.fst) leftEnv).1 =
          (exactNextViews (rounds.map Prod.snd) rightEnv).1 := by
      rw [← pairedViewEquality_advanceViewsWithEnvironment] at hone
      simpa [pairedViewEquality, exactNextViews] using hone
    exact hlocal.1 _ _ _ _ hview
  · intro htwo
    have hview :
        (exactNextViews (rounds.map Prod.fst) leftEnv).2 =
          (exactNextViews (rounds.map Prod.snd) rightEnv).2 := by
      rw [← pairedViewEquality_advanceViewsWithEnvironment] at htwo
      simpa [pairedViewEquality, exactNextViews] using htwo
    exact hlocal.2 _ _ _ _ hview

/-- The physical round selected by a global action tree at one node. -/
def exactViewGlobalTreeRound
    (tree : LabeledTree (EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (envs : List (EnvironmentRound In₁ In₂))
    (env : EnvironmentRound In₁ In₂) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  { inputOne := env.inputOne
    inputTwo := env.inputTwo
    graph := env.graph
    outputOne := (tree envs env).1
    outputTwo := (tree envs env).2 }

/-- The omega word read along one environment branch of a global action
tree. -/
def exactViewGlobalTreeWord
    (tree : LabeledTree (EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n => exactViewGlobalTreeRound tree (branchNode env n) (env n)

/-- Universal global parity of the single strategy tree. -/
def ExactViewGlobalTreeWinning
    (tree : LabeledTree (EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) : Prop :=
  ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (exactViewGlobalTreeWord tree env)

section
omit [Inhabited In₁] [Inhabited In₂]

/-- Finite-list execution along the depth-`n` branch node is the ordinary
execution prefix. -/
theorem executionPrefixFromList_branchNode
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) : ∀ n,
    executionPrefixFromList strategy (branchNode env n) =
      executionPrefix strategy env n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode env (n + 1) =
          branchNode env n ++ [env n] from rfl,
        executionPrefixFromList_snoc, executionPrefix_succ, ih]

/-- The global action tree of a raw strategy reads back exactly its real
execution on every environment branch. -/
theorem exactViewGlobalTreeWord_actionTree
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    exactViewGlobalTreeWord (exactViewGlobalActionTree strategy) env =
      execution strategy env := by
  funext n
  unfold exactViewGlobalTreeWord exactViewGlobalTreeRound
    exactViewGlobalActionTree
  rw [executionPrefixFromList_branchNode strategy env n]
  rw [execution_apply]
  rfl

/-- A winning distributed strategy supplies the combined finite-label tree:
global parity and the synchronous exact-view pair law hold simultaneously,
before rationalization. -/
theorem exactViewGlobalTreeWinning_actionTree
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    ExactViewGlobalTreeWinning A (exactViewGlobalActionTree strategy) := by
  intro env
  rw [exactViewGlobalTreeWord_actionTree]
  exact hwin env

end

omit [Inhabited In₁] in
/-- The semantic block sender factors definitionally through the exact blind
view and own-input word. -/
theorem blockSenderOne_eq_exactBlindRoundTable
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁) :
    blockSenderOne strategy history word =
      exactBlindRoundTableOne strategy (currentView Proc.one history) word := by
  funext input
  unfold blockSenderOne exactBlindRoundTableOne
  rw [nextView_one_of_graph_right _ _ rfl]
  have hright :
      ∀ env ∈ word.map
          (fun sIn => rightEnvironment ((default : In₂), sIn)),
        env.graph = Graph.right := by
    intro env henv
    rcases List.mem_map.mp henv with ⟨sIn, _, rfl⟩
    rfl
  rw [currentView_one_extendPrefix_right strategy history _ hright]
  simp [exactBlindViewOneAfter, List.foldl_map, rightEnvironment]

omit [Inhabited In₂] in
/-- Mirror exact-view factorization. -/
theorem blockSenderTwo_eq_exactBlindRoundTable
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂) :
    blockSenderTwo strategy history word =
      exactBlindRoundTableTwo strategy (currentView Proc.two history) word := by
  funext input
  unfold blockSenderTwo exactBlindRoundTableTwo
  rw [nextView_two_of_graph_left _ _ rfl]
  have hleft :
      ∀ env ∈ word.map
          (fun sIn => leftEnvironment ((default : In₁), sIn)),
        env.graph = Graph.left := by
    intro env henv
    rcases List.mem_map.mp henv with ⟨sIn, _, rfl⟩
    rfl
  rw [currentView_two_extendPrefix_left strategy history _ hleft]
  simp [exactBlindViewTwoAfter, List.foldl_map, leftEnvironment]

/-- The exact process-one local strategy tree rooted at a concrete view.  It
has finite branching and a finite label alphabet. -/
def exactBlindTreeOne
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (view : View In₁ In₂ Proc.one) :
    LabeledTree In₁ (In₁ → Out₁) :=
  fun word => exactBlindRoundTableOne strategy view word

/-- Process-two exact local tree. -/
def exactBlindTreeTwo
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (view : View In₁ In₂ Proc.two) :
    LabeledTree In₂ (In₂ → Out₂) :=
  fun word => exactBlindRoundTableTwo strategy view word

omit [Inhabited In₁] in
/-- A semantic process-one block sender is exactly the local tree rooted at
its current blind view. -/
theorem blockSenderOne_eq_exactBlindTree
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : History In₁ In₂ Graph Out₁ Out₂) :
    blockSenderOne strategy history =
      exactBlindTreeOne strategy (currentView Proc.one history) := by
  funext word
  exact blockSenderOne_eq_exactBlindRoundTable strategy history word

omit [Inhabited In₂] in
/-- Mirror tree equation. -/
theorem blockSenderTwo_eq_exactBlindTree
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : History In₁ In₂ Graph Out₁ Out₂) :
    blockSenderTwo strategy history =
      exactBlindTreeTwo strategy (currentView Proc.two history) := by
  funext word
  exact blockSenderTwo_eq_exactBlindRoundTable strategy history word

omit [Inhabited In₁] in
/-- Equal exact process-one blind views determine the entire future blind
sender fragment. -/
theorem procOne_lambda_blind_eq_of_exactView_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (left right : ProcOnePairedEntryRep strategy)
    (hview : currentView Proc.one left.leftHistory =
      currentView Proc.one right.leftHistory) :
    left.lambdaOfStrategy.blind = right.lambdaOfStrategy.blind := by
  simpa [ProcOnePairedEntryRep.lambdaOfStrategy] using
    (blockSenderOne_eq_of_view_eq strategy hview)

omit [Inhabited In₂] in
/-- Process-two mirror. -/
theorem procTwo_lambda_blind_eq_of_exactView_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (left right : ProcTwoPairedEntryRep strategy)
    (hview : currentView Proc.two left.rightHistory =
      currentView Proc.two right.rightHistory) :
    left.lambdaOfStrategy.blind = right.lambdaOfStrategy.blind := by
  simpa [ProcTwoPairedEntryRep.lambdaOfStrategy] using
    (blockSenderTwo_eq_of_view_eq strategy hview)

/-- Exact-view equality makes the finite round table identical at every pair
of equal own-input words.  This is the node-pair test required by the global
alternating construction. -/
theorem blindRoundTable_eq_of_exactBlindView_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (left right : PairedStrategyMemory A strategy)
    (hview : left.exactBlindView A = right.exactBlindView A)
    {wordOne wordOne' : List In₁} {wordTwo wordTwo' : List In₂}
    (hone : wordOne = wordOne') (htwo : wordTwo = wordTwo') :
    left.blindRoundTable A wordOne wordTwo =
      right.blindRoundTable A wordOne' wordTwo' := by
  subst wordOne'
  subst wordTwo'
  cases left with
  | sink =>
      cases right <;> simp [PairedStrategyMemory.exactBlindView] at hview ⊢
  | processOne leftEntry leftMinimum =>
      cases right with
      | sink => simp [PairedStrategyMemory.exactBlindView] at hview
      | processTwo rightEntry rightMinimum =>
          simp [PairedStrategyMemory.exactBlindView] at hview
      | processOne rightEntry rightMinimum =>
          simp only [PairedStrategyMemory.exactBlindView,
            PairedExactBlindView.processOne.injEq] at hview
          simp only [PairedStrategyMemory.blindRoundTable,
            PairedBlindRoundTable.processOne.injEq]
          rw [procOne_lambda_blind_eq_of_exactView_eq strategy leftEntry
            rightEntry hview]
  | processTwo leftEntry leftMinimum =>
      cases right with
      | sink => simp [PairedStrategyMemory.exactBlindView] at hview
      | processOne rightEntry rightMinimum =>
          simp [PairedStrategyMemory.exactBlindView] at hview
      | processTwo rightEntry rightMinimum =>
          simp only [PairedStrategyMemory.exactBlindView,
            PairedExactBlindView.processTwo.injEq] at hview
          simp only [PairedStrategyMemory.blindRoundTable,
            PairedBlindRoundTable.processTwo.injEq]
          rw [procTwo_lambda_blind_eq_of_exactView_eq strategy leftEntry
            rightEntry hview]

/-- Tree-level form: arbitrary nodes of the raw paired strategy tree that
carry the same exact blind view have identical finite blind action tables at
every common interior own-input word. -/
theorem atNode_blindRoundTable_eq_of_exactBlindView_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (initial : PairedStrategyMemory A strategy)
    (left right : TreeNode
      (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)))
    (hview :
      (PairedStrategyMemory.atNode (A := A) initial left).exactBlindView A =
        (PairedStrategyMemory.atNode (A := A) initial right).exactBlindView A)
    (wordOne : List In₁) (wordTwo : List In₂) :
    (PairedStrategyMemory.atNode (A := A) initial left).blindRoundTable A
        wordOne wordTwo =
      (PairedStrategyMemory.atNode (A := A) initial right).blindRoundTable A
        wordOne wordTwo :=
  blindRoundTable_eq_of_exactBlindView_eq A _ _ hview rfl rfl

/-- One semantic witness carrying global epoch acceptance and exact-view
round consistency simultaneously, before either component is rationalized.
The run state is the existing finite profiled paired-entry state; exact views
occur only in the consistency law on raw nodes. -/
structure PairedExactViewProfiledTreeWitness
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : PairedStrategyMemory A strategy) where
  accepting :
    (pairedProfiledEntryRunAutomaton A
      (initial.toProfiledTreeState (A := A))).IsAcceptingRun
        InputFreeRunParityTreeAutomaton.uniqueTree
        (initial.profiledRun (A := A))
  blindRoundConsistent :
    ∀ (left right : TreeNode
        (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)))
      (wordOne : List In₁) (wordTwo : List In₂),
      (PairedStrategyMemory.atNode (A := A) initial left).exactBlindView A =
          (PairedStrategyMemory.atNode (A := A) initial right).exactBlindView A →
        (PairedStrategyMemory.atNode (A := A) initial left).blindRoundTable A
            wordOne wordTwo =
          (PairedStrategyMemory.atNode (A := A) initial right).blindRoundTable A
            wordOne wordTwo

/-- Fail-fast semantic theorem for the exact-view route.  A raw winning
distributed strategy supplies one object in which global epoch parity and
the finite node-pair consistency test already hold together. -/
theorem exactViewProfiledTreeWitness_of_winning
    [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : PairedStrategyMemory A strategy) :
    PairedExactViewProfiledTreeWitness A strategy initial := by
  refine {
    accepting := PairedStrategyMemory.profiledIsAcceptingRun (A := A) initial
      (initial.foreverAccepts_of_winning (A := A) hwin)
      (PairedStrategyMemory.switchingAccepts_of_winning hwin initial)
    blindRoundConsistent := ?_ }
  intro left right wordOne wordTwo hview
  exact atNode_blindRoundTable_eq_of_exactBlindView_eq A initial left right
    hview wordOne wordTwo

end


end DetParityAutomaton

end DistributedSynthesis
