/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefViews
import Mathlib.Data.Fintype.Prod

/-! # Distributed strategies and execution

In each synchronous round the environment chooses two private inputs and one
of the three communication graphs. Each process receives its own input and,
when the corresponding edge is present, the other process's previous full
view and current input. It then chooses an output using its updated local view.

A strategy is an arbitrary function on local views, with no restriction on
memory or computation. Realizability means that one fixed pair of strategies
satisfies the specification for every infinite environment sequence. A graph
promise can be expressed by an implication in the specification, or by the
restricted quantifier in `GraphAdversaries.Realizable`.

For the finite-game certificate API, import
`DistributedSynthesis.Library.Distributed.ParitySpecification` separately.
-/

namespace DistributedSynthesis

universe u v x y a b

/-- An environment move consists of both current inputs and the current graph. -/
structure EnvironmentRound (In₁ : Type u) (In₂ : Type v) where
  inputOne : In₁
  inputTwo : In₂
  graph : Graph

namespace EnvironmentRound

def toProd {In₁ : Type u} {In₂ : Type v}
    (round : EnvironmentRound In₁ In₂) : In₁ × In₂ × Graph :=
  (round.inputOne, round.inputTwo, round.graph)

def ofProd {In₁ : Type u} {In₂ : Type v}
    (round : In₁ × In₂ × Graph) : EnvironmentRound In₁ In₂ :=
  {
    inputOne := round.1
    inputTwo := round.2.1
    graph := round.2.2
  }

def equivProd {In₁ : Type u} {In₂ : Type v} :
    EnvironmentRound In₁ In₂ ≃ In₁ × In₂ × Graph where
  toFun := toProd
  invFun := ofProd
  left_inv := by
    intro round
    cases round
    rfl
  right_inv := by
    intro round
    rcases round with ⟨inputOne, inputTwo, graph⟩
    rfl

end EnvironmentRound

instance {In₁ : Type u} {In₂ : Type v} [Fintype In₁] [Fintype In₂] :
    Fintype (EnvironmentRound In₁ In₂) :=
  Fintype.ofEquiv (In₁ × In₂ × Graph) EnvironmentRound.equivProd.symm

/-- An infinite environment sequence. -/
abbrev EnvironmentSequence (In₁ : Type u) (In₂ : Type v) := Nat -> EnvironmentRound In₁ In₂

/-- A deterministic strategy for process one: its output depends on its entire
local view after the current round's input and reception. -/
abbrev StrategyOne (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) :=
  View In₁ In₂ Proc.one -> Out₁

/-- A deterministic strategy for process two, with the same reception-before-output
timing and unrestricted perfect recall. -/
abbrev StrategyTwo (In₁ : Type u) (In₂ : Type v) (Out₂ : Type y) :=
  View In₁ In₂ Proc.two -> Out₂

/-- Two local strategies chosen before the environment sequence. Each component
sees only its own view; equal local views must produce equal local outputs. -/
structure StrategyPair (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y) where
  one : StrategyOne In₁ In₂ Out₁
  two : StrategyTwo In₁ In₂ Out₂

/-- Update the two local views using only the current environment move. -/
def advanceViewsWithEnvironment
    {In₁ : Type u} {In₂ : Type v}
    (views : View In₁ In₂ Proc.one × View In₁ In₂ Proc.two)
    (env : EnvironmentRound In₁ In₂) :
    View In₁ In₂ Proc.one × View In₁ In₂ Proc.two :=
  let v₁ := views.1
  let v₂ := views.2
  match env.graph with
    | .left =>
      ( .recv v₁ (.inl env.inputOne) v₂ (.inr env.inputTwo)
      , .noRecv v₂ (.inr env.inputTwo)
      )
    | .right =>
      ( .noRecv v₁ (.inl env.inputOne)
      , .recv v₂ (.inr env.inputTwo) v₁ (.inl env.inputOne)
      )
    | .both =>
      ( .recv v₁ (.inl env.inputOne) v₂ (.inr env.inputTwo)
      , .recv v₂ (.inr env.inputTwo) v₁ (.inl env.inputOne)
      )

/-- The current view after applying one environment move to a finite history. -/
def nextView
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentRound In₁ In₂) :
    View In₁ In₂ p :=
  match p with
  | .one => (advanceViewsWithEnvironment (viewPair h) env).1
  | .two => (advanceViewsWithEnvironment (viewPair h) env).2

/-- The pair of next local views determines the whole current environment move. -/
theorem environmentRound_eq_of_nextView_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {h h' : History In₁ In₂ Graph Out₁ Out₂}
    {env env' : EnvironmentRound In₁ In₂}
    (hone :
      nextView Proc.one h env =
        nextView Proc.one h' env')
    (htwo :
      nextView Proc.two h env =
        nextView Proc.two h' env') :
    env = env' := by
  cases env with
  | mk inputOne inputTwo graph =>
      cases env' with
      | mk inputOne' inputTwo' graph' =>
          cases graph <;> cases graph' <;>
            simp [nextView, advanceViewsWithEnvironment] at hone htwo ⊢ <;>
              tauto

/--
The non-fringe payload plus current receipt tags of the two next local views
determine the whole current environment move.
-/
theorem environmentRound_eq_of_nextView_nonFringe_receiptTag_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {h h' : History In₁ In₂ Graph Out₁ Out₂}
    {env env' : EnvironmentRound In₁ In₂}
    (honeNonFringe :
      (nextView Proc.one h env).nonFringe =
        (nextView Proc.one h' env').nonFringe)
    (honeReceipt :
      (nextView Proc.one h env).receiptTag =
        (nextView Proc.one h' env').receiptTag)
    (htwoNonFringe :
      (nextView Proc.two h env).nonFringe =
        (nextView Proc.two h' env').nonFringe)
    (htwoReceipt :
      (nextView Proc.two h env).receiptTag =
        (nextView Proc.two h' env').receiptTag) :
    env = env' := by
  apply environmentRound_eq_of_nextView_eq
  · calc
      nextView Proc.one h env
          = (nextView Proc.one h env).nonFringe.withReceiptTag
              (nextView Proc.one h env).receiptTag := by
              exact (View.withReceiptTag_nonFringe_receiptTag
                (nextView Proc.one h env)).symm
      _ = (nextView Proc.one h' env').nonFringe.withReceiptTag
              (nextView Proc.one h' env').receiptTag := by
              rw [honeNonFringe, honeReceipt]
      _ = nextView Proc.one h' env' := by
              exact View.withReceiptTag_nonFringe_receiptTag
                (nextView Proc.one h' env')
  · calc
      nextView Proc.two h env
          = (nextView Proc.two h env).nonFringe.withReceiptTag
              (nextView Proc.two h env).receiptTag := by
              exact (View.withReceiptTag_nonFringe_receiptTag
                (nextView Proc.two h env)).symm
      _ = (nextView Proc.two h' env').nonFringe.withReceiptTag
              (nextView Proc.two h' env').receiptTag := by
              rw [htwoNonFringe, htwoReceipt]
      _ = nextView Proc.two h' env' := by
              exact View.withReceiptTag_nonFringe_receiptTag
                (nextView Proc.two h' env')

/-- Build the next execution round from the current finite history and environment move. -/
def nextRound
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentRound In₁ In₂) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  {
    inputOne := env.inputOne
    inputTwo := env.inputTwo
    graph := env.graph
    outputOne := σ.one (nextView Proc.one h env)
    outputTwo := σ.two (nextView Proc.two h env)
  }

@[simp]
theorem nextRound_outputOne
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentRound In₁ In₂) :
    (nextRound σ h env).outputOne = σ.one (nextView Proc.one h env) :=
  rfl

@[simp]
theorem nextRound_outputTwo
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentRound In₁ In₂) :
    (nextRound σ h env).outputTwo = σ.two (nextView Proc.two h env) :=
  rfl

/--
For a fixed strategy, the two next local views determine the whole generated
round, including the strategy-chosen outputs.
-/
theorem nextRound_eq_of_nextView_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h h' : History In₁ In₂ Graph Out₁ Out₂}
    {env env' : EnvironmentRound In₁ In₂}
    (hone :
      nextView Proc.one h env =
        nextView Proc.one h' env')
    (htwo :
      nextView Proc.two h env =
        nextView Proc.two h' env') :
    nextRound σ h env = nextRound σ h' env' := by
  have henv : env = env' :=
    environmentRound_eq_of_nextView_eq hone htwo
  subst env'
  simp [nextRound, hone, htwo]

@[simp]
theorem currentView_append_nextRound
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentRound In₁ In₂) :
    currentView p (History.append h (nextRound σ h env)) =
      nextView p h env := by
  cases p <;> cases hGraph : env.graph <;>
    simp [currentView, nextView, nextRound, advanceViews,
      advanceViewsWithEnvironment, hGraph]

/-- The first `n` completed rounds under the fixed strategies and environment.
The prefix at depth zero is empty; round `n` extends the prefix at depth `n`
using the environment move at index `n`. -/
def executionPrefix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) : Nat -> History In₁ In₂ Graph Out₁ Out₂
  | 0 => []
  | n + 1 =>
      History.append (executionPrefix σ env n) (nextRound σ (executionPrefix σ env n) (env n))

@[simp]
theorem executionPrefix_zero
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    executionPrefix σ env 0 = [] := rfl

@[simp]
theorem executionPrefix_succ
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (n : Nat) :
    executionPrefix σ env (n + 1) =
      History.append
        (executionPrefix σ env n)
        (nextRound σ (executionPrefix σ env n) (env n)) := rfl

/--
An execution prefix depends only on the environment moves before its length.
-/
theorem executionPrefix_congr_of_env_eq_lt
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {env env' : EnvironmentSequence In₁ In₂}
    {n : Nat}
    (henv : ∀ k : Nat, k < n -> env k = env' k) :
    executionPrefix σ env n = executionPrefix σ env' n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have hprefix :
          executionPrefix σ env n = executionPrefix σ env' n := by
        exact ih (fun k hk => henv k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      have hround : env n = env' n := henv n (Nat.lt_succ_self n)
      simp [executionPrefix_succ, hprefix, hround]

@[simp]
theorem currentView_executionPrefix_succ
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (n : Nat) :
    currentView p (executionPrefix σ env (n + 1)) =
      nextView p (executionPrefix σ env n) (env n) := by
  simp [executionPrefix_succ]

@[simp]
theorem executionPrefix_length
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (n : Nat) :
    History.length (executionPrefix σ env n) = n := by
  induction n with
  | zero => simp [executionPrefix, History.length]
  | succ n ih =>
      simp only [executionPrefix_succ, History.length_append, Nat.add_right_cancel_iff]
      exact ih

/--
The finite execution prefix generated from a finite list of environment moves.
This is the finite analogue of `executionPrefix` and avoids choosing an
arbitrary infinite tail.
-/
def executionPrefixFromList
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (envs : List (EnvironmentRound In₁ In₂)) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  envs.foldl (fun h env => History.append h (nextRound σ h env)) []

@[simp]
theorem executionPrefixFromList_nil
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂) :
    executionPrefixFromList σ ([] : List (EnvironmentRound In₁ In₂)) = [] :=
  rfl

@[simp]
theorem executionPrefixFromList_snoc
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (envs : List (EnvironmentRound In₁ In₂))
    (env : EnvironmentRound In₁ In₂) :
    executionPrefixFromList σ (envs ++ [env]) =
      History.append (executionPrefixFromList σ envs)
        (nextRound σ (executionPrefixFromList σ envs) env) := by
  simp [executionPrefixFromList, List.foldl_append]

@[simp]
theorem executionPrefixFromList_length
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (envs : List (EnvironmentRound In₁ In₂)) :
    History.length (executionPrefixFromList σ envs) = envs.length := by
  induction envs using List.reverseRecOn with
  | nil =>
      simp [History.length]
  | append_singleton envs env ih =>
      simp [History.length_append, ih]

/--
Finite histories generated by repeatedly following a fixed strategy against
some finite prefix of environment moves.
-/
inductive StrategyGeneratedPrefix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂) :
    History In₁ In₂ Graph Out₁ Out₂ -> Prop where
  | empty :
      StrategyGeneratedPrefix σ []
  | append
      {h : History In₁ In₂ Graph Out₁ Out₂}
      (hhistory : StrategyGeneratedPrefix σ h)
      (env : EnvironmentRound In₁ In₂) :
      StrategyGeneratedPrefix σ
        (History.append h (nextRound σ h env))

/-- Every concrete `executionPrefix` is a generated prefix. -/
theorem strategyGeneratedPrefix_executionPrefix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (n : Nat) :
    StrategyGeneratedPrefix σ (executionPrefix σ env n) := by
  induction n with
  | zero =>
      exact StrategyGeneratedPrefix.empty
  | succ n ih =>
      simpa [executionPrefix_succ] using
        StrategyGeneratedPrefix.append ih (env n)

/-- Every finite-list execution prefix is a generated prefix. -/
theorem strategyGeneratedPrefix_executionPrefixFromList
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (envs : List (EnvironmentRound In₁ In₂)) :
    StrategyGeneratedPrefix σ (executionPrefixFromList σ envs) := by
  induction envs using List.reverseRecOn with
  | nil =>
      exact StrategyGeneratedPrefix.empty
  | append_singleton envs env ih =>
      simpa using StrategyGeneratedPrefix.append ih env

/--
Every inductively generated finite prefix is represented by a finite list of
environment moves.
-/
theorem strategyGeneratedPrefix_exists_executionPrefixFromList
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hhistory : StrategyGeneratedPrefix σ h) :
    ∃ envs : List (EnvironmentRound In₁ In₂),
      h = executionPrefixFromList σ envs := by
  induction hhistory with
  | empty =>
      exact ⟨[], rfl⟩
  | append hhistory env ih =>
      rcases ih with ⟨envs, hrepr⟩
      refine ⟨envs ++ [env], ?_⟩
      simp [hrepr]

/-- Finite-list execution prefixes are exactly the strategy-generated prefixes. -/
theorem strategyGeneratedPrefix_iff_exists_executionPrefixFromList
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    StrategyGeneratedPrefix σ h ↔
      ∃ envs : List (EnvironmentRound In₁ In₂),
        h = executionPrefixFromList σ envs := by
  constructor
  · exact strategyGeneratedPrefix_exists_executionPrefixFromList σ
  · intro hrepr
    rcases hrepr with ⟨envs, rfl⟩
    exact strategyGeneratedPrefix_executionPrefixFromList σ envs

/--
Finite-list and infinite-sequence execution prefixes agree when the infinite
environment sequence has the finite list as its prefix.
-/
theorem executionPrefixFromList_eq_executionPrefix_of_getElem_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (envs : List (EnvironmentRound In₁ In₂))
    (env : EnvironmentSequence In₁ In₂)
    (henv :
      ∀ k : Nat, (hk : k < envs.length) ->
        env k = envs.get ⟨k, hk⟩) :
    executionPrefixFromList σ envs =
      executionPrefix σ env envs.length := by
  induction envs using List.reverseRecOn with
  | nil =>
      rfl
  | append_singleton envs envLast ih =>
      have hprefix :
          executionPrefixFromList σ envs =
            executionPrefix σ env envs.length := by
        apply ih
        intro k hk
        have hkAppend : k < (envs ++ [envLast]).length := by
          simpa [List.length_append] using Nat.lt_succ_of_lt hk
        have henvk := henv k hkAppend
        simpa [List.getElem_append, hk] using henvk
      have hlast :
          env envs.length = envLast := by
        have hkAppend :
            envs.length < (envs ++ [envLast]).length := by
          simp
        have henvLast := henv envs.length hkAppend
        simpa using henvLast
      calc
        executionPrefixFromList σ (envs ++ [envLast])
            = History.append (executionPrefixFromList σ envs)
                (nextRound σ (executionPrefixFromList σ envs) envLast) := by
                simp
        _ = executionPrefix σ env (envs.length + 1) := by
                simp [executionPrefix_succ, hprefix, hlast]
        _ = executionPrefix σ env (envs ++ [envLast]).length := by
                simp [List.length_append]

/--
Every inductively generated finite prefix can be represented as an
`executionPrefix` for some infinite environment sequence.
-/
theorem strategyGeneratedPrefix_exists_executionPrefix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    [Inhabited In₁] [Inhabited In₂]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hhistory : StrategyGeneratedPrefix σ h) :
    ∃ env : EnvironmentSequence In₁ In₂,
      ∃ n : Nat,
        h = executionPrefix σ env n := by
  induction hhistory with
  | empty =>
      let env : EnvironmentSequence In₁ In₂ :=
        fun _ => { inputOne := default, inputTwo := default, graph := .both }
      exact ⟨env, 0, rfl⟩
  | append hhistory envNext ih =>
      rcases ih with ⟨env, n, hrepr⟩
      let env' : EnvironmentSequence In₁ In₂ :=
        fun k => if k = n then envNext else env k
      refine ⟨env', n + 1, ?_⟩
      have hprefix :
          executionPrefix σ env n = executionPrefix σ env' n := by
        apply executionPrefix_congr_of_env_eq_lt
        intro k hk
        simp [env', Nat.ne_of_lt hk]
      have henvAt : env' n = envNext := by
        simp [env']
      calc
        History.append _ (nextRound σ _ envNext)
            = History.append (executionPrefix σ env n)
                (nextRound σ (executionPrefix σ env n) envNext) := by
                rw [hrepr]
        _ = executionPrefix σ env' (n + 1) := by
                simp [executionPrefix_succ, hprefix, henvAt]

/--
Pointwise strategy-generated histories supply the existential generated-history
form used by higher-level proof skeletons.
-/
theorem generatedHistory_of_strategyGeneratedPrefix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    [Inhabited In₁] [Inhabited In₂]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hgenerated :
      ∀ h : History In₁ In₂ Graph Out₁ Out₂,
        StrategyGeneratedPrefix σ h) :
    ∀ h : History In₁ In₂ Graph Out₁ Out₂,
      ∃ env : EnvironmentSequence In₁ In₂,
        ∃ n : Nat,
          h = executionPrefix σ env n := by
  intro h
  exact strategyGeneratedPrefix_exists_executionPrefix σ (hgenerated h)

/-- The infinite execution generated by a strategy pair against an environment sequence. -/
def execution
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    Nat -> RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  fun n => by
    have hlen : List.length (executionPrefix σ env (n + 1)) = n + 1 := by
      simpa [History.length] using executionPrefix_length σ env (n + 1)
    exact
      (executionPrefix σ env (n + 1)).get ⟨n, by rw [hlen]; exact Nat.lt_succ_self n⟩

@[simp]
theorem execution_apply
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (n : Nat) :
    execution σ env n =
      nextRound σ (executionPrefix σ env n) (env n) := by
  have hprefix :
      (executionPrefix σ env n).length = n := by
    simpa [History.length] using executionPrefix_length σ env n
  simp [execution, executionPrefix_succ, History.append]
  have hle : (executionPrefix σ env n).length ≤ n := by
    rw [hprefix]
  rw [List.getElem_append_right hle]
  simp

/-- An abstract specification on infinite executions. -/
abbrev Specification (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y) :=
  (Nat -> RoundRecord In₁ In₂ Graph Out₁ Out₂) -> Prop

/-- A strategy pair realizes a specification if every environment execution satisfies it. -/
def Realizes
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (φ : Specification In₁ In₂ Out₁ Out₂)
    (σ : StrategyPair In₁ In₂ Out₁ Out₂) : Prop :=
  ∀ env : EnvironmentSequence In₁ In₂, φ (execution σ env)

/-- A specification is realizable if there exist two local strategies such
that every infinite environment sequence produces an execution satisfying it.
The existential choice of strategies precedes the universal choice of inputs
and graphs. -/
def SynthesisProblem
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (φ : Specification In₁ In₂ Out₁ Out₂) : Prop :=
  ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂, Realizes φ σ

end DistributedSynthesis
