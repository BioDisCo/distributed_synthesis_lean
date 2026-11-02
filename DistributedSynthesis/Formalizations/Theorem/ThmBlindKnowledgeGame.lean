/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmBundleDeterminization
import DistributedSynthesis.Formalizations.Theorem.ThmEpochArenaAnchor
import DistributedSynthesis.Formalizations.Proposition.PropEpochhierarchical

/-!
# The blind knowledge game and its summary automaton

This file formalizes the knowledge-arena step of paper `prop:starcomplete` --
the Berwanger--Mathew--van den Bogaard Theorem 10 instance for the theta-bar
dynamic hierarchy. It uses the
hierarchy facts of `prop:dynhier` (the model's dynamic hierarchy) and the
one-bit receiver ambiguity of `thm:onebitfringe`, and builds on the bundle
determinization of `ThmBundleDeterminization.lean`.

Design choices, recorded explicitly:

* **Role identity.**  The designated blind observer is process one throughout;
  process two is the designated informed side.  A blind observation letter is
  process one's per-round view increment of Definition `def:views`: a `noRecv`
  tag with its own input on rounds where it does not receive (graph `right`,
  containment order `firstInSecond` in the sense of
  `PropEpochhierarchical.graphContainmentOrder`), and a `recv` tag with both
  inputs on rounds where it receives (graphs `left` and `both`).  The one-bit
  fringe of `thm:onebitfringe` is exactly what a `recv` letter does *not*
  reveal: whether the round graph was `left` or `both`.  Role switches across
  blocks are handled on the summary side: the informed copy of the tracked
  position resynchronizes on every round on which process two receives (the
  reset reading of the `bidirectionalBoundary_epochReset` and handoff clauses
  of `PropEpochhierarchical.lean`), and holds otherwise.

* **Letters carry the committed move.**  A full knowledge letter is the pair
  of a blind observation and the coalition move committed for that round (the
  blind output together with the contingent informed table over the finite
  informed annotation).  The bundle automaton must read the committed move:
  quantifying over resolutions with unconstrained outputs would force the
  universal-run objective to range over plays no strategy emits, which is
  sound but provably incomplete for the belief lifting.

* **Hidden resolutions.**  What the letters do not determine is exactly the
  informed side's private input on `noRecv` rounds and the one fringe bit on
  `recv` rounds; a `BlindResolution` supplies both.  Runs of the thread system
  over a letter word are precisely the hidden resolutions of the blind stream.

* **The informed annotation is parametric.**  The annotation automaton `N`
  (finite state, reading process two's view increments) is a parameter; the
  knowledge thread space, the bundle automaton, the knowledge game, and the
  summary automaton are all uniform in it.  Brick 4 instantiates `N`.

* **Consistency.**  Thread steps are total functions and letters carry no
  claim refutable against a single thread, so a blind observation is
  consistent with a belief exactly when the belief is nonempty; this is
  decidable, and inconsistent observations move to an absorbing position of
  even priority `0`, an immediate loss for the environment (Odd).

The constructions: the finite thread system over knowledge letters
(`blindThreadSystem`), the bundle parity automaton `blindBundleDPA` with its
universal acceptance characterization, the knowledge game `blindKnowledgeGame`
as a `CountableParityGame` (Even commits moves at staging nodes, Odd resolves
consistent blind observations), the blind-computable position fold, and the
summary automaton `knowledgeSummaryAutomaton` (the `M*` of the route-delta
design) whose process-one summaries carry the tracked game position per move
selector and whose process-two summaries add the informed annotation.
-/

namespace DistributedSynthesis

universe u v w a

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type w} {Out₂ : Type a}

/--
A blind observation letter: the designated blind observer's (process one's)
per-round view increment.  `noRecv` records its own input on a round on which
it does not receive; `recv` records its own input together with the received
payload input of the other process.
-/
inductive BlindObservation (In₁ : Type u) (In₂ : Type v) where
  | noRecv (inputOne : In₁)
  | recv (inputOne : In₁) (inputTwo : In₂)

namespace BlindObservation

/-- Blind observations are a sum of the `noRecv` and `recv` payloads. -/
def equivSum : BlindObservation In₁ In₂ ≃ (In₁ ⊕ In₁ × In₂) where
  toFun o :=
    match o with
    | .noRecv inputOne => Sum.inl inputOne
    | .recv inputOne inputTwo => Sum.inr (inputOne, inputTwo)
  invFun s :=
    match s with
    | Sum.inl inputOne => .noRecv inputOne
    | Sum.inr (inputOne, inputTwo) => .recv inputOne inputTwo
  left_inv := by
    intro o
    cases o <;> rfl
  right_inv := by
    intro s
    rcases s with _ | ⟨_, _⟩ <;> rfl

instance [Fintype In₁] [Fintype In₂] : Fintype (BlindObservation In₁ In₂) :=
  Fintype.ofEquiv _ equivSum.symm

instance [Inhabited In₁] : Inhabited (BlindObservation In₁ In₂) :=
  ⟨.noRecv default⟩

end BlindObservation

/-- The blind observation of a real environment round: the designated blind
observer receives exactly on `left` and `both` rounds. -/
def roundObservation (envRound : EnvironmentRound In₁ In₂) :
    BlindObservation In₁ In₂ :=
  match envRound.graph with
  | .right => .noRecv envRound.inputOne
  | .left => .recv envRound.inputOne envRound.inputTwo
  | .both => .recv envRound.inputOne envRound.inputTwo

/-- The blind observer receives exactly when its non-fringe view is not below
the other side's, in the containment order of `PropEpochhierarchical`. -/
theorem roundObservation_recv_iff (envRound : EnvironmentRound In₁ In₂) :
    (∃ inputOne inputTwo,
        roundObservation envRound = .recv inputOne inputTwo) ↔
      graphContainmentOrder envRound.graph ≠
        NonFringeContainmentOrder.firstInSecond := by
  cases hGraph : envRound.graph <;>
    simp [roundObservation, graphContainmentOrder, hGraph]

/--
A hidden resolution of one blind letter: the informed side's private input
(read on `noRecv` rounds, where the letter does not carry it) and the one
fringe bit of `thm:onebitfringe` (read on `recv` rounds, where the letter does
not distinguish the graphs `left` and `both`).
-/
abbrev BlindResolution (In₂ : Type v) := In₂ × Bool

/-- The hidden resolution realized by a real environment round. -/
def roundResolution (envRound : EnvironmentRound In₁ In₂) :
    BlindResolution In₂ :=
  (envRound.inputTwo,
    match envRound.graph with
    | .both => true
    | _ => false)

/-- The environment round reconstructed from a blind observation and a hidden
resolution. -/
def letterEnvironment (o : BlindObservation In₁ In₂)
    (r : BlindResolution In₂) : EnvironmentRound In₁ In₂ :=
  match o with
  | .noRecv inputOne =>
      { inputOne := inputOne, inputTwo := r.1, graph := .right }
  | .recv inputOne inputTwo =>
      { inputOne := inputOne
        inputTwo := inputTwo
        graph := if r.2 then .both else .left }

/-- The observation and resolution of a real round reconstruct that round. -/
theorem letterEnvironment_roundObservation
    (envRound : EnvironmentRound In₁ In₂) :
    letterEnvironment (roundObservation envRound)
        (roundResolution envRound) = envRound := by
  cases envRound with
  | mk inputOne inputTwo graph =>
      cases graph <;> rfl

/--
A finite automaton on the designated informed side's (process two's) view
increments, supplying the private annotation the contingent informed tables
read.  It is a parameter of the knowledge-arena construction.
-/
structure InformedAnnotationAutomaton (In₁ : Type u) (In₂ : Type v) where
  Ann : Type (max u v w a)
  annFinite : Fintype Ann
  init : Ann
  stepSend : Ann -> In₂ -> Ann
  stepRecv : Ann -> In₂ -> In₁ -> Ann

attribute [instance] InformedAnnotationAutomaton.annFinite

namespace InformedAnnotationAutomaton

variable (N : InformedAnnotationAutomaton.{u, v, w, a} In₁ In₂)

/-- One-round advance of the informed annotation: process two receives on
`right` and `both` rounds and sends on `left` rounds. -/
def advanceRound (ann : N.Ann) (envRound : EnvironmentRound In₁ In₂) :
    N.Ann :=
  match envRound.graph with
  | .left => N.stepSend ann envRound.inputTwo
  | .right => N.stepRecv ann envRound.inputTwo envRound.inputOne
  | .both => N.stepRecv ann envRound.inputTwo envRound.inputOne

/-- The annotation resynchronizes (receives) exactly when the round's
containment order is not `secondInFirst`; this is the reset reading of the
epoch handoff clauses of `PropEpochhierarchical`. -/
theorem advanceRound_recv_iff (envRound : EnvironmentRound In₁ In₂) :
    (envRound.graph = .right ∨ envRound.graph = .both) ↔
      graphContainmentOrder envRound.graph ≠
        NonFringeContainmentOrder.secondInFirst := by
  cases envRound.graph <;> simp [graphContainmentOrder]

end InformedAnnotationAutomaton

section ThreadSystem

variable
  (A :
    DetParityAutomaton.{max u v w a, max u v w a}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (N : InformedAnnotationAutomaton.{u, v, w, a} In₁ In₂)

/-- A coalition move committed for one round: the blind output and the
contingent informed table over the finite informed annotation. -/
abbrev KnowledgeMove (Out₁ : Type w) (Out₂ : Type a)
    (N : InformedAnnotationAutomaton.{u, v, w, a} In₁ In₂) :=
  Out₁ × (N.Ann -> Out₂)

/-- A full knowledge letter: the blind observation together with the
committed coalition move. -/
abbrev KnowledgeLetter (Out₁ : Type w) (Out₂ : Type a)
    (N : InformedAnnotationAutomaton.{u, v, w, a} In₁ In₂) :=
  BlindObservation In₁ In₂ × KnowledgeMove Out₁ Out₂ N

/-- A knowledge thread: the objective-automaton state together with the
informed annotation of the hidden resolution it tracks. -/
abbrev KnowledgeThread := A.State × N.Ann

/-- One thread step: reconstruct the round from letter and resolution,
advance the annotation, resolve the informed output through the committed
table at the advanced annotation, and step the objective automaton on the
resulting full round record. -/
def knowledgeThreadStep (thread : KnowledgeThread A N)
    (letter : KnowledgeLetter Out₁ Out₂ N) (r : BlindResolution In₂) :
    KnowledgeThread A N :=
  let envRound := letterEnvironment letter.1 r
  let ann := N.advanceRound thread.2 envRound
  (A.step thread.1
      { inputOne := envRound.inputOne
        inputTwo := envRound.inputTwo
        graph := envRound.graph
        outputOne := letter.2.1
        outputTwo := letter.2.2 ann },
    ann)

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

noncomputable instance :
    Fintype (KnowledgeMove Out₁ Out₂ N) :=
  letI : DecidableEq N.Ann := Classical.decEq _
  inferInstance

/--
**The blind-letter thread system** (instantiation of the
functor): states are knowledge threads, letters are knowledge letters, and
the hidden input is a blind resolution.  Its runs over a letter word are
exactly the hidden resolutions of the blind stream, and the priority is the
objective automaton's priority of the tracked state.
-/
def blindThreadSystem :
    FiniteThreadSystem.{max u v w a, max u v w a, v}
      (KnowledgeLetter Out₁ Out₂ N) where
  State := KnowledgeThread A N
  stateFinite := inferInstance
  initial := (A.initial, N.init)
  Resolution := BlindResolution In₂
  step := knowledgeThreadStep A N
  priority thread := A.priority thread.1

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Runs of the blind thread system are exactly the hidden resolutions of
the blind stream: evolutions from the initial thread in which every step is
resolved by some private input and fringe bit. -/
theorem blindThreadSystem_isRun_iff
    (word : OmegaWord (KnowledgeLetter Out₁ Out₂ N))
    (threads : Nat -> KnowledgeThread A N) :
    (blindThreadSystem A N).IsRun word threads ↔
      threads 0 = (A.initial, N.init) ∧
        ∀ n : Nat, ∃ r : BlindResolution In₂,
          threads (n + 1) = knowledgeThreadStep A N (threads n) (word n) r :=
  Iff.rfl

/--
**The bundle parity automaton** `D` of the knowledge arena: the universal-run
determinization of the blind thread system.  It reads the joint stream of
blind observations and committed moves.
-/
noncomputable def blindBundleDPA :
    DetParityAutomaton.{max u v w a, max u v w a}
      (KnowledgeLetter Out₁ Out₂ N) :=
  (blindThreadSystem A N).universalRunDPA

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- **Acceptance characterization of the bundle automaton**: `D` accepts a
blind stream iff the objective run of every consistent hidden resolution
satisfies min-even parity. -/
theorem blindBundleDPA_accepts_iff
    (word : OmegaWord (KnowledgeLetter Out₁ Out₂ N)) :
    (blindBundleDPA A N).Accepts word ↔
      ∀ threads : Nat -> KnowledgeThread A N,
        (blindThreadSystem A N).IsRun word threads ->
          NatSeqMinEvenParity (fun n => A.priority (threads n).1) :=
  (blindThreadSystem A N).universalRunDPA_accepts_iff word

end ThreadSystem

section KnowledgeGame

variable
  (A :
    DetParityAutomaton.{max u v w a, max u v w a}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (N : InformedAnnotationAutomaton.{u, v, w, a} In₁ In₂)
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-- A belief of the blind observer: a finite set of knowledge threads. -/
abbrev KnowledgeBelief := Finset (KnowledgeThread A N)

/-- An Odd (environment) node of the knowledge game: the current belief and
the current bundle-automaton state. -/
abbrev KnowledgeResolveNode :=
  KnowledgeBelief A N × (blindBundleDPA A N).State

/-- An Even (coalition) staging node: a resolve node together with the blind
observation Odd has just revealed. -/
abbrev KnowledgeCommitNode :=
  KnowledgeResolveNode A N × BlindObservation In₁ In₂

/-- The initial knowledge thread. -/
def initialKnowledgeThread : KnowledgeThread A N := (A.initial, N.init)

/-- The initial resolve node: the singleton belief at the initial thread and
the initial bundle state. -/
noncomputable def initialResolveNode : KnowledgeResolveNode A N :=
  ({initialKnowledgeThread A N}, (blindBundleDPA A N).initial)

/--
Consistency of a blind observation with a belief.  Thread steps are total and
letters carry no claim refutable against a single thread, so an observation
is consistent exactly when the belief is nonempty; the parameter `o` is kept
so that refinements of the thread space can strengthen the test without
changing the game interface.
-/
def ObservationConsistent (belief : KnowledgeBelief A N)
    (_o : BlindObservation In₁ In₂) : Prop :=
  belief.Nonempty

/-- Consistency is decidable (the thread space is finite). -/
instance (belief : KnowledgeBelief A N) (o : BlindObservation In₁ In₂) :
    Decidable (ObservationConsistent A N belief o) :=
  inferInstanceAs (Decidable belief.Nonempty)

/-- The belief image of one knowledge letter: all thread successors under
every hidden resolution. -/
noncomputable def beliefStep (belief : KnowledgeBelief A N)
    (letter : KnowledgeLetter Out₁ Out₂ N) : KnowledgeBelief A N :=
  letI : DecidableEq (KnowledgeThread A N) := Classical.decEq _
  belief.biUnion fun thread =>
    Finset.univ.image fun r : BlindResolution In₂ =>
      knowledgeThreadStep A N thread letter r

omit [Fintype In₁] [Fintype Out₁] [Fintype Out₂] in
theorem mem_beliefStep
    {belief : KnowledgeBelief A N} {letter : KnowledgeLetter Out₁ Out₂ N}
    {thread' : KnowledgeThread A N} :
    thread' ∈ beliefStep A N belief letter ↔
      ∃ thread ∈ belief, ∃ r : BlindResolution In₂,
        thread' = knowledgeThreadStep A N thread letter r := by
  simp [beliefStep, eq_comm]

/-- One Even commitment resolves a staging node: subset image on the belief
and bundle step on the emitted knowledge letter. -/
noncomputable def knowledgeCommitStep (node : KnowledgeCommitNode A N)
    (move : KnowledgeMove Out₁ Out₂ N) : KnowledgeResolveNode A N :=
  (beliefStep A N node.1.1 (node.2, move),
    (blindBundleDPA A N).step node.1.2 (node.2, move))

/-- The blind-computable fold of the knowledge positions over a finite list
of emitted knowledge letters. -/
noncomputable def knowledgePositionFold
    (letters : List (KnowledgeLetter Out₁ Out₂ N)) :
    KnowledgeResolveNode A N :=
  letters.foldl
    (fun node letter =>
      (beliefStep A N node.1 letter, (blindBundleDPA A N).step node.2 letter))
    (initialResolveNode A N)

section
omit [Fintype In₁] [Fintype Out₁] [Fintype Out₂]

@[simp]
theorem knowledgePositionFold_nil :
    knowledgePositionFold A N ([] : List (KnowledgeLetter Out₁ Out₂ N)) =
      initialResolveNode A N :=
  rfl

theorem knowledgePositionFold_append
    (letters : List (KnowledgeLetter Out₁ Out₂ N))
    (letter : KnowledgeLetter Out₁ Out₂ N) :
    knowledgePositionFold A N (letters ++ [letter]) =
      (beliefStep A N (knowledgePositionFold A N letters).1 letter,
        (blindBundleDPA A N).step
          (knowledgePositionFold A N letters).2 letter) := by
  simp [knowledgePositionFold]

/-- **Knowledge positions are blind-computable folds** (definitional, stated
for the record): one Even commitment from a fold position is the fold of the
extended letter list. -/
theorem knowledgeCommitStep_positionFold
    (letters : List (KnowledgeLetter Out₁ Out₂ N))
    (o : BlindObservation In₁ In₂) (move : KnowledgeMove Out₁ Out₂ N) :
    knowledgeCommitStep A N (knowledgePositionFold A N letters, o) move =
      knowledgePositionFold A N (letters ++ [(o, move)]) := by
  rw [knowledgePositionFold_append]
  rfl

end

variable [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂]

/--
**The blind knowledge game** `G†`: Odd (the environment) owns the resolve
nodes and reveals a consistent blind observation; Even (the coalition) owns
the staging nodes and commits a knowledge move; inconsistent observations
move to an absorbing Even-winning position of priority `0`.  Priority is the
bundle automaton's priority of the tracked bundle state, so the parity
objective is bundle acceptance of the emitted letter stream.
-/
noncomputable def blindKnowledgeGame : CountableParityGame.{max u v w a} where
  Position :=
    KnowledgeResolveNode A N ⊕ (KnowledgeCommitNode A N ⊕ Unit)
  positionCountable := by
    haveI : Countable (KnowledgeResolveNode A N) := Finite.to_countable
    haveI : Countable (KnowledgeCommitNode A N) := Finite.to_countable
    exact inferInstance
  owner :=
    Sum.elim (fun _ => ParityPlayer.odd)
      (Sum.elim (fun _ => ParityPlayer.even) fun _ => ParityPlayer.odd)
  step p q :=
    match p, q with
    | Sum.inl node, Sum.inr (Sum.inl staging) =>
        staging.1 = node ∧ ObservationConsistent A N node.1 staging.2
    | Sum.inl node, Sum.inr (Sum.inr _) =>
        ∃ o : BlindObservation In₁ In₂,
          ¬ ObservationConsistent A N node.1 o
    | Sum.inr (Sum.inl staging), Sum.inl node' =>
        ∃ move : KnowledgeMove Out₁ Out₂ N,
          node' = knowledgeCommitStep A N staging move
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => True
    | _, _ => False
  step_total p := by
    rcases p with node | staging | u
    · by_cases h : ObservationConsistent A N node.1 (default)
      · exact ⟨Sum.inr (Sum.inl (node, default)), rfl, h⟩
      · exact ⟨Sum.inr (Sum.inr Unit.unit), default, h⟩
    · exact
        ⟨Sum.inl
            (knowledgeCommitStep A N staging (default, fun _ => default)),
          (default, fun _ => default), rfl⟩
    · exact ⟨Sum.inr (Sum.inr Unit.unit), trivial⟩
  priority :=
    Sum.elim (fun node => (blindBundleDPA A N).priority node.2)
      (Sum.elim
        (fun staging => (blindBundleDPA A N).priority staging.1.2)
        fun _ => 0)
  priority_finite := by
    apply
      (Set.Finite.insert 0
        (Set.finite_range (blindBundleDPA A N).priority)).subset
    rintro _ ⟨p, rfl⟩
    rcases p with node | staging | u
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨node.2, rfl⟩)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨staging.1.2, rfl⟩)
    · exact Set.mem_insert 0 _

/--
The **fixed-informed-table subgame**.  It has the same positions, Odd moves,
and priorities as `blindKnowledgeGame`, but at an Even staging node the
informed component of the committed move is definitionally the single table
`F`; Even chooses only the blind output.  Thus uniformity is enforced by the
arena rather than requested after unrestricted positional determinacy.
-/
noncomputable def fixedTableKnowledgeGame (F : N.Ann -> Out₂) :
    CountableParityGame.{max u v w a} where
  Position :=
    KnowledgeResolveNode A N ⊕ (KnowledgeCommitNode A N ⊕ Unit)
  positionCountable := by
    haveI : Countable (KnowledgeResolveNode A N) := Finite.to_countable
    haveI : Countable (KnowledgeCommitNode A N) := Finite.to_countable
    exact inferInstance
  owner :=
    Sum.elim (fun _ => ParityPlayer.odd)
      (Sum.elim (fun _ => ParityPlayer.even) fun _ => ParityPlayer.odd)
  step p q :=
    match p, q with
    | Sum.inl node, Sum.inr (Sum.inl staging) =>
        staging.1 = node ∧ ObservationConsistent A N node.1 staging.2
    | Sum.inl node, Sum.inr (Sum.inr _) =>
        ∃ o : BlindObservation In₁ In₂,
          ¬ ObservationConsistent A N node.1 o
    | Sum.inr (Sum.inl staging), Sum.inl node' =>
        ∃ outputOne : Out₁,
          node' = knowledgeCommitStep A N staging (outputOne, F)
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => True
    | _, _ => False
  step_total p := by
    rcases p with node | staging | u
    · by_cases h : ObservationConsistent A N node.1 (default)
      · exact ⟨Sum.inr (Sum.inl (node, default)), rfl, h⟩
      · exact ⟨Sum.inr (Sum.inr Unit.unit), default, h⟩
    · exact
        ⟨Sum.inl (knowledgeCommitStep A N staging (default, F)),
          default, rfl⟩
    · exact ⟨Sum.inr (Sum.inr Unit.unit), trivial⟩
  priority :=
    Sum.elim (fun node => (blindBundleDPA A N).priority node.2)
      (Sum.elim
        (fun staging => (blindBundleDPA A N).priority staging.1.2)
        fun _ => 0)
  priority_finite := by
    apply
      (Set.Finite.insert 0
        (Set.finite_range (blindBundleDPA A N).priority)).subset
    rintro _ ⟨p, rfl⟩
    rcases p with node | staging | u
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨node.2, rfl⟩)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨staging.1.2, rfl⟩)
    · exact Set.mem_insert 0 _

section
omit [Fintype Out₁] [Fintype Out₂]

@[simp]
theorem fixedTableKnowledgeGame_owner (F : N.Ann -> Out₂)
    (p : (fixedTableKnowledgeGame A N F).Position) :
    (fixedTableKnowledgeGame A N F).owner p =
      (blindKnowledgeGame A N).owner p :=
  rfl

@[simp]
theorem fixedTableKnowledgeGame_priority (F : N.Ann -> Out₂)
    (p : (fixedTableKnowledgeGame A N F).Position) :
    (fixedTableKnowledgeGame A N F).priority p =
      (blindKnowledgeGame A N).priority p :=
  rfl

/-- Every fixed-table move is an unrestricted knowledge-game move. -/
theorem fixedTableKnowledgeGame_step_mono (F : N.Ann -> Out₂)
    {p q : (fixedTableKnowledgeGame A N F).Position}
    (hstep : (fixedTableKnowledgeGame A N F).step p q) :
    (blindKnowledgeGame A N).step p q := by
  rcases p with node | staging | u <;>
    rcases q with node' | staging' | u' <;>
    simp only [fixedTableKnowledgeGame, blindKnowledgeGame] at hstep ⊢
  all_goals try exact hstep
  obtain ⟨outputOne, houtput⟩ := hstep
  exact ⟨(outputOne, F), houtput⟩

/-- At Odd-owned positions the fixed-table and unrestricted games have
identical moves. -/
theorem fixedTableKnowledgeGame_step_of_odd (F : N.Ann -> Out₂)
    {p q : (blindKnowledgeGame A N).Position}
    (howner : (blindKnowledgeGame A N).owner p = ParityPlayer.odd)
    (hstep : (blindKnowledgeGame A N).step p q) :
    (fixedTableKnowledgeGame A N F).step p q := by
  rcases p with node | staging | u <;>
    rcases q with node' | staging' | u' <;>
    simp only [blindKnowledgeGame, fixedTableKnowledgeGame] at howner hstep ⊢
  all_goals try exact hstep
  all_goals contradiction

end

/-- The initial position of the knowledge game. -/
noncomputable def blindKnowledgeGameInitial :
    (blindKnowledgeGame A N).Position :=
  Sum.inl (initialResolveNode A N)

section
omit [Fintype Out₁] [Fintype Out₂]

/-- Sanity: the knowledge game has a move from every position. -/
theorem blindKnowledgeGame_step_total
    (p : (blindKnowledgeGame A N).Position) :
    ∃ q : (blindKnowledgeGame A N).Position,
      (blindKnowledgeGame A N).step p q :=
  (blindKnowledgeGame A N).step_total p

/-- Sanity: the knowledge game uses finitely many priorities. -/
theorem blindKnowledgeGame_priority_finite :
    (Set.range (blindKnowledgeGame A N).priority).Finite :=
  (blindKnowledgeGame A N).priority_finite

/-- Legality forces an Even positional strategy to commit some knowledge
move at every staging node. -/
theorem exists_evenKnowledgeMove
    (τ :
      (blindKnowledgeGame A N).PositionalStrategy ParityPlayer.even)
    (staging : KnowledgeCommitNode A N) :
    ∃ move : KnowledgeMove Out₁ Out₂ N,
      τ.move (Sum.inr (Sum.inl staging)) =
        Sum.inl (knowledgeCommitStep A N staging move) := by
  have hleg := τ.legal (Sum.inr (Sum.inl staging)) rfl
  cases hmv : τ.move (Sum.inr (Sum.inl staging)) with
  | inl node' =>
      rw [hmv] at hleg
      obtain ⟨move, hmove⟩ :
          ∃ move : KnowledgeMove Out₁ Out₂ N,
            node' = knowledgeCommitStep A N staging move := by
        simpa [blindKnowledgeGame] using hleg
      exact ⟨move, congrArg Sum.inl hmove⟩
  | inr q =>
      rw [hmv] at hleg
      rcases q with staging' | u <;>
        exact absurd hleg (by simp [blindKnowledgeGame])

end

/-- The knowledge move an Even positional strategy commits at a staging
node. -/
noncomputable def evenKnowledgeMove
    (τ :
      (blindKnowledgeGame A N).PositionalStrategy ParityPlayer.even)
    (staging : KnowledgeCommitNode A N) : KnowledgeMove Out₁ Out₂ N :=
  (exists_evenKnowledgeMove A N τ staging).choose

omit [Fintype Out₁] [Fintype Out₂] in
theorem evenKnowledgeMove_spec
    (τ :
      (blindKnowledgeGame A N).PositionalStrategy ParityPlayer.even)
    (staging : KnowledgeCommitNode A N) :
    τ.move (Sum.inr (Sum.inl staging)) =
      Sum.inl
        (knowledgeCommitStep A N staging
          (evenKnowledgeMove A N τ staging)) :=
  (exists_evenKnowledgeMove A N τ staging).choose_spec

end KnowledgeGame

section SummaryAutomaton

variable
  (A :
    DetParityAutomaton.{max u v w a, max u v w a}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (N : InformedAnnotationAutomaton.{u, v, w, a} In₁ In₂)
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [Inhabited Out₁] [Inhabited Out₂]

/-- A move selector: one knowledge move per staging node.  The summary
automaton tracks the game position under every selector simultaneously, so
that its transition structure is uniform in the eventual winner. -/
abbrev KnowledgeSelector :=
  KnowledgeCommitNode A N -> KnowledgeMove Out₁ Out₂ N

/-- A tracked position: the current resolve node together with the last
committed move (whose blind output the readback table reads). -/
abbrev KnowledgeTrack :=
  KnowledgeResolveNode A N × KnowledgeMove Out₁ Out₂ N

/-- One tracked step under a selector: commit the selector's move at the
revealed observation. -/
noncomputable def knowledgeTrackStep (ζ : KnowledgeSelector A N)
    (track : KnowledgeTrack A N) (o : BlindObservation In₁ In₂) :
    KnowledgeTrack A N :=
  (knowledgeCommitStep A N (track.1, o) (ζ (track.1, o)),
    ζ (track.1, o))

/-- The initial tracked position (the initial move component is junk and is
never read: readback tables read post-step summaries only). -/
noncomputable def initialKnowledgeTrack : KnowledgeTrack A N :=
  (initialResolveNode A N, (default, fun _ => default))

/-- The process-one (blind side) summary: the tracked position per selector. -/
abbrev KnowledgeSummaryOne := KnowledgeSelector A N -> KnowledgeTrack A N

/-- The process-two (informed side) summary: an informed copy of the
process-one summary together with the informed annotation. -/
abbrev KnowledgeSummaryTwo := KnowledgeSummaryOne A N × N.Ann

noncomputable instance : Fintype (KnowledgeSummaryOne A N) :=
  letI : DecidableEq (KnowledgeCommitNode A N) := Classical.decEq _
  letI : DecidableEq (KnowledgeSelector A N) := Classical.decEq _
  letI : DecidableEq N.Ann := Classical.decEq _
  inferInstance

noncomputable instance : Fintype (KnowledgeSummaryTwo A N) :=
  inferInstance

noncomputable instance : Inhabited (KnowledgeSummaryOne A N) :=
  ⟨fun _ => initialKnowledgeTrack A N⟩

noncomputable instance : Inhabited (KnowledgeSummaryTwo A N) :=
  ⟨(default, N.init)⟩

noncomputable instance : DecidableEq (KnowledgeSummaryOne A N) :=
  Classical.decEq _

noncomputable instance : DecidableEq (KnowledgeSummaryTwo A N) :=
  Classical.decEq _

/-- The summary family of the knowledge summary automaton. -/
def KnowledgeSummary : Proc -> Type (max u v w a)
  | .one => KnowledgeSummaryOne A N
  | .two => KnowledgeSummaryTwo A N

noncomputable instance (d : Proc) : Fintype (KnowledgeSummary A N d) := by
  cases d
  · exact inferInstanceAs (Fintype (KnowledgeSummaryOne A N))
  · exact inferInstanceAs (Fintype (KnowledgeSummaryTwo A N))

/-- The process-one summary step on one blind observation. -/
noncomputable def knowledgeSummaryOneStep (s : KnowledgeSummaryOne A N)
    (o : BlindObservation In₁ In₂) : KnowledgeSummaryOne A N :=
  fun ζ => knowledgeTrackStep A N ζ (s ζ) o

/--
**The knowledge summary automaton** `M*` of the route-delta design.  Process
one folds its view increments into the tracked knowledge position per move
selector; process two carries the informed annotation and an informed copy of
the process-one summary that resynchronizes on every round on which it
receives (the epoch handoff/reset reading of `PropEpochhierarchical`; the
fringe-ambiguous resynchronization fixes the dominant `right` reading of the
current round, the one-bit ambiguity of `thm:onebitfringe`).
-/
noncomputable def knowledgeSummaryAutomaton :
    LocalSummaryAutomaton.{u, v, max u v w a} In₁ In₂ where
  Summary := KnowledgeSummary A N
  finite d := inferInstance
  initial d :=
    match d with
    | .one => fun _ => initialKnowledgeTrack A N
    | .two => (fun _ => initialKnowledgeTrack A N, N.init)
  stepNoRecv d :=
    match d with
    | .one => fun s inp =>
        match inp with
        | .inl inputOne =>
            knowledgeSummaryOneStep A N s (.noRecv inputOne)
        | .inr _ => s
    | .two => fun s inp =>
        match inp with
        | .inr inputTwo => (s.1, N.stepSend s.2 inputTwo)
        | .inl _ => s
  stepRecv d :=
    match d with
    | .one => fun s inp _sOther inpOther =>
        match inp, inpOther with
        | .inl inputOne, .inr inputTwo =>
            knowledgeSummaryOneStep A N s (.recv inputOne inputTwo)
        | _, _ => s
    | .two => fun s inp sOther inpOther =>
        match inp, inpOther with
        | .inr inputTwo, .inl inputOne =>
            (knowledgeSummaryOneStep A N sOther (.noRecv inputOne),
              N.stepRecv s.2 inputTwo inputOne)
        | _, _ => s

/-- The joint one-round update of the knowledge summaries, in terms of the
blind observation and the informed-annotation advance of the round. -/
theorem knowledgeSummaryAutomaton_advance
    (pair : (knowledgeSummaryAutomaton A N).Pair)
    (envRound : EnvironmentRound In₁ In₂) :
    (knowledgeSummaryAutomaton A N).advance pair envRound.graph
        envRound.inputOne envRound.inputTwo =
      (knowledgeSummaryOneStep A N pair.1 (roundObservation envRound),
        ((match envRound.graph with
          | .left => pair.2.1
          | .right =>
              knowledgeSummaryOneStep A N pair.1
                (.noRecv envRound.inputOne)
          | .both =>
              knowledgeSummaryOneStep A N pair.1
                (.noRecv envRound.inputOne)),
          N.advanceRound pair.2.2 envRound)) := by
  cases hGraph : envRound.graph <;>
    simp [LocalSummaryAutomaton.advance, knowledgeSummaryAutomaton,
      roundObservation, InformedAnnotationAutomaton.advanceRound, hGraph] <;>
    rfl

end SummaryAutomaton

end DistributedSynthesis
