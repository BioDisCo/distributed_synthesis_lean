/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmVardiWolperStreett
import DistributedSynthesis.Formalizations.Theorem.ThmZielonkaCountableParity

/-!
# APA support-run normal form interface

This file gives a Lean shape to the remaining English support-normal-form step
in the Miyano-Hayashi/Vardi-Wolper APA backend.

The checked material here proves that the paper's frontier/support formulation
is exactly strong enough for the already-formalized rank-monitor backend.  The
only external mathematical content still needed for a fully unconditional
compiler is the positional parity-game theorem that turns an accepting APA run
tree into such a state-based normal form.
-/

namespace DistributedSynthesis

universe u v

namespace AlternatingParityAutomaton
namespace VardiWolper

/--
The paper's state-based support-run normal form for one APA and one word.

At level `n`, `frontier n` is the finite set of active APA states.  The
support choice at level `n` gives, for each active state, a finite
positive-Boolean transition support.  The next frontier is exactly the union of
these supports.  The final field is the parity condition on every timed support
path through these choices.
-/
structure SupportRunNormalForm
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) where
  frontier : Nat -> Finset A.State
  initial_frontier : frontier 0 = ({A.initial} : Finset A.State)
  supportChoice :
    ∀ n : Nat, A.MacroStepSupport (frontier n) (word n)
  next_frontier :
    ∀ n : Nat, (supportChoice n).support = frontier (n + 1)
  path_accepting :
    ∀ path : Nat -> A.State,
      path 0 = A.initial ->
        (∀ n : Nat,
          ∃ hfrontier : path n ∈ frontier n,
            path (n + 1) ∈
              ((supportChoice n).choice
                ⟨path n, hfrontier⟩).support) ->
          ∃ p : Nat,
            DetParityAutomaton.NatEven p ∧
              A.SupportEdgePathPrioritySeenInfinitelyOften path p ∧
                ∀ q : Nat,
                  A.SupportEdgePathPrioritySeenInfinitelyOften path q -> p ≤ q

/--
The positional-strategy certificate delivered by the cited countable parity-game
determinacy theorem for the APA support game on one fixed word.

`reachable i q` says that Adam can reach game position `(i,q)` while playing
against the positional strategy.  The finite `frontier i` is its finitary Lean
carrier.  The local choice is the support selected by Eve's positional strategy
for each reachable state at level `i`, and `next_reachable` states that Adam's
reachable positions at the next level are exactly the successors in those
supports.
-/
structure PositionalSupportStrategy
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) where
  reachable : Nat -> A.State -> Prop
  frontier : Nat -> Finset A.State
  mem_frontier : ∀ n state, state ∈ frontier n ↔ reachable n state
  initial_reachable : ∀ state, reachable 0 state ↔ state = A.initial
  choice :
    ∀ n : Nat, A.MacroStepSupport (frontier n) (word n)
  next_reachable :
    ∀ n state, reachable (n + 1) state ↔ state ∈ (choice n).support
  path_accepting :
    ∀ path : Nat -> A.State,
      path 0 = A.initial ->
        (∀ n : Nat,
          ∃ hfrontier : path n ∈ frontier n,
            path (n + 1) ∈
              ((choice n).choice
                ⟨path n, hfrontier⟩).support) ->
          ∃ p : Nat,
            DetParityAutomaton.NatEven p ∧
              A.SupportEdgePathPrioritySeenInfinitelyOften path p ∧
                ∀ q : Nat,
                  A.SupportEdgePathPrioritySeenInfinitelyOften path q -> p ≤ q

namespace PositionalSupportStrategy

/--
A positional winning strategy for the support game gives the paper's
frontier/support normal form by taking the reachable states as frontiers.
-/
def toSupportRunNormalForm
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : PositionalSupportStrategy A word) :
    SupportRunNormalForm A word where
  frontier := strategy.frontier
  initial_frontier := by
    classical
    ext state
    rw [strategy.mem_frontier, strategy.initial_reachable]
    simp
  supportChoice := strategy.choice
  next_frontier := by
    classical
    intro n
    ext state
    rw [strategy.mem_frontier, strategy.next_reachable]
  path_accepting := strategy.path_accepting

end PositionalSupportStrategy

namespace SupportGame

/-!
## The fixed-word APA support game

The support game used for the positional-normal-form extraction has two real
layers.  At an accepted APA state `(n,q)`, Even chooses a finite transition
support.  Odd then chooses one state from that support and the game advances to
time `n+1`.  Empty supports move to a harmless accepting sink; this keeps the
arena total without adding artificial APA branches.
-/

/-- Accepted APA states at a fixed time of a fixed word. -/
structure AcceptedState
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) where
  time : Nat
  state : A.State
  accepts : A.AcceptsFrom state (OmegaWord.drop word time)

/--
One Even move in the support game: a finite support for one accepted APA state,
together with the continuation-acceptance proof for every successor in it.
-/
structure SupportMove
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) where
  source : AcceptedState A word
  support : A.StepSupport source.state (word source.time)
  support_accepts :
    ∀ nextState, nextState ∈ support.support ->
      A.AcceptsFrom nextState (OmegaWord.drop word (source.time + 1))
  /--
  A ghost tag used only by history-dependent strategies.  It has no effect on
  edges, priorities, or the support frontiers extracted from positional
  strategies, but lets a history strategy remember which run-tree node its
  previous support choice represented.
  -/
  tag : Node := []

/-- Positions of the fixed-word support game. -/
inductive Position
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) where
  | state : AcceptedState A word -> Position A word
  | support : SupportMove A word -> Position A word
  | sink : Position A word

namespace AcceptedState

instance
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    Countable (AcceptedState A word) := by
  classical
  let code : AcceptedState A word -> Nat × A.State :=
    fun state => (state.time, state.state)
  have hcode : Function.Injective code := by
    intro left right h
    cases left
    cases right
    simp [code] at h
    rcases h with ⟨htime, hstate⟩
    cases htime
    cases hstate
    rfl
  exact hcode.countable

end AcceptedState

namespace SupportMove

instance
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    Countable (SupportMove A word) := by
  classical
  let code : SupportMove A word ->
      AcceptedState A word × Finset A.State × Node :=
    fun move => (move.source, move.support.support, move.tag)
  have hcode : Function.Injective code := by
    intro left right h
    cases left with
    | mk leftSource leftSupport leftAccepts leftTag =>
    cases right with
    | mk rightSource rightSupport rightAccepts rightTag =>
    simp [code] at h
    rcases h with ⟨hsource, hsupport, htag⟩
    cases hsource
    cases leftSupport
    cases rightSupport
    simp at hsupport
    cases hsupport
    cases htag
    rfl
  exact hcode.countable

end SupportMove

namespace Position

instance
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    Countable (Position A word) := by
  classical
  let code :
      Position A word ->
        Option (AcceptedState A word ⊕ SupportMove A word) :=
    Position.rec
      (motive :=
        fun _ => Option (AcceptedState A word ⊕ SupportMove A word))
      (fun state => some (Sum.inl state))
      (fun move => some (Sum.inr move))
      none
  have hcode : Function.Injective code := by
    intro left right h
    cases left <;> cases right <;> simp [code] at h ⊢ <;> assumption
  exact hcode.countable

end Position

/-- A priority larger than every APA state priority. -/
noncomputable def supportPriorityBound
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Nat :=
  2 * (Finset.univ.sup A.priority + 1)

theorem supportPriorityBound_even
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    DetParityAutomaton.NatEven (supportPriorityBound A) :=
  ⟨Finset.univ.sup A.priority + 1, rfl⟩

theorem priority_lt_supportPriorityBound
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.State) :
    A.priority state < supportPriorityBound A := by
  classical
  have hle : A.priority state ≤ Finset.univ.sup A.priority :=
    Finset.le_sup (by simp : state ∈ (Finset.univ : Finset A.State))
  dsimp [supportPriorityBound]
  omega

/-- Owner assignment for the support game. -/
def owner
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    Position A word -> ParityPlayer
  | .state _ => ParityPlayer.even
  | .support _ => ParityPlayer.odd
  | .sink => ParityPlayer.even

/-- Edge relation of the fixed-word support game. -/
def step
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    Position A word -> Position A word -> Prop
  | .state state, .support move =>
      move.source = state
  | .support move, .state state =>
      state.time = move.source.time + 1 ∧
        state.state ∈ move.support.support
  | .support move, .sink =>
      move.support.support = ∅
  | .sink, .sink =>
      True
  | _, _ =>
      False

/-- Priority assignment of the fixed-word support game. -/
noncomputable def priority
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    Position A word -> Nat
  | .state state => A.priority state.state
  | .support move => A.priority move.source.state
  | .sink => supportPriorityBound A

/-- A support-game state for the initial APA state, from a word-acceptance proof. -/
def initialAcceptedState
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (haccepts : A.Accepts word) :
    AcceptedState A word where
  time := 0
  state := A.initial
  accepts := by
    simpa [AlternatingParityAutomaton.AcceptsFrom,
      AlternatingParityAutomaton.withInitial, OmegaWord.drop_zero] using
      haccepts

/-- The initial position of the support game. -/
def initial
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (haccepts : A.Accepts word) :
    Position A word :=
  .state (initialAcceptedState haccepts)

/--
Accepted APA states have at least one support-game successor, obtained from the
one-step acceptance equation.
-/
theorem state_step_total
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (state : AcceptedState A word) :
    ∃ next : Position A word,
      step A word (.state state) next := by
  classical
  have hstepRaw :
      PosBool.Eval
        (fun nextState =>
          A.AcceptsFrom nextState
            (OmegaWord.drop (OmegaWord.drop word state.time) 1))
        (A.step state.state ((OmegaWord.drop word state.time) 0)) :=
    A.acceptsFrom_step state.state (OmegaWord.drop word state.time)
      state.accepts
  have hstep :
      PosBool.Eval
        (fun nextState =>
          A.AcceptsFrom nextState
            (OmegaWord.drop word (state.time + 1)))
        (A.step state.state (word state.time)) := by
    simpa [OmegaWord.drop, Nat.add_comm, Nat.add_assoc] using hstepRaw
  rcases
      A.stepSupport_exists_of_eval
        (fun nextState =>
          A.AcceptsFrom nextState
            (OmegaWord.drop word (state.time + 1)))
        state.state (word state.time) hstep with
    ⟨support, hsupportAccepts⟩
  refine
    ⟨.support
      { source := state
        support := support
        support_accepts := hsupportAccepts },
      ?_⟩
  rfl

/-- Support-choice positions have a successor: either a supported next state or the sink. -/
theorem support_step_total
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (move : SupportMove A word) :
    ∃ next : Position A word,
      step A word (.support move) next := by
  classical
  by_cases hnonempty : move.support.support.Nonempty
  · rcases hnonempty with ⟨nextState, hnextState⟩
    refine
      ⟨.state
        { time := move.source.time + 1
          state := nextState
          accepts := move.support_accepts nextState hnextState },
        ?_⟩
    exact ⟨rfl, hnextState⟩
  · have hempty : move.support.support = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    exact ⟨.sink, hempty⟩

/-- The fixed-word support-game edge relation is total. -/
theorem step_total
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    ∀ position : Position A word,
      ∃ next : Position A word, step A word position next
  | Position.state state => state_step_total A word state
  | Position.support move => support_step_total A word move
  | Position.sink => ⟨.sink, trivial⟩

/-- The support-game priority range is finite. -/
theorem priority_finite
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    Set.Finite (Set.range (priority A word)) := by
  classical
  refine
    (Finset.finite_toSet
      (insert (supportPriorityBound A) A.priorityFinset)).subset ?_
  intro p hp
  rcases hp with ⟨position, rfl⟩
  cases position with
  | state state =>
      simp [priority, AlternatingParityAutomaton.mem_priorityFinset]
  | support move =>
      simp [priority]
  | sink =>
      simp [priority]

/-- The countable parity game associated with one APA and one word. -/
noncomputable def game
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    CountableParityGame where
  Position := Position A word
  positionCountable := by infer_instance
  owner := owner A word
  step := step A word
  step_total := step_total A word
  priority := priority A word
  priority_finite := priority_finite A word

/--
At an accepted-state position, any legal Even positional strategy must move to
a support-choice position whose source is that state.
-/
theorem exists_strategy_support_move
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (state : AcceptedState A word) :
    ∃ move : SupportMove A word,
      strategy.move (.state state) = .support move ∧ move.source = state := by
  classical
  have hlegal :
      step A word (.state state) (strategy.move (.state state)) := by
    simpa [game, owner] using
      strategy.legal (.state state) rfl
  cases hmove : strategy.move (.state state) with
  | state nextState =>
      exfalso
      simp [step, hmove] at hlegal
  | support move =>
      refine ⟨move, rfl, ?_⟩
      simpa [step, hmove] using hlegal
  | sink =>
      exfalso
      simp [step, hmove] at hlegal

/-- The support move selected by a positional Even strategy at an accepted state. -/
noncomputable def chosenSupportMove
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (state : AcceptedState A word) :
    SupportMove A word :=
  Classical.choose (exists_strategy_support_move strategy state)

theorem chosenSupportMove_move
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (state : AcceptedState A word) :
    strategy.move (.state state) =
      .support (chosenSupportMove strategy state) :=
  (Classical.choose_spec
    (exists_strategy_support_move strategy state)).1

theorem chosenSupportMove_source
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (state : AcceptedState A word) :
    (chosenSupportMove strategy state).source = state :=
  (Classical.choose_spec
    (exists_strategy_support_move strategy state)).2

/--
At an accepted-state position, package the support selected by a legal
positional strategy with the source fixed definitionally to that accepted state.
-/
theorem exists_strategy_step_support_package
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (state : AcceptedState A word) :
    ∃ package :
      ({ support : A.StepSupport state.state (word state.time) //
        ∀ nextState, nextState ∈ support.support ->
          A.AcceptsFrom nextState (OmegaWord.drop word (state.time + 1)) } ×
        Node),
      strategy.move (.state state) =
        .support
          { source := state
            support := package.1.1
            support_accepts := package.1.2
            tag := package.2 } := by
  classical
  have hlegal :
      step A word (.state state) (strategy.move (.state state)) := by
    simpa [game, owner] using
      strategy.legal (.state state) rfl
  cases hmove : strategy.move (.state state) with
  | state nextState =>
      exfalso
      simp [step, hmove] at hlegal
  | support move =>
      have hsource : move.source = state := by
        simpa [step, hmove] using hlegal
      cases hsource
      refine ⟨(⟨move.support, move.support_accepts⟩, move.tag), ?_⟩
      simp
  | sink =>
      exfalso
      simp [step, hmove] at hlegal

/-- The actual APA step support selected by a strategy, bundled with successor acceptance. -/
noncomputable def chosenStepSupportPackage
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (state : AcceptedState A word) :
    { support : A.StepSupport state.state (word state.time) //
      ∀ nextState, nextState ∈ support.support ->
        A.AcceptsFrom nextState (OmegaWord.drop word (state.time + 1)) } ×
      Node :=
  Classical.choose (exists_strategy_step_support_package strategy state)

theorem chosenStepSupportPackage_move
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (state : AcceptedState A word) :
    strategy.move (.state state) =
      .support
        { source := state
          support := (chosenStepSupportPackage strategy state).1.1
          support_accepts := (chosenStepSupportPackage strategy state).1.2
          tag := (chosenStepSupportPackage strategy state).2 } :=
  Classical.choose_spec (exists_strategy_step_support_package strategy state)

/-- The actual APA step support selected by a strategy at an accepted state. -/
noncomputable def chosenStepSupport
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (state : AcceptedState A word) :
    A.StepSupport state.state (word state.time) :=
  (chosenStepSupportPackage strategy state).1.1

/-- Every successor in the chosen step support carries an acceptance proof. -/
theorem chosenStepSupport_accepts
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (state : AcceptedState A word)
    {nextState : A.State}
    (hnext : nextState ∈ (chosenStepSupport strategy state).support) :
    A.AcceptsFrom nextState (OmegaWord.drop word (state.time + 1)) := by
  exact
    (chosenStepSupportPackage strategy state).1.2 nextState hnext

/-- The support-game position selected by a strategy at an accepted state. -/
noncomputable def chosenSupportPosition
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (state : AcceptedState A word) :
    Position A word :=
  .support
    { source := state
      support := chosenStepSupport strategy state
      support_accepts := by
        intro nextState hnextState
        exact chosenStepSupport_accepts strategy state hnextState
      tag := (chosenStepSupportPackage strategy state).2 }

theorem chosenSupportPosition_move
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (state : AcceptedState A word) :
    strategy.move (.state state) =
      chosenSupportPosition strategy state := by
  simpa [chosenSupportPosition, chosenStepSupport] using
    chosenStepSupportPackage_move strategy state

theorem chosenSupportPosition_step
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (state : AcceptedState A word) :
    step A word (.state state) (chosenSupportPosition strategy state) := by
  simp [chosenSupportPosition, step]

/-- Finite frontier data generated by a positional support-game strategy. -/
structure FrontierData
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    (n : Nat) where
  frontier : Finset A.State
  accepts :
    ∀ state, state ∈ frontier ->
      A.AcceptsFrom state (OmegaWord.drop word n)

/-- The simultaneous macro-support selected on one finite frontier. -/
noncomputable def frontierChoiceFromData
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    {n : Nat}
    (data : FrontierData A word n) :
    A.MacroStepSupport data.frontier (word n) where
  choice state :=
    chosenStepSupport strategy
      { time := n
        state := state.1
        accepts := data.accepts state.1 state.2 }

/-- The next frontier induced by one frontier and the positional strategy. -/
noncomputable def frontierDataNext
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    {n : Nat}
    (data : FrontierData A word n) :
    FrontierData A word (n + 1) where
  frontier := (frontierChoiceFromData strategy data).support
  accepts := by
    intro nextState hnextState
    rcases
        (MacroStepSupport.mem_support
          (supportChoice := frontierChoiceFromData strategy data)
          (nextState := nextState)).mp hnextState with
      ⟨state, hstateNext⟩
    exact
      chosenStepSupport_accepts strategy
        { time := n
          state := state.1
          accepts := data.accepts state.1 state.2 }
        hstateNext

/-- The finite frontiers recursively generated by a positional support-game strategy. -/
noncomputable def frontierData
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (haccepts : A.Accepts word)
    (strategy : (game A word).PositionalStrategy ParityPlayer.even) :
    ∀ n : Nat, FrontierData A word n
  | 0 =>
      { frontier := ({A.initial} : Finset A.State)
        accepts := by
          intro state hstate
          have hstateInitial : state = A.initial := by
            simpa using hstate
          subst state
          simpa [AlternatingParityAutomaton.AcceptsFrom,
            AlternatingParityAutomaton.withInitial, OmegaWord.drop_zero] using
            haccepts }
  | n + 1 =>
      frontierDataNext strategy (frontierData haccepts strategy n)

/-- The macro-support selected at level `n` by a positional support-game strategy. -/
noncomputable def frontierChoice
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (haccepts : A.Accepts word)
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (n : Nat) :
    A.MacroStepSupport (frontierData haccepts strategy n).frontier (word n) :=
  frontierChoiceFromData strategy (frontierData haccepts strategy n)

@[simp]
theorem frontierData_zero_frontier
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (haccepts : A.Accepts word)
    (strategy : (game A word).PositionalStrategy ParityPlayer.even) :
    (frontierData haccepts strategy 0).frontier =
      ({A.initial} : Finset A.State) :=
  rfl

@[simp]
theorem frontierData_succ_frontier
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (haccepts : A.Accepts word)
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (n : Nat) :
    (frontierData haccepts strategy (n + 1)).frontier =
      (frontierChoice haccepts strategy n).support :=
  rfl

/--
Package the frontiers generated by a positional support-game strategy as a
paper-facing positional support strategy, once the semantic path-acceptance
condition has been proved for those generated supports.
-/
noncomputable def positionalSupportStrategyOfPathAccepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (haccepts : A.Accepts word)
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (hpathAccepting :
      ∀ path : Nat -> A.State,
        path 0 = A.initial ->
          (∀ n : Nat,
            ∃ hfrontier :
              path n ∈ (frontierData haccepts strategy n).frontier,
              path (n + 1) ∈
                ((frontierChoice haccepts strategy n).choice
                  ⟨path n, hfrontier⟩).support) ->
            ∃ p : Nat,
              DetParityAutomaton.NatEven p ∧
                A.SupportEdgePathPrioritySeenInfinitelyOften path p ∧
                  ∀ q : Nat,
                    A.SupportEdgePathPrioritySeenInfinitelyOften path q ->
                      p ≤ q) :
    PositionalSupportStrategy A word where
  reachable n state :=
    state ∈ (frontierData haccepts strategy n).frontier
  frontier n :=
    (frontierData haccepts strategy n).frontier
  mem_frontier := by
    intro n state
    rfl
  initial_reachable := by
    intro state
    simp [frontierData]
  choice n :=
    frontierChoice haccepts strategy n
  next_reachable := by
    intro n state
    simp [frontierData_succ_frontier, frontierChoice]
  path_accepting := hpathAccepting

/-- Arithmetic normalization for even support-game times. -/
@[simp]
theorem two_mul_div_two (n : Nat) :
    (2 * n) / 2 = n := by
  exact Nat.mul_div_right n (by decide : 0 < 2)

/-- Arithmetic normalization for even support-game times. -/
@[simp]
theorem two_mul_mod_two (n : Nat) :
    (2 * n) % 2 = 0 := by
  have h := Nat.div_add_mod (2 * n) 2
  omega

/-- Arithmetic normalization for odd support-game times. -/
@[simp]
theorem two_mul_add_one_div_two (n : Nat) :
    (2 * n + 1) / 2 = n := by
  exact
    Nat.div_eq_of_lt_le
      (by omega : n * 2 ≤ 2 * n + 1)
      (by omega : 2 * n + 1 < (n + 1) * 2)

/-- Arithmetic normalization for odd support-game times. -/
@[simp]
theorem two_mul_add_one_mod_two (n : Nat) :
    (2 * n + 1) % 2 = 1 := by
  have h := Nat.div_add_mod (2 * n + 1) 2
  have hdiv : (2 * n + 1) / 2 = n := two_mul_add_one_div_two n
  have hlt := Nat.mod_lt (2 * n + 1) (by decide : 0 < 2)
  omega

/-- The path-through-frontiers premise used by the support-game transfer proof. -/
def FrontierPath
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (haccepts : A.Accepts word)
    (strategy : (game A word).PositionalStrategy ParityPlayer.even)
    (path : Nat -> A.State) :
    Prop :=
  ∀ n : Nat,
    ∃ hfrontier :
      path n ∈ (frontierData haccepts strategy n).frontier,
      path (n + 1) ∈
        ((frontierChoice haccepts strategy n).choice
          ⟨path n, hfrontier⟩).support

/-- Accepted support-game state corresponding to one level of a frontier path. -/
noncomputable def acceptedPathState
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {strategy : (game A word).PositionalStrategy ParityPlayer.even}
    {path : Nat -> A.State}
    (hpath : FrontierPath haccepts strategy path)
    (n : Nat) :
    AcceptedState A word where
  time := n
  state := path n
  accepts :=
    (frontierData haccepts strategy n).accepts
      (path n) (Classical.choose (hpath n))

theorem acceptedPathState_next_mem_chosenSupport
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {strategy : (game A word).PositionalStrategy ParityPlayer.even}
    {path : Nat -> A.State}
    (hpath : FrontierPath haccepts strategy path)
    (n : Nat) :
    path (n + 1) ∈
      (chosenStepSupport strategy (acceptedPathState hpath n)).support := by
  simpa [FrontierPath, frontierChoice, frontierChoiceFromData,
    acceptedPathState, chosenStepSupport] using
    (Classical.choose_spec (hpath n))

/-- The support-game play interleaving APA states and selected support moves. -/
noncomputable def interleavedPath
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {strategy : (game A word).PositionalStrategy ParityPlayer.even}
    {path : Nat -> A.State}
    (hpath : FrontierPath haccepts strategy path) :
    Nat -> Position A word :=
  fun time =>
    if time % 2 = 0 then
      .state (acceptedPathState hpath (time / 2))
    else
      chosenSupportPosition strategy (acceptedPathState hpath (time / 2))

@[simp]
theorem interleavedPath_even
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {strategy : (game A word).PositionalStrategy ParityPlayer.even}
    {path : Nat -> A.State}
    (hpath : FrontierPath haccepts strategy path)
    (n : Nat) :
    interleavedPath hpath (2 * n) =
      .state (acceptedPathState hpath n) := by
  simp [interleavedPath]

@[simp]
theorem interleavedPath_odd
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {strategy : (game A word).PositionalStrategy ParityPlayer.even}
    {path : Nat -> A.State}
    (hpath : FrontierPath haccepts strategy path)
    (n : Nat) :
    interleavedPath hpath (2 * n + 1) =
      chosenSupportPosition strategy (acceptedPathState hpath n) := by
  have hmod : (2 * n + 1) % 2 ≠ 0 := by simp
  simp [interleavedPath]

theorem chosenSupportPosition_step_to_state
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {strategy : (game A word).PositionalStrategy ParityPlayer.even}
    {source target : AcceptedState A word}
    (hnext :
      target.state ∈ (chosenStepSupport strategy source).support)
    (htime : target.time = source.time + 1) :
    step A word
      (chosenSupportPosition strategy source)
      (.state target) := by
  simp [chosenSupportPosition, step, htime, hnext]

theorem interleavedPath_play
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {strategy : (game A word).PositionalStrategy ParityPlayer.even}
    {path : Nat -> A.State}
    (hpath : FrontierPath haccepts strategy path) :
    (game A word).Play (interleavedPath hpath) := by
  intro time
  rcases Nat.mod_two_eq_zero_or_one time with hmod | hmod
  · let n := time / 2
    have htime : time = 2 * n := by
      dsimp [n]
      have h := Nat.div_add_mod time 2
      omega
    rw [htime]
    simpa [game] using
      chosenSupportPosition_step strategy (acceptedPathState hpath n)
  · let n := time / 2
    have htime : time = 2 * n + 1 := by
      dsimp [n]
      have h := Nat.div_add_mod time 2
      omega
    rw [htime]
    have hnext :
        (acceptedPathState hpath (n + 1)).state ∈
          (chosenStepSupport strategy (acceptedPathState hpath n)).support := by
      simpa [acceptedPathState] using
        acceptedPathState_next_mem_chosenSupport hpath n
    have htimeTarget :
        (acceptedPathState hpath (n + 1)).time =
          (acceptedPathState hpath n).time + 1 := by
      simp [acceptedPathState]
    have hsucc : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
    rw [hsucc]
    simpa [game] using
      chosenSupportPosition_step_to_state
        (strategy := strategy)
        (source := acceptedPathState hpath n)
        (target := acceptedPathState hpath (n + 1))
        hnext htimeTarget

theorem interleavedPath_consistent
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {strategy : (game A word).PositionalStrategy ParityPlayer.even}
    {path : Nat -> A.State}
    (hpath : FrontierPath haccepts strategy path) :
    CountableParityGame.PositionalStrategy.Consistent
      (G := game A word) strategy (interleavedPath hpath) := by
  intro time howner
  rcases Nat.mod_two_eq_zero_or_one time with hmod | hmod
  · let n := time / 2
    have htime : time = 2 * n := by
      dsimp [n]
      have h := Nat.div_add_mod time 2
      omega
    rw [htime]
    simpa [game, owner] using
      (chosenSupportPosition_move strategy (acceptedPathState hpath n)).symm
  · let n := time / 2
    have htime : time = 2 * n + 1 := by
      dsimp [n]
      have h := Nat.div_add_mod time 2
      omega
    rw [htime] at howner
    simp [game, owner, chosenSupportPosition] at howner

theorem interleavedPath_zero
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {strategy : (game A word).PositionalStrategy ParityPlayer.even}
    {path : Nat -> A.State}
    (hpath : FrontierPath haccepts strategy path)
    (hinit : path 0 = A.initial) :
    interleavedPath hpath 0 = initial haccepts := by
  simp [interleavedPath, acceptedPathState, initial, initialAcceptedState, hinit]

theorem interleavedPath_priority_at
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {strategy : (game A word).PositionalStrategy ParityPlayer.even}
    {path : Nat -> A.State}
    (hpath : FrontierPath haccepts strategy path)
    (time : Nat) :
    priority A word (interleavedPath hpath time) =
      A.priority (path (time / 2)) := by
  by_cases hmod : time % 2 = 0
  · simp [interleavedPath, hmod, priority, acceptedPathState]
  · simp [interleavedPath, hmod, priority, chosenSupportPosition,
      acceptedPathState]

theorem prioritySeenInfinitelyOften_path_of_interleaved
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {strategy : (game A word).PositionalStrategy ParityPlayer.even}
    {path : Nat -> A.State}
    (hpath : FrontierPath haccepts strategy path)
    {p : Nat}
    (hseen :
      (game A word).PrioritySeenInfinitelyOften
        (interleavedPath hpath) p) :
    A.SupportEdgePathPrioritySeenInfinitelyOften path p := by
  intro n
  rcases hseen (2 * n) with ⟨time, htime, hpriority⟩
  refine ⟨time / 2, ?_, ?_⟩
  · rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
    omega
  · simpa [game, interleavedPath_priority_at hpath time] using hpriority

theorem prioritySeenInfinitelyOften_interleaved_of_path
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {strategy : (game A word).PositionalStrategy ParityPlayer.even}
    {path : Nat -> A.State}
    (hpath : FrontierPath haccepts strategy path)
    {p : Nat}
    (hseen : A.SupportEdgePathPrioritySeenInfinitelyOften path p) :
    (game A word).PrioritySeenInfinitelyOften
      (interleavedPath hpath) p := by
  intro time
  rcases hseen time with ⟨n, hn, hpriority⟩
  refine ⟨2 * n, ?_, ?_⟩
  · omega
  · simpa [game, interleavedPath_priority_at hpath (2 * n)] using hpriority

/-- A finite prefix, ending in an APA state, together with the run-tree node it follows. -/
structure PrefixNodeData
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    {n : Nat}
    (pref : (game A word).Prefix n)
    (node : Node) where
  source : AcceptedState A word
  last_eq : (game A word).prefixLast pref = .state source
  length_eq : node.length = source.time
  state_eq : run.stateAt node = source.state
  path_active : run.PathActive node

/--
Local, tag-based recovery of the run-tree node followed by a finite history.

The initial prefix follows the root.  Later state prefixes recover their parent
node from the ghost tag on the immediately preceding support choice, then pick
an active child matching Adam's chosen successor state.
-/
inductive PrefixTaggedNode
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (haccepts : A.Accepts word) :
    {n : Nat} -> (game A word).Prefix n -> Node -> Type (max u v)
  | initial {pref : (game A word).Prefix 0}
      (hstart : pref 0 = initial haccepts) :
      PrefixTaggedNode run haccepts pref []
  | step {m : Nat}
      {pref : (game A word).Prefix (m + 1)}
      {parent : Node}
      {move : SupportMove A word}
      {target : AcceptedState A word}
      {child : Nat}
      (hprev : pref ⟨m, by omega⟩ = .support move)
      (hlast : (game A word).prefixLast pref = .state target)
      (htag : move.tag = parent)
      (hlength : parent.length = move.source.time)
      (hstate : run.stateAt parent = move.source.state)
      (hpath : run.PathActive parent)
      (htargetTime : target.time = move.source.time + 1)
      (htargetMem : target.state ∈ move.support.support)
      (hchildActive : run.active (child :: parent))
      (hchildState : run.stateAt (child :: parent) = target.state) :
      PrefixTaggedNode run haccepts pref (child :: parent)

def prefixTaggedNode_data
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {run : A.Run word}
    {haccepts : A.Accepts word}
    {n : Nat}
    {pref : (game A word).Prefix n}
    {node : Node}
    (hnode : PrefixTaggedNode run haccepts pref node) :
    PrefixNodeData run pref node := by
  cases hnode with
  | initial hstart =>
      exact
        { source := initialAcceptedState haccepts
          last_eq := by
            simpa [game, CountableParityGame.prefixLast,
              CountableParityGame.singletonPrefix] using hstart
          length_eq := rfl
          state_eq := run.root_state
          path_active := run.pathActive_nil }
  | @step m pref parent move target child hprev hlast htag
      hlength hstate hpath htargetTime htargetMem hchildActive hchildState =>
      exact
        { source := target
          last_eq := hlast
          length_eq := by
            simp [htargetTime, hlength]
          state_eq := hchildState
          path_active := hpath.extend run parent child hchildActive }

/-- Canonical local recovery of the tagged run-tree node from a finite prefix. -/
noncomputable def choosePrefixTaggedNode
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (haccepts : A.Accepts word)
    {n : Nat}
    (pref : (game A word).Prefix n) :
    Option (Σ node : Node, PrefixTaggedNode run haccepts pref node) := by
  classical
  exact
    if hnode : ∃ node : Node,
        Nonempty (PrefixTaggedNode run haccepts pref node) then
      some
        ⟨Classical.choose hnode,
          Classical.choice (Classical.choose_spec hnode)⟩
    else
      none

theorem choosePrefixTaggedNode_some_of_exists
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {run : A.Run word}
    {haccepts : A.Accepts word}
    {n : Nat}
    {pref : (game A word).Prefix n}
    (hnode :
      ∃ node : Node, Nonempty (PrefixTaggedNode run haccepts pref node)) :
    ∃ chosen : Σ node : Node, PrefixTaggedNode run haccepts pref node,
      choosePrefixTaggedNode run haccepts pref = some chosen := by
  classical
  unfold choosePrefixTaggedNode
  simp [hnode]

/--
The step support obtained from the accepting run tree at the node recovered
from the current history.
-/
noncomputable def runNodeStepSupportPackage
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (hacc : run.Accepting)
    {n : Nat}
    {pref : (game A word).Prefix n}
    {node : Node}
    (data : PrefixNodeData run pref node) :
    { support : A.StepSupport data.source.state (word data.source.time) //
      ∀ nextState, nextState ∈ support.support ->
        ∃ child : Nat,
          run.active (child :: node) ∧
            run.stateAt (child :: node) = nextState ∧
              A.AcceptsFrom nextState
                (OmegaWord.drop word (data.source.time + 1)) } := by
  classical
  let valuation : A.State -> Prop :=
    fun nextState =>
      ∃ child : Nat,
        run.active (child :: node) ∧
          run.stateAt (child :: node) = nextState
  have hactive : run.active node :=
    run.pathActive_self node data.path_active
  have hstep :
      PosBool.Eval valuation
        (A.step data.source.state (word data.source.time)) := by
    have hraw := run.step_satisfied node hactive
    simpa [valuation, data.state_eq, data.length_eq] using hraw
  let support :=
    Classical.choose
      (A.stepSupport_exists_of_eval
        valuation data.source.state (word data.source.time) hstep)
  have hsupport :
      ∀ nextState, nextState ∈ support.support -> valuation nextState :=
    Classical.choose_spec
      (A.stepSupport_exists_of_eval
        valuation data.source.state (word data.source.time) hstep)
  refine ⟨support, ?_⟩
  intro nextState hnextState
  rcases hsupport nextState hnextState with
    ⟨child, hchildActive, hchildState⟩
  have hchildPath : run.PathActive (child :: node) :=
    data.path_active.extend run node child hchildActive
  have hchildAccepts :
      A.AcceptsFrom
        (run.stateAt (child :: node))
        (OmegaWord.drop word (child :: node).length) :=
    run.subRun_acceptsFrom
      (child :: node) hchildPath
      (run.pathActive_self (child :: node) hchildPath) hacc
  refine ⟨child, hchildActive, hchildState, ?_⟩
  simpa [hchildState, data.length_eq] using hchildAccepts

/-- The support-game move selected from a run-tree node, tagged by that node. -/
noncomputable def runTaggedSupportMove
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (hacc : run.Accepting)
    {n : Nat}
    {pref : (game A word).Prefix n}
    {node : Node}
    (data : PrefixNodeData run pref node) :
    SupportMove A word where
  source := data.source
  support := (runNodeStepSupportPackage run hacc data).1
  support_accepts := by
    intro nextState hnextState
    rcases
        (runNodeStepSupportPackage run hacc data).2 nextState hnextState with
      ⟨_child, _hchildActive, _hchildState, haccepts⟩
    exact haccepts
  tag := node

theorem runTaggedSupportMove_child
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {run : A.Run word}
    {hacc : run.Accepting}
    {n : Nat}
    {pref : (game A word).Prefix n}
    {node : Node}
    (data : PrefixNodeData run pref node)
    {nextState : A.State}
    (hnextState :
      nextState ∈ (runTaggedSupportMove run hacc data).support.support) :
    ∃ child : Nat,
      run.active (child :: node) ∧
        run.stateAt (child :: node) = nextState := by
  rcases
      (runNodeStepSupportPackage run hacc data).2 nextState hnextState with
    ⟨child, hchildActive, hchildState, _haccepts⟩
  exact ⟨child, hchildActive, hchildState⟩

/-- The history-dependent strategy that follows one accepting run tree. -/
noncomputable def runTreeStrategy
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (haccepts : A.Accepts word)
    (run : A.Run word)
    (hacc : run.Accepting) :
    (game A word).Strategy ParityPlayer.even where
  move _ pref :=
    match choosePrefixTaggedNode run haccepts pref with
    | some chosen =>
        .support (runTaggedSupportMove run hacc (prefixTaggedNode_data chosen.2))
    | none =>
        Classical.choose ((game A word).step_total ((game A word).prefixLast pref))

theorem runTreeStrategy_legal
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (haccepts : A.Accepts word)
    (run : A.Run word)
    (hacc : run.Accepting) :
    (runTreeStrategy haccepts run hacc).Legal := by
  classical
  intro n pref _hlegal _howner
  cases hchosen : choosePrefixTaggedNode run haccepts pref with
  | some chosen =>
    let data : PrefixNodeData run pref chosen.1 :=
      prefixTaggedNode_data chosen.2
    have hlast : (game A word).prefixLast pref = .state data.source :=
      data.last_eq
    rw [hlast]
    simp [runTreeStrategy, hchosen, data, game, step, runTaggedSupportMove]
  | none =>
    simpa [runTreeStrategy, hchosen] using
      Classical.choose_spec
        ((game A word).step_total ((game A word).prefixLast pref))

theorem sink_eventually_constant
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {path : Nat -> Position A word}
    (hplay : (game A word).Play path)
    {base : Nat}
    (hsink : path base = .sink) :
    ∀ time : Nat, base ≤ time -> path time = .sink := by
  intro time hbase
  induction hbase with
  | refl =>
      exact hsink
  | @step time hle ih =>
      have hstep := hplay time
      rw [ih] at hstep
      cases hnext : path (time + 1) <;> simp [game, step, hnext] at hstep
      simp

theorem playerWinsPath_of_eventually_sink
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet)
    {path : Nat -> Position A word}
    (heventual : ∃ base : Nat, ∀ time : Nat, base ≤ time -> path time = .sink) :
    (game A word).PlayerWinsPath ParityPlayer.even path := by
  rcases heventual with ⟨base, hbase⟩
  refine ⟨supportPriorityBound A, supportPriorityBound_even A, ?_, ?_⟩
  · intro n
    refine ⟨max n base, Nat.le_max_left n base, ?_⟩
    have hsink : path (max n base) = .sink :=
      hbase (max n base) (Nat.le_max_right n base)
    simp [game, priority, hsink]
  · intro q hqSeen
    rcases hqSeen base with ⟨time, htime, hpriority⟩
    have hsink : path time = .sink := hbase time htime
    have hq : q = supportPriorityBound A := by
      simpa [game, priority, hsink] using hpriority.symm
    simp [hq]

theorem runTreeStrategy_even_prefix_tagged
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {run : A.Run word}
    {hacc : run.Accepting}
    {path : Nat -> Position A word}
    (hplay :
      (game A word).PlayFrom (initial haccepts) path)
    (hconsistent :
      (runTreeStrategy haccepts run hacc).Consistent path)
    (hnoSink : ∀ time : Nat, path time ≠ .sink) :
    ∀ n : Nat,
      ∃ node : Node,
        Nonempty
          (PrefixTaggedNode run haccepts
            ((game A word).prefixOfPath path (2 * n)) node) := by
  classical
  intro n
  induction n with
  | zero =>
      refine ⟨[], ⟨PrefixTaggedNode.initial ?_⟩⟩
      simpa [CountableParityGame.prefixOfPath] using hplay.1
  | succ n ih =>
      let evenPref := (game A word).prefixOfPath path (2 * n)
      rcases
        choosePrefixTaggedNode_some_of_exists
          (run := run) (haccepts := haccepts) (pref := evenPref) ih with
        ⟨chosen, hchosen⟩
      let node := chosen.1
      let data : PrefixNodeData run evenPref node :=
        prefixTaggedNode_data chosen.2
      have hlastEven :
          path (2 * n) = .state data.source := by
        simpa [evenPref, CountableParityGame.prefixLast_prefixOfPath]
          using data.last_eq
      have hownerEven :
          (game A word).owner (path (2 * n)) = ParityPlayer.even := by
        simp [game, owner, hlastEven]
      have hstrategy :
          (runTreeStrategy haccepts run hacc).move (2 * n) evenPref =
            Position.support (runTaggedSupportMove run hacc data) := by
        simp [runTreeStrategy, hchosen, node, data]
      have hodd :
          path (2 * n + 1) =
            Position.support (runTaggedSupportMove run hacc data) := by
        rw [hconsistent (2 * n) hownerEven]
        simpa [evenPref] using hstrategy
      have hstepOdd :
          step A word
            (.support (runTaggedSupportMove run hacc data))
            (path (2 * n + 2)) := by
        have hplayOdd := hplay.2 (2 * n + 1)
        simpa [game, hodd] using hplayOdd
      cases htarget : path (2 * n + 2) with
      | state target =>
          have hstepTarget :
              step A word
                (.support (runTaggedSupportMove run hacc data))
                (.state target) := by
            simpa [htarget] using hstepOdd
          rcases hstepTarget with ⟨htime, hmem⟩
          rcases runTaggedSupportMove_child data hmem with
            ⟨child, hchildActive, hchildState⟩
          refine
            ⟨child :: node,
              ⟨PrefixTaggedNode.step
                (m := 2 * n + 1)
                (pref :=
                  (game A word).prefixOfPath path (2 * (n + 1)))
                (parent := node)
                (move := runTaggedSupportMove run hacc data)
                (target := target)
                (child := child)
                ?_ ?_ ?_ data.length_eq data.state_eq data.path_active
                htime hmem hchildActive hchildState⟩⟩
          · simp [CountableParityGame.prefixOfPath, hodd]
          · have htwo : 2 * (n + 1) = 2 * n + 2 := by omega
            simpa [CountableParityGame.prefixLast_prefixOfPath, htwo, htarget]
          · simp [runTaggedSupportMove]
      | support move =>
          simp [step, htarget] at hstepOdd
      | sink =>
          exact False.elim (hnoSink (2 * n + 2) htarget)

theorem runTreeStrategy_odd_support_data
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {run : A.Run word}
    {hacc : run.Accepting}
    {path : Nat -> Position A word}
    (hplay :
      (game A word).PlayFrom (initial haccepts) path)
    (hconsistent :
      (runTreeStrategy haccepts run hacc).Consistent path)
    (hnoSink : ∀ time : Nat, path time ≠ .sink)
    (n : Nat) :
    ∃ node : Node,
      ∃ tagged :
        PrefixTaggedNode run haccepts
          ((game A word).prefixOfPath path (2 * n)) node,
        path (2 * n + 1) =
          Position.support
            (runTaggedSupportMove run hacc
              (prefixTaggedNode_data tagged)) := by
  classical
  have hprefix :=
    runTreeStrategy_even_prefix_tagged
      (hplay := hplay) (hconsistent := hconsistent)
      (hnoSink := hnoSink) n
  let evenPref := (game A word).prefixOfPath path (2 * n)
  rcases
    choosePrefixTaggedNode_some_of_exists
      (run := run) (haccepts := haccepts) (pref := evenPref) hprefix with
    ⟨chosen, hchosen⟩
  let data : PrefixNodeData run evenPref chosen.1 :=
    prefixTaggedNode_data chosen.2
  have hlastEven :
      path (2 * n) = .state data.source := by
    simpa [evenPref, CountableParityGame.prefixLast_prefixOfPath]
      using data.last_eq
  have hownerEven :
      (game A word).owner (path (2 * n)) = ParityPlayer.even := by
    simp [game, owner, hlastEven]
  refine ⟨chosen.1, chosen.2, ?_⟩
  rw [hconsistent (2 * n) hownerEven]
  simp [runTreeStrategy, hchosen, evenPref]

noncomputable def playTaggedNode
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {run : A.Run word}
    {hacc : run.Accepting}
    {path : Nat -> Position A word}
    (hplay :
      (game A word).PlayFrom (initial haccepts) path)
    (hconsistent :
      (runTreeStrategy haccepts run hacc).Consistent path)
    (hnoSink : ∀ time : Nat, path time ≠ .sink)
    (n : Nat) :
    Σ node : Node,
      PrefixTaggedNode run haccepts
        ((game A word).prefixOfPath path (2 * n)) node := by
  classical
  let h := runTreeStrategy_odd_support_data
    (hplay := hplay) (hconsistent := hconsistent)
    (hnoSink := hnoSink) n
  exact
    ⟨Classical.choose h,
      Classical.choose (Classical.choose_spec h)⟩

theorem playTaggedNode_odd_eq
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {run : A.Run word}
    {hacc : run.Accepting}
    {path : Nat -> Position A word}
    (hplay :
      (game A word).PlayFrom (initial haccepts) path)
    (hconsistent :
      (runTreeStrategy haccepts run hacc).Consistent path)
    (hnoSink : ∀ time : Nat, path time ≠ .sink)
    (n : Nat) :
    path (2 * n + 1) =
      Position.support
        (runTaggedSupportMove run hacc
          (prefixTaggedNode_data
            (playTaggedNode hplay hconsistent hnoSink n).2)) := by
  classical
  let h := runTreeStrategy_odd_support_data
    (hplay := hplay) (hconsistent := hconsistent)
    (hnoSink := hnoSink) n
  exact Classical.choose_spec (Classical.choose_spec h)

noncomputable def playTag
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {run : A.Run word}
    {hacc : run.Accepting}
    {path : Nat -> Position A word}
    (hplay :
      (game A word).PlayFrom (initial haccepts) path)
    (hconsistent :
      (runTreeStrategy haccepts run hacc).Consistent path)
    (hnoSink : ∀ time : Nat, path time ≠ .sink)
    (n : Nat) :
    Node :=
  (playTaggedNode hplay hconsistent hnoSink n).1

theorem playTag_pathActive
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {run : A.Run word}
    {hacc : run.Accepting}
    {path : Nat -> Position A word}
    (hplay :
      (game A word).PlayFrom (initial haccepts) path)
    (hconsistent :
      (runTreeStrategy haccepts run hacc).Consistent path)
    (hnoSink : ∀ time : Nat, path time ≠ .sink)
    (n : Nat) :
    run.PathActive (playTag hplay hconsistent hnoSink n) :=
  (prefixTaggedNode_data
    (playTaggedNode hplay hconsistent hnoSink n).2).path_active

theorem playTag_state_eq
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {run : A.Run word}
    {hacc : run.Accepting}
    {path : Nat -> Position A word}
    (hplay :
      (game A word).PlayFrom (initial haccepts) path)
    (hconsistent :
      (runTreeStrategy haccepts run hacc).Consistent path)
    (hnoSink : ∀ time : Nat, path time ≠ .sink)
    (n : Nat) :
    run.stateAt (playTag hplay hconsistent hnoSink n) =
      (prefixTaggedNode_data
        (playTaggedNode hplay hconsistent hnoSink n).2).source.state :=
  (prefixTaggedNode_data
    (playTaggedNode hplay hconsistent hnoSink n).2).state_eq

theorem playTag_zero
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {run : A.Run word}
    {hacc : run.Accepting}
    {path : Nat -> Position A word}
    (hplay :
      (game A word).PlayFrom (initial haccepts) path)
    (hconsistent :
      (runTreeStrategy haccepts run hacc).Consistent path)
    (hnoSink : ∀ time : Nat, path time ≠ .sink) :
    playTag hplay hconsistent hnoSink 0 = [] := by
  rcases htag : playTaggedNode hplay hconsistent hnoSink 0 with
    ⟨node, tagged⟩
  cases tagged with
  | initial hstart =>
      simp [playTag, htag]

theorem playTag_succ
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {run : A.Run word}
    {hacc : run.Accepting}
    {path : Nat -> Position A word}
    (hplay :
      (game A word).PlayFrom (initial haccepts) path)
    (hconsistent :
      (runTreeStrategy haccepts run hacc).Consistent path)
    (hnoSink : ∀ time : Nat, path time ≠ .sink)
    (n : Nat) :
    ∃ child : Nat,
      playTag hplay hconsistent hnoSink (n + 1) =
        child :: playTag hplay hconsistent hnoSink n ∧
      run.active (child :: playTag hplay hconsistent hnoSink n) := by
  classical
  rcases hprevTagged : playTaggedNode hplay hconsistent hnoSink n with
    ⟨prevNode, prevTagged⟩
  rcases hnextTagged : playTaggedNode hplay hconsistent hnoSink (n + 1) with
    ⟨nextNode, nextTagged⟩
  have hprevOdd :
      path (2 * n + 1) =
        Position.support
          (runTaggedSupportMove run hacc
            (prefixTaggedNode_data prevTagged)) := by
    have hraw := playTaggedNode_odd_eq hplay hconsistent hnoSink n
    rw [hprevTagged] at hraw
    exact hraw
  cases nextTagged with
  | @step m pref parent move target child hprev hlast htag hlength hstate
      hpath htargetTime htargetMem hchildActive hchildState =>
      have htwo : 2 * (n + 1) = 2 * n + 2 := by omega
      have hprevIndex :
          path (2 * n + 1) = Position.support move := by
        simpa [CountableParityGame.prefixOfPath, htwo] using hprev
      have hsupportEq :
          Position.support move =
            Position.support
              (runTaggedSupportMove run hacc
                (prefixTaggedNode_data prevTagged)) :=
        hprevIndex.symm.trans hprevOdd
      cases hsupportEq
      have hparent :
          parent = playTag hplay hconsistent hnoSink n := by
        simpa [runTaggedSupportMove, playTag, hprevTagged] using htag.symm
      subst parent
      have htagPrev :
          (runTaggedSupportMove run hacc
            (prefixTaggedNode_data prevTagged)).tag = prevNode := by
        simpa [playTag, hprevTagged] using hparent.symm
      refine ⟨child, ?_, ?_⟩
      · simp [playTag, hnextTagged, hprevTagged, htagPrev]
      · simpa [playTag, hprevTagged, htagPrev] using hchildActive

noncomputable def playBranch
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {run : A.Run word}
    {hacc : run.Accepting}
    {path : Nat -> Position A word}
    (hplay :
      (game A word).PlayFrom (initial haccepts) path)
    (hconsistent :
      (runTreeStrategy haccepts run hacc).Consistent path)
    (hnoSink : ∀ time : Nat, path time ≠ .sink) :
    Nat -> Nat :=
  fun n => Classical.choose (playTag_succ hplay hconsistent hnoSink n)

theorem branchPrefix_playBranch
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {run : A.Run word}
    {hacc : run.Accepting}
    {path : Nat -> Position A word}
    (hplay :
      (game A word).PlayFrom (initial haccepts) path)
    (hconsistent :
      (runTreeStrategy haccepts run hacc).Consistent path)
    (hnoSink : ∀ time : Nat, path time ≠ .sink)
    (n : Nat) :
    branchPrefix (playBranch hplay hconsistent hnoSink) n =
      playTag hplay hconsistent hnoSink n := by
  induction n with
  | zero =>
      exact (playTag_zero hplay hconsistent hnoSink).symm
  | succ n ih =>
      have hspec :=
        Classical.choose_spec (playTag_succ hplay hconsistent hnoSink n)
      rw [branchPrefix_succ, ih]
      exact hspec.1.symm

theorem playBranch_active
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {run : A.Run word}
    {hacc : run.Accepting}
    {path : Nat -> Position A word}
    (hplay :
      (game A word).PlayFrom (initial haccepts) path)
    (hconsistent :
      (runTreeStrategy haccepts run hacc).Consistent path)
    (hnoSink : ∀ time : Nat, path time ≠ .sink) :
    run.ActiveBranch (playBranch hplay hconsistent hnoSink) := by
  intro n
  rw [branchPrefix_playBranch hplay hconsistent hnoSink n]
  exact
    run.pathActive_self
      (playTag hplay hconsistent hnoSink n)
      (playTag_pathActive hplay hconsistent hnoSink n)

theorem runTreeStrategy_priority_at
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    {haccepts : A.Accepts word}
    {run : A.Run word}
    {hacc : run.Accepting}
    {path : Nat -> Position A word}
    (hplay :
      (game A word).PlayFrom (initial haccepts) path)
    (hconsistent :
      (runTreeStrategy haccepts run hacc).Consistent path)
    (hnoSink : ∀ time : Nat, path time ≠ .sink)
    (time : Nat) :
    priority A word (path time) =
      A.priority
        (run.stateAt (playTag hplay hconsistent hnoSink (time / 2))) := by
  rcases Nat.mod_two_eq_zero_or_one time with hmod | hmod
  · let n := time / 2
    have htime : time = 2 * n := by
      dsimp [n]
      have h := Nat.div_add_mod time 2
      omega
    rw [htime]
    let tagged := playTaggedNode hplay hconsistent hnoSink n
    let data := prefixTaggedNode_data tagged.2
    have heven :
        path (2 * n) = .state data.source := by
      simpa [data, tagged, CountableParityGame.prefixLast_prefixOfPath]
        using data.last_eq
    have hstate :
        data.source.state =
          run.stateAt (playTag hplay hconsistent hnoSink n) := by
      simpa [playTag, tagged, data] using data.state_eq.symm
    simp [priority, heven, hstate]
  · let n := time / 2
    have htime : time = 2 * n + 1 := by
      dsimp [n]
      have h := Nat.div_add_mod time 2
      omega
    rw [htime]
    let tagged := playTaggedNode hplay hconsistent hnoSink n
    let data := prefixTaggedNode_data tagged.2
    have hodd :
        path (2 * n + 1) =
          Position.support (runTaggedSupportMove run hacc data) := by
      simpa [tagged, data] using
        playTaggedNode_odd_eq hplay hconsistent hnoSink n
    have hstate :
        data.source.state =
          run.stateAt (playTag hplay hconsistent hnoSink n) := by
      simpa [playTag, tagged, data] using data.state_eq.symm
    simp [priority, hodd, runTaggedSupportMove, hstate]

theorem runTreeStrategy_winningFrom
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (haccepts : A.Accepts word)
    (run : A.Run word)
    (hacc : run.Accepting) :
    CountableParityGame.Strategy.WinningFrom
      (G := game A word)
      (runTreeStrategy haccepts run hacc)
      (initial haccepts) := by
  classical
  constructor
  · exact runTreeStrategy_legal haccepts run hacc
  · intro path hplay hconsistent
    by_cases hsink : ∃ time : Nat, path time = .sink
    · rcases hsink with ⟨base, hbase⟩
      exact
        playerWinsPath_of_eventually_sink A word
          ⟨base, sink_eventually_constant hplay.2 hbase⟩
    · have hnoSink : ∀ time : Nat, path time ≠ .sink := by
        intro time htime
        exact hsink ⟨time, htime⟩
      let branch := playBranch hplay hconsistent hnoSink
      have hbranchActive : run.ActiveBranch branch := by
        simpa [branch] using playBranch_active hplay hconsistent hnoSink
      rcases hacc branch hbranchActive with
        ⟨p, hpEven, hpSeen, hpMin⟩
      refine ⟨p, hpEven, ?_, ?_⟩
      · intro start
        rcases hpSeen start with ⟨k, hk, hkprio⟩
        refine ⟨2 * k, ?_, ?_⟩
        · omega
        · have hpriority :=
            runTreeStrategy_priority_at
              hplay hconsistent hnoSink (2 * k)
          change priority A word (path (2 * k)) = p
          rw [hpriority]
          have htag :
              playTag hplay hconsistent hnoSink k =
                branchPrefix branch k := by
            simpa [branch] using
              (branchPrefix_playBranch hplay hconsistent hnoSink k).symm
          simpa [htag] using hkprio
      · intro q hqSeen
        apply hpMin q
        intro start
        rcases hqSeen (2 * start) with
          ⟨time, htime, hpriorityPath⟩
        refine ⟨time / 2, ?_, ?_⟩
        · rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
          omega
        · have hpriority :=
            runTreeStrategy_priority_at
              hplay hconsistent hnoSink time
          change priority A word (path time) = q at hpriorityPath
          rw [hpriority] at hpriorityPath
          have htag :
              playTag hplay hconsistent hnoSink (time / 2) =
                branchPrefix branch (time / 2) := by
            simpa [branch] using
              (branchPrefix_playBranch hplay hconsistent hnoSink
                (time / 2)).symm
          simpa [htag] using hpriorityPath

end SupportGame

/--
Semantic adequacy obligation, history-strategy side: every accepted word makes
the initial support-game position history-winning for Even.
-/
def SupportGameHistoryWinning
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ word : OmegaWord Alphabet,
    ∀ haccepts : A.Accepts word,
      SupportGame.initial haccepts ∈
        (SupportGame.game A word).WinningRegion ParityPlayer.even

/-- An accepting APA run tree gives a history-winning strategy in the support game. -/
theorem supportGameHistoryWinning
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    SupportGameHistoryWinning A := by
  classical
  intro word haccepts
  rcases haccepts with ⟨run, hacc⟩
  exact
    ⟨SupportGame.runTreeStrategy (⟨run, hacc⟩ : A.Accepts word) run hacc,
      SupportGame.runTreeStrategy_winningFrom
        (⟨run, hacc⟩ : A.Accepts word) run hacc⟩

/--
Semantic adequacy obligation, positional-strategy side: every positional
support-game strategy that wins from the accepted initial position gives the
APA support-path parity condition on the frontiers it generates.
-/
def SupportGamePositionalPathTransfer
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ word : OmegaWord Alphabet,
    ∀ haccepts : A.Accepts word,
      ∀ strategy :
        (SupportGame.game A word).PositionalStrategy ParityPlayer.even,
        CountableParityGame.PositionalStrategy.WinningFrom
          (G := SupportGame.game A word) strategy
          (SupportGame.initial haccepts) ->
          ∀ path : Nat -> A.State,
            path 0 = A.initial ->
              (∀ n : Nat,
                ∃ hfrontier :
                  path n ∈
                    (SupportGame.frontierData haccepts strategy n).frontier,
                  path (n + 1) ∈
                    ((SupportGame.frontierChoice haccepts strategy n).choice
                      ⟨path n, hfrontier⟩).support) ->
                ∃ p : Nat,
                  DetParityAutomaton.NatEven p ∧
                    A.SupportEdgePathPrioritySeenInfinitelyOften path p ∧
                      ∀ q : Nat,
                        A.SupportEdgePathPrioritySeenInfinitelyOften path q ->
                          p ≤ q

/-- A positional winning support-game strategy makes every extracted support path accepting. -/
theorem supportGamePositionalPathTransfer
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    SupportGamePositionalPathTransfer A := by
  classical
  intro word haccepts strategy hwinning path hinit hpathRaw
  let hpath : SupportGame.FrontierPath haccepts strategy path := hpathRaw
  let gamePath := SupportGame.interleavedPath hpath
  have hplay :
      (SupportGame.game A word).PlayFrom
        (SupportGame.initial haccepts) gamePath := by
    constructor
    · exact SupportGame.interleavedPath_zero hpath hinit
    · exact SupportGame.interleavedPath_play hpath
  have hconsistent :
      CountableParityGame.PositionalStrategy.Consistent
        (G := SupportGame.game A word) strategy gamePath :=
    SupportGame.interleavedPath_consistent hpath
  have hgameWins :
      (SupportGame.game A word).PlayerWinsPath ParityPlayer.even gamePath :=
    hwinning gamePath hplay hconsistent
  rcases hgameWins with ⟨p, hpEven, hpSeen, hpMin⟩
  refine ⟨p, hpEven, ?_, ?_⟩
  · exact
      SupportGame.prioritySeenInfinitelyOften_path_of_interleaved
        hpath hpSeen
  · intro q hqSeen
    exact hpMin q
      (SupportGame.prioritySeenInfinitelyOften_interleaved_of_path
        hpath hqSeen)

/--
The reusable game-theoretic completeness statement needed from the cited
countable parity-game theorem: every accepted word has a positional winning
support strategy in the APA support game.
-/
def PositionalSupportStrategyCompleteness
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Prop :=
  ∀ word : OmegaWord Alphabet,
    A.Accepts word -> Nonempty (PositionalSupportStrategy A word)

/--
Checked Zielonka handoff for item 1: once the two support-game semantic
adequacy obligations are supplied, countable positional parity determinacy
produces the positional APA support strategy required by the backend.
-/
theorem positionalSupportStrategyCompleteness_of_supportGameAdequacy
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hhistory : SupportGameHistoryWinning A)
    (htransfer : SupportGamePositionalPathTransfer A) :
    PositionalSupportStrategyCompleteness A := by
  classical
  intro word haccepts
  let G := SupportGame.game A word
  have hinitialWinning :
      SupportGame.initial haccepts ∈
        G.WinningRegion ParityPlayer.even := by
    simpa [G] using hhistory word haccepts
  rcases G.uniformPositionalDeterminacy ParityPlayer.even with
    ⟨strategy, hstrategy⟩
  have hposWinning :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := G) strategy (SupportGame.initial haccepts) :=
    hstrategy (SupportGame.initial haccepts) hinitialWinning
  exact
    ⟨SupportGame.positionalSupportStrategyOfPathAccepting
      haccepts strategy
      (by
        simpa [G] using
          htransfer word haccepts strategy hposWinning)⟩

/--
Unconditional item 1 closure: Zielonka's positional theorem, plus the support
game adequacy proofs above, yields the paper's positional support strategy.
-/
theorem positionalSupportStrategyCompleteness
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    PositionalSupportStrategyCompleteness A :=
  positionalSupportStrategyCompleteness_of_supportGameAdequacy
    A (supportGameHistoryWinning A) (supportGamePositionalPathTransfer A)

namespace SupportRunNormalForm

/-- The edge-witnessed support run carried by a support normal form. -/
noncomputable def toEdgeWitnessedMacroRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (normal : SupportRunNormalForm A word) :
    A.EdgeWitnessedMacroRun ({A.initial} : Finset A.State) word where
  toMacroRun :=
    { states := normal.frontier
      initial_states := normal.initial_frontier
      step_transition := by
        intro n
        exact ⟨normal.supportChoice n, normal.next_frontier n⟩ }
  stateEdges n := (normal.supportChoice n).stateEdges
  step_stateEdges_transition := by
    intro n
    exact ⟨normal.supportChoice n, normal.next_frontier n, rfl⟩

@[simp]
theorem toEdgeWitnessedMacroRun_states
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (normal : SupportRunNormalForm A word)
    (n : Nat) :
    normal.toEdgeWitnessedMacroRun.toMacroRun.states n =
      normal.frontier n :=
  rfl

@[simp]
theorem toEdgeWitnessedMacroRun_stateEdges
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (normal : SupportRunNormalForm A word)
    (n : Nat) :
    normal.toEdgeWitnessedMacroRun.stateEdges n =
      (normal.supportChoice n).stateEdges :=
  rfl

/--
Every timed support path of the edge-witnessed run is one of the paths covered
by the normal-form parity condition.
-/
theorem toEdgeWitnessedMacroRun_supportAccepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (normal : SupportRunNormalForm A word) :
    normal.toEdgeWitnessedMacroRun.SupportAccepting := by
  classical
  intro path hpath
  have hinit : path 0 = A.initial := by
    simpa using hpath.1
  apply normal.path_accepting path hinit
  intro n
  have hedge :
      (path n, path (n + 1)) ∈
        (normal.supportChoice n).stateEdges := by
    simpa [toEdgeWitnessedMacroRun] using hpath.2 n
  rcases
      (MacroStepSupport.mem_stateEdges
        (supportChoice := normal.supportChoice n)
        (edge := (path n, path (n + 1)))).mp hedge with
    ⟨source, hsource, htarget⟩
  rcases source with ⟨source, hsourceFrontier⟩
  simp at hsource
  subst source
  exact ⟨hsourceFrontier, htarget⟩

/-- A support-run normal form supplies the backend's support-run witness. -/
theorem hasAcceptingSupportRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (normal : SupportRunNormalForm A word) :
    HasAcceptingSupportRun A word :=
  ⟨normal.toEdgeWitnessedMacroRun,
    normal.toEdgeWitnessedMacroRun_supportAccepting⟩

end SupportRunNormalForm

namespace PositionalSupportStrategy

/-- A positional winning strategy supplies the backend's support-run witness. -/
theorem hasAcceptingSupportRun
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (strategy : PositionalSupportStrategy A word) :
    HasAcceptingSupportRun A word :=
  strategy.toSupportRunNormalForm.hasAcceptingSupportRun

end PositionalSupportStrategy

/--
The positional game-theoretic completeness statement implies the
frontier/support normal-form completeness statement used by the rank monitor.
-/
theorem supportRunNormalForm_complete_of_positionalSupportStrategyCompleteness
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (hstrategy : PositionalSupportStrategyCompleteness A) :
    ∀ word : OmegaWord Alphabet,
      A.Accepts word -> Nonempty (SupportRunNormalForm A word) := by
  intro word haccepts
  exact
    ⟨(Classical.choice (hstrategy word haccepts)).toSupportRunNormalForm⟩

/--
Support-normal-form completeness, stated in the exact frontier/support language
of the English proof, gives the rank-monitor Buchi equivalence.
-/
theorem rankMonitorBuchi_correct_of_supportRunNormalForm
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hnormal :
      ∀ word : OmegaWord Alphabet,
        A.Accepts word -> Nonempty (SupportRunNormalForm A word))
    (word : OmegaWord Alphabet) :
    (rankMonitorBuchi A).Accepts word ↔ A.Accepts word := by
  exact
    rankMonitorBuchi_correct_of_supportNormalForm A
      (fun word haccepts =>
        let normal := Classical.choice (hnormal word haccepts)
        normal.hasAcceptingSupportRun)
      word

/--
The APA support-game positional-completeness theorem gives the rank-monitor
Büchi equivalence.
-/
theorem rankMonitorBuchi_correct_of_positionalSupportStrategyCompleteness
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (hstrategy : PositionalSupportStrategyCompleteness A)
    (word : OmegaWord Alphabet) :
    (rankMonitorBuchi A).Accepts word ↔ A.Accepts word := by
  exact
    rankMonitorBuchi_correct_of_supportRunNormalForm A
      (supportRunNormalForm_complete_of_positionalSupportStrategyCompleteness
        hstrategy)
      word

/-- Closed rank-monitor Buchi correctness, using the proved support-game bridge. -/
theorem rankMonitorBuchi_correct
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    (rankMonitorBuchi A).Accepts word ↔ A.Accepts word :=
  rankMonitorBuchi_correct_of_positionalSupportStrategyCompleteness
    A (positionalSupportStrategyCompleteness A) word

/-- The concrete APA-to-Buchi compilation supplied by the rank monitor. -/
noncomputable def rankMonitorBuchiCompilation
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    APARunToNondetBuchiCompilation.{u, v, v} A where
  buchi := rankMonitorBuchi A
  correct := rankMonitorBuchi_correct A

/-- Uniform APA-to-Buchi compiler obtained from the rank-monitor construction. -/
noncomputable def rankMonitorBuchiCompiler
    (Alphabet : Type u) :
    APARunToNondetBuchiCompiler.{u, v, v} Alphabet where
  compile := fun A => rankMonitorBuchiCompilation A

/-!
The next definitions expose the full paper path:
rank-monitor Buchi compilation followed by the checked Piterman compiler.
-/

/-- Uniform APA-to-DPA compiler obtained by composing the rank monitor with Piterman. -/
noncomputable def rankMonitorPitermanDPACompiler
    (Alphabet : Type u) :
    APARunToDPACompiler.{u, v, v} Alphabet :=
  (rankMonitorBuchiCompiler Alphabet).toDPACompiler
    (NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler Alphabet)

/-- Correctness of the concrete rank-monitor/Piterman APA-to-DPA compiler. -/
theorem rankMonitorPitermanDPACompiler_correct
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    (((rankMonitorPitermanDPACompiler Alphabet).compile A).dpa.Accepts
        word ↔
      A.Accepts word) :=
  ((rankMonitorPitermanDPACompiler Alphabet).compile A).correct word

/--
Paper-facing Buchi/Piterman factorization with no supplied compiler: the Buchi
automaton is the rank monitor and the DPA is its Piterman determinization.
-/
theorem exists_rankMonitorBuchi_piterman_dpa
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    ∃ B : NondetBuchiAutomaton.{u, v} Alphabet,
      ∃ D : DetParityAutomaton.{u, v} Alphabet,
        (∀ word : OmegaWord Alphabet, B.Accepts word ↔ A.Accepts word) ∧
          (∀ word : OmegaWord Alphabet, D.Accepts word ↔ B.Accepts word) ∧
            (∀ word : OmegaWord Alphabet, D.Accepts word ↔ A.Accepts word) :=
  APARunToDPACompiler.exists_buchi_piterman_dpa_of_nondetBuchiCompiler
    (rankMonitorBuchiCompiler Alphabet) A

/-- Standard no-premise APA-to-DPA backend, using the concrete rank monitor. -/
theorem standardAPABackend
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    ∃ D : DetParityAutomaton.{u, v} Alphabet,
      ∀ word : OmegaWord Alphabet, D.Accepts word ↔ A.Accepts word :=
  DistributedSynthesis.standardAPABackend_of_nondetBuchiCompiler
    (rankMonitorBuchiCompiler Alphabet) A

/-- Finite-alphabet spelling of the concrete standard APA backend. -/
theorem standardAPABackend_finiteAlphabet
    {Alphabet : Type u}
    [Fintype Alphabet]
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    ∃ D : DetParityAutomaton.{u, v} Alphabet,
      ∀ word : OmegaWord Alphabet, D.Accepts word ↔ A.Accepts word :=
  standardAPABackend A

end VardiWolper
end AlternatingParityAutomaton

namespace APARunToNondetBuchiCompiler

/-- The concrete uniform APA-to-Buchi compiler: the rank-monitor construction. -/
noncomputable def rankMonitor
    (Alphabet : Type u) :
    APARunToNondetBuchiCompiler.{u, v, v} Alphabet :=
  AlternatingParityAutomaton.VardiWolper.rankMonitorBuchiCompiler Alphabet

end APARunToNondetBuchiCompiler

namespace APARunToDPACompiler

/--
The concrete uniform APA-to-DPA compiler: rank-monitor Buchi compilation
followed by the checked Piterman determinization.
-/
noncomputable def rankMonitorPiterman
    (Alphabet : Type u) :
    APARunToDPACompiler.{u, v, v} Alphabet :=
  AlternatingParityAutomaton.VardiWolper.rankMonitorPitermanDPACompiler Alphabet

/-- Correctness of the concrete rank-monitor/Piterman APA-to-DPA compiler. -/
theorem rankMonitorPiterman_correct
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    (((rankMonitorPiterman Alphabet).compile A).dpa.Accepts word ↔
      A.Accepts word) :=
  ((rankMonitorPiterman Alphabet).compile A).correct word

end APARunToDPACompiler

/--
Paper-facing Buchi/Piterman factorization with no supplied compiler: the Buchi
automaton is the rank monitor and the DPA is its Piterman determinization.
-/
theorem exists_rankMonitorBuchi_piterman_dpa
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    ∃ B : NondetBuchiAutomaton.{u, v} Alphabet,
      ∃ D : DetParityAutomaton.{u, v} Alphabet,
        (∀ word : OmegaWord Alphabet, B.Accepts word ↔ A.Accepts word) ∧
          (∀ word : OmegaWord Alphabet, D.Accepts word ↔ B.Accepts word) ∧
            (∀ word : OmegaWord Alphabet, D.Accepts word ↔ A.Accepts word) :=
  AlternatingParityAutomaton.VardiWolper.exists_rankMonitorBuchi_piterman_dpa A

/-- Standard no-premise APA-to-DPA backend, using the concrete rank monitor. -/
theorem standardAPABackend
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    ∃ D : DetParityAutomaton.{u, v} Alphabet,
      ∀ word : OmegaWord Alphabet, D.Accepts word ↔ A.Accepts word :=
  AlternatingParityAutomaton.VardiWolper.standardAPABackend A

/-- Finite-alphabet spelling of the concrete standard APA backend. -/
theorem standardAPABackend_finiteAlphabet
    {Alphabet : Type u}
    [Fintype Alphabet]
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    ∃ D : DetParityAutomaton.{u, v} Alphabet,
      ∀ word : OmegaWord Alphabet, D.Accepts word ↔ A.Accepts word :=
  standardAPABackend A

end DistributedSynthesis
