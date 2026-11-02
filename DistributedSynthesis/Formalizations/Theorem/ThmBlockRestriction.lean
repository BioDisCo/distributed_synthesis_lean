/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefSynthesisProblem
import DistributedSynthesis.Formalizations.Theorem.ThmParityTreeEmptinessGame
import DistributedSynthesis.Formalizations.Theorem.ThmAutomataBackend
import DistributedSynthesis.Formalizations.Lemma.LemBlocktreecorrespondence

/-!
# Block restriction of distributed strategies

This file provides the strategy-side interface of
`prop:journalgivesuniform` from `paper.tex`: restricting a global
distributed strategy, at a strategy-generated finite history, to a
local block strategy pair for the following one-sided dominance block,
with exactly the information sets of Lemma `lem:syncblockinfo`.

During a block dominated by process one, the receiver observes both
inputs of every round while the sender observes only its own inputs;
views record no outputs.  Consequently the restriction of the receiver
is a `ReceiverBlockStrategy` on full move histories, and the
restriction of the sender is a well-defined `SenderBlockStrategy` on
sender words: the sender's view along the block is independent of the
receiver inputs used to complete the word
(`currentView_two_extendPrefix_left`).

The main results identify block plays with real executions: against
every block environment word, the play of the restricted pair is the
tail, after the given history, of a real execution of the global
strategy (`execution_leftBlockEnvironment_eq_pairPlay`,
`exists_execution_extension_of_strategyGenerated`).  Therefore every
block objective that is a tail consequence of global acceptance is won
by the restricted pair (`blockPair_wins_of_acceptance`); this is the
hypothesis shape of
`block_realizable_iff_implementable_controller_unconditional` and feeds
the per-block narrowing step of the journal construction.
-/

namespace DistributedSynthesis

universe u v x y

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- The environment move recorded by a round. -/
def RoundRecord.environment
    (round : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    EnvironmentRound In₁ In₂ where
  inputOne := round.inputOne
  inputTwo := round.inputTwo
  graph := round.graph

@[simp]
theorem environment_nextRound
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentRound In₁ In₂) :
    (nextRound σ h env).environment = env :=
  rfl

/-- Play a strategy pair from a given history along a list of moves. -/
def extendPrefix
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (envs : List (EnvironmentRound In₁ In₂)) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  envs.foldl (fun h' env => History.append h' (nextRound σ h' env)) h

@[simp]
theorem extendPrefix_nil
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    extendPrefix σ h [] = h :=
  rfl

@[simp]
theorem extendPrefix_snoc
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (envs : List (EnvironmentRound In₁ In₂))
    (env : EnvironmentRound In₁ In₂) :
    extendPrefix σ h (envs ++ [env]) =
      History.append (extendPrefix σ h envs)
        (nextRound σ (extendPrefix σ h envs) env) := by
  simp [extendPrefix, List.foldl_append]

/-- A strategy-generated history is replayed by its recorded moves. -/
theorem executionPrefixFromList_map_environment
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h) :
    executionPrefixFromList σ (h.map RoundRecord.environment) = h := by
  induction hgen with
  | empty => rfl
  | append hhistory env ih =>
      simp [History.append, ih]

/-- The one-sided environment move of a block round. -/
def leftEnvironment (move : In₁ × In₂) : EnvironmentRound In₁ In₂ where
  inputOne := move.1
  inputTwo := move.2
  graph := Graph.left

/--
The real environment sequence that replays a history and then plays a
block of left rounds with the given moves.
-/
def leftBlockEnvironment
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (env : Nat -> In₁ × In₂) :
    EnvironmentSequence In₁ In₂ :=
  fun n =>
    if hn : n < h.length then (h.get ⟨n, hn⟩).environment
    else leftEnvironment (env (n - h.length))

theorem leftBlockEnvironment_ge
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (env : Nat -> In₁ × In₂)
    (t : Nat) :
    leftBlockEnvironment h env (h.length + t) = leftEnvironment (env t) := by
  have hnot : ¬ h.length + t < h.length := by omega
  simp [leftBlockEnvironment, hnot]

/-- Replaying a strategy-generated history reproduces it. -/
theorem executionPrefix_leftBlockEnvironment
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (env : Nat -> In₁ × In₂) :
    executionPrefix σ (leftBlockEnvironment h env) h.length = h := by
  have hmap := executionPrefixFromList_map_environment σ hgen
  have hagree :
      executionPrefixFromList σ (h.map RoundRecord.environment) =
        executionPrefix σ (leftBlockEnvironment h env)
          (h.map RoundRecord.environment).length := by
    apply executionPrefixFromList_eq_executionPrefix_of_getElem_eq
    intro k hk
    have hk' : k < h.length := by simpa using hk
    simp [leftBlockEnvironment, hk']
  rw [hmap] at hagree
  simpa using hagree.symm

/--
The receiver restriction of a global strategy at a history: the block
node and current move are played as left rounds after the history, and
the receiver output is read from the resulting view.
-/
def blockReceiverOne
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    ReceiverBlockStrategy In₁ In₂ Out₁ :=
  fun node move =>
    σ.one
      (nextView Proc.one (extendPrefix σ h (node.map leftEnvironment))
        (leftEnvironment move))

/--
The sender restriction of a global strategy at a history: the sender
word is completed by arbitrary receiver inputs, played as left rounds
after the history, and the sender output is read from the resulting
view.  The completion is irrelevant because the sender's view along a
left block records only its own inputs.
-/
def blockSenderTwo [Inhabited In₁]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    SenderBlockStrategy In₂ Out₂ :=
  fun word input =>
    σ.two
      (nextView Proc.two
        (extendPrefix σ h
          (word.map (fun sIn => leftEnvironment ((default : In₁), sIn))))
        (leftEnvironment ((default : In₁), input)))

theorem nextView_two_of_graph_left
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentRound In₁ In₂)
    (he : env.graph = Graph.left) :
    nextView Proc.two h env =
      View.noRecv (currentView Proc.two h) (.inr env.inputTwo) := by
  simp [nextView, advanceViewsWithEnvironment, he, currentView]

/--
Along a block of left rounds, the sender's view folds only its own
inputs: outputs and receiver inputs do not enter.
-/
theorem currentView_two_extendPrefix_left
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (envs : List (EnvironmentRound In₁ In₂))
    (hleft : ∀ env ∈ envs, env.graph = Graph.left) :
    currentView Proc.two (extendPrefix σ h envs) =
      envs.foldl (fun view env => View.noRecv view (.inr env.inputTwo))
        (currentView Proc.two h) := by
  induction envs using List.reverseRecOn with
  | nil => rfl
  | append_singleton envs env ih =>
      have he : env.graph = Graph.left := hleft env (by simp)
      have hprev : ∀ env' ∈ envs, env'.graph = Graph.left :=
        fun env' henv' => hleft env' (by simp [henv'])
      rw [extendPrefix_snoc, List.foldl_append]
      rw [currentView_two_append]
      simp [nextRound, he, ih hprev]

/--
The sender restriction agrees with the receiver-complete play: on the
sender word of a block node, it plays the global strategy's output at
the actual node.
-/
theorem blockSenderTwo_eq [Inhabited In₁]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (node : TreeNode (In₁ × In₂))
    (move : In₁ × In₂) :
    blockSenderTwo σ h (senderWord node) move.2 =
      σ.two
        (nextView Proc.two (extendPrefix σ h (node.map leftEnvironment))
          (leftEnvironment move)) := by
  have hleftWord :
      ∀ env ∈ (senderWord node).map
          (fun sIn => leftEnvironment ((default : In₁), sIn)),
        env.graph = Graph.left := by
    intro env henv
    rcases List.mem_map.mp henv with ⟨sIn, _, rfl⟩
    rfl
  have hleftNode :
      ∀ env ∈ node.map leftEnvironment, env.graph = Graph.left := by
    intro env henv
    rcases List.mem_map.mp henv with ⟨m, _, rfl⟩
    rfl
  rw [
    blockSenderTwo,
    nextView_two_of_graph_left _ _ rfl,
    nextView_two_of_graph_left _ _ rfl,
    currentView_two_extendPrefix_left σ h _ hleftWord,
    currentView_two_extendPrefix_left σ h _ hleftNode
  ]
  simp [senderWord, leftEnvironment, List.foldl_map, List.map_map,
    Function.comp_def]

/-- The round record realized by a block round, as a left round. -/
def realizedRoundRecord
    (round : RealizedBlockRound In₁ In₂ Out₁ Out₂) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ where
  inputOne := round.1.1
  inputTwo := round.1.2
  graph := Graph.left
  outputOne := round.2.1
  outputTwo := round.2.2

/--
Playing a strategy-generated history and then a block of left rounds,
the real execution prefix is the strategy extension of the history by
the block node.
-/
theorem executionPrefix_leftBlockEnvironment_add
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (env : Nat -> In₁ × In₂)
    (t : Nat) :
    executionPrefix σ (leftBlockEnvironment h env) (h.length + t) =
      extendPrefix σ h ((branchNode env t).map leftEnvironment) := by
  induction t with
  | zero =>
      simpa [branchNode] using
        executionPrefix_leftBlockEnvironment σ hgen env
  | succ t ih =>
      rw [
        show h.length + (t + 1) = (h.length + t) + 1 from rfl,
        executionPrefix_succ,
        ih,
        leftBlockEnvironment_ge
      ]
      simp [branchNode, List.map_append]

/--
The play of the restricted block pair is the tail of the real execution
of the global strategy after the history: round by round, the realized
block round is the emitted round record.
-/
theorem execution_leftBlockEnvironment_eq_pairPlay [Inhabited In₁]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (env : Nat -> In₁ × In₂)
    (t : Nat) :
    execution σ (leftBlockEnvironment h env) (h.length + t) =
      realizedRoundRecord
        (pairPlay (blockReceiverOne σ h) (blockSenderTwo σ h) env t) := by
  rw [
    execution_apply,
    executionPrefix_leftBlockEnvironment_add σ hgen env t,
    leftBlockEnvironment_ge
  ]
  have hsender := blockSenderTwo_eq σ h (branchNode env t) (env t)
  simp only [pairPlay, treePlay, treeOfPair, blockLabelApply]
  simp [nextRound, realizedRoundRecord, blockReceiverOne, leftEnvironment,
    hsender]

/--
Package form: every block environment word extends the history to a
real execution of the global strategy whose tail realizes the play of
the restricted pair.
-/
theorem exists_execution_extension_of_strategyGenerated [Inhabited In₁]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (env : Nat -> In₁ × In₂) :
    ∃ env' : EnvironmentSequence In₁ In₂,
      executionPrefix σ env' h.length = h ∧
        ∀ t : Nat,
          execution σ env' (h.length + t) =
            realizedRoundRecord
              (pairPlay (blockReceiverOne σ h) (blockSenderTwo σ h)
                env t) :=
  ⟨leftBlockEnvironment h env,
    executionPrefix_leftBlockEnvironment σ hgen env,
    fun t => execution_leftBlockEnvironment_eq_pairPlay σ hgen env t⟩

/--
Objective transport: every block objective that is a tail consequence
of a global execution property is won by the restricted pair.  This is
the hypothesis shape of the per-block narrowing step.
-/
theorem blockPair_wins_of_acceptance [Inhabited In₁]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (P : (Nat -> RoundRecord In₁ In₂ Graph Out₁ Out₂) -> Prop)
    (hP : ∀ env' : EnvironmentSequence In₁ In₂, P (execution σ env'))
    (Q : (Nat -> RealizedBlockRound In₁ In₂ Out₁ Out₂) -> Prop)
    (hQ :
      ∀ (word : Nat -> RoundRecord In₁ In₂ Graph Out₁ Out₂)
        (play : Nat -> RealizedBlockRound In₁ In₂ Out₁ Out₂),
        P word ->
        FiniteEpochTransformer.wordPrefix word h.length = h ->
        (∀ t : Nat, word (h.length + t) = realizedRoundRecord (play t)) ->
          Q play) :
    ∀ env : Nat -> In₁ × In₂,
      Q (pairPlay (blockReceiverOne σ h) (blockSenderTwo σ h) env) := by
  intro env
  rcases exists_execution_extension_of_strategyGenerated σ hgen env with
    ⟨env', hprefix, hplay⟩
  refine hQ _ _ (hP env') ?_ hplay
  rw [FiniteEpochTransformer.wordPrefix_execution]
  exact hprefix

/-! ### The right-dominant mirror

During a block dominated by process two, process two is the receiver
and process one is the sender.  Block moves are receiver-first pairs
`In₂ × In₁`.
-/

/-- The one-sided environment move of a right block round. -/
def rightEnvironment (move : In₂ × In₁) : EnvironmentRound In₁ In₂ where
  inputOne := move.2
  inputTwo := move.1
  graph := Graph.right

/--
The real environment sequence that replays a history and then plays a
block of right rounds with the given moves.
-/
def rightBlockEnvironment
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (env : Nat -> In₂ × In₁) :
    EnvironmentSequence In₁ In₂ :=
  fun n =>
    if hn : n < h.length then (h.get ⟨n, hn⟩).environment
    else rightEnvironment (env (n - h.length))

theorem rightBlockEnvironment_ge
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (env : Nat -> In₂ × In₁)
    (t : Nat) :
    rightBlockEnvironment h env (h.length + t) =
      rightEnvironment (env t) := by
  have hnot : ¬ h.length + t < h.length := by omega
  simp [rightBlockEnvironment, hnot]

/-- Replaying a strategy-generated history reproduces it. -/
theorem executionPrefix_rightBlockEnvironment
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (env : Nat -> In₂ × In₁) :
    executionPrefix σ (rightBlockEnvironment h env) h.length = h := by
  have hmap := executionPrefixFromList_map_environment σ hgen
  have hagree :
      executionPrefixFromList σ (h.map RoundRecord.environment) =
        executionPrefix σ (rightBlockEnvironment h env)
          (h.map RoundRecord.environment).length := by
    apply executionPrefixFromList_eq_executionPrefix_of_getElem_eq
    intro k hk
    have hk' : k < h.length := by simpa using hk
    simp [rightBlockEnvironment, hk']
  rw [hmap] at hagree
  simpa using hagree.symm

/-- The receiver restriction of a global strategy for a right block. -/
def blockReceiverTwo
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    ReceiverBlockStrategy In₂ In₁ Out₂ :=
  fun node move =>
    σ.two
      (nextView Proc.two (extendPrefix σ h (node.map rightEnvironment))
        (rightEnvironment move))

/-- The sender restriction of a global strategy for a right block. -/
def blockSenderOne [Inhabited In₂]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    SenderBlockStrategy In₁ Out₁ :=
  fun word input =>
    σ.one
      (nextView Proc.one
        (extendPrefix σ h
          (word.map (fun sIn => rightEnvironment ((default : In₂), sIn))))
        (rightEnvironment ((default : In₂), input)))

theorem nextView_one_of_graph_right
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentRound In₁ In₂)
    (he : env.graph = Graph.right) :
    nextView Proc.one h env =
      View.noRecv (currentView Proc.one h) (.inl env.inputOne) := by
  simp [nextView, advanceViewsWithEnvironment, he, currentView]

/--
Along a block of right rounds, the sender's view folds only its own
inputs.
-/
theorem currentView_one_extendPrefix_right
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (envs : List (EnvironmentRound In₁ In₂))
    (hright : ∀ env ∈ envs, env.graph = Graph.right) :
    currentView Proc.one (extendPrefix σ h envs) =
      envs.foldl (fun view env => View.noRecv view (.inl env.inputOne))
        (currentView Proc.one h) := by
  induction envs using List.reverseRecOn with
  | nil => rfl
  | append_singleton envs env ih =>
      have he : env.graph = Graph.right := hright env (by simp)
      have hprev : ∀ env' ∈ envs, env'.graph = Graph.right :=
        fun env' henv' => hright env' (by simp [henv'])
      rw [extendPrefix_snoc, List.foldl_append]
      rw [currentView_one_append]
      simp [nextRound, he, ih hprev]

/-- The sender restriction agrees with the receiver-complete play. -/
theorem blockSenderOne_eq [Inhabited In₂]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (node : TreeNode (In₂ × In₁))
    (move : In₂ × In₁) :
    blockSenderOne σ h (senderWord node) move.2 =
      σ.one
        (nextView Proc.one (extendPrefix σ h (node.map rightEnvironment))
          (rightEnvironment move)) := by
  have hrightWord :
      ∀ env ∈ (senderWord node).map
          (fun sIn => rightEnvironment ((default : In₂), sIn)),
        env.graph = Graph.right := by
    intro env henv
    rcases List.mem_map.mp henv with ⟨sIn, _, rfl⟩
    rfl
  have hrightNode :
      ∀ env ∈ node.map rightEnvironment, env.graph = Graph.right := by
    intro env henv
    rcases List.mem_map.mp henv with ⟨m, _, rfl⟩
    rfl
  rw [
    blockSenderOne,
    nextView_one_of_graph_right _ _ rfl,
    nextView_one_of_graph_right _ _ rfl,
    currentView_one_extendPrefix_right σ h _ hrightWord,
    currentView_one_extendPrefix_right σ h _ hrightNode
  ]
  simp [senderWord, rightEnvironment, List.foldl_map, List.map_map,
    Function.comp_def]

/-- The round record realized by a right block round. -/
def realizedRoundRecordRight
    (round : RealizedBlockRound In₂ In₁ Out₂ Out₁) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ where
  inputOne := round.1.2
  inputTwo := round.1.1
  graph := Graph.right
  outputOne := round.2.2
  outputTwo := round.2.1

/-- The real execution prefix along a right block. -/
theorem executionPrefix_rightBlockEnvironment_add
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (env : Nat -> In₂ × In₁)
    (t : Nat) :
    executionPrefix σ (rightBlockEnvironment h env) (h.length + t) =
      extendPrefix σ h ((branchNode env t).map rightEnvironment) := by
  induction t with
  | zero =>
      simpa [branchNode] using
        executionPrefix_rightBlockEnvironment σ hgen env
  | succ t ih =>
      rw [
        show h.length + (t + 1) = (h.length + t) + 1 from rfl,
        executionPrefix_succ,
        ih,
        rightBlockEnvironment_ge
      ]
      simp [branchNode, List.map_append]

/-- The play of the restricted right-block pair is a real execution tail. -/
theorem execution_rightBlockEnvironment_eq_pairPlay [Inhabited In₂]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (env : Nat -> In₂ × In₁)
    (t : Nat) :
    execution σ (rightBlockEnvironment h env) (h.length + t) =
      realizedRoundRecordRight
        (pairPlay (blockReceiverTwo σ h) (blockSenderOne σ h) env t) := by
  rw [
    execution_apply,
    executionPrefix_rightBlockEnvironment_add σ hgen env t,
    rightBlockEnvironment_ge
  ]
  have hsender := blockSenderOne_eq σ h (branchNode env t) (env t)
  simp only [pairPlay, treePlay, treeOfPair, blockLabelApply]
  simp [nextRound, realizedRoundRecordRight, blockReceiverTwo,
    rightEnvironment, hsender]

/-- Package form of the right-block correspondence. -/
theorem exists_execution_extension_of_strategyGenerated_right
    [Inhabited In₂]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (env : Nat -> In₂ × In₁) :
    ∃ env' : EnvironmentSequence In₁ In₂,
      executionPrefix σ env' h.length = h ∧
        ∀ t : Nat,
          execution σ env' (h.length + t) =
            realizedRoundRecordRight
              (pairPlay (blockReceiverTwo σ h) (blockSenderOne σ h)
                env t) :=
  ⟨rightBlockEnvironment h env,
    executionPrefix_rightBlockEnvironment σ hgen env,
    fun t => execution_rightBlockEnvironment_eq_pairPlay σ hgen env t⟩

/-- Objective transport for right blocks. -/
theorem blockPair_wins_of_acceptance_right [Inhabited In₂]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (P : (Nat -> RoundRecord In₁ In₂ Graph Out₁ Out₂) -> Prop)
    (hP : ∀ env' : EnvironmentSequence In₁ In₂, P (execution σ env'))
    (Q : (Nat -> RealizedBlockRound In₂ In₁ Out₂ Out₁) -> Prop)
    (hQ :
      ∀ (word : Nat -> RoundRecord In₁ In₂ Graph Out₁ Out₂)
        (play : Nat -> RealizedBlockRound In₂ In₁ Out₂ Out₁),
        P word ->
        FiniteEpochTransformer.wordPrefix word h.length = h ->
        (∀ t : Nat,
          word (h.length + t) = realizedRoundRecordRight (play t)) ->
          Q play) :
    ∀ env : Nat -> In₂ × In₁,
      Q (pairPlay (blockReceiverTwo σ h) (blockSenderOne σ h) env) := by
  intro env
  rcases exists_execution_extension_of_strategyGenerated_right σ hgen env
    with ⟨env', hprefix, hplay⟩
  refine hQ _ _ (hP env') ?_ hplay
  rw [FiniteEpochTransformer.wordPrefix_execution]
  exact hprefix

end DistributedSynthesis
