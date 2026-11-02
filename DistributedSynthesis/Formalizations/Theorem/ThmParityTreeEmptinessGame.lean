/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefTreeAutomata
import DistributedSynthesis.Formalizations.Theorem.ThmZielonkaCountableParity

/-!
# Emptiness game for run-based parity tree automata

This file discharges the regular-tree rationality interface of
`InputFreeParityTreeAutomaton` for concrete run-based automata.

`RunParityTreeAutomaton` is a run-based parity tree automaton given by an
explicit transition relation and priority map.  Its branch and label types
are deliberately unrestricted; only its state type is finite.  Acceptance is
the standard run-tree semantics with the min-even parity condition on every
infinite branch.

For finite branch and label types, the emptiness parity game is finite, so the
checked Zielonka theorem `CountableParityGame.positionalGameDetermined`
applies.  A positional strategy of the automaton player in that game is
literally a `TransitionRationalTree`, which yields the Rabin basis theorem
`RunParityTreeAutomaton.exists_transitionRational_accepted`: a run-based
automaton that accepts some tree accepts a transition-rational tree.  The
separation of unrestricted semantics from this finite extraction theorem is
important for the Bérard input-free, infinitely-branching interface.

`RunParityTreeAutomaton.toInputFree` packages the result as an
`InputFreeParityTreeAutomaton` whose `rationality` and `transitionRationality`
fields are proved rather than assumed.  This is the constructor that concrete
block-game automata should be built through: any automaton obtained from
`toInputFree` satisfies the rational-run interface unconditionally.
-/

namespace DistributedSynthesis

universe u v w x

/-- Priority `p` occurs infinitely often in a priority sequence. -/
def NatSeqSeenInfinitelyOften (s : Nat -> Nat) (p : Nat) : Prop :=
  ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ s k = p

/-- The min-even parity condition for a priority sequence. -/
def NatSeqMinEvenParity (s : Nat -> Nat) : Prop :=
  ∃ p : Nat,
    DetParityAutomaton.NatEven p ∧
      NatSeqSeenInfinitelyOften s p ∧
        ∀ q : Nat, NatSeqSeenInfinitelyOften s q -> p ≤ q

/-- The complementary min-odd parity condition for a priority sequence. -/
def NatSeqMinOddParity (s : Nat -> Nat) : Prop :=
  ∃ p : Nat,
    ¬ DetParityAutomaton.NatEven p ∧
      NatSeqSeenInfinitelyOften s p ∧
        ∀ q : Nat, NatSeqSeenInfinitelyOften s q -> p ≤ q

/-- Even constant offsets preserve min-even parity. -/
theorem natSeqMinEvenParity_add_const
    {f : Nat -> Nat} {d : Nat} (hd : DetParityAutomaton.NatEven d) :
    NatSeqMinEvenParity (fun n => f n + d) ↔ NatSeqMinEvenParity f := by
  obtain ⟨b, hb⟩ := hd
  constructor
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    obtain ⟨k, -, hk⟩ := hpSeen 0
    have hk' : f k + d = p := hk
    obtain ⟨a, ha⟩ := hpEven
    refine ⟨p - d, ⟨a - b, by omega⟩, ?_, ?_⟩
    · intro n
      obtain ⟨m, hm, hval⟩ := hpSeen n
      have hval' : f m + d = p := hval
      exact ⟨m, hm, by omega⟩
    · intro q hq
      have hq' :
          NatSeqSeenInfinitelyOften (fun n => f n + d) (q + d) := by
        intro n
        obtain ⟨m, hm, hval⟩ := hq n
        exact ⟨m, hm, show f m + d = q + d by omega⟩
      have := hpMin (q + d) hq'
      omega
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    obtain ⟨a, ha⟩ := hpEven
    refine ⟨p + d, ⟨a + b, by omega⟩, ?_, ?_⟩
    · intro n
      obtain ⟨m, hm, hval⟩ := hpSeen n
      exact ⟨m, hm, show f m + d = p + d by omega⟩
    · intro q hq
      obtain ⟨k, -, hk⟩ := hq 0
      have hk' : f k + d = q := hk
      have hq' : NatSeqSeenInfinitelyOften f (q - d) := by
        intro n
        obtain ⟨m, hm, hval⟩ := hq n
        have hval' : f m + d = q := hval
        exact ⟨m, hm, by omega⟩
      have := hpMin (q - d) hq'
      omega

/-- A min-even sequence cannot be eventually constantly the odd priority 1. -/
theorem not_natSeqMinEvenParity_of_eventually_one
    (priority : Nat -> Nat) (N : Nat)
    (heventual : ∀ n, N ≤ n -> priority n = 1) :
    ¬ NatSeqMinEvenParity priority := by
  rintro ⟨p, hpEven, hpSeen, hpMin⟩
  have hone : NatSeqSeenInfinitelyOften priority 1 := by
    intro n
    exact ⟨max n N, Nat.le_max_left _ _, heventual _ (Nat.le_max_right _ _)⟩
  have hpLe : p ≤ 1 := hpMin 1 hone
  have hpZero : p = 0 := by
    rcases hpEven with ⟨k, hk⟩
    omega
  obtain ⟨n, hn, hpriority⟩ := hpSeen N
  rw [hpZero, heventual n hn] at hpriority
  omega

/-- A priority sequence has a unique minimal infinitely-recurring priority. -/
theorem not_natSeqMinEvenParity_and_natSeqMinOddParity
    (s : Nat -> Nat) :
    ¬ (NatSeqMinEvenParity s ∧ NatSeqMinOddParity s) := by
  rintro ⟨⟨p, hpEven, hpSeen, hpMin⟩, ⟨q, hqOdd, hqSeen, hqMin⟩⟩
  have hpq : p = q := le_antisymm (hpMin q hqSeen) (hqMin p hpSeen)
  exact hqOdd (hpq ▸ hpEven)

/--
Halving transfer: a sequence that repeats each entry of `s` twice has the same
infinitely-recurring priorities as `s`.
-/
theorem natSeqSeenInfinitelyOften_halved
    {f s : Nat -> Nat}
    (h : ∀ k : Nat, f k = s (k / 2))
    (p : Nat) :
    NatSeqSeenInfinitelyOften f p ↔ NatSeqSeenInfinitelyOften s p := by
  constructor
  · intro hseen n
    rcases hseen (2 * n) with ⟨k, hk, hfk⟩
    refine ⟨k / 2, by omega, ?_⟩
    rw [← h k]
    exact hfk
  · intro hseen n
    rcases hseen n with ⟨k, hk, hsk⟩
    refine ⟨2 * k, by omega, ?_⟩
    rw [h (2 * k), (by omega : 2 * k / 2 = k)]
    exact hsk

/-- Halving transfer for the min-even parity condition. -/
theorem natSeqMinEvenParity_halved
    {f s : Nat -> Nat}
    (h : ∀ k : Nat, f k = s (k / 2)) :
    NatSeqMinEvenParity f ↔ NatSeqMinEvenParity s := by
  constructor
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    exact ⟨p, hpEven, (natSeqSeenInfinitelyOften_halved h p).mp hpSeen,
      fun q hq => hpMin q ((natSeqSeenInfinitelyOften_halved h q).mpr hq)⟩
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    exact ⟨p, hpEven, (natSeqSeenInfinitelyOften_halved h p).mpr hpSeen,
      fun q hq => hpMin q ((natSeqSeenInfinitelyOften_halved h q).mp hq)⟩

/-- Repeating every priority four times preserves min-even parity. -/
theorem natSeqMinEvenParity_quartered
    {f s : Nat -> Nat}
    (h : ∀ k : Nat, f k = s (k / 4)) :
    NatSeqMinEvenParity f ↔ NatSeqMinEvenParity s := by
  let middle : Nat -> Nat := fun n => s (n / 2)
  have hfirst : ∀ k, f k = middle (k / 2) := by
    intro k
    rw [h]
    simp [middle, Nat.div_div_eq_div_mul]
  exact (natSeqMinEvenParity_halved hfirst).trans
    (natSeqMinEvenParity_halved (f := middle) (s := s) (fun _ => rfl))

/-- Halving transfer for the min-odd parity condition. -/
theorem natSeqMinOddParity_halved
    {f s : Nat -> Nat}
    (h : ∀ k : Nat, f k = s (k / 2)) :
    NatSeqMinOddParity f ↔ NatSeqMinOddParity s := by
  constructor
  · rintro ⟨p, hpOdd, hpSeen, hpMin⟩
    exact ⟨p, hpOdd, (natSeqSeenInfinitelyOften_halved h p).mp hpSeen,
      fun q hq => hpMin q ((natSeqSeenInfinitelyOften_halved h q).mpr hq)⟩
  · rintro ⟨p, hpOdd, hpSeen, hpMin⟩
    exact ⟨p, hpOdd, (natSeqSeenInfinitelyOften_halved h p).mpr hpSeen,
      fun q hq => hpMin q ((natSeqSeenInfinitelyOften_halved h q).mp hq)⟩

/--
The alternating play built from an even-indexed and an odd-indexed position
sequence: position `2 * j` is `e j` and position `2 * j + 1` is `o j`.
-/
def interleavePlay {Position : Type x}
    (e o : Nat -> Position) (k : Nat) : Position :=
  if k % 2 = 0 then e (k / 2) else o (k / 2)

theorem interleavePlay_of_mod_eq_zero {Position : Type x}
    (e o : Nat -> Position) {k : Nat} (hk : k % 2 = 0) :
    interleavePlay e o k = e (k / 2) := by
  unfold interleavePlay
  exact if_pos hk

theorem interleavePlay_of_mod_eq_one {Position : Type x}
    (e o : Nat -> Position) {k : Nat} (hk : k % 2 = 1) :
    interleavePlay e o k = o (k / 2) := by
  unfold interleavePlay
  exact if_neg (by omega)

theorem interleavePlay_zero {Position : Type x}
    (e o : Nat -> Position) :
    interleavePlay e o 0 = e 0 :=
  interleavePlay_of_mod_eq_zero e o rfl

/-- The interleaved play follows a step relation with alternating edges. -/
theorem interleavePlay_play {Position : Type x}
    (step : Position -> Position -> Prop)
    (e o : Nat -> Position)
    (hEven : ∀ j : Nat, step (e j) (o j))
    (hOdd : ∀ j : Nat, step (o j) (e (j + 1))) :
    ∀ k : Nat, step (interleavePlay e o k) (interleavePlay e o (k + 1)) := by
  intro k
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [interleavePlay_of_mod_eq_zero e o hk,
      interleavePlay_of_mod_eq_one e o (by omega : (k + 1) % 2 = 1),
      (by omega : (k + 1) / 2 = k / 2)]
    exact hEven (k / 2)
  · rw [interleavePlay_of_mod_eq_one e o hk,
      interleavePlay_of_mod_eq_zero e o (by omega : (k + 1) % 2 = 0),
      (by omega : (k + 1) / 2 = k / 2 + 1)]
    exact hOdd (k / 2)

/-- The interleaved play repeats each priority of the state sequence twice. -/
theorem interleavePlay_priority {Position : Type x}
    (pri : Position -> Nat) (e o : Nat -> Position) (s : Nat -> Nat)
    (he : ∀ j : Nat, pri (e j) = s j)
    (ho : ∀ j : Nat, pri (o j) = s j) :
    ∀ k : Nat, pri (interleavePlay e o k) = s (k / 2) := by
  intro k
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [interleavePlay_of_mod_eq_zero e o hk]
    exact he (k / 2)
  · rw [interleavePlay_of_mod_eq_one e o hk]
    exact ho (k / 2)

/-- The depth-`n` node along an infinite branch. -/
def branchNode {Branch : Type u} (branch : Nat -> Branch) :
    Nat -> TreeNode Branch
  | 0 => []
  | n + 1 => branchNode branch n ++ [branch n]

/-- The depth-`n` node generated by a node-indexed branch selector. -/
def selectorNode {Branch : Type u} (select : TreeNode Branch -> Branch) :
    Nat -> TreeNode Branch
  | 0 => []
  | n + 1 => selectorNode select n ++ [select (selectorNode select n)]

/-- Selector-generated nodes lie along the branch induced by the selector. -/
theorem selectorNode_eq_branchNode {Branch : Type u}
    (select : TreeNode Branch -> Branch) :
    ∀ n : Nat,
      selectorNode select n =
        branchNode (fun k => select (selectorNode select k)) n
  | 0 => rfl
  | n + 1 => by
      have ih := selectorNode_eq_branchNode select n
      simp only [selectorNode, branchNode]
      rw [← ih]

/--
An input-free parity tree automaton given by an explicit transition relation
and priority map.  Acceptance is run-based: a run assigns a state to every
node, respects `delta`, and satisfies the min-even parity condition on every
infinite branch.  This is the concrete class for which the rational-run
interface of `InputFreeParityTreeAutomaton` is a theorem, not an assumption.
-/
structure RunParityTreeAutomaton (Branch : Type u) (Alphabet : Type v) where
  State : Type w
  stateFinite : Fintype State
  initial : State
  delta : State -> Alphabet -> (Branch -> State) -> Prop
  priority : State -> Nat

attribute [instance] RunParityTreeAutomaton.stateFinite

/-- Explicit finite-direction/finite-label specialization.  The semantic
automaton remains `toRunAutomaton`; these two fields are exactly the extra
hypotheses used by the checked finite emptiness-game extraction. -/
structure FiniteRunParityTreeAutomaton
    (Branch : Type u) (Alphabet : Type v)
    extends RunParityTreeAutomaton.{u, v, w} Branch Alphabet where
  branchFinite : Fintype Branch
  alphabetFinite : Fintype Alphabet

attribute [instance] FiniteRunParityTreeAutomaton.branchFinite
attribute [instance] FiniteRunParityTreeAutomaton.alphabetFinite

namespace FiniteRunParityTreeAutomaton

/-- Forget only the external finiteness witnesses. -/
def toRunAutomaton
    {Branch : Type u} {Alphabet : Type v}
    (A : FiniteRunParityTreeAutomaton.{u, v, w} Branch Alphabet) :
    RunParityTreeAutomaton.{u, v, w} Branch Alphabet :=
  A.toRunParityTreeAutomaton

end FiniteRunParityTreeAutomaton

namespace RunParityTreeAutomaton

variable {Branch : Type u} {Alphabet : Type v}

/-- A run starts at `initial` and respects `delta` at every node. -/
def IsRun (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (tree : LabeledTree Branch Alphabet)
    (run : TreeNode Branch -> A.State) : Prop :=
  run [] = A.initial ∧
    ∀ node : TreeNode Branch,
      A.delta (run node) (tree node) (fun b => run (node ++ [b]))

/-- A run is accepting if every infinite branch satisfies min-even parity. -/
def IsAcceptingRun (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (tree : LabeledTree Branch Alphabet)
    (run : TreeNode Branch -> A.State) : Prop :=
  A.IsRun tree run ∧
    ∀ branch : Nat -> Branch,
      NatSeqMinEvenParity (fun n => A.priority (run (branchNode branch n)))

/-- Run-based tree acceptance. -/
def acceptsTree (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (tree : LabeledTree Branch Alphabet) : Prop :=
  ∃ run : TreeNode Branch -> A.State, A.IsAcceptingRun tree run

/-- A run is rational in the paper's transition sense: equal run states use
the same node label and the same complete successor assignment.  This
definition is meaningful without any finiteness assumption on directions or
labels; finiteness comes solely from the automaton state space. -/
def IsTransitionRationalRun
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (tree : LabeledTree Branch Alphabet)
    (run : TreeNode Branch -> A.State) : Prop :=
  A.IsAcceptingRun tree run ∧
    ∀ u v : TreeNode Branch, run u = run v ->
      tree u = tree v ∧
        (fun b => run (u ++ [b])) = fun b => run (v ++ [b])

/-- The automaton admits an accepting rational run. -/
def AcceptsTransitionRationalRun
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet) : Prop :=
  ∃ tree : LabeledTree Branch Alphabet,
    ∃ run : TreeNode Branch -> A.State,
      A.IsTransitionRationalRun tree run

/- From here through the emptiness-game extraction, directions and labels are
finite.  The run semantics above intentionally has no such restriction. -/
section FiniteBranchAlphabet

variable [Fintype Branch] [Fintype Alphabet]

/--
Positions of the emptiness game.  `some (Sum.inl q)` is an automaton position
at state `q`, `some (Sum.inr (q, a, f))` is a pathfinder position after the
automaton has chosen label `a` and successor assignment `f` at `q`, and `none`
is the losing sink for the automaton player.
-/
abbrev GamePosition (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet) :=
  Option (A.State ⊕ A.State × Alphabet × (Branch -> A.State))

/-- The automaton player is Even; the pathfinder is Odd. -/
def gameOwner (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet) :
    GamePosition A -> ParityPlayer
  | some (Sum.inr _) => ParityPlayer.odd
  | _ => ParityPlayer.even

/--
Game priorities repeat the source-state priority on choice positions; the
sink carries the odd priority `1`, so a play falling into the sink is lost by
the automaton player.
-/
def gamePriority (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet) :
    GamePosition A -> Nat
  | none => 1
  | some (Sum.inl q) => A.priority q
  | some (Sum.inr (q, _, _)) => A.priority q

/--
Edges of the emptiness game: the automaton picks a `delta`-allowed label and
successor assignment (or falls into the sink if none exists), the pathfinder
picks a branch direction, and the sink loops.
-/
def gameStep (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet) :
    GamePosition A -> GamePosition A -> Prop
  | none, target => target = none
  | some (Sum.inl q), target =>
      (∃ a : Alphabet, ∃ f : Branch -> A.State,
        A.delta q a f ∧ target = some (Sum.inr (q, a, f))) ∨
        ((¬ ∃ a : Alphabet, ∃ f : Branch -> A.State, A.delta q a f) ∧
          target = none)
  | some (Sum.inr (_, _, f)), target =>
      ∃ b : Branch, target = some (Sum.inl (f b))

theorem gameStep_total (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    [Nonempty Branch] :
    ∀ position : GamePosition A,
      ∃ next : GamePosition A, gameStep A position next := by
  classical
  intro position
  match position with
  | none => exact ⟨none, rfl⟩
  | some (Sum.inl q) =>
      by_cases hchoice :
          ∃ a : Alphabet, ∃ f : Branch -> A.State, A.delta q a f
      · rcases hchoice with ⟨a, f, hdelta⟩
        exact ⟨some (Sum.inr (q, a, f)), Or.inl ⟨a, f, hdelta, rfl⟩⟩
      · exact ⟨none, Or.inr ⟨hchoice, rfl⟩⟩
  | some (Sum.inr (q, a, f)) =>
      exact ⟨some (Sum.inl (f (Classical.arbitrary Branch))),
        ⟨Classical.arbitrary Branch, rfl⟩⟩

/-- The finite emptiness parity game of a run-based automaton. -/
def emptinessGame (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    [Nonempty Branch] :
    CountableParityGame.{max u v w} where
  Position := GamePosition A
  positionCountable := inferInstance
  owner := gameOwner A
  step := gameStep A
  step_total := gameStep_total A
  priority := gamePriority A
  priority_finite := Set.finite_range (gamePriority A)

/-- The automaton position carrying the run state at a node. -/
def runStatePosition (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (run : TreeNode Branch -> A.State) (node : TreeNode Branch) :
    GamePosition A :=
  some (Sum.inl (run node))

/-- The transition-choice position offered by a run at a node. -/
def runChoicePosition (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (tree : LabeledTree Branch Alphabet)
    (run : TreeNode Branch -> A.State) (node : TreeNode Branch) :
    GamePosition A :=
  some (Sum.inr (run node, tree node, fun b => run (node ++ [b])))

/--
Soundness half of the emptiness game: if the automaton accepts some tree, the
pathfinder does not win the game positionally from the initial state.  A
positional pathfinder strategy played against an accepting run would trace an
infinite branch whose state priorities are simultaneously min-odd (pathfinder
wins the play) and min-even (the run is accepting).
-/
theorem not_positionalWinningRegion_odd_of_accepts
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet) [Nonempty Branch]
    {tree : LabeledTree Branch Alphabet}
    (haccepts : A.acceptsTree tree) :
    some (Sum.inl A.initial) ∉
      (emptinessGame A).PositionalWinningRegion ParityPlayer.odd := by
  classical
  rintro ⟨τ, hτ⟩
  rcases haccepts with ⟨run, ⟨hinit, hdelta⟩, hbranch⟩
  have hlegalChoice :
      ∀ node : TreeNode Branch,
        ∃ b : Branch,
          τ.move (runChoicePosition A tree run node) =
            some (Sum.inl (run (node ++ [b]))) := by
    intro node
    have hlegal :
        gameStep A (runChoicePosition A tree run node)
          (τ.move (runChoicePosition A tree run node)) :=
      τ.legal (runChoicePosition A tree run node) rfl
    rcases hlegal with ⟨b, hb⟩
    exact ⟨b, hb⟩
  choose select hselect using hlegalChoice
  have hplay :
      (emptinessGame A).Play
        (interleavePlay
          (fun j => runStatePosition A run (selectorNode select j))
          (fun j => runChoicePosition A tree run (selectorNode select j))) := by
    refine interleavePlay_play _ _ _ ?_ ?_
    · intro j
      exact Or.inl
        ⟨tree (selectorNode select j),
          fun b => run (selectorNode select j ++ [b]),
          hdelta (selectorNode select j), rfl⟩
    · intro j
      exact ⟨select (selectorNode select j), rfl⟩
  have hstart :
      interleavePlay
          (fun j => runStatePosition A run (selectorNode select j))
          (fun j => runChoicePosition A tree run (selectorNode select j)) 0 =
        some (Sum.inl A.initial) := by
    rw [interleavePlay_zero]
    simp [runStatePosition, selectorNode, hinit]
  have hconsistent :
      CountableParityGame.PositionalStrategy.Consistent
        (G := emptinessGame A) τ
        (interleavePlay
          (fun j => runStatePosition A run (selectorNode select j))
          (fun j => runChoicePosition A tree run (selectorNode select j))) := by
    intro k howner
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · rw [interleavePlay_of_mod_eq_zero _ _ hk] at howner
      simp [emptinessGame, gameOwner, runStatePosition] at howner
    · rw [interleavePlay_of_mod_eq_one _ _ hk,
        interleavePlay_of_mod_eq_zero _ _ (by omega : (k + 1) % 2 = 0),
        (by omega : (k + 1) / 2 = k / 2 + 1)]
      exact (hselect (selectorNode select (k / 2))).symm
  have hwins :
      NatSeqMinOddParity
        (fun k =>
          gamePriority A
            (interleavePlay
              (fun j => runStatePosition A run (selectorNode select j))
              (fun j => runChoicePosition A tree run (selectorNode select j))
              k)) :=
    hτ _ ⟨hstart, hplay⟩ hconsistent
  have hpri :
      ∀ k : Nat,
        gamePriority A
            (interleavePlay
              (fun j => runStatePosition A run (selectorNode select j))
              (fun j => runChoicePosition A tree run (selectorNode select j))
              k) =
          A.priority (run (selectorNode select (k / 2))) :=
    interleavePlay_priority (gamePriority A) _ _
      (fun n => A.priority (run (selectorNode select n)))
      (fun j => rfl) (fun j => rfl)
  have hodd :
      NatSeqMinOddParity
        (fun n => A.priority (run (selectorNode select n))) :=
    (natSeqMinOddParity_halved hpri).mp hwins
  have heven :
      NatSeqMinEvenParity
        (fun n => A.priority (run (selectorNode select n))) := by
    have hb := hbranch (fun k => select (selectorNode select k))
    have hnodes :
        (fun n =>
            A.priority
              (run (branchNode (fun k => select (selectorNode select k)) n))) =
          fun n => A.priority (run (selectorNode select n)) := by
      funext n
      exact congrArg (fun node => A.priority (run node))
        (selectorNode_eq_branchNode select n).symm
    rw [hnodes] at hb
    exact hb
  exact not_natSeqMinEvenParity_and_natSeqMinOddParity _ ⟨heven, hodd⟩

section EvenExtraction

variable (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
variable [Nonempty Branch]
variable (σ : (emptinessGame A).PositionalStrategy ParityPlayer.even)
variable (dflt : Alphabet)

attribute [local instance] Classical.propDecidable

/-- The Even strategy selects a `delta`-allowed transition at state `q`. -/
def GoodState (q : A.State) : Prop :=
  ∃ a : Alphabet, ∃ f : Branch -> A.State,
    A.delta q a f ∧
      σ.move (some (Sum.inl q)) = some (Sum.inr (q, a, f))

/-- Legality dichotomy at an automaton position. -/
theorem goodState_or_stuck (q : A.State) :
    GoodState A σ q ∨
      ((¬ ∃ a : Alphabet, ∃ f : Branch -> A.State, A.delta q a f) ∧
        σ.move (some (Sum.inl q)) = none) := by
  have hlegal :
      gameStep A (some (Sum.inl q)) (σ.move (some (Sum.inl q))) :=
    σ.legal (some (Sum.inl q)) rfl
  rcases hlegal with ⟨a, f, hdelta, hmove⟩ | ⟨hstuck, hmove⟩
  · exact Or.inl ⟨a, f, hdelta, hmove⟩
  · exact Or.inr ⟨hstuck, hmove⟩

/-- The Even strategy is forced to loop at the sink. -/
theorem sigma_move_none : σ.move none = none :=
  σ.legal none rfl

/-- The label chosen by the Even strategy at a good state. -/
noncomputable def chosenLabel (q : A.State) : Alphabet :=
  if h : GoodState A σ q then h.choose else dflt

/-- The successor assignment chosen by the Even strategy at a good state. -/
noncomputable def chosenChildren (q : A.State) : Branch -> A.State :=
  if h : GoodState A σ q then h.choose_spec.choose else fun _ => q

/-- The chosen label and successors are `delta`-allowed and follow `σ`. -/
theorem chosenLabel_children_spec {q : A.State} (h : GoodState A σ q) :
    A.delta q (chosenLabel A σ dflt q) (chosenChildren A σ q) ∧
      σ.move (some (Sum.inl q)) =
        some (Sum.inr (q, chosenLabel A σ dflt q, chosenChildren A σ q)) := by
  simp only [chosenLabel, chosenChildren, dif_pos h]
  exact h.choose_spec.choose_spec

/-- The finite control reached by the extracted controller at a node. -/
noncomputable def extractedControl (node : TreeNode Branch) : A.State :=
  node.foldl (chosenChildren A σ) A.initial

@[simp]
theorem extractedControl_nil : extractedControl A σ [] = A.initial :=
  rfl

theorem extractedControl_append (node : TreeNode Branch) (b : Branch) :
    extractedControl A σ (node ++ [b]) =
      chosenChildren A σ (extractedControl A σ node) b := by
  simp [extractedControl, List.foldl_append]

/-- The automaton position at the extracted control of a node. -/
noncomputable def controlStatePosition (node : TreeNode Branch) :
    GamePosition A :=
  some (Sum.inl (extractedControl A σ node))

/-- The choice position selected by `σ` at the extracted control of a node. -/
noncomputable def controlChoicePosition (node : TreeNode Branch) :
    GamePosition A :=
  some (Sum.inr
    (extractedControl A σ node,
      chosenLabel A σ dflt (extractedControl A σ node),
      chosenChildren A σ (extractedControl A σ node)))

/--
Core reachability lemma: if `σ` wins from the initial automaton position and
all proper prefixes of a node have good extracted controls, then the node's
extracted control is good.  Otherwise the play following the controller along
the node and then falling into the sink would be a `σ`-consistent losing play.
-/
theorem goodState_extractedControl_of_prefix
    (dfltLabel : Alphabet)
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := emptinessGame A) σ (some (Sum.inl A.initial)))
    (w : TreeNode Branch)
    (hprefix :
      ∀ j : Nat, j < w.length ->
        GoodState A σ (extractedControl A σ (w.take j))) :
    GoodState A σ (extractedControl A σ w) := by
  classical
  by_contra hbad
  rcases goodState_or_stuck A σ (extractedControl A σ w) with hgood | ⟨hstuck, hmove⟩
  · exact hbad hgood
  set m := w.length with hm
  set path : Nat -> GamePosition A :=
    fun k =>
      if k ≤ 2 * m then
        interleavePlay
          (fun j => controlStatePosition A σ (w.take j))
          (fun j => controlChoicePosition A σ dfltLabel (w.take j)) k
      else none
    with hpathdef
  have hpathIn :
      ∀ k : Nat, k ≤ 2 * m ->
        path k =
          interleavePlay
            (fun j => controlStatePosition A σ (w.take j))
            (fun j => controlChoicePosition A σ dfltLabel (w.take j)) k := by
    intro k hk
    simp only [hpathdef]
    exact if_pos hk
  have hpathOut : ∀ k : Nat, 2 * m < k -> path k = none := by
    intro k hk
    simp only [hpathdef]
    exact if_neg (by omega)
  have hpathEven :
      ∀ j : Nat, j ≤ m ->
        path (2 * j) = controlStatePosition A σ (w.take j) := by
    intro j hj
    rw [hpathIn (2 * j) (by omega),
      interleavePlay_of_mod_eq_zero _ _ (by omega : 2 * j % 2 = 0),
      (by omega : 2 * j / 2 = j)]
  have hpathOdd :
      ∀ j : Nat, j < m ->
        path (2 * j + 1) = controlChoicePosition A σ dfltLabel (w.take j) := by
    intro j hj
    rw [hpathIn (2 * j + 1) (by omega),
      interleavePlay_of_mod_eq_one _ _ (by omega : (2 * j + 1) % 2 = 1),
      (by omega : (2 * j + 1) / 2 = j)]
  have htakeFull : w.take m = w := by
    rw [hm]
    exact List.take_length
  have hplay : (emptinessGame A).Play path := by
    intro k
    rcases lt_trichotomy k (2 * m) with hklt | hkeq | hkgt
    · rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · obtain ⟨j, rfl⟩ : ∃ j : Nat, k = 2 * j := ⟨k / 2, by omega⟩
        have hj : j < m := by omega
        rw [hpathEven j (by omega), hpathOdd j hj]
        exact Or.inl
          ⟨chosenLabel A σ dfltLabel (extractedControl A σ (w.take j)),
            chosenChildren A σ (extractedControl A σ (w.take j)),
            (chosenLabel_children_spec A σ dfltLabel (hprefix j hj)).1, rfl⟩
      · obtain ⟨j, rfl⟩ : ∃ j : Nat, k = 2 * j + 1 := ⟨k / 2, by omega⟩
        have hj : j < m := by omega
        have hjlen : j < w.length := by omega
        rw [hpathOdd j hj, (by omega : 2 * j + 1 + 1 = 2 * (j + 1)),
          hpathEven (j + 1) (by omega)]
        refine ⟨w[j], ?_⟩
        have htake : w.take (j + 1) = w.take j ++ [w[j]] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hjlen]
          rfl
        show some (Sum.inl (extractedControl A σ (w.take (j + 1)))) =
          some (Sum.inl
            (chosenChildren A σ (extractedControl A σ (w.take j)) w[j]))
        rw [htake, extractedControl_append]
    · subst hkeq
      rw [hpathEven m le_rfl, htakeFull, hpathOut (2 * m + 1) (by omega)]
      exact Or.inr ⟨hstuck, rfl⟩
    · rw [hpathOut k (by omega), hpathOut (k + 1) (by omega)]
      rfl
  have hstart : path 0 = some (Sum.inl A.initial) := by
    have h0 := hpathEven 0 (by omega)
    simpa [controlStatePosition] using h0
  have hconsistent :
      CountableParityGame.PositionalStrategy.Consistent
        (G := emptinessGame A) σ path := by
    intro k howner
    rcases lt_trichotomy k (2 * m) with hklt | hkeq | hkgt
    · rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · obtain ⟨j, rfl⟩ : ∃ j : Nat, k = 2 * j := ⟨k / 2, by omega⟩
        have hj : j < m := by omega
        rw [hpathOdd j hj, hpathEven j (by omega)]
        exact ((chosenLabel_children_spec A σ dfltLabel (hprefix j hj)).2).symm
      · obtain ⟨j, rfl⟩ : ∃ j : Nat, k = 2 * j + 1 := ⟨k / 2, by omega⟩
        have hj : j < m := by omega
        rw [hpathOdd j hj] at howner
        simp [emptinessGame, gameOwner, controlChoicePosition] at howner
    · subst hkeq
      rw [hpathOut (2 * m + 1) (by omega), hpathEven m le_rfl, htakeFull]
      exact hmove.symm
    · rw [hpathOut k (by omega), hpathOut (k + 1) (by omega)]
      exact (sigma_move_none A σ).symm
  have hminEven :
      NatSeqMinEvenParity (fun k => gamePriority A (path k)) :=
    hwin path ⟨hstart, hplay⟩ hconsistent
  rcases hminEven with ⟨p, hpEven, hpSeen, _⟩
  rcases hpSeen (2 * m + 1) with ⟨k, hk, hpk⟩
  have hpk' : gamePriority A (path k) = p := hpk
  rw [hpathOut k (by omega)] at hpk'
  have hp1 : p = 1 := by simpa [gamePriority] using hpk'.symm
  rcases hpEven with ⟨half, hhalf⟩
  omega

/-- All controller-reachable states are good. -/
theorem goodState_extractedControl
    (dfltLabel : Alphabet)
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := emptinessGame A) σ (some (Sum.inl A.initial)))
    (w : TreeNode Branch) :
    GoodState A σ (extractedControl A σ w) := by
  suffices h :
      ∀ n : Nat, ∀ w' : TreeNode Branch,
        w'.length ≤ n -> GoodState A σ (extractedControl A σ w') from
    h w.length w le_rfl
  intro n
  induction n with
  | zero =>
      intro w' hw'
      refine goodState_extractedControl_of_prefix A σ dfltLabel hwin w' ?_
      intro j hj
      exact absurd hj (by omega)
  | succ n ih =>
      intro w' hw'
      refine goodState_extractedControl_of_prefix A σ dfltLabel hwin w' ?_
      intro j hj
      refine ih (w'.take j) ?_
      rw [List.length_take]
      omega

/-- The transition-rational tree extracted from an Even positional strategy. -/
noncomputable def extractedTree :
    TransitionRationalTree.{u, v, w} Branch Alphabet where
  Control := A.State
  controlFinite := A.stateFinite
  initial := A.initial
  step := chosenChildren A σ
  labelOf := chosenLabel A σ dflt

/-- The extracted control itself is an accepting run of the generated tree. -/
theorem isAcceptingRun_extractedControl
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := emptinessGame A) σ (some (Sum.inl A.initial))) :
    A.IsAcceptingRun (extractedTree A σ dflt).labeledTree
      (extractedControl A σ) := by
  have hall := goodState_extractedControl A σ dflt hwin
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro node
    have hfun :
        (fun b => extractedControl A σ (node ++ [b])) =
          chosenChildren A σ (extractedControl A σ node) :=
      funext fun b => extractedControl_append A σ node b
    rw [hfun]
    exact (chosenLabel_children_spec A σ dflt (hall node)).1
  · intro branch
    have hplay :
        (emptinessGame A).Play
          (interleavePlay
            (fun j => controlStatePosition A σ (branchNode branch j))
            (fun j => controlChoicePosition A σ dflt (branchNode branch j))) := by
      refine interleavePlay_play _ _ _ ?_ ?_
      · intro j
        exact Or.inl
          ⟨chosenLabel A σ dflt (extractedControl A σ (branchNode branch j)),
            chosenChildren A σ (extractedControl A σ (branchNode branch j)),
            (chosenLabel_children_spec A σ dflt (hall (branchNode branch j))).1,
            rfl⟩
      · intro j
        refine ⟨branch j, ?_⟩
        show some (Sum.inl
            (extractedControl A σ (branchNode branch j ++ [branch j]))) =
          some (Sum.inl
            (chosenChildren A σ (extractedControl A σ (branchNode branch j))
              (branch j)))
        rw [extractedControl_append]
    have hstart :
        interleavePlay
            (fun j => controlStatePosition A σ (branchNode branch j))
            (fun j => controlChoicePosition A σ dflt (branchNode branch j)) 0 =
          some (Sum.inl A.initial) := by
      rw [interleavePlay_zero]
      simp [controlStatePosition, branchNode]
    have hconsistent :
        CountableParityGame.PositionalStrategy.Consistent
          (G := emptinessGame A) σ
          (interleavePlay
            (fun j => controlStatePosition A σ (branchNode branch j))
            (fun j => controlChoicePosition A σ dflt (branchNode branch j))) := by
      intro k howner
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [interleavePlay_of_mod_eq_zero _ _ hk,
          interleavePlay_of_mod_eq_one _ _ (by omega : (k + 1) % 2 = 1),
          (by omega : (k + 1) / 2 = k / 2)]
        exact
          ((chosenLabel_children_spec A σ dflt
            (hall (branchNode branch (k / 2)))).2).symm
      · rw [interleavePlay_of_mod_eq_one _ _ hk] at howner
        simp [emptinessGame, gameOwner, controlChoicePosition] at howner
    have hwins :
        NatSeqMinEvenParity
          (fun k =>
            gamePriority A
              (interleavePlay
                (fun j => controlStatePosition A σ (branchNode branch j))
                (fun j => controlChoicePosition A σ dflt (branchNode branch j))
                k)) :=
      hwin _ ⟨hstart, hplay⟩ hconsistent
    have hpri :
        ∀ k : Nat,
          gamePriority A
              (interleavePlay
                (fun j => controlStatePosition A σ (branchNode branch j))
                (fun j => controlChoicePosition A σ dflt (branchNode branch j))
                k) =
            A.priority (extractedControl A σ (branchNode branch (k / 2))) :=
      interleavePlay_priority (gamePriority A) _ _
        (fun n => A.priority (extractedControl A σ (branchNode branch n)))
        (fun j => rfl) (fun j => rfl)
    exact (natSeqMinEvenParity_halved hpri).mp hwins

/-- The automaton accepts the tree generated by the extracted controller. -/
theorem acceptsTree_extractedTree
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := emptinessGame A) σ (some (Sum.inl A.initial))) :
    A.acceptsTree (extractedTree A σ dflt).labeledTree :=
  ⟨extractedControl A σ, isAcceptingRun_extractedControl A σ dflt hwin⟩

/-- The extracted run is rational in the transition sense: its current state
determines both the selected label and its complete successor assignment. -/
theorem isTransitionRationalRun_extractedControl
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := emptinessGame A) σ (some (Sum.inl A.initial))) :
    A.IsTransitionRationalRun (extractedTree A σ dflt).labeledTree
      (extractedControl A σ) := by
  refine ⟨isAcceptingRun_extractedControl A σ dflt hwin, ?_⟩
  intro u v huv
  constructor
  · exact congrArg (chosenLabel A σ dflt) huv
  · funext b
    rw [extractedControl_append, extractedControl_append, huv]

end EvenExtraction

/--
Rabin basis theorem for run-based parity tree automata: an automaton that
accepts some tree accepts a transition-rational tree.  The proof applies the
checked Zielonka positional determinacy to the finite emptiness game; the
degenerate branch-free case is handled directly.
-/
theorem exists_transitionRational_accepted
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (haccepts : ∃ tree : LabeledTree Branch Alphabet, A.acceptsTree tree) :
    ∃ rationalTree : TransitionRationalTree.{u, v, w} Branch Alphabet,
      A.acceptsTree rationalTree.labeledTree := by
  classical
  rcases haccepts with ⟨tree, htree⟩
  rcases isEmpty_or_nonempty Branch with hempty | hnonempty
  · rcases htree with ⟨run, ⟨hinit, hdelta⟩, _⟩
    refine
      ⟨{ Control := PUnit.{w + 1}
         controlFinite := inferInstance
         initial := PUnit.unit
         step := fun control _ => control
         labelOf := fun _ => tree [] }, ?_⟩
    refine ⟨fun _ => A.initial, ⟨rfl, ?_⟩, ?_⟩
    · intro node
      have hnode : node = [] := by
        cases node with
        | nil => rfl
        | cons b _ => exact isEmptyElim b
      subst hnode
      show A.delta A.initial (tree []) fun _ => A.initial
      have hd := hdelta []
      rw [hinit] at hd
      have hchild :
          (fun b : Branch => run ([] ++ [b])) = fun _ : Branch => A.initial :=
        funext fun b => isEmptyElim b
      rw [hchild] at hd
      exact hd
    · intro branch
      exact isEmptyElim (branch 0)
  · rcases (emptinessGame A).positionalGameDetermined
        (some (Sum.inl A.initial)) with heven | hodd
    · rcases heven with ⟨σ, hwin⟩
      exact ⟨extractedTree A σ (tree []),
        acceptsTree_extractedTree A σ (tree []) hwin⟩
    · exact absurd hodd (not_positionalWinningRegion_odd_of_accepts A htree)

/-- Finite-branch/finite-alphabet rational-*run* basis.  Unlike the older
tree-level interface, this exposes the paper's exact invariant: equal run
states select equal complete transitions. -/
theorem exists_transitionRationalRun_accepted
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (haccepts : ∃ tree : LabeledTree Branch Alphabet, A.acceptsTree tree) :
    A.AcceptsTransitionRationalRun := by
  classical
  rcases haccepts with ⟨tree, htree⟩
  rcases isEmpty_or_nonempty Branch with hempty | hnonempty
  · rcases htree with ⟨run, hrun⟩
    refine ⟨tree, run, hrun, ?_⟩
    intro u v _
    have hu : u = [] := by
      cases u with
      | nil => rfl
      | cons b _ => exact isEmptyElim b
    have hv : v = [] := by
      cases v with
      | nil => rfl
      | cons b _ => exact isEmptyElim b
    subst hu
    subst hv
    exact ⟨rfl, rfl⟩
  · rcases (emptinessGame A).positionalGameDetermined
        (some (Sum.inl A.initial)) with heven | hodd
    · rcases heven with ⟨σ, hwin⟩
      exact ⟨(extractedTree A σ (tree [])).labeledTree,
        extractedControl A σ,
        isTransitionRationalRun_extractedControl A σ (tree []) hwin⟩
    · exact absurd hodd (not_positionalWinningRegion_odd_of_accepts A htree)

/--
Package a run-based automaton as an interface automaton whose `rationality`
and `transitionRationality` fields are proved.  Concrete block-game automata
built through this constructor satisfy the rational-run interface of
`ThmBerardfinitememory` unconditionally.
-/
def toInputFree (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet) :
    InputFreeParityTreeAutomaton.{u, v, w} Branch Alphabet where
  alphabetFinite := inferInstance
  branchFinite := inferInstance
  State := A.State
  stateFinite := A.stateFinite
  acceptsTree := A.acceptsTree
  acceptsRationalTree := fun rationalTree =>
    ∃ transitionTree : TransitionRationalTree.{u, v, w} Branch Alphabet,
      transitionTree.toRationalTree = rationalTree ∧
        A.acceptsTree transitionTree.labeledTree
  rationality := by
    intro haccepts
    rcases A.exists_transitionRational_accepted haccepts with ⟨t, ht⟩
    exact ⟨t.toRationalTree, t, rfl, ht⟩
  transitionRationality := fun haccepts =>
    A.exists_transitionRational_accepted haccepts

@[simp]
theorem toInputFree_acceptsTree
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet) :
    A.toInputFree.acceptsTree = A.acceptsTree :=
  rfl

end FiniteBranchAlphabet

end RunParityTreeAutomaton

end DistributedSynthesis
