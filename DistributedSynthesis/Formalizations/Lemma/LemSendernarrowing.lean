/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemBlocktreecorrespondence

/-!
# Sender-side narrowing of one-directional blocks

This file formalizes Lemma `lem:sendernarrowing` from `paper.tex`.

`LemBlocktreecorrespondence` reduced block realizability to the existence of
a sender-oblivious winning tree over the product branching `RIn × SIn`.  The
obliviousness constraint is not branchwise, so the Rabin extraction applied
to the product branching need not return an implementable controller.  This
file removes the constraint by narrowing to the sender branching `SIn`.

A narrowed tree carries `NarrowedBlockLabel` labels: the sender response
`SIn -> SOut` and a receiver table `M.State -> RIn × SIn -> ROut` indexed by
the objective-monitor state, which is a sufficient statistic for the parity
objective.  The semantics is universal over the receiver-side inputs: along
every full environment word, the induced monitor thread must satisfy the
min-even parity condition (`NarrowedAllThreadsWin`).

The two directions of the narrowing correspondence are proved:

* soundness (`senderOblivious_narrowedInducedTree`,
  `narrowedInducedTree_winningTree_of_allThreadsWin`): a narrowed tree with
  all threads winning induces a sender-oblivious winning tree over the
  product branching;
* completeness (`exists_narrowed_of_senderOblivious_winningTree`): from a
  sender-oblivious winning tree, the receiver is folded to a function of the
  sender word, the monitor state, and the current move.  The folding is the
  positional determinacy of a perfect-information countable parity game
  whose positions are sender-word/monitor-state pairs — the checked Zielonka
  theorem — applied to the game in which the sender part of the tree is
  fixed.  No surgery on the tree and no alternating tree automata are used.

The only remaining external ingredient is branchwise determinization of the
universal thread condition (`NarrowedThreadDPACertificate`): a deterministic
block monitor over the sender branching whose winning trees are exactly the
narrowed trees with all threads winning.  This is the universal-parity word
determinization supplied by the alternation-removal backend.  Given such a
certificate, `exists_implementable_controller_of_block_realizable` closes
the loop: block realizability yields a transition-rational controller over
the sender branching whose readback receiver/sender pair is winning and
finite-state — the sender reads its own word through the finite control,
the receiver reads the finite control at its sender word together with the
monitor state.
-/

namespace DistributedSynthesis

universe u v x y w z

section SenderNarrowing

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}

/--
A narrowed block label: the sender response to its own current input, and a
receiver table indexed by the objective-monitor state and the full current
move.
-/
abbrev NarrowedBlockLabel (RIn : Type u) (SIn : Type v)
    (ROut : Type x) (SOut : Type y) (Q : Type w) :=
  (SIn -> SOut) × (Q -> RIn × SIn -> ROut)

variable (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

/-- The realized record of one narrowed round at monitor state `q`. -/
def narrowedRecord
    (label : NarrowedBlockLabel RIn SIn ROut SOut M.State)
    (q : M.State) (move : RIn × SIn) :
    RealizedBlockRound RIn SIn ROut SOut :=
  (move, label.2 q move, label.1 move.2)

/--
The monitor state threaded along a full environment prefix under a narrowed
tree, tracking the sender word and the monitor state.
-/
def narrowedControlAux
    (narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State)) :
    List SIn -> M.State -> TreeNode (RIn × SIn) -> M.State
  | _, q, [] => q
  | word, q, move :: rest =>
      narrowedControlAux narrowed (word ++ [move.2])
        (M.step q (narrowedRecord M (narrowed word) q move)) rest

/-- The monitor state of the narrowed semantics at a full node. -/
def narrowedControl
    (narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (node : TreeNode (RIn × SIn)) : M.State :=
  narrowedControlAux M narrowed [] M.initial node

theorem senderWord_append (node : TreeNode (RIn × SIn)) (move : RIn × SIn) :
    senderWord (node ++ [move]) = senderWord node ++ [move.2] := by
  simp [senderWord]

theorem narrowedControlAux_append
    (narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State)) :
    ∀ (node : TreeNode (RIn × SIn)) (word : List SIn) (q : M.State)
      (move : RIn × SIn),
      narrowedControlAux M narrowed word q (node ++ [move]) =
        M.step (narrowedControlAux M narrowed word q node)
          (narrowedRecord M (narrowed (word ++ senderWord node))
            (narrowedControlAux M narrowed word q node) move)
  | [], word, q, move => by
      simp [narrowedControlAux, senderWord]
  | first :: rest, word, q, move => by
      show narrowedControlAux M narrowed (word ++ [first.2])
          (M.step q (narrowedRecord M (narrowed word) q first)) (rest ++ [move]) = _
      rw [narrowedControlAux_append narrowed rest]
      have hword :
          word ++ [first.2] ++ senderWord rest =
            word ++ senderWord (first :: rest) := by
        simp [senderWord]
      rw [hword]
      rfl

/-- One-step law of the narrowed monitor state at a full node. -/
theorem narrowedControl_append
    (narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (node : TreeNode (RIn × SIn)) (move : RIn × SIn) :
    narrowedControl M narrowed (node ++ [move]) =
      M.step (narrowedControl M narrowed node)
        (narrowedRecord M (narrowed (senderWord node))
          (narrowedControl M narrowed node) move) := by
  have h := narrowedControlAux_append M narrowed node [] M.initial move
  simpa [narrowedControl] using h

/-- The thread state along a full environment word. -/
def narrowedThreadState
    (narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (env : Nat -> RIn × SIn) (n : Nat) : M.State :=
  narrowedControl M narrowed (branchNode env n)

/--
The universal thread semantics of a narrowed tree: along every full
environment word the induced monitor thread satisfies min-even parity.
-/
def NarrowedAllThreadsWin
    (narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State)) :
    Prop :=
  ∀ env : Nat -> RIn × SIn,
    NatSeqMinEvenParity
      (fun n => M.priority (narrowedThreadState M narrowed env n))

/--
The full product-branching tree induced by a narrowed tree: at a full node,
the receiver plays the table at the current narrowed monitor state, and the
sender plays the narrowed sender response of the sender word.
-/
def narrowedInducedTree
    (narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State)) :
    LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut) :=
  fun node =>
    (fun move =>
        (narrowed (senderWord node)).2 (narrowedControl M narrowed node) move,
      (narrowed (senderWord node)).1)

/-- Induced trees are sender-oblivious. -/
theorem senderOblivious_narrowedInducedTree
    (narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State)) :
    SenderOblivious (narrowedInducedTree M narrowed) := by
  intro left right h
  simp [narrowedInducedTree, h]

section SoundnessMonitor

variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

/-- The lifted-monitor control of the induced tree is the narrowed control. -/
theorem lift_control_narrowedInducedTree
    (narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (node : TreeNode (RIn × SIn)) :
    M.lift.control (narrowedInducedTree M narrowed) node =
      narrowedControl M narrowed node := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node move ih =>
      rw [M.lift.control_append (narrowedInducedTree M narrowed) node move, ih,
        narrowedControl_append M narrowed node move]
      rfl

/-- Soundness: all threads winning makes the induced tree a winning tree. -/
theorem narrowedInducedTree_winningTree_of_allThreadsWin
    {narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State)}
    (hthreads : NarrowedAllThreadsWin M narrowed) :
    M.lift.WinningTree (narrowedInducedTree M narrowed) := by
  intro env
  have h := hthreads env
  have heq :
      (fun n =>
          M.lift.priority
            (M.lift.control (narrowedInducedTree M narrowed)
              (branchNode env n))) =
        fun n => M.priority (narrowedThreadState M narrowed env n) := by
    funext n
    rw [lift_control_narrowedInducedTree M narrowed (branchNode env n)]
    rfl
  rw [heq]
  exact h

end SoundnessMonitor

section FoldingGame

variable (senderTree : List SIn -> SIn -> SOut)
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable [Fintype RIn] [Fintype SIn]

/--
Positions of the receiver-folding game: environment positions carry the
sender word and the monitor state; receiver positions additionally carry the
current environment move.
-/
abbrev FoldPosition (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut) :=
  (List SIn × M.State) ⊕ (List SIn × M.State × (RIn × SIn))

/-- The environment owns move positions; the receiver owns response positions. -/
def foldOwner : FoldPosition M -> ParityPlayer
  | Sum.inl _ => ParityPlayer.odd
  | Sum.inr _ => ParityPlayer.even

/-- Both tiers of a round carry the monitor priority of their state. -/
def foldPriority : FoldPosition M -> Nat
  | Sum.inl (_, q) => M.priority q
  | Sum.inr (_, q, _) => M.priority q

/--
Edges of the folding game: the environment picks the move, the receiver
picks its output; the sender output is fixed by the given sender tree.
-/
def foldStep : FoldPosition M -> FoldPosition M -> Prop
  | Sum.inl (word, q), target =>
      ∃ move : RIn × SIn, target = Sum.inr (word, q, move)
  | Sum.inr (word, q, move), target =>
      ∃ out : ROut,
        target =
          Sum.inl (word ++ [move.2],
            M.step q (move, out, senderTree word move.2))

omit [Fintype RIn] [Fintype SIn] in
theorem foldStep_total :
    ∀ position : FoldPosition M,
      ∃ next : FoldPosition M, foldStep M senderTree position next := by
  intro position
  match position with
  | Sum.inl (word, q) =>
      exact ⟨Sum.inr (word, q, default), ⟨default, rfl⟩⟩
  | Sum.inr (word, q, move) =>
      exact ⟨Sum.inl (word ++ [move.2],
        M.step q (move, default, senderTree word move.2)), ⟨default, rfl⟩⟩

/-- The receiver-folding game is a countable parity game. -/
@[reducible] def foldGame : CountableParityGame.{max u v w} where
  Position := FoldPosition M
  positionCountable := by
    haveI : Countable RIn := Finite.to_countable
    haveI : Countable SIn := Finite.to_countable
    haveI : Countable M.State := Finite.to_countable
    exact inferInstance
  owner := foldOwner M
  step := foldStep M senderTree
  step_total := foldStep_total M senderTree
  priority := foldPriority M
  priority_finite := by
    refine Set.Finite.subset (Set.finite_range M.priority) ?_
    rintro p ⟨(⟨word, q⟩ | ⟨word, q, move⟩), rfl⟩
    · exact ⟨q, rfl⟩
    · exact ⟨q, rfl⟩

/-- Move extraction from receiver positions. -/
def foldExtractMove : FoldPosition M -> Option (RIn × SIn)
  | Sum.inr (_, _, move) => some move
  | _ => none

/-- Total move reader with a default at environment positions. -/
def foldMoveAt (position : FoldPosition M) : RIn × SIn :=
  match position with
  | Sum.inr (_, _, move) => move
  | _ => default

/-- Decode the environment move history from a game prefix. -/
def foldDecode {n : Nat} (pref : Fin (n + 1) -> FoldPosition M) :
    List (RIn × SIn) :=
  (List.ofFn pref).filterMap (foldExtractMove M)

/-- The Even move of the memory strategy at a receiver position. -/
def foldMemoryMove
    (T : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut))
    (last : FoldPosition M) (decoded : List (RIn × SIn)) : FoldPosition M :=
  match last with
  | Sum.inr (word, q, move) =>
      Sum.inl (word ++ [move.2],
        M.step q (move, (T decoded.dropLast).1 move, senderTree word move.2))
  | position => position

/--
The memory strategy replaying the receiver component of a full tree: the
move history is decoded from the receiver positions of the prefix.
-/
def foldMemoryStrategy
    (T : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut)) :
    (foldGame M senderTree).Strategy ParityPlayer.even where
  move _n pref :=
    foldMemoryMove M senderTree T
      ((foldGame M senderTree).prefixLast pref) (foldDecode M pref)

theorem foldMemoryStrategy_legal
    (T : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut)) :
    (foldMemoryStrategy M senderTree T).Legal := by
  intro n pref _hlegal howner
  show (foldGame M senderTree).step ((foldGame M senderTree).prefixLast pref)
    (foldMemoryMove M senderTree T
      ((foldGame M senderTree).prefixLast pref) (foldDecode M pref))
  cases hlast : (foldGame M senderTree).prefixLast pref with
  | inl pair =>
      rw [hlast] at howner
      simp [foldOwner] at howner
  | inr triple =>
      obtain ⟨word, q, move⟩ := triple
      exact ⟨(T (foldDecode M pref).dropLast).1 move, rfl⟩

section MemoryWinning

variable [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

/--
The memory strategy wins the folding game from the root whenever the full
tree is sender-oblivious and winning, and the game's sender tree is read off
the full tree.
-/
theorem foldMemoryStrategy_winningFrom
    {T : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut)}
    (hoblivious : SenderOblivious T)
    (hsender :
      ∀ word : List SIn,
        senderTree word =
          (T (word.map (fun sIn => ((default : RIn), sIn)))).2)
    (hwin : M.lift.WinningTree T) :
    CountableParityGame.Strategy.WinningFrom (G := foldGame M senderTree)
      (foldMemoryStrategy M senderTree T)
      (Sum.inl ([], M.initial)) := by
  classical
  constructor
  · exact foldMemoryStrategy_legal M senderTree T
  · intro path hplayfrom hconsistent
    obtain ⟨hzero, hplay⟩ := hplayfrom
    set u : Nat -> List (RIn × SIn) :=
      fun n =>
        (List.ofFn fun i : Fin (2 * n + 1) => path i).filterMap
          (foldExtractMove M)
      with hu
    set mv : Nat -> RIn × SIn := fun n => foldMoveAt M (path (2 * n + 1))
      with hmv
    have hsend : ∀ word : List SIn, ∀ node : TreeNode (RIn × SIn),
        senderWord node = word -> senderTree word = (T node).2 := by
      intro word node hword
      rw [hsender word]
      refine hoblivious _ _ ?_
      rw [senderWord_completion word, hword]
    have hu0 : u 0 = [] := by
      have hofn :
          (List.ofFn fun i : Fin (2 * 0 + 1) => path i) = [path 0] := by
        simp [List.ofFn_succ]
      simp only [hu, hofn, hzero]
      rfl
    have hstep : ∀ n : Nat,
        path (2 * n) =
            Sum.inl (senderWord (u n), M.lift.control T (u n)) ->
          path (2 * n + 1) =
              Sum.inr (senderWord (u n), M.lift.control T (u n), mv n) ∧
            u (n + 1) = u n ++ [mv n] ∧
            path (2 * n + 2) =
              Sum.inl (senderWord (u n ++ [mv n]),
                M.lift.control T (u n ++ [mv n])) := by
      intro n hA
      have hstep1 :
          foldStep M senderTree (path (2 * n)) (path (2 * n + 1)) :=
        hplay (2 * n)
      rw [hA] at hstep1
      obtain ⟨move, hmove⟩ := hstep1
      have hmvn : mv n = move := by
        simp [hmv, hmove, foldMoveAt]
      have hC :
          path (2 * n + 1) =
            Sum.inr (senderWord (u n), M.lift.control T (u n), mv n) := by
        rw [hmvn]
        exact hmove
      have hdec1 :
          (List.ofFn fun i : Fin (2 * n + 1 + 1) => path i).filterMap
              (foldExtractMove M) =
            u n ++ [mv n] := by
        rw [List.ofFn_add (n := 2 * n + 1) (m := 1)
          (f := fun i : Fin (2 * n + 1 + 1) => path i)]
        simp only [List.filterMap_append]
        have hfirstu :
            List.filterMap (foldExtractMove M)
              (List.ofFn fun i : Fin (2 * n + 1) =>
                path ((Fin.castLE (by omega) i : Fin (2 * n + 1 + 1)) : Nat)) =
              u n := rfl
        rw [hfirstu]
        simp [List.ofFn_succ, hC, foldExtractMove]
      have howner :
          (foldGame M senderTree).owner (path (2 * n + 1)) =
            ParityPlayer.even := by
        rw [hC]
        rfl
      have hcons := hconsistent (2 * n + 1) howner
      have hlast :
          (foldGame M senderTree).prefixLast
              ((foldGame M senderTree).prefixOfPath path (2 * n + 1)) =
            path (2 * n + 1) :=
        (foldGame M senderTree).prefixLast_prefixOfPath path (2 * n + 1)
      have hdecodePref :
          foldDecode M ((foldGame M senderTree).prefixOfPath path (2 * n + 1)) =
            u n ++ [mv n] := by
        simpa [foldDecode, CountableParityGame.prefixOfPath] using hdec1
      have hmove2 :
          path (2 * n + 2) =
            Sum.inl (senderWord (u n ++ [mv n]),
              M.lift.control T (u n ++ [mv n])) := by
        rw [hcons]
        show foldMemoryMove M senderTree T _ _ = _
        rw [hlast, hdecodePref, hC]
        show Sum.inl (senderWord (u n) ++ [(mv n).2],
            M.step (M.lift.control T (u n))
              ((mv n), (T (u n ++ [mv n]).dropLast).1 (mv n),
                senderTree (senderWord (u n)) (mv n).2)) = _
        rw [List.dropLast_concat,
          hsend (senderWord (u n)) (u n) rfl,
          ← senderWord_append (u n) (mv n),
          M.lift.control_append T (u n) (mv n)]
        rfl
      have hB : u (n + 1) = u n ++ [mv n] := by
        show (List.ofFn fun i : Fin (2 * (n + 1) + 1) => path i).filterMap
            (foldExtractMove M) = u n ++ [mv n]
        rw [List.ofFn_add (n := 2 * n + 2) (m := 1)
          (f := fun i : Fin (2 * (n + 1) + 1) => path i)]
        simp only [List.filterMap_append]
        have hfirst :
            List.filterMap (foldExtractMove M)
              (List.ofFn fun i : Fin (2 * n + 2) =>
                path ((Fin.castLE (by omega) i : Fin (2 * n + 2 + 1)) : Nat)) =
              u n ++ [mv n] := hdec1
        rw [hfirst]
        simp [List.ofFn_succ, hmove2, foldExtractMove]
      exact ⟨hC, hB, hmove2⟩
    have hA : ∀ n : Nat,
        path (2 * n) =
          Sum.inl (senderWord (u n), M.lift.control T (u n)) := by
      intro n
      induction n with
      | zero =>
          rw [hu0]
          simpa [senderWord] using hzero
      | succ n ih =>
          have h := hstep n ih
          rw [h.2.1]
          exact h.2.2
    have hC_all : ∀ n : Nat,
        path (2 * n + 1) =
          Sum.inr (senderWord (u n), M.lift.control T (u n), mv n) :=
      fun n => (hstep n (hA n)).1
    have hB_all : ∀ n : Nat, u (n + 1) = u n ++ [mv n] :=
      fun n => (hstep n (hA n)).2.1
    have hu_branch : ∀ n : Nat, u n = branchNode mv n := by
      intro n
      induction n with
      | zero => simpa [branchNode] using hu0
      | succ n ih =>
          rw [hB_all n, ih]
          rfl
    have hpri : ∀ k : Nat,
        (foldGame M senderTree).priority (path k) =
          M.priority (M.lift.control T (u (k / 2))) := by
      intro k
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · obtain ⟨j, rfl⟩ : ∃ j : Nat, k = 2 * j := ⟨k / 2, by omega⟩
        rw [hA j, (by omega : 2 * j / 2 = j)]
        rfl
      · obtain ⟨j, rfl⟩ : ∃ j : Nat, k = 2 * j + 1 := ⟨k / 2, by omega⟩
        rw [hC_all j, (by omega : (2 * j + 1) / 2 = j)]
        rfl
    have hTwin := hwin mv
    have hs :
        NatSeqMinEvenParity
          (fun n => M.priority (M.lift.control T (u n))) := by
      have heq :
          (fun n =>
              M.lift.priority (M.lift.control T (branchNode mv n))) =
            fun n => M.priority (M.lift.control T (u n)) := by
        funext n
        rw [← hu_branch n]
        rfl
      rw [heq] at hTwin
      exact hTwin
    exact (natSeqMinEvenParity_halved hpri).mpr hs

end MemoryWinning

end FoldingGame

/--
Completeness of the narrowing: from a sender-oblivious winning tree, the
positional determinacy of the receiver-folding game folds the receiver to a
table over sender words, monitor states, and current moves, yielding a
narrowed tree with all threads winning.
-/
theorem exists_narrowed_of_senderOblivious_winningTree
    [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq RIn] [DecidableEq SIn]
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    {T : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut)}
    (hoblivious : SenderOblivious T)
    (hwin : M.lift.WinningTree T) :
    ∃ narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State),
      NarrowedAllThreadsWin M narrowed := by
  classical
  set senderTree : List SIn -> SIn -> SOut :=
    fun word => (T (word.map (fun sIn => ((default : RIn), sIn)))).2
    with hsdef
  have hmem :
      (Sum.inl ([], M.initial) : FoldPosition M) ∈
        (foldGame M senderTree).WinningRegion ParityPlayer.even :=
    ⟨foldMemoryStrategy M senderTree T,
      foldMemoryStrategy_winningFrom M senderTree hoblivious
        (fun word => rfl) hwin⟩
  obtain ⟨σ, hσ⟩ :=
    (foldGame M senderTree).positionalDeterminacy ParityPlayer.even _ hmem
  have hout : ∀ (word : List SIn) (q : M.State) (move : RIn × SIn),
      ∃ out : ROut,
        σ.move (Sum.inr (word, q, move)) =
          Sum.inl (word ++ [move.2],
            M.step q (move, out, senderTree word move.2)) := by
    intro word q move
    have howner :
        (foldGame M senderTree).owner
          (Sum.inr (word, q, move) : FoldPosition M) = ParityPlayer.even := rfl
    have hlegal := σ.legal (Sum.inr (word, q, move)) howner
    simpa [foldGame] using hlegal
  choose table htable using hout
  refine ⟨fun word => (senderTree word, fun q move => table word q move), ?_⟩
  intro env
  set narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State) :=
    fun word => (senderTree word, fun q move => table word q move)
    with hndef
  set sw : Nat -> List SIn := fun n => senderWord (branchNode env n) with hsw
  set qs : Nat -> M.State :=
    fun n => narrowedControl M narrowed (branchNode env n) with hqs
  have hsw0 : sw 0 = [] := rfl
  have hswsucc : ∀ n : Nat, sw (n + 1) = sw n ++ [(env n).2] := by
    intro n
    show senderWord (branchNode env n ++ [env n]) = _
    rw [senderWord_append]
  have hqssucc : ∀ n : Nat,
      qs (n + 1) =
        M.step (qs n)
          (env n, table (sw n) (qs n) (env n),
            senderTree (sw n) (env n).2) := by
    intro n
    show narrowedControl M narrowed (branchNode env n ++ [env n]) = _
    rw [narrowedControl_append M narrowed (branchNode env n) (env n)]
    rfl
  have hplay :
      (foldGame M senderTree).Play
        (interleavePlay
          (fun n => (Sum.inl (sw n, qs n) : FoldPosition M))
          (fun n => (Sum.inr (sw n, qs n, env n) : FoldPosition M))) := by
    refine interleavePlay_play _ _ _ ?_ ?_
    · intro j
      exact ⟨env j, rfl⟩
    · intro j
      refine ⟨table (sw j) (qs j) (env j), ?_⟩
      rw [hswsucc j, hqssucc j]
  have hstart :
      interleavePlay
          (fun n => (Sum.inl (sw n, qs n) : FoldPosition M))
          (fun n => (Sum.inr (sw n, qs n, env n) : FoldPosition M)) 0 =
        Sum.inl ([], M.initial) := by
    rw [interleavePlay_zero]
    rfl
  have hcons :
      CountableParityGame.PositionalStrategy.Consistent
        (G := foldGame M senderTree) σ
        (interleavePlay
          (fun n => (Sum.inl (sw n, qs n) : FoldPosition M))
          (fun n => (Sum.inr (sw n, qs n, env n) : FoldPosition M))) := by
    intro k howner
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · rw [interleavePlay_of_mod_eq_zero _ _ hk] at howner
      simp [foldOwner] at howner
    · rw [interleavePlay_of_mod_eq_one _ _ hk,
        interleavePlay_of_mod_eq_zero _ _ (by omega : (k + 1) % 2 = 0),
        (by omega : (k + 1) / 2 = k / 2 + 1)]
      rw [hswsucc (k / 2), hqssucc (k / 2)]
      exact (htable (sw (k / 2)) (qs (k / 2)) (env (k / 2))).symm
  have hwins := hσ _ ⟨hstart, hplay⟩ hcons
  have hpri : ∀ k : Nat,
      (foldGame M senderTree).priority
          (interleavePlay
            (fun n => (Sum.inl (sw n, qs n) : FoldPosition M))
            (fun n => (Sum.inr (sw n, qs n, env n) : FoldPosition M)) k) =
        M.priority (qs (k / 2)) :=
    interleavePlay_priority _ _ _ (fun n => M.priority (qs n))
      (fun j => rfl) (fun j => rfl)
  exact (natSeqMinEvenParity_halved hpri).mp hwins

/--
Branchwise determinization certificate for the universal thread condition:
a deterministic block monitor over the sender branching whose winning trees
are exactly the narrowed trees with all threads winning.

The thread condition quantifies over the receiver inputs revealed along one
sender branch, so this is determinization of a universal parity word
condition over the finite alphabet `RIn` threaded against the narrowed
labels.  It is supplied by the standard alternation-removal/determinization
backend; it is not model-specific mathematics.
-/
structure NarrowedThreadDPACertificate
    (RIn : Type u) (SIn : Type v) (ROut : Type x) (SOut : Type y)
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut) where
  monitor :
    DeterministicBlockMonitor.{v, max u v x y w, z}
      SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State)
  winning_iff :
    ∀ narrowed :
        LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State),
      monitor.WinningTree narrowed ↔ NarrowedAllThreadsWin M narrowed

/--
An implementable finite block controller: a transition-rational tree over
the sender branching with narrowed labels, all of whose threads win.  Its
readback local pair is finite-state on both sides: the sender output is the
label's sender component at the finite control reached by its own word, and
the receiver output is the label's table at that control, evaluated at the
monitor state and the current move.
-/
theorem exists_implementable_controller_of_block_realizable
    [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq RIn] [DecidableEq SIn]
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (cert : NarrowedThreadDPACertificate.{u, v, x, y, w, z} RIn SIn ROut SOut M)
    (hrealizable :
      ∃ receiver : ReceiverBlockStrategy RIn SIn ROut,
        ∃ sender : SenderBlockStrategy SIn SOut,
          ∀ env : Nat -> RIn × SIn,
            M.WinsPlay (pairPlay receiver sender env)) :
    ∃ controller :
        TransitionRationalTree.{v, max u v x y w, z}
          SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State),
      NarrowedAllThreadsWin M controller.labeledTree := by
  letI := cert.monitor.branchFinite
  letI := cert.monitor.alphabetFinite
  rcases (block_realizable_iff_senderOblivious_winningTree M).mp hrealizable with
    ⟨tree, hoblivious, hwin⟩
  rcases exists_narrowed_of_senderOblivious_winningTree M hoblivious hwin with
    ⟨narrowed, hthreads⟩
  rcases cert.monitor.toRunAutomaton.exists_transitionRational_accepted
      ⟨narrowed,
        (cert.monitor.acceptsTree_iff_winningTree narrowed).mpr
          ((cert.winning_iff narrowed).mpr hthreads)⟩ with
    ⟨controller, haccepts⟩
  exact ⟨controller,
    (cert.winning_iff controller.labeledTree).mp
      ((cert.monitor.acceptsTree_iff_winningTree controller.labeledTree).mp
        haccepts)⟩

/--
Round-trip soundness: the induced full tree of any implementable controller
is sender-oblivious and winning, so the controller's readback local pair
realizes the block objective.  Together with
`exists_implementable_controller_of_block_realizable` this closes the
narrowing loop: block realizability is equivalent to the existence of a
finite-state implementable controller, given the thread determinization
certificate.
-/
theorem block_realizable_iff_implementable_controller
    [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq RIn] [DecidableEq SIn]
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (cert : NarrowedThreadDPACertificate.{u, v, x, y, w, z} RIn SIn ROut SOut M) :
    (∃ receiver : ReceiverBlockStrategy RIn SIn ROut,
      ∃ sender : SenderBlockStrategy SIn SOut,
        ∀ env : Nat -> RIn × SIn,
          M.WinsPlay (pairPlay receiver sender env)) ↔
      ∃ controller :
          TransitionRationalTree.{v, max u v x y w, z}
            SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State),
        NarrowedAllThreadsWin M controller.labeledTree := by
  constructor
  · exact exists_implementable_controller_of_block_realizable M cert
  · rintro ⟨controller, hthreads⟩
    refine (block_realizable_iff_senderOblivious_winningTree M).mpr ?_
    exact ⟨narrowedInducedTree M controller.labeledTree,
      senderOblivious_narrowedInducedTree M controller.labeledTree,
      narrowedInducedTree_winningTree_of_allThreadsWin M hthreads⟩

end SenderNarrowing

end DistributedSynthesis
