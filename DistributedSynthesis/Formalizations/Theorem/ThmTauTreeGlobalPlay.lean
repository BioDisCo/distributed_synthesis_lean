/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Data.List.GetD
import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeRegimeB

/-!
# The global play: per-boundary segments

Regime (a) requires that the boundary-atom
priority subsequence of a never-sinking branch is min-even.  The proof
is a single winner-consistent play visiting each boundary atom,
assembled from finite segments, each a winner-consistent path from one
boundary to the next.

This file builds the segments.  A segment between boundaries `a` and
`a'` is packaged as `SegmentSpec`: a finite play with legal steps,
winner-consistency at Even positions, and every interior priority at
least the priority of `a'`'s sampled minimum.  Three constructors
cover the branch shapes: a synchronizing round, a left block closed at
its recorded length, and the right mirror.  The block constructors
reuse the environment-driven block plays of `ThmTauTreeRegimeB.lean`:
feeding the closing move as the environment's final entry makes the
block play hit the closing receive position on the nose, and the
continue-versus-close decision belongs to the environment, so the
segment closes without deviating from the winner.

The thread-trace inversions recover, from membership in the run's
realized thread sets, an explicit environment word whose narrowed
thread fold is the closing thread; this is what connects the branch's
close direction to a concrete in-game path.
-/

set_option linter.unusedSectionVars false

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- The depth-`j` node of the branch reading off a finite list is the
list's prefix. -/
theorem branchNode_getD {α : Type u} [Inhabited α] (l : List α) :
    ∀ j, j ≤ l.length ->
      branchNode (fun i => l.getD i default) j = l.take j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      rw [show branchNode (fun i => l.getD i default) (j + 1) =
          branchNode (fun i => l.getD i default) j ++ [l.getD j default]
          from rfl,
        ih (by omega), List.getD_eq_getElem l default (by omega),
        List.take_add_one, List.getElem?_eq_getElem (by omega)]
      rfl

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]
variable (σ : StrategyPair In₁ In₂ Out₁ Out₂)
variable
  (τ :
    (uniformizationGame A σ).PositionalStrategy ParityPlayer.even)

/-- The winner's winning region is closed under consistent
reachability: a position reached by a consistent play from the initial
boundary is itself a winning start. -/
theorem winningFrom_of_reaches
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := uniformizationGame A σ) τ (.bnd (A.initial, A.initial)))
    (P : UniformizationPosition (In₁ := In₁) A)
    (hP : Reaches σ τ P) :
    CountableParityGame.PositionalStrategy.WinningFrom
      (G := uniformizationGame A σ) τ P := by
  intro path hpath hcons
  exact
    minPriorityEven_of_reaches_cont σ τ hwin P hP path hpath.1 hpath.2 hcons

/-! ### Monitor-step bridges

The block monitors fold `narrowedRecord`s exactly as the automaton's
thread subsets fold `leftThreadOpen`/`leftThreadStep`, and mirrored on
the right.  All four equations are definitional. -/

theorem leftBlockMonitor_step_narrowedRecord (b : A.State)
    (qm : A.State × A.State)
    (label : NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (move : In₁ × In₂) :
    (A.leftBlockMonitor b).step qm
        (narrowedRecord (A.leftBlockMonitor b) label qm move) =
      leftThreadStep qm label move.1 move.2 :=
  rfl

theorem leftBlockMonitor_step_open (atom : A.State × A.State)
    (label : NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (move : In₁ × In₂) :
    (A.leftBlockMonitor atom.1).step (A.leftBlockMonitor atom.1).initial
        (narrowedRecord (A.leftBlockMonitor atom.1) label
          (A.leftBlockMonitor atom.1).initial move) =
      leftThreadOpen atom label move.1 move.2 :=
  rfl

theorem rightBlockMonitor_step_narrowedRecord (b : A.State)
    (qm : A.State × A.State)
    (label : NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State))
    (move : In₂ × In₁) :
    (A.rightBlockMonitor b).step qm
        (narrowedRecord (A.rightBlockMonitor b) label qm move) =
      rightThreadStep qm label move.1 move.2 :=
  rfl

theorem rightBlockMonitor_step_open (atom : A.State × A.State)
    (label : NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State))
    (move : In₂ × In₁) :
    (A.rightBlockMonitor atom.1).step (A.rightBlockMonitor atom.1).initial
        (narrowedRecord (A.rightBlockMonitor atom.1) label
          (A.rightBlockMonitor atom.1).initial move) =
      rightThreadOpen atom label move.1 move.2 :=
  rfl

/-! ### The sampled minimum dominates nothing: min-state chains

Along a narrowed thread of a block monitor the sampled minimum's
priority is antitone, bounded by the tracked state's priority and by
the boundary's. -/

theorem leftBlockMonitor_step_snd_le (b : A.State)
    (state : A.State × A.State)
    (round : RealizedBlockRound In₁ In₂ Out₁ Out₂) :
    A.priority ((A.leftBlockMonitor b).step state round).2 ≤
        A.priority state.2 ∧
      A.priority ((A.leftBlockMonitor b).step state round).2 ≤
        A.priority ((A.leftBlockMonitor b).step state round).1 := by
  constructor
  · show
      A.priority
          (if A.priority (A.step state.1 (realizedRoundRecord round)) <
              A.priority state.2 then
            A.step state.1 (realizedRoundRecord round)
          else state.2) ≤
        A.priority state.2
    split <;> omega
  · show
      A.priority
          (if A.priority (A.step state.1 (realizedRoundRecord round)) <
              A.priority state.2 then
            A.step state.1 (realizedRoundRecord round)
          else state.2) ≤
        A.priority (A.step state.1 (realizedRoundRecord round))
    split <;> omega

theorem rightBlockMonitor_step_snd_le (b : A.State)
    (state : A.State × A.State)
    (round : RealizedBlockRound In₂ In₁ Out₂ Out₁) :
    A.priority ((A.rightBlockMonitor b).step state round).2 ≤
        A.priority state.2 ∧
      A.priority ((A.rightBlockMonitor b).step state round).2 ≤
        A.priority ((A.rightBlockMonitor b).step state round).1 := by
  constructor
  · show
      A.priority
          (if A.priority (A.step state.1 (realizedRoundRecordRight round)) <
              A.priority state.2 then
            A.step state.1 (realizedRoundRecordRight round)
          else state.2) ≤
        A.priority state.2
    split <;> omega
  · show
      A.priority
          (if A.priority (A.step state.1 (realizedRoundRecordRight round)) <
              A.priority state.2 then
            A.step state.1 (realizedRoundRecordRight round)
          else state.2) ≤
        A.priority (A.step state.1 (realizedRoundRecordRight round))
    split <;> omega

theorem leftThread_snd_le_fst (b : A.State)
    (narrowed :
      LabeledTree In₂
        (NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)))
    (env : Nat -> In₁ × In₂) :
    ∀ j : Nat,
      A.priority
          (narrowedThreadState (A.leftBlockMonitor b) narrowed env j).2 ≤
        A.priority
          (narrowedThreadState (A.leftBlockMonitor b) narrowed env j).1
  | 0 => Nat.le_refl _
  | j + 1 => by
      have hsucc :
          narrowedThreadState (A.leftBlockMonitor b) narrowed env (j + 1) =
            (A.leftBlockMonitor b).step
              (narrowedThreadState (A.leftBlockMonitor b) narrowed env j)
              (narrowedRecord (A.leftBlockMonitor b)
                (narrowed (senderWord (branchNode env j)))
                (narrowedThreadState (A.leftBlockMonitor b) narrowed env j)
                (env j)) := by
        show
          narrowedControl (A.leftBlockMonitor b) narrowed
              (branchNode env (j + 1)) =
            _
        rw [show branchNode env (j + 1) = branchNode env j ++ [env j]
            from rfl,
          narrowedControl_append]
        rfl
      rw [hsucc]
      exact (leftBlockMonitor_step_snd_le b _ _).2

theorem leftThread_snd_antitone (b : A.State)
    (narrowed :
      LabeledTree In₂
        (NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)))
    (env : Nat -> In₁ × In₂) (j : Nat) :
    ∀ d : Nat,
      A.priority
          (narrowedThreadState (A.leftBlockMonitor b) narrowed env
            (j + d)).2 ≤
        A.priority
          (narrowedThreadState (A.leftBlockMonitor b) narrowed env j).2
  | 0 => Nat.le_refl _
  | d + 1 => by
      have hsucc :
          narrowedThreadState (A.leftBlockMonitor b) narrowed env
              (j + d + 1) =
            (A.leftBlockMonitor b).step
              (narrowedThreadState (A.leftBlockMonitor b) narrowed env
                (j + d))
              (narrowedRecord (A.leftBlockMonitor b)
                (narrowed (senderWord (branchNode env (j + d))))
                (narrowedThreadState (A.leftBlockMonitor b) narrowed env
                  (j + d))
                (env (j + d))) := by
        show
          narrowedControl (A.leftBlockMonitor b) narrowed
              (branchNode env (j + d + 1)) =
            _
        rw [show branchNode env (j + d + 1) =
            branchNode env (j + d) ++ [env (j + d)] from rfl,
          narrowedControl_append]
        rfl
      rw [show j + (d + 1) = j + d + 1 by omega, hsucc]
      exact
        Nat.le_trans (leftBlockMonitor_step_snd_le b _ _).1
          (leftThread_snd_antitone b narrowed env j d)

theorem rightThread_snd_le_fst (b : A.State)
    (narrowed :
      LabeledTree In₁
        (NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)))
    (env : Nat -> In₂ × In₁) :
    ∀ j : Nat,
      A.priority
          (narrowedThreadState (A.rightBlockMonitor b) narrowed env j).2 ≤
        A.priority
          (narrowedThreadState (A.rightBlockMonitor b) narrowed env j).1
  | 0 => Nat.le_refl _
  | j + 1 => by
      have hsucc :
          narrowedThreadState (A.rightBlockMonitor b) narrowed env (j + 1) =
            (A.rightBlockMonitor b).step
              (narrowedThreadState (A.rightBlockMonitor b) narrowed env j)
              (narrowedRecord (A.rightBlockMonitor b)
                (narrowed (senderWord (branchNode env j)))
                (narrowedThreadState (A.rightBlockMonitor b) narrowed env j)
                (env j)) := by
        show
          narrowedControl (A.rightBlockMonitor b) narrowed
              (branchNode env (j + 1)) =
            _
        rw [show branchNode env (j + 1) = branchNode env j ++ [env j]
            from rfl,
          narrowedControl_append]
        rfl
      rw [hsucc]
      exact (rightBlockMonitor_step_snd_le b _ _).2

theorem rightThread_snd_antitone (b : A.State)
    (narrowed :
      LabeledTree In₁
        (NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)))
    (env : Nat -> In₂ × In₁) (j : Nat) :
    ∀ d : Nat,
      A.priority
          (narrowedThreadState (A.rightBlockMonitor b) narrowed env
            (j + d)).2 ≤
        A.priority
          (narrowedThreadState (A.rightBlockMonitor b) narrowed env j).2
  | 0 => Nat.le_refl _
  | d + 1 => by
      have hsucc :
          narrowedThreadState (A.rightBlockMonitor b) narrowed env
              (j + d + 1) =
            (A.rightBlockMonitor b).step
              (narrowedThreadState (A.rightBlockMonitor b) narrowed env
                (j + d))
              (narrowedRecord (A.rightBlockMonitor b)
                (narrowed (senderWord (branchNode env (j + d))))
                (narrowedThreadState (A.rightBlockMonitor b) narrowed env
                  (j + d))
                (env (j + d))) := by
        show
          narrowedControl (A.rightBlockMonitor b) narrowed
              (branchNode env (j + d + 1)) =
            _
        rw [show branchNode env (j + d + 1) =
            branchNode env (j + d) ++ [env (j + d)] from rfl,
          narrowedControl_append]
        rfl
      rw [show j + (d + 1) = j + d + 1 by omega, hsucc]
      exact
        Nat.le_trans (rightBlockMonitor_step_snd_le b _ _).1
          (rightThread_snd_antitone b narrowed env j d)

/-! ### Winner-consistent segments between boundaries -/

/--
A winner-consistent finite play from boundary `a` to boundary `a'`:
legal steps, the winner's moves at Even positions, and every interior
priority at least the priority of `a'`'s sampled minimum.
-/
structure SegmentSpec (a a' : A.State × A.State) where
  len : Nat
  play : Nat -> UniformizationPosition (In₁ := In₁) A
  len_pos : 1 ≤ len
  play_zero : play 0 = .bnd a
  play_len : play len = .bnd a'
  step : ∀ t, t < len ->
    (uniformizationGame A σ).step (play t) (play (t + 1))
  consistent :
    ∀ t, t < len ->
      (uniformizationGame A σ).owner (play t) = ParityPlayer.even ->
        play (t + 1) = τ.move (play t)
  bound :
    ∀ t, 0 < t -> t < len ->
      A.priority a'.2 ≤ uniformizationPriority (play t)

/-- The synchronizing-round segment. -/
noncomputable def segmentBoth (a a' : A.State × A.State)
    (move : In₁ × In₂)
    (ha' :
      a' =
        bothThreadAtom a (tauOpeningLeftLabel σ τ a)
          (tauOpeningRightLabel σ τ a) move.1 move.2) :
    SegmentSpec σ τ a a' where
  len := 4
  play := fun t =>
    match t with
    | 0 => .bnd a
    | 1 => .committed a (commitmentOf σ τ a)
    | 2 => .opening a (commitmentOf σ τ a) move
    | 3 =>
        .openingResolve a (commitmentOf σ τ a) move
          (openingChoice σ τ a move).1 (openingChoice σ τ a move).2
    | _ + 4 => .bnd a'
  len_pos := by omega
  play_zero := rfl
  play_len := rfl
  step := by
    intro t ht
    match t, ht with
    | 0, _ => exact ⟨commitmentOf σ τ a, rfl⟩
    | 1, _ => exact ⟨move, rfl⟩
    | 2, _ =>
        exact ⟨(openingChoice σ τ a move).1,
          (openingChoice σ τ a move).2, rfl⟩
    | 3, _ =>
        refine Or.inl ?_
        rw [ha']
        rfl
  consistent := by
    intro t ht howner
    match t, ht with
    | 0, _ => exact (commitmentOf_spec σ τ a).symm
    | 1, _ => simp [uniformizationGame, uniformizationOwner] at howner
    | 2, _ => exact (openingChoice_spec σ τ a move).symm
    | 3, _ => simp [uniformizationGame, uniformizationOwner] at howner
  bound := by
    intro t ht0 htlen
    have ha2 : A.priority a'.2 = A.priority a.1 := by
      rw [ha']
      rfl
    match t, ht0, htlen with
    | 1, _, _ => rw [ha2]; exact Nat.le_refl _
    | 2, _, _ => rw [ha2]; exact Nat.le_refl _
    | 3, _, _ => rw [ha2]; exact Nat.le_refl _

/-- The left-block segment: drive the environment-driven block play
along the traced thread, then close at the recorded move.  The play
follows the winner at every Even position; continuing versus closing
is the environment's decision, taken here at the block's recorded
length. -/
theorem segmentLeft_exists
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (a a' : A.State × A.State)
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode a)
    (w : List In₂) (ms : TreeNode (In₁ × In₂))
    (base : A.State × A.State) (move : In₁ × In₂)
    (hne : ms ≠ [])
    (hsw : senderWord ms = w)
    (hctrl :
      narrowedControl (A.leftBlockMonitor a.1)
        (leftBlockNarrowed (tauTree σ τ) node₀) ms = base)
    (ha' :
      a' =
        leftThreadClose base (tauLeftLabel σ τ a w)
          (tauLeftClose σ τ a w) move.1 move.2) :
    Nonempty (SegmentSpec σ τ a a') := by
  obtain ⟨L, env, hL, hwL, hbnL, henvL⟩ :
      ∃ (L : Nat) (env : Nat -> In₁ × In₂),
        1 ≤ L ∧ w.length = L ∧ branchNode env L = ms ∧ env L = move := by
    refine ⟨ms.length, fun j => (ms ++ [move]).getD j default,
      List.length_pos_of_ne_nil hne, ?_, ?_, ?_⟩
    · rw [← hsw]
      simp [senderWord]
    · rw [branchNode_getD (ms ++ [move]) ms.length
        (by rw [List.length_append]; omega), List.take_left]
    · show (ms ++ [move]).getD ms.length default = move
      rw [List.getD_append_right ms [move] default ms.length
        (Nat.le_refl _)]
      simp
  have hnts :
      narrowedThreadState (A.leftBlockMonitor a.1)
          (leftBlockNarrowed (tauTree σ τ) node₀) env L =
        base := by
    show
      narrowedControl (A.leftBlockMonitor a.1)
          (leftBlockNarrowed (tauTree σ τ) node₀) (branchNode env L) =
        base
    rw [hbnL]
    exact hctrl
  have h1 :
      blockLeftPlay σ τ a env (4 * L) =
        .blockL (commitmentOf σ τ a) w base.1 base.2 := by
    have h := blockLeftPlay_blockL σ τ a env node₀ hp (L - 1)
    rw [show L - 1 + 1 = L by omega] at h
    rw [show 4 * L = 4 * (L - 1) + 4 by omega, h, hbnL, hsw, hnts]
  have h2 :
      blockLeftPlay σ τ a env (4 * L + 2) =
        .recvL (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableL σ τ a w base.1 base.2) move := by
    rw [show 4 * L + 2 = (4 * L + 1) + 1 by omega,
      blockLeftPlay_succ σ τ a env (4 * L + 1),
      blockLeftPlay_succ σ τ a env (4 * L), h1,
      show advance σ τ env (.blockL (commitmentOf σ τ a) w base.1 base.2) =
          τ.move (.blockL (commitmentOf σ τ a) w base.1 base.2) from rfl,
      blockRevTableL_spec σ τ a w base.1 base.2]
    show
      UniformizationPosition.recvL (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableL σ τ a w base.1 base.2) (env w.length) =
        _
    rw [hwL, henvL]
  have h3 :
      blockLeftPlay σ τ a env (4 * L + 3) =
        .resolveL (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableL σ τ a w base.1 base.2) move
          (recvChoiceL σ τ a w base.1 base.2 move) := by
    rw [show 4 * L + 3 = (4 * L + 2) + 1 by omega,
      blockLeftPlay_succ σ τ a env (4 * L + 2), h2]
    exact recvChoiceL_spec σ τ a w base.1 base.2 move
  have hclose :
      uCloseTarget (A := A) base.1 base.2 move
          (recvChoiceL σ τ a w base.1 base.2 move)
          (closeChoiceL σ τ a w base.1 base.2 move) =
        .bnd a' := by
    rw [ha']
    rfl
  have hb2 : A.priority a'.2 = A.priority base.2 := by
    rw [ha']
    rfl
  refine ⟨⟨4 * L + 6,
    fun t =>
      if t ≤ 4 * L + 3 then blockLeftPlay σ τ a env t
      else if t = 4 * L + 4 then
        .closeL (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableL σ τ a w base.1 base.2) move
          (recvChoiceL σ τ a w base.1 base.2 move)
      else if t = 4 * L + 5 then
        .closeResolveL (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableL σ τ a w base.1 base.2) move
          (recvChoiceL σ τ a w base.1 base.2 move)
          (closeChoiceL σ τ a w base.1 base.2 move)
      else .bnd a',
    by omega, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- play_zero
    simp only []
    rw [if_pos (show (0 : Nat) ≤ 4 * L + 3 by omega)]
    rfl
  · -- play_len
    simp only []
    rw [if_neg (show ¬ 4 * L + 6 ≤ 4 * L + 3 by omega),
      if_neg (show ¬ 4 * L + 6 = 4 * L + 4 by omega),
      if_neg (show ¬ 4 * L + 6 = 4 * L + 5 by omega)]
  · -- step
    intro t ht
    simp only []
    by_cases hc1 : t ≤ 4 * L + 2
    · rw [if_pos (show t ≤ 4 * L + 3 by omega),
        if_pos (show t + 1 ≤ 4 * L + 3 by omega)]
      exact blockLeftPlay_step σ τ a env t
    · by_cases hc2 : t = 4 * L + 3
      · subst hc2
        rw [if_pos (show 4 * L + 3 ≤ 4 * L + 3 by omega),
          if_neg (show ¬ 4 * L + 3 + 1 ≤ 4 * L + 3 by omega),
          if_pos (show 4 * L + 3 + 1 = 4 * L + 4 by omega), h3]
        exact Or.inr rfl
      · by_cases hc3 : t = 4 * L + 4
        · subst hc3
          rw [if_neg (show ¬ 4 * L + 4 ≤ 4 * L + 3 by omega),
            if_pos (show (4 * L + 4 : Nat) = 4 * L + 4 from rfl),
            if_neg (show ¬ 4 * L + 4 + 1 ≤ 4 * L + 3 by omega),
            if_neg (show ¬ 4 * L + 4 + 1 = 4 * L + 4 by omega),
            if_pos (show 4 * L + 4 + 1 = 4 * L + 5 by omega)]
          exact ⟨closeChoiceL σ τ a w base.1 base.2 move, rfl⟩
        · have hc4 : t = 4 * L + 5 := by omega
          subst hc4
          rw [if_neg (show ¬ 4 * L + 5 ≤ 4 * L + 3 by omega),
            if_neg (show ¬ 4 * L + 5 = 4 * L + 4 by omega),
            if_pos rfl,
            if_neg (show ¬ 4 * L + 5 + 1 ≤ 4 * L + 3 by omega),
            if_neg (show ¬ 4 * L + 5 + 1 = 4 * L + 4 by omega),
            if_neg (show ¬ 4 * L + 5 + 1 = 4 * L + 5 by omega)]
          exact Or.inl hclose.symm
  · -- consistent
    intro t ht howner
    simp only [] at howner ⊢
    by_cases hc1 : t ≤ 4 * L + 2
    · rw [if_pos (show t ≤ 4 * L + 3 by omega)] at howner
      rw [if_pos (show t ≤ 4 * L + 3 by omega),
        if_pos (show t + 1 ≤ 4 * L + 3 by omega)]
      exact blockLeftPlay_consistent σ τ a env t howner
    · by_cases hc2 : t = 4 * L + 3
      · subst hc2
        rw [if_pos (show 4 * L + 3 ≤ 4 * L + 3 by omega), h3] at howner
        simp [uniformizationGame, uniformizationOwner] at howner
      · by_cases hc3 : t = 4 * L + 4
        · subst hc3
          rw [if_neg (show ¬ 4 * L + 4 ≤ 4 * L + 3 by omega),
            if_pos (show (4 * L + 4 : Nat) = 4 * L + 4 from rfl),
            if_neg (show ¬ 4 * L + 4 + 1 ≤ 4 * L + 3 by omega),
            if_neg (show ¬ 4 * L + 4 + 1 = 4 * L + 4 by omega),
            if_pos (show 4 * L + 4 + 1 = 4 * L + 5 by omega)]
          exact (closeChoiceL_spec σ τ a w base.1 base.2 move).symm
        · have hc4 : t = 4 * L + 5 := by omega
          subst hc4
          rw [if_neg (show ¬ 4 * L + 5 ≤ 4 * L + 3 by omega),
            if_neg (show ¬ 4 * L + 5 = 4 * L + 4 by omega),
            if_pos rfl] at howner
          simp [uniformizationGame, uniformizationOwner] at howner
  · -- bound
    intro t ht0 htlen
    simp only []
    by_cases hc1 : t ≤ 4 * L + 3
    · rw [if_pos hc1]
      by_cases hopen : t ≤ 3
      · have hle : A.priority a'.2 ≤ A.priority a.1 := by
          rw [hb2]
          have hchain :=
            leftThread_snd_antitone a.1
              (leftBlockNarrowed (tauTree σ τ) node₀) env 0 L
          rw [show 0 + L = L by omega, hnts] at hchain
          exact
            Nat.le_trans hchain
              (leftThread_snd_le_fst a.1
                (leftBlockNarrowed (tauTree σ τ) node₀) env 0)
        interval_cases t
        · rw [blockLeftPlay_one]; exact hle
        · rw [blockLeftPlay_two]; exact hle
        · rw [blockLeftPlay_three]; exact hle
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 4 := ⟨t - 4, by omega⟩
        rw [blockLeftPlay_priority σ τ a env node₀ hp s, hb2]
        show
          A.priority base.2 ≤
            A.priority
              (narrowedThreadState (A.leftBlockMonitor a.1)
                (leftBlockNarrowed (tauTree σ τ) node₀) env (s / 4 + 1)).1
        have hchain :=
          leftThread_snd_antitone a.1
            (leftBlockNarrowed (tauTree σ τ) node₀) env (s / 4 + 1)
            (L - (s / 4 + 1))
        rw [show s / 4 + 1 + (L - (s / 4 + 1)) = L by omega, hnts] at hchain
        exact
          Nat.le_trans hchain
            (leftThread_snd_le_fst a.1
              (leftBlockNarrowed (tauTree σ τ) node₀) env (s / 4 + 1))
    · by_cases hc3 : t = 4 * L + 4
      · subst hc3
        rw [if_neg hc1, if_pos rfl, hb2]
        show A.priority base.2 ≤ A.priority base.1
        have h := leftThread_snd_le_fst a.1
          (leftBlockNarrowed (tauTree σ τ) node₀) env L
        rw [hnts] at h
        exact h
      · have hc4 : t = 4 * L + 5 := by omega
        subst hc4
        rw [if_neg hc1,
          if_neg (show ¬ 4 * L + 5 = 4 * L + 4 by omega),
          if_pos rfl, hb2]
        show A.priority base.2 ≤ A.priority base.1
        have h := leftThread_snd_le_fst a.1
          (leftBlockNarrowed (tauTree σ τ) node₀) env L
        rw [hnts] at h
        exact h

/-- The right-block segment: the orientation mirror. -/
theorem segmentRight_exists
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (a a' : A.State × A.State)
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode a)
    (w : List In₁) (ms : TreeNode (In₂ × In₁))
    (base : A.State × A.State) (move : In₂ × In₁)
    (hne : ms ≠ [])
    (hsw : senderWord ms = w)
    (hctrl :
      narrowedControl (A.rightBlockMonitor a.1)
        (rightBlockNarrowed (tauTree σ τ) node₀) ms = base)
    (ha' :
      a' =
        rightThreadClose base (tauRightLabel σ τ a w)
          (tauRightClose σ τ a w) move.1 move.2) :
    Nonempty (SegmentSpec σ τ a a') := by
  obtain ⟨L, renv, hL, hwL, hbnL, henvL⟩ :
      ∃ (L : Nat) (renv : Nat -> In₂ × In₁),
        1 ≤ L ∧ w.length = L ∧ branchNode renv L = ms ∧ renv L = move := by
    refine ⟨ms.length, fun j => (ms ++ [move]).getD j default,
      List.length_pos_of_ne_nil hne, ?_, ?_, ?_⟩
    · rw [← hsw]
      simp [senderWord]
    · rw [branchNode_getD (ms ++ [move]) ms.length
        (by rw [List.length_append]; omega), List.take_left]
    · show (ms ++ [move]).getD ms.length default = move
      rw [List.getD_append_right ms [move] default ms.length
        (Nat.le_refl _)]
      simp
  have hswap : swapEnv renv L = (move.2, move.1) := by
    show ((renv L).2, (renv L).1) = (move.2, move.1)
    rw [henvL]
  have hnts :
      narrowedThreadState (A.rightBlockMonitor a.1)
          (rightBlockNarrowed (tauTree σ τ) node₀) renv L =
        base := by
    show
      narrowedControl (A.rightBlockMonitor a.1)
          (rightBlockNarrowed (tauTree σ τ) node₀) (branchNode renv L) =
        base
    rw [hbnL]
    exact hctrl
  have h1 :
      blockRightPlay σ τ a (swapEnv renv) (4 * L) =
        .blockR (commitmentOf σ τ a) w base.1 base.2 := by
    have h := blockRightPlay_blockR σ τ a renv node₀ hp (L - 1)
    rw [show L - 1 + 1 = L by omega] at h
    rw [show 4 * L = 4 * (L - 1) + 4 by omega, h, hbnL, hsw, hnts]
  have h2 :
      blockRightPlay σ τ a (swapEnv renv) (4 * L + 2) =
        .recvR (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableR σ τ a w base.1 base.2) (move.2, move.1) := by
    rw [show 4 * L + 2 = (4 * L + 1) + 1 by omega,
      blockRightPlay_succ σ τ a (swapEnv renv) (4 * L + 1),
      blockRightPlay_succ σ τ a (swapEnv renv) (4 * L), h1,
      show advanceR σ τ (swapEnv renv)
          (.blockR (commitmentOf σ τ a) w base.1 base.2) =
          τ.move (.blockR (commitmentOf σ τ a) w base.1 base.2) from rfl,
      blockRevTableR_spec σ τ a w base.1 base.2]
    show
      UniformizationPosition.recvR (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableR σ τ a w base.1 base.2) (swapEnv renv w.length) =
        _
    rw [hwL, hswap]
  have h3 :
      blockRightPlay σ τ a (swapEnv renv) (4 * L + 3) =
        .resolveR (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableR σ τ a w base.1 base.2) (move.2, move.1)
          (recvChoiceR σ τ a w base.1 base.2 (move.2, move.1)) := by
    rw [show 4 * L + 3 = (4 * L + 2) + 1 by omega,
      blockRightPlay_succ σ τ a (swapEnv renv) (4 * L + 2), h2]
    exact recvChoiceR_spec σ τ a w base.1 base.2 (move.2, move.1)
  have hclose :
      uCloseTarget (A := A) base.1 base.2 (move.2, move.1)
          (closeChoiceR σ τ a w base.1 base.2 (move.2, move.1))
          (recvChoiceR σ τ a w base.1 base.2 (move.2, move.1)) =
        .bnd a' := by
    rw [ha']
    rfl
  have hb2 : A.priority a'.2 = A.priority base.2 := by
    rw [ha']
    rfl
  refine ⟨⟨4 * L + 6,
    fun t =>
      if t ≤ 4 * L + 3 then blockRightPlay σ τ a (swapEnv renv) t
      else if t = 4 * L + 4 then
        .closeR (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableR σ τ a w base.1 base.2) (move.2, move.1)
          (recvChoiceR σ τ a w base.1 base.2 (move.2, move.1))
      else if t = 4 * L + 5 then
        .closeResolveR (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableR σ τ a w base.1 base.2) (move.2, move.1)
          (recvChoiceR σ τ a w base.1 base.2 (move.2, move.1))
          (closeChoiceR σ τ a w base.1 base.2 (move.2, move.1))
      else .bnd a',
    by omega, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- play_zero
    simp only []
    rw [if_pos (show (0 : Nat) ≤ 4 * L + 3 by omega)]
    rfl
  · -- play_len
    simp only []
    rw [if_neg (show ¬ 4 * L + 6 ≤ 4 * L + 3 by omega),
      if_neg (show ¬ 4 * L + 6 = 4 * L + 4 by omega),
      if_neg (show ¬ 4 * L + 6 = 4 * L + 5 by omega)]
  · -- step
    intro t ht
    simp only []
    by_cases hc1 : t ≤ 4 * L + 2
    · rw [if_pos (show t ≤ 4 * L + 3 by omega),
        if_pos (show t + 1 ≤ 4 * L + 3 by omega)]
      exact blockRightPlay_step σ τ a (swapEnv renv) t
    · by_cases hc2 : t = 4 * L + 3
      · subst hc2
        rw [if_pos (show 4 * L + 3 ≤ 4 * L + 3 by omega),
          if_neg (show ¬ 4 * L + 3 + 1 ≤ 4 * L + 3 by omega),
          if_pos (show 4 * L + 3 + 1 = 4 * L + 4 by omega), h3]
        exact Or.inr rfl
      · by_cases hc3 : t = 4 * L + 4
        · subst hc3
          rw [if_neg (show ¬ 4 * L + 4 ≤ 4 * L + 3 by omega),
            if_pos (show (4 * L + 4 : Nat) = 4 * L + 4 from rfl),
            if_neg (show ¬ 4 * L + 4 + 1 ≤ 4 * L + 3 by omega),
            if_neg (show ¬ 4 * L + 4 + 1 = 4 * L + 4 by omega),
            if_pos (show 4 * L + 4 + 1 = 4 * L + 5 by omega)]
          exact ⟨closeChoiceR σ τ a w base.1 base.2 (move.2, move.1), rfl⟩
        · have hc4 : t = 4 * L + 5 := by omega
          subst hc4
          rw [if_neg (show ¬ 4 * L + 5 ≤ 4 * L + 3 by omega),
            if_neg (show ¬ 4 * L + 5 = 4 * L + 4 by omega),
            if_pos rfl,
            if_neg (show ¬ 4 * L + 5 + 1 ≤ 4 * L + 3 by omega),
            if_neg (show ¬ 4 * L + 5 + 1 = 4 * L + 4 by omega),
            if_neg (show ¬ 4 * L + 5 + 1 = 4 * L + 5 by omega)]
          exact Or.inl hclose.symm
  · -- consistent
    intro t ht howner
    simp only [] at howner ⊢
    by_cases hc1 : t ≤ 4 * L + 2
    · rw [if_pos (show t ≤ 4 * L + 3 by omega)] at howner
      rw [if_pos (show t ≤ 4 * L + 3 by omega),
        if_pos (show t + 1 ≤ 4 * L + 3 by omega)]
      exact blockRightPlay_consistent σ τ a (swapEnv renv) t howner
    · by_cases hc2 : t = 4 * L + 3
      · subst hc2
        rw [if_pos (show 4 * L + 3 ≤ 4 * L + 3 by omega), h3] at howner
        simp [uniformizationGame, uniformizationOwner] at howner
      · by_cases hc3 : t = 4 * L + 4
        · subst hc3
          rw [if_neg (show ¬ 4 * L + 4 ≤ 4 * L + 3 by omega),
            if_pos (show (4 * L + 4 : Nat) = 4 * L + 4 from rfl),
            if_neg (show ¬ 4 * L + 4 + 1 ≤ 4 * L + 3 by omega),
            if_neg (show ¬ 4 * L + 4 + 1 = 4 * L + 4 by omega),
            if_pos (show 4 * L + 4 + 1 = 4 * L + 5 by omega)]
          exact
            (closeChoiceR_spec σ τ a w base.1 base.2
              (move.2, move.1)).symm
        · have hc4 : t = 4 * L + 5 := by omega
          subst hc4
          rw [if_neg (show ¬ 4 * L + 5 ≤ 4 * L + 3 by omega),
            if_neg (show ¬ 4 * L + 5 = 4 * L + 4 by omega),
            if_pos rfl] at howner
          simp [uniformizationGame, uniformizationOwner] at howner
  · -- bound
    intro t ht0 htlen
    simp only []
    by_cases hc1 : t ≤ 4 * L + 3
    · rw [if_pos hc1]
      by_cases hopen : t ≤ 3
      · have hle : A.priority a'.2 ≤ A.priority a.1 := by
          rw [hb2]
          have hchain :=
            rightThread_snd_antitone a.1
              (rightBlockNarrowed (tauTree σ τ) node₀) renv 0 L
          rw [show 0 + L = L by omega, hnts] at hchain
          exact
            Nat.le_trans hchain
              (rightThread_snd_le_fst a.1
                (rightBlockNarrowed (tauTree σ τ) node₀) renv 0)
        interval_cases t
        · rw [blockRightPlay_one]; exact hle
        · rw [blockRightPlay_two]; exact hle
        · rw [blockRightPlay_three]; exact hle
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 4 := ⟨t - 4, by omega⟩
        rw [blockRightPlay_priority σ τ a renv node₀ hp s, hb2]
        show
          A.priority base.2 ≤
            A.priority
              (narrowedThreadState (A.rightBlockMonitor a.1)
                (rightBlockNarrowed (tauTree σ τ) node₀) renv (s / 4 + 1)).1
        have hchain :=
          rightThread_snd_antitone a.1
            (rightBlockNarrowed (tauTree σ τ) node₀) renv (s / 4 + 1)
            (L - (s / 4 + 1))
        rw [show s / 4 + 1 + (L - (s / 4 + 1)) = L by omega, hnts] at hchain
        exact
          Nat.le_trans hchain
            (rightThread_snd_le_fst a.1
              (rightBlockNarrowed (tauTree σ τ) node₀) renv (s / 4 + 1))
    · by_cases hc3 : t = 4 * L + 4
      · subst hc3
        rw [if_neg hc1, if_pos rfl, hb2]
        show A.priority base.2 ≤ A.priority base.1
        have h := rightThread_snd_le_fst a.1
          (rightBlockNarrowed (tauTree σ τ) node₀) renv L
        rw [hnts] at h
        exact h
      · have hc4 : t = 4 * L + 5 := by omega
        subst hc4
        rw [if_neg hc1,
          if_neg (show ¬ 4 * L + 5 = 4 * L + 4 by omega),
          if_pos rfl, hb2]
        show A.priority base.2 ≤ A.priority base.1
        have h := rightThread_snd_le_fst a.1
          (rightBlockNarrowed (tauTree σ τ) node₀) renv L
        rw [hnts] at h
        exact h

/-! ### Thread-trace inversions

Membership in the run's realized thread set yields an explicit
environment word whose narrowed thread fold is the thread.  The label
alignment is definitional: `leftBlockNarrowed` reads the tree's label
at the corresponding node. -/

section Inversion

variable (CL : LeftThreadChecker (In₁ := In₁) A)
variable (CR : RightThreadChecker (In₁ := In₁) A)
variable (CC : ChainThreadChecker (In₁ := In₁) (A := A))

theorem leftThread_trace
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (atom₀ : A.State × A.State)
    (hrun₀ :
      globalRunIn CL CR CC (tauTree σ τ) (Sum.inl (A.initial, A.initial))
          node₀ =
        Sum.inl atom₀) :
    ∀ (w : TreeNode In₂) (x : In₂) (c : CL.monitor.State)
      (threads : Finset (A.State × A.State)),
      globalRunIn CL CR CC (tauTree σ τ) (Sum.inl (A.initial, A.initial))
          (node₀ ++ senderLNode (A := A) (w ++ [x])) =
        Sum.inr (Sum.inl (c, threads)) ->
      ∀ qm ∈ threads,
        ∃ ms : TreeNode (In₁ × In₂),
          senderWord ms = w ++ [x] ∧
            narrowedControl (A.leftBlockMonitor atom₀.1)
              (leftBlockNarrowed (tauTree σ τ) node₀) ms = qm := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro x c threads hrun qm hqm
      have hcomp :
          globalRunIn CL CR CC (tauTree σ τ)
              (Sum.inl (A.initial, A.initial))
              (node₀ ++ senderLNode (A := A) (([] : TreeNode In₂) ++ [x])) =
            Sum.inr (Sum.inl
              (CL.monitor.step (CL.start atom₀.1)
                  (leftBlockNarrowed (tauTree σ τ) node₀ []) x,
                leftOpenSubset atom₀
                  (leftBlockNarrowed (tauTree σ τ) node₀ []) x)) := by
        rw [show senderLNode (A := A) (([] : TreeNode In₂) ++ [x]) =
          [Sum.inr (Sum.inl x)] from rfl]
        rw [globalRunIn_append, hrun₀]
        rw [leftBlockNarrowed_nil]
        rfl
      have hpair := Sum.inl.inj (Sum.inr.inj (hrun.symm.trans hcomp))
      have hthreads :
          threads =
            leftOpenSubset atom₀
              (leftBlockNarrowed (tauTree σ τ) node₀ []) x :=
        congrArg Prod.snd hpair
      rw [hthreads] at hqm
      obtain ⟨inputOne, hqm'⟩ := mem_leftOpenSubset hqm
      refine ⟨[(inputOne, x)], rfl, ?_⟩
      have hctrl :
          narrowedControl (A.leftBlockMonitor atom₀.1)
              (leftBlockNarrowed (tauTree σ τ) node₀)
              ([] ++ [(inputOne, x)]) =
            (A.leftBlockMonitor atom₀.1).step
              (A.leftBlockMonitor atom₀.1).initial
              (narrowedRecord (A.leftBlockMonitor atom₀.1)
                (leftBlockNarrowed (tauTree σ τ) node₀ [])
                (A.leftBlockMonitor atom₀.1).initial (inputOne, x)) := by
        rw [narrowedControl_append]
        rfl
      rw [show ([(inputOne, x)] : TreeNode (In₁ × In₂)) =
        [] ++ [(inputOne, x)] from rfl, hctrl,
        leftBlockMonitor_step_open atom₀
          (leftBlockNarrowed (tauTree σ τ) node₀ []) (inputOne, x)]
      exact hqm'.symm
  | append_singleton w x' ih =>
      intro x c threads hrun qm hqm
      obtain ⟨threads', hrun'⟩ :=
        globalRunIn_block_left CL CR CC (tauTree σ τ) node₀ atom₀ hrun₀ w x'
      have hcomp :
          globalRunIn CL CR CC (tauTree σ τ)
              (Sum.inl (A.initial, A.initial))
              (node₀ ++ senderLNode (A := A) ((w ++ [x']) ++ [x])) =
            Sum.inr (Sum.inl
              (CL.monitor.step
                  (DeterministicBlockMonitor.controlIn CL.monitor
                    (leftBlockNarrowed (tauTree σ τ) node₀)
                    (CL.start atom₀.1) (w ++ [x']))
                  (leftBlockNarrowed (tauTree σ τ) node₀ (w ++ [x'])) x,
                leftStepSubset threads'
                  (leftBlockNarrowed (tauTree σ τ) node₀ (w ++ [x']))
                  x)) := by
        rw [show node₀ ++ senderLNode (A := A) ((w ++ [x']) ++ [x]) =
          (node₀ ++ senderLNode (A := A) (w ++ [x'])) ++
            [Sum.inr (Sum.inl x)] from by
          rw [senderLNode_append (A := A) (w ++ [x']) x,
            List.append_assoc]]
        rw [globalRunIn_append, hrun']
        rfl
      have hpair := Sum.inl.inj (Sum.inr.inj (hrun.symm.trans hcomp))
      have hthreads :
          threads =
            leftStepSubset threads'
              (leftBlockNarrowed (tauTree σ τ) node₀ (w ++ [x'])) x :=
        congrArg Prod.snd hpair
      rw [hthreads] at hqm
      obtain ⟨base, inputOne, hbase, hqm'⟩ := mem_leftStepSubset hqm
      obtain ⟨ms', hsw', hctrl'⟩ :=
        ih x' _ threads' hrun' base hbase
      refine ⟨ms' ++ [(inputOne, x)], ?_, ?_⟩
      · rw [senderWord_append, hsw']
      · rw [narrowedControl_append, hctrl', hsw',
          leftBlockMonitor_step_narrowedRecord atom₀.1 base
            (leftBlockNarrowed (tauTree σ τ) node₀ (w ++ [x']))
            (inputOne, x)]
        exact hqm'.symm

theorem rightThread_trace
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (atom₀ : A.State × A.State)
    (hrun₀ :
      globalRunIn CL CR CC (tauTree σ τ) (Sum.inl (A.initial, A.initial))
          node₀ =
        Sum.inl atom₀) :
    ∀ (w : TreeNode In₁) (x : In₁) (c : CR.monitor.State)
      (threads : Finset (A.State × A.State)),
      globalRunIn CL CR CC (tauTree σ τ) (Sum.inl (A.initial, A.initial))
          (node₀ ++ senderRNode (A := A) (w ++ [x])) =
        Sum.inr (Sum.inr (Sum.inl (c, threads))) ->
      ∀ qm ∈ threads,
        ∃ ms : TreeNode (In₂ × In₁),
          senderWord ms = w ++ [x] ∧
            narrowedControl (A.rightBlockMonitor atom₀.1)
              (rightBlockNarrowed (tauTree σ τ) node₀) ms = qm := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro x c threads hrun qm hqm
      have hcomp :
          globalRunIn CL CR CC (tauTree σ τ)
              (Sum.inl (A.initial, A.initial))
              (node₀ ++ senderRNode (A := A) (([] : TreeNode In₁) ++ [x])) =
            Sum.inr (Sum.inr (Sum.inl
              (CR.monitor.step (CR.start atom₀.1)
                  (rightBlockNarrowed (tauTree σ τ) node₀ []) x,
                rightOpenSubset atom₀
                  (rightBlockNarrowed (tauTree σ τ) node₀ []) x))) := by
        rw [show senderRNode (A := A) (([] : TreeNode In₁) ++ [x]) =
          [Sum.inr (Sum.inr x)] from rfl]
        rw [globalRunIn_append, hrun₀]
        rw [rightBlockNarrowed_nil]
        rfl
      have hpair :=
        Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (hrun.symm.trans hcomp)))
      have hthreads :
          threads =
            rightOpenSubset atom₀
              (rightBlockNarrowed (tauTree σ τ) node₀ []) x :=
        congrArg Prod.snd hpair
      rw [hthreads] at hqm
      obtain ⟨inputTwo, hqm'⟩ := mem_rightOpenSubset hqm
      refine ⟨[(inputTwo, x)], rfl, ?_⟩
      have hctrl :
          narrowedControl (A.rightBlockMonitor atom₀.1)
              (rightBlockNarrowed (tauTree σ τ) node₀)
              ([] ++ [(inputTwo, x)]) =
            (A.rightBlockMonitor atom₀.1).step
              (A.rightBlockMonitor atom₀.1).initial
              (narrowedRecord (A.rightBlockMonitor atom₀.1)
                (rightBlockNarrowed (tauTree σ τ) node₀ [])
                (A.rightBlockMonitor atom₀.1).initial (inputTwo, x)) := by
        rw [narrowedControl_append]
        rfl
      rw [show ([(inputTwo, x)] : TreeNode (In₂ × In₁)) =
        [] ++ [(inputTwo, x)] from rfl, hctrl,
        rightBlockMonitor_step_open atom₀
          (rightBlockNarrowed (tauTree σ τ) node₀ []) (inputTwo, x)]
      exact hqm'.symm
  | append_singleton w x' ih =>
      intro x c threads hrun qm hqm
      obtain ⟨threads', hrun'⟩ :=
        globalRunIn_block_right CL CR CC (tauTree σ τ) node₀ atom₀ hrun₀ w x'
      have hcomp :
          globalRunIn CL CR CC (tauTree σ τ)
              (Sum.inl (A.initial, A.initial))
              (node₀ ++ senderRNode (A := A) ((w ++ [x']) ++ [x])) =
            Sum.inr (Sum.inr (Sum.inl
              (CR.monitor.step
                  (DeterministicBlockMonitor.controlIn CR.monitor
                    (rightBlockNarrowed (tauTree σ τ) node₀)
                    (CR.start atom₀.1) (w ++ [x']))
                  (rightBlockNarrowed (tauTree σ τ) node₀ (w ++ [x'])) x,
                rightStepSubset threads'
                  (rightBlockNarrowed (tauTree σ τ) node₀ (w ++ [x']))
                  x))) := by
        rw [show node₀ ++ senderRNode (A := A) ((w ++ [x']) ++ [x]) =
          (node₀ ++ senderRNode (A := A) (w ++ [x'])) ++
            [Sum.inr (Sum.inr x)] from by
          rw [senderRNode_append (A := A) (w ++ [x']) x,
            List.append_assoc]]
        rw [globalRunIn_append, hrun']
        rfl
      have hpair :=
        Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (hrun.symm.trans hcomp)))
      have hthreads :
          threads =
            rightStepSubset threads'
              (rightBlockNarrowed (tauTree σ τ) node₀ (w ++ [x'])) x :=
        congrArg Prod.snd hpair
      rw [hthreads] at hqm
      obtain ⟨base, inputTwo, hbase, hqm'⟩ := mem_rightStepSubset hqm
      obtain ⟨ms', hsw', hctrl'⟩ :=
        ih x' _ threads' hrun' base hbase
      refine ⟨ms' ++ [(inputTwo, x)], ?_, ?_⟩
      · rw [senderWord_append, hsw']
      · rw [narrowedControl_append, hctrl', hsw',
          rightBlockMonitor_step_narrowedRecord atom₀.1 base
            (rightBlockNarrowed (tauTree σ τ) node₀ (w ++ [x']))
            (inputTwo, x)]
        exact hqm'.symm

end Inversion

end DetParityAutomaton

end DistributedSynthesis
