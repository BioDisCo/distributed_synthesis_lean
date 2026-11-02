/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmTauTree

/-!
# Realization of the journal tree inside the uniformization game

Every non-sink state of the deterministic run over the winner's
journal tree is realized by a consistent play of the uniformization
game: atoms are reached boundaries, and every realized thread of a
block mode is a reachable block position.  Reachability is closed
under single steps by play surgery (replace the tail beyond the
reached position by the deterministic follow-up play), and the
invariant is a forward induction over nodes, consuming the
subset-membership witnesses of the automaton's transitions.
-/

set_option linter.unusedSectionVars false

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

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

/-! ### The deterministic follow-up play -/

/-- Follow the winner at its positions, any legal move elsewhere. -/
noncomputable def followMove
    (position : UniformizationPosition (In₁ := In₁) A) :
    UniformizationPosition (In₁ := In₁) A :=
  if _h :
      (uniformizationGame A σ).owner position = ParityPlayer.even then
    τ.move position
  else Classical.choose ((uniformizationGame A σ).step_total position)

theorem followMove_step
    (position : UniformizationPosition (In₁ := In₁) A) :
    (uniformizationGame A σ).step position (followMove σ τ position) := by
  unfold followMove
  split
  · exact τ.legal position (by assumption)
  · exact
      Classical.choose_spec ((uniformizationGame A σ).step_total position)

/-- The deterministic play following the winner from a position. -/
noncomputable def followPlay
    (start : UniformizationPosition (In₁ := In₁) A) :
    Nat -> UniformizationPosition (In₁ := In₁) A
  | 0 => start
  | n + 1 => followMove σ τ (followPlay start n)

theorem followPlay_playFrom
    (start : UniformizationPosition (In₁ := In₁) A) :
    (uniformizationGame A σ).PlayFrom start (followPlay σ τ start) :=
  ⟨rfl, fun n => followMove_step σ τ (followPlay σ τ start n)⟩

theorem followPlay_consistent
    (start : UniformizationPosition (In₁ := In₁) A) :
    CountableParityGame.PositionalStrategy.Consistent
      (G := uniformizationGame A σ) τ (followPlay σ τ start) := by
  intro n howner
  show followMove σ τ (followPlay σ τ start n) = _
  unfold followMove
  rw [dif_pos howner]

/-! ### Reachability by consistent plays -/

/-- A position is reached by some consistent play from the initial
boundary. -/
def Reaches (position : UniformizationPosition (In₁ := In₁) A) : Prop :=
  ∃ (path : Nat -> UniformizationPosition (In₁ := In₁) A) (n : Nat),
    (uniformizationGame A σ).PlayFrom (.bnd (A.initial, A.initial))
        path ∧
      CountableParityGame.PositionalStrategy.Consistent
        (G := uniformizationGame A σ) τ path ∧
      path n = position

theorem reaches_initial :
    Reaches σ τ (.bnd (A.initial, A.initial) :
      UniformizationPosition (In₁ := In₁) A) :=
  ⟨followPlay σ τ _, 0, followPlay_playFrom σ τ _,
    followPlay_consistent σ τ _, rfl⟩

/-- Reachability extends along steps whose Even moves agree with the
winner: play surgery replaces the tail by the follow-up play. -/
theorem reaches_step
    {P Q : UniformizationPosition (In₁ := In₁) A}
    (hP : Reaches σ τ P)
    (hstep : (uniformizationGame A σ).step P Q)
    (heven :
      (uniformizationGame A σ).owner P = ParityPlayer.even ->
        τ.move P = Q) :
    Reaches σ τ Q := by
  obtain ⟨path, n, hplay, hcons, hn⟩ := hP
  refine
    ⟨fun m => if m ≤ n then path m else followPlay σ τ Q (m - (n + 1)),
      n + 1, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only []
    rw [if_pos (Nat.zero_le n)]
    exact hplay.1
  · intro m
    simp only []
    rcases Nat.lt_trichotomy m n with hlt | heq | hgt
    · rw [if_pos (by omega), if_pos (by omega)]
      exact hplay.2 m
    · subst heq
      rw [if_pos (Nat.le_refl m), if_neg (by omega),
        show m + 1 - (m + 1) = 0 by omega, hn]
      exact hstep
    · rw [if_neg (by omega), if_neg (by omega),
        show m + 1 - (n + 1) = m - (n + 1) + 1 by omega]
      exact followMove_step σ τ _
  · intro m howner
    simp only [] at howner ⊢
    rcases Nat.lt_trichotomy m n with hlt | heq | hgt
    · rw [if_pos (by omega)] at howner ⊢
      rw [if_pos (by omega)]
      exact hcons m howner
    · subst heq
      rw [if_pos (Nat.le_refl m)] at howner ⊢
      rw [if_neg (by omega), show m + 1 - (m + 1) = 0 by omega]
      rw [hn] at howner ⊢
      exact (heven howner).symm
    · rw [if_neg (by omega)] at howner ⊢
      rw [if_neg (by omega),
        show m + 1 - (n + 1) = m - (n + 1) + 1 by omega]
      show followMove σ τ _ = _
      unfold followMove
      rw [dif_pos howner]
  · simp only []
    rw [if_neg (by omega), show n + 1 - (n + 1) = 0 by omega]
    rfl

/-! ### Choice specifications -/

theorem openingChoice_spec (atom : A.State × A.State)
    (move : In₁ × In₂) :
    τ.move (.opening atom (commitmentOf σ τ atom) move) =
      .openingResolve atom (commitmentOf σ τ atom) move
        (openingChoice σ τ atom move).1
        (openingChoice σ τ atom move).2 := by
  obtain ⟨outOne, outTwo, hmv⟩ :=
    τ.legal (.opening atom (commitmentOf σ τ atom) move) rfl
  rw [hmv]
  unfold openingChoice
  rw [hmv]

theorem recvChoiceL_spec (atom : A.State × A.State) (word : List In₂)
    (state minState : A.State) (move : In₁ × In₂) :
    τ.move
        (.recvL (commitmentOf σ τ atom) word state minState
          (blockRevTableL σ τ atom word state minState) move) =
      .resolveL (commitmentOf σ τ atom) word state minState
        (blockRevTableL σ τ atom word state minState) move
        (recvChoiceL σ τ atom word state minState move) := by
  obtain ⟨outOne, hmv⟩ :=
    τ.legal
      (.recvL (commitmentOf σ τ atom) word state minState
        (blockRevTableL σ τ atom word state minState) move)
      rfl
  rw [hmv]
  unfold recvChoiceL
  rw [hmv]

theorem recvChoiceR_spec (atom : A.State × A.State) (word : List In₁)
    (state minState : A.State) (move : In₁ × In₂) :
    τ.move
        (.recvR (commitmentOf σ τ atom) word state minState
          (blockRevTableR σ τ atom word state minState) move) =
      .resolveR (commitmentOf σ τ atom) word state minState
        (blockRevTableR σ τ atom word state minState) move
        (recvChoiceR σ τ atom word state minState move) := by
  obtain ⟨outTwo, hmv⟩ :=
    τ.legal
      (.recvR (commitmentOf σ τ atom) word state minState
        (blockRevTableR σ τ atom word state minState) move)
      rfl
  rw [hmv]
  unfold recvChoiceR
  rw [hmv]

theorem closeChoiceL_spec (atom : A.State × A.State) (word : List In₂)
    (state minState : A.State) (move : In₁ × In₂) :
    τ.move
        (.closeL (commitmentOf σ τ atom) word state minState
          (blockRevTableL σ τ atom word state minState) move
          (recvChoiceL σ τ atom word state minState move)) =
      .closeResolveL (commitmentOf σ τ atom) word state minState
        (blockRevTableL σ τ atom word state minState) move
        (recvChoiceL σ τ atom word state minState move)
        (closeChoiceL σ τ atom word state minState move) :=
  (τ.legal
      (.closeL (commitmentOf σ τ atom) word state minState
        (blockRevTableL σ τ atom word state minState) move
        (recvChoiceL σ τ atom word state minState move))
      rfl).choose_spec

theorem closeChoiceR_spec (atom : A.State × A.State) (word : List In₁)
    (state minState : A.State) (move : In₁ × In₂) :
    τ.move
        (.closeR (commitmentOf σ τ atom) word state minState
          (blockRevTableR σ τ atom word state minState) move
          (recvChoiceR σ τ atom word state minState move)) =
      .closeResolveR (commitmentOf σ τ atom) word state minState
        (blockRevTableR σ τ atom word state minState) move
        (recvChoiceR σ τ atom word state minState move)
        (closeChoiceR σ τ atom word state minState move) :=
  (τ.legal
      (.closeR (commitmentOf σ τ atom) word state minState
        (blockRevTableR σ τ atom word state minState) move
        (recvChoiceR σ τ atom word state minState move))
      rfl).choose_spec

/-- The block-level reversal table is the winner's committed choice at
the block position. -/
theorem blockRevTableL_spec (atom : A.State × A.State)
    (word : List In₂) (state minState : A.State) :
    τ.move (.blockL (commitmentOf σ τ atom) word state minState) =
      .blockEnvL (commitmentOf σ τ atom) word state minState
        (blockRevTableL σ τ atom word state minState) := by
  obtain ⟨tbl, hmv⟩ :=
    τ.legal (.blockL (commitmentOf σ τ atom) word state minState) rfl
  rw [hmv]
  unfold blockRevTableL
  rw [hmv]

theorem blockRevTableR_spec (atom : A.State × A.State)
    (word : List In₁) (state minState : A.State) :
    τ.move (.blockR (commitmentOf σ τ atom) word state minState) =
      .blockEnvR (commitmentOf σ τ atom) word state minState
        (blockRevTableR σ τ atom word state minState) := by
  obtain ⟨tbl, hmv⟩ :=
    τ.legal (.blockR (commitmentOf σ τ atom) word state minState) rfl
  rw [hmv]
  unfold blockRevTableR
  rw [hmv]

/-- The committed virtual view is the winner's choice at the handoff
into a reversed left block. -/
theorem commitmentRevL_spec (word : List In₂)
    (entryState entryMin : A.State) :
    τ.move (.revCommitL word entryState entryMin) =
      .revBlockL (commitmentRevL σ τ word entryState entryMin) word
        entryState entryMin entryState entryMin := by
  obtain ⟨hc, hmv⟩ :=
    τ.legal (.revCommitL word entryState entryMin) rfl
  rw [hmv]
  unfold commitmentRevL
  rw [hmv]

theorem commitmentRevR_spec (word : List In₁)
    (entryState entryMin : A.State) :
    τ.move (.revCommitR word entryState entryMin) =
      .revBlockR (commitmentRevR σ τ word entryState entryMin) word
        entryState entryMin entryState entryMin := by
  obtain ⟨hc, hmv⟩ :=
    τ.legal (.revCommitR word entryState entryMin) rfl
  rw [hmv]
  unfold commitmentRevR
  rw [hmv]

/-- The blind-send table is the winner's choice at the reversed-block
position. -/
theorem revSendTableL_spec (hc : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₂) (entryState entryMin state minState : A.State) :
    τ.move (.revBlockL hc word entryState entryMin state minState) =
      .revEnvL hc word entryState entryMin state minState
        (revSendTableL σ τ hc word entryState entryMin state minState) := by
  obtain ⟨tbl, hmv⟩ :=
    τ.legal (.revBlockL hc word entryState entryMin state minState) rfl
  rw [hmv]
  unfold revSendTableL
  rw [hmv]

theorem revSendTableR_spec (hc : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₁) (entryState entryMin state minState : A.State) :
    τ.move (.revBlockR hc word entryState entryMin state minState) =
      .revEnvR hc word entryState entryMin state minState
        (revSendTableR σ τ hc word entryState entryMin state minState) := by
  obtain ⟨tbl, hmv⟩ :=
    τ.legal (.revBlockR hc word entryState entryMin state minState) rfl
  rw [hmv]
  unfold revSendTableR
  rw [hmv]

/-- The shared receive responses are the winner's choices at the
reversed-block receiver stage. -/
theorem revRecvChoiceL_spec (hc : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₂) (entryState entryMin state minState : A.State)
    (move : In₁ × In₂) :
    τ.move
        (.revRecvL hc word entryState entryMin state minState
          (revSendTableL σ τ hc word entryState entryMin state minState)
          move) =
      .revResolveL hc word entryState entryMin state minState
        (revSendTableL σ τ hc word entryState entryMin state minState)
        move
        (revRecvChoiceL σ τ hc word entryState entryMin state minState
            move).1
        (revRecvChoiceL σ τ hc word entryState entryMin state minState
            move).2 := by
  obtain ⟨o1r, o2r, hmv⟩ :=
    τ.legal
      (.revRecvL hc word entryState entryMin state minState
        (revSendTableL σ τ hc word entryState entryMin state minState)
        move)
      rfl
  rw [hmv]
  unfold revRecvChoiceL
  rw [hmv]

theorem revRecvChoiceR_spec (hc : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₁) (entryState entryMin state minState : A.State)
    (move : In₁ × In₂) :
    τ.move
        (.revRecvR hc word entryState entryMin state minState
          (revSendTableR σ τ hc word entryState entryMin state minState)
          move) =
      .revResolveR hc word entryState entryMin state minState
        (revSendTableR σ τ hc word entryState entryMin state minState)
        move
        (revRecvChoiceR σ τ hc word entryState entryMin state minState
            move).1
        (revRecvChoiceR σ τ hc word entryState entryMin state minState
            move).2 := by
  obtain ⟨o1r, o2r, hmv⟩ :=
    τ.legal
      (.revRecvR hc word entryState entryMin state minState
        (revSendTableR σ τ hc word entryState entryMin state minState)
        move)
      rfl
  rw [hmv]
  unfold revRecvChoiceR
  rw [hmv]

/-! ### Reachability chains through the staged rounds -/

theorem reaches_opening (atom : A.State × A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.bnd atom :
      UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ (.opening atom (commitmentOf σ τ atom) move) := by
  have h1 :=
    reaches_step σ τ h
      (show (uniformizationGame A σ).step _ _ from
        ⟨commitmentOf σ τ atom, rfl⟩)
      fun _ => commitmentOf_spec σ τ atom
  exact
    reaches_step σ τ h1
      (show (uniformizationGame A σ).step _ _ from ⟨move, rfl⟩)
      fun howner => absurd howner (by simp [uniformizationGame,
        uniformizationOwner])

theorem reaches_openingResolve (atom : A.State × A.State)
    (move : In₁ × In₂)
    (h : Reaches σ τ (.bnd atom :
      UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (.openingResolve atom (commitmentOf σ τ atom) move
        (openingChoice σ τ atom move).1
        (openingChoice σ τ atom move).2) :=
  reaches_step σ τ (reaches_opening σ τ atom move h)
    (show (uniformizationGame A σ).step _ _ from ⟨_, _, rfl⟩)
    fun _ => openingChoice_spec σ τ atom move

theorem reaches_both_target (atom : A.State × A.State)
    (move : In₁ × In₂)
    (h : Reaches σ τ (.bnd atom :
      UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uOpenBothTarget (A := A) atom move
        (openingChoice σ τ atom move).1
        (openingChoice σ τ atom move).2) :=
  reaches_step σ τ (reaches_openingResolve σ τ atom move h)
    (Or.inl rfl)
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

theorem reaches_open_left (atom : A.State × A.State)
    (move : In₁ × In₂)
    (h : Reaches σ τ (.bnd atom :
      UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uOpenLeftTarget σ atom (commitmentOf σ τ atom) move
        (openingChoice σ τ atom move).1) :=
  reaches_step σ τ (reaches_openingResolve σ τ atom move h)
    (Or.inr (Or.inl rfl))
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

theorem reaches_open_right (atom : A.State × A.State)
    (move : In₁ × In₂)
    (h : Reaches σ τ (.bnd atom :
      UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uOpenRightTarget σ atom (commitmentOf σ τ atom) move
        (openingChoice σ τ atom move).2) :=
  reaches_step σ τ (reaches_openingResolve σ τ atom move h)
    (Or.inr (Or.inr rfl))
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

theorem reaches_resolveL (atom : A.State × A.State) (word : List In₂)
    (state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.blockL (commitmentOf σ τ atom) word state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (.resolveL (commitmentOf σ τ atom) word state minState
        (blockRevTableL σ τ atom word state minState) move
        (recvChoiceL σ τ atom word state minState move)) := by
  have h0 :=
    reaches_step σ τ h
      (show (uniformizationGame A σ).step _ _ from ⟨_, rfl⟩)
      fun _ => blockRevTableL_spec σ τ atom word state minState
  have h1 :=
    reaches_step σ τ h0
      (show (uniformizationGame A σ).step _ _ from ⟨move, rfl⟩)
      fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])
  exact
    reaches_step σ τ h1
      (show (uniformizationGame A σ).step _ _ from ⟨_, rfl⟩)
      fun _ => recvChoiceL_spec σ τ atom word state minState move

theorem reaches_continue_left (atom : A.State × A.State)
    (word : List In₂) (state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.blockL (commitmentOf σ τ atom) word state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uContinueLTarget σ (commitmentOf σ τ atom) word state minState
        move (recvChoiceL σ τ atom word state minState move)) :=
  reaches_step σ τ
    (reaches_resolveL σ τ atom word state minState move h)
    (Or.inl rfl)
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

theorem reaches_closeResolve_left (atom : A.State × A.State)
    (word : List In₂) (state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.blockL (commitmentOf σ τ atom) word state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (.closeResolveL (commitmentOf σ τ atom) word state minState
        (blockRevTableL σ τ atom word state minState) move
        (recvChoiceL σ τ atom word state minState move)
        (closeChoiceL σ τ atom word state minState move)) := by
  have h1 :=
    reaches_step σ τ
      (reaches_resolveL σ τ atom word state minState move h)
      (Or.inr rfl)
      fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])
  exact
    reaches_step σ τ h1
      (show (uniformizationGame A σ).step _ _ from ⟨_, rfl⟩)
      fun _ => closeChoiceL_spec σ τ atom word state minState move

theorem reaches_close_left (atom : A.State × A.State)
    (word : List In₂) (state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.blockL (commitmentOf σ τ atom) word state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uCloseTarget (A := A) state minState move
        (recvChoiceL σ τ atom word state minState move)
        (closeChoiceL σ τ atom word state minState move)) :=
  reaches_step σ τ
    (reaches_closeResolve_left σ τ atom word state minState move h)
    (Or.inl rfl)
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

/-- A direct reversal out of a left block is reached. -/
theorem reaches_reverse_right (atom : A.State × A.State)
    (word : List In₂) (state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.blockL (commitmentOf σ τ atom) word state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uRevReverseRTarget (A := A) state minState move
        (blockRevTableL σ τ atom word state minState move.1)
        (closeChoiceL σ τ atom word state minState move)) :=
  reaches_step σ τ
    (reaches_closeResolve_left σ τ atom word state minState move h)
    (Or.inr rfl)
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

theorem reaches_resolveR (atom : A.State × A.State) (word : List In₁)
    (state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.blockR (commitmentOf σ τ atom) word state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (.resolveR (commitmentOf σ τ atom) word state minState
        (blockRevTableR σ τ atom word state minState) move
        (recvChoiceR σ τ atom word state minState move)) := by
  have h0 :=
    reaches_step σ τ h
      (show (uniformizationGame A σ).step _ _ from ⟨_, rfl⟩)
      fun _ => blockRevTableR_spec σ τ atom word state minState
  have h1 :=
    reaches_step σ τ h0
      (show (uniformizationGame A σ).step _ _ from ⟨move, rfl⟩)
      fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])
  exact
    reaches_step σ τ h1
      (show (uniformizationGame A σ).step _ _ from ⟨_, rfl⟩)
      fun _ => recvChoiceR_spec σ τ atom word state minState move

theorem reaches_continue_right (atom : A.State × A.State)
    (word : List In₁) (state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.blockR (commitmentOf σ τ atom) word state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uContinueRTarget σ (commitmentOf σ τ atom) word state minState
        move (recvChoiceR σ τ atom word state minState move)) :=
  reaches_step σ τ
    (reaches_resolveR σ τ atom word state minState move h)
    (Or.inl rfl)
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

theorem reaches_closeResolve_right (atom : A.State × A.State)
    (word : List In₁) (state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.blockR (commitmentOf σ τ atom) word state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (.closeResolveR (commitmentOf σ τ atom) word state minState
        (blockRevTableR σ τ atom word state minState) move
        (recvChoiceR σ τ atom word state minState move)
        (closeChoiceR σ τ atom word state minState move)) := by
  have h1 :=
    reaches_step σ τ
      (reaches_resolveR σ τ atom word state minState move h)
      (Or.inr rfl)
      fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])
  exact
    reaches_step σ τ h1
      (show (uniformizationGame A σ).step _ _ from ⟨_, rfl⟩)
      fun _ => closeChoiceR_spec σ τ atom word state minState move

theorem reaches_close_right (atom : A.State × A.State)
    (word : List In₁) (state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.blockR (commitmentOf σ τ atom) word state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uCloseTarget (A := A) state minState move
        (closeChoiceR σ τ atom word state minState move)
        (recvChoiceR σ τ atom word state minState move)) :=
  reaches_step σ τ
    (reaches_closeResolve_right σ τ atom word state minState move h)
    (Or.inl rfl)
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

/-- A direct reversal out of a right block is reached. -/
theorem reaches_reverse_left (atom : A.State × A.State)
    (word : List In₁) (state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.blockR (commitmentOf σ τ atom) word state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uRevReverseLTarget (A := A) state minState move
        (closeChoiceR σ τ atom word state minState move)
        (blockRevTableR σ τ atom word state minState move.2)) :=
  reaches_step σ τ
    (reaches_closeResolve_right σ τ atom word state minState move h)
    (Or.inr rfl)
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

/-! ### Reachability through reversed blocks -/

/-- The handoff into a reversed left block commits the virtual view
and enters the reversed block. -/
theorem reaches_revBlockL (word : List In₂)
    (entryState entryMin : A.State)
    (h : Reaches σ τ (.revCommitL word entryState entryMin :
      UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (.revBlockL (commitmentRevL σ τ word entryState entryMin) word
        entryState entryMin entryState entryMin) :=
  reaches_step σ τ h
    (show (uniformizationGame A σ).step _ _ from ⟨_, rfl⟩)
    fun _ => commitmentRevL_spec σ τ word entryState entryMin

theorem reaches_revResolve_left
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (entryState entryMin state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.revBlockL hc word entryState entryMin state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (.revResolveL hc word entryState entryMin state minState
        (revSendTableL σ τ hc word entryState entryMin state minState)
        move
        (revRecvChoiceL σ τ hc word entryState entryMin state minState
            move).1
        (revRecvChoiceL σ τ hc word entryState entryMin state minState
            move).2) := by
  have h0 :=
    reaches_step σ τ h
      (show (uniformizationGame A σ).step _ _ from ⟨_, rfl⟩)
      fun _ =>
        revSendTableL_spec σ τ hc word entryState entryMin state minState
  have h1 :=
    reaches_step σ τ h0
      (show (uniformizationGame A σ).step _ _ from ⟨move, rfl⟩)
      fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])
  exact
    reaches_step σ τ h1
      (show (uniformizationGame A σ).step _ _ from ⟨_, _, rfl⟩)
      fun _ =>
        revRecvChoiceL_spec σ τ hc word entryState entryMin state
          minState move

theorem reaches_revContinue_left
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (entryState entryMin state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.revBlockL hc word entryState entryMin state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uRevContinueLTarget σ hc word entryState entryMin state minState
        move
        (revRecvChoiceL σ τ hc word entryState entryMin state minState
            move).1) :=
  reaches_step σ τ
    (reaches_revResolve_left σ τ hc word entryState entryMin state
      minState move h)
    (Or.inl rfl)
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

theorem reaches_revClose_left
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (entryState entryMin state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.revBlockL hc word entryState entryMin state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uCloseTarget (A := A) state minState move
        (revRecvChoiceL σ τ hc word entryState entryMin state minState
            move).1
        (revRecvChoiceL σ τ hc word entryState entryMin state minState
            move).2) :=
  reaches_step σ τ
    (reaches_revResolve_left σ τ hc word entryState entryMin state
      minState move h)
    (Or.inr (Or.inl rfl))
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

theorem reaches_revReverse_right
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (entryState entryMin state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.revBlockL hc word entryState entryMin state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uRevReverseRTarget (A := A) state minState move
        (revSendTableL σ τ hc word entryState entryMin state minState
            move.1)
        (revRecvChoiceL σ τ hc word entryState entryMin state minState
            move).2) :=
  reaches_step σ τ
    (reaches_revResolve_left σ τ hc word entryState entryMin state
      minState move h)
    (Or.inr (Or.inr rfl))
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

/-- The handoff into a reversed right block: the mirror. -/
theorem reaches_revBlockR (word : List In₁)
    (entryState entryMin : A.State)
    (h : Reaches σ τ (.revCommitR word entryState entryMin :
      UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (.revBlockR (commitmentRevR σ τ word entryState entryMin) word
        entryState entryMin entryState entryMin) :=
  reaches_step σ τ h
    (show (uniformizationGame A σ).step _ _ from ⟨_, rfl⟩)
    fun _ => commitmentRevR_spec σ τ word entryState entryMin

theorem reaches_revResolve_right
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (entryState entryMin state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.revBlockR hc word entryState entryMin state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (.revResolveR hc word entryState entryMin state minState
        (revSendTableR σ τ hc word entryState entryMin state minState)
        move
        (revRecvChoiceR σ τ hc word entryState entryMin state minState
            move).1
        (revRecvChoiceR σ τ hc word entryState entryMin state minState
            move).2) := by
  have h0 :=
    reaches_step σ τ h
      (show (uniformizationGame A σ).step _ _ from ⟨_, rfl⟩)
      fun _ =>
        revSendTableR_spec σ τ hc word entryState entryMin state minState
  have h1 :=
    reaches_step σ τ h0
      (show (uniformizationGame A σ).step _ _ from ⟨move, rfl⟩)
      fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])
  exact
    reaches_step σ τ h1
      (show (uniformizationGame A σ).step _ _ from ⟨_, _, rfl⟩)
      fun _ =>
        revRecvChoiceR_spec σ τ hc word entryState entryMin state
          minState move

theorem reaches_revContinue_right
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (entryState entryMin state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.revBlockR hc word entryState entryMin state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uRevContinueRTarget σ hc word entryState entryMin state minState
        move
        (revRecvChoiceR σ τ hc word entryState entryMin state minState
            move).2) :=
  reaches_step σ τ
    (reaches_revResolve_right σ τ hc word entryState entryMin state
      minState move h)
    (Or.inl rfl)
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

theorem reaches_revClose_right
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (entryState entryMin state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.revBlockR hc word entryState entryMin state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uCloseTarget (A := A) state minState move
        (revRecvChoiceR σ τ hc word entryState entryMin state minState
            move).1
        (revRecvChoiceR σ τ hc word entryState entryMin state minState
            move).2) :=
  reaches_step σ τ
    (reaches_revResolve_right σ τ hc word entryState entryMin state
      minState move h)
    (Or.inr (Or.inl rfl))
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

theorem reaches_revReverse_left
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (entryState entryMin state minState : A.State) (move : In₁ × In₂)
    (h : Reaches σ τ (.revBlockR hc word entryState entryMin state
      minState : UniformizationPosition (In₁ := In₁) A)) :
    Reaches σ τ
      (uRevReverseLTarget (A := A) state minState move
        (revRecvChoiceR σ τ hc word entryState entryMin state minState
            move).1
        (revSendTableR σ τ hc word entryState entryMin state minState
            move.2)) :=
  reaches_step σ τ
    (reaches_revResolve_right σ τ hc word entryState entryMin state
      minState move h)
    (Or.inr (Or.inr rfl))
    fun howner => absurd howner (by simp [uniformizationGame,
      uniformizationOwner])

end DetParityAutomaton

end DistributedSynthesis
