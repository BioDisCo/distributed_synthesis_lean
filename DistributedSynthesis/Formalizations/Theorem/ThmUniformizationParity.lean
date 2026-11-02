/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmUniformizationTracking
import DistributedSynthesis.Formalizations.Theorem.ThmArenaFold

/-!
# Parity transfer for the tracking strategy

This file completes step W1 of the heart plan: along every play of the
tracking strategy, the play's design-D3 priorities are squeezed
against the run priorities of the real word played by the tracked
strategy, so a winning tracked strategy makes every consistent play
min-even (`trackingStrategy_winningFrom`), placing the initial
boundary in Even's winning region of the uniformization game.
Positional determinacy of countable parity games then yields step W2:
a positional Even winner of the uniformization game
(`exists_positional_uniformization_winner`), whose boundary
commitments are per atom.

The infrastructure reads the environment sequence off the play: the
tracking memory grows by exactly the completed rounds (a stage rank
argument shows a round completes within every four steps), its
histories are nested prefixes, and the induced infinite environment
sequence is no-direct with the memory as its execution prefixes.
-/

set_option linter.unusedSectionVars false

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

instance [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] :
    Inhabited (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  ⟨⟨default, default, Graph.both, default, default⟩⟩

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

open UniformizationPosition

section Clock

variable (σ : StrategyPair In₁ In₂ Out₁ Out₂)
variable [Inhabited In₁] [Inhabited In₂]

omit [Inhabited In₁] [Inhabited In₂] in
/-- Every memory step either keeps the history or appends one round. -/
theorem trackUpdate_fst_cases
    (mem :
      History In₁ In₂ Graph Out₁ Out₂ ×
        UniformizationPosition (In₁ := In₁) A)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ mem p).1 = mem.1 ∨
      ∃ env : EnvironmentRound In₁ In₂,
        (trackUpdate σ mem p).1 =
          History.append mem.1 (nextRound σ mem.1 env) := by
  rcases mem with ⟨h, prev⟩
  cases prev <;> cases p <;>
    first
      | exact Or.inl rfl
      | exact Or.inr ⟨_, rfl⟩

variable (path : Nat -> UniformizationPosition (In₁ := In₁) A)

/-- The number of completed rounds after `n` game steps. -/
def playClock (n : Nat) : Nat :=
  List.length (pathMemory σ path n).1

omit [Inhabited In₁] [Inhabited In₂] in
@[simp]
theorem playClock_zero : playClock σ path 0 = 0 :=
  rfl

theorem playClock_succ_cases (n : Nat) :
    playClock σ path (n + 1) = playClock σ path n ∨
      playClock σ path (n + 1) = playClock σ path n + 1 := by
  have hcases :=
    trackUpdate_fst_cases σ ((pathMemory σ path n).1, path n) (path (n + 1))
  rcases hcases with hsame | ⟨env, happ⟩
  · left
    show List.length (pathMemory σ path (n + 1)).1 = _
    rw [pathMemory_fst_succ σ path n, hsame]
    rfl
  · right
    show List.length (pathMemory σ path (n + 1)).1 = _
    rw [pathMemory_fst_succ σ path n, happ]
    simp [History.append, playClock]

theorem playClock_le_succ (n : Nat) :
    playClock σ path n ≤ playClock σ path (n + 1) := by
  rcases playClock_succ_cases σ path n with h | h <;> omega

theorem playClock_mono : Monotone (playClock σ path) :=
  monotone_nat_of_le_succ (playClock_le_succ σ path)

theorem playClock_le_self (n : Nat) : playClock σ path n ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rcases playClock_succ_cases σ path n with h | h <;> omega

/-- Stage rank: strictly decreasing along non-completing steps. -/
def stageRank : UniformizationPosition (In₁ := In₁) A -> Nat
  | .bnd _ => 5
  | .committed _ _ => 4
  | .opening _ _ _ => 3
  | .openingResolve _ _ _ _ _ => 2
  | .blockL _ _ _ _ => 6
  | .blockEnvL _ _ _ _ _ => 5
  | .recvL _ _ _ _ _ _ => 4
  | .resolveL _ _ _ _ _ _ _ => 3
  | .closeL _ _ _ _ _ _ _ => 2
  | .closeResolveL _ _ _ _ _ _ _ _ => 1
  | .blockR _ _ _ _ => 6
  | .blockEnvR _ _ _ _ _ => 5
  | .recvR _ _ _ _ _ _ => 4
  | .resolveR _ _ _ _ _ _ _ => 3
  | .closeR _ _ _ _ _ _ _ => 2
  | .closeResolveR _ _ _ _ _ _ _ _ => 1
  | .revCommitL _ _ _ => 7
  | .revBlockL _ _ _ _ _ _ => 6
  | .revEnvL _ _ _ _ _ _ _ => 5
  | .revRecvL _ _ _ _ _ _ _ _ => 4
  | .revResolveL _ _ _ _ _ _ _ _ _ _ => 3
  | .revCommitR _ _ _ => 7
  | .revBlockR _ _ _ _ _ _ => 6
  | .revEnvR _ _ _ _ _ _ _ => 5
  | .revRecvR _ _ _ _ _ _ _ _ => 4
  | .revResolveR _ _ _ _ _ _ _ _ _ _ => 3

/-- Every legal step completes a round or strictly decreases the rank. -/
theorem playClock_succ_or_rank_lt
    (hplay : ∀ k, uniformizationStep σ (path k) (path (k + 1)))
    (n : Nat) :
    playClock σ path (n + 1) = playClock σ path n + 1 ∨
      stageRank (path (n + 1)) < stageRank (path n) := by
  have hstep := hplay n
  have happend :
      ∀ env : EnvironmentRound In₁ In₂,
        (trackUpdate σ ((pathMemory σ path n).1, path n) (path (n + 1))).1 =
            History.append (pathMemory σ path n).1
              (nextRound σ (pathMemory σ path n).1 env) ->
          playClock σ path (n + 1) = playClock σ path n + 1 := by
    intro env happ
    show List.length (pathMemory σ path (n + 1)).1 = _
    rw [pathMemory_fst_succ σ path n, happ]
    simp [History.append, playClock]
  rcases hpos : path n with
    atom | ⟨atom, h⟩ | ⟨atom, h, move⟩ | ⟨atom, h, move, outOne, outTwo⟩ |
    ⟨h, word, state, minState⟩ | ⟨h, word, state, minState, tbl⟩ |
    ⟨h, word, state, minState, tbl, move⟩ |
    ⟨h, word, state, minState, tbl, move, outOne⟩ |
    ⟨h, word, state, minState, tbl, move, outOne⟩ |
    ⟨h, word, state, minState, tbl, move, outOne, outTwo⟩ |
    ⟨h, word, state, minState⟩ | ⟨h, word, state, minState, tbl⟩ |
    ⟨h, word, state, minState, tbl, move⟩ |
    ⟨h, word, state, minState, tbl, move, outTwo⟩ |
    ⟨h, word, state, minState, tbl, move, outTwo⟩ |
    ⟨h, word, state, minState, tbl, move, outTwo, outOne⟩ |
    ⟨word, eqs, ems⟩ | ⟨hc, word, eqs, ems, state, minState⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl, move⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl, move, o1r, o2r⟩ |
    ⟨word, eqs, ems⟩ | ⟨hc, word, eqs, ems, state, minState⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl, move⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl, move, o1r, o2r⟩
  all_goals rw [hpos] at hstep happend
  · obtain ⟨h', hnext⟩ :
        ∃ h', path (n + 1) = .committed atom h' := hstep
    right
    rw [hnext]
    simp [stageRank]
  · obtain ⟨move, hnext⟩ :
        ∃ move : In₁ × In₂, path (n + 1) = .opening atom h move := hstep
    right
    rw [hnext]
    simp [stageRank]
  · obtain ⟨outOne, outTwo, hnext⟩ :
        ∃ (outOne : Out₁) (outTwo : Out₂),
          path (n + 1) = .openingResolve atom h move outOne outTwo := hstep
    right
    rw [hnext]
    simp [stageRank]
  · have hstep' :
        path (n + 1) = uOpenBothTarget (A := A) atom move outOne outTwo ∨
          path (n + 1) = uOpenLeftTarget σ atom h move outOne ∨
          path (n + 1) = uOpenRightTarget σ atom h move outTwo := hstep
    left
    rcases hstep' with hnext | hnext | hnext
    · exact happend (bothEnvironment move) (by rw [hnext]; rfl)
    · exact happend (leftEnvironment move) (by rw [hnext]; rfl)
    · exact happend (rightEnvironment (move.2, move.1)) (by rw [hnext]; rfl)
  · obtain ⟨tbl, hnext⟩ :
        ∃ tbl : In₁ -> Out₁,
          path (n + 1) = .blockEnvL h word state minState tbl := hstep
    right
    rw [hnext]
    simp [stageRank]
  · obtain ⟨move, hnext⟩ :
        ∃ move : In₁ × In₂,
          path (n + 1) = .recvL h word state minState tbl move := hstep
    right
    rw [hnext]
    simp [stageRank]
  · obtain ⟨outOne, hnext⟩ :
        ∃ outOne : Out₁,
          path (n + 1) =
            .resolveL h word state minState tbl move outOne := hstep
    right
    rw [hnext]
    simp [stageRank]
  · have hstep' :
        path (n + 1) =
            uContinueLTarget σ h word state minState move outOne ∨
          path (n + 1) =
            .closeL h word state minState tbl move outOne := hstep
    rcases hstep' with hnext | hnext
    · exact Or.inl (happend (leftEnvironment move) (by rw [hnext]; rfl))
    · right
      rw [hnext]
      simp [stageRank]
  · obtain ⟨outTwo, hnext⟩ :
        ∃ outTwo : Out₂,
          path (n + 1) =
            .closeResolveL h word state minState tbl move outOne
              outTwo := hstep
    right
    rw [hnext]
    simp [stageRank]
  · have hstep' :
        path (n + 1) =
            uCloseTarget (A := A) state minState move outOne outTwo ∨
          path (n + 1) =
            uRevReverseRTarget (A := A) state minState move
              (tbl move.1) outTwo := hstep
    left
    rcases hstep' with hnext | hnext
    · exact happend (bothEnvironment move) (by rw [hnext]; rfl)
    · exact happend (rightEnvironment (move.2, move.1)) (by rw [hnext]; rfl)
  · obtain ⟨tbl, hnext⟩ :
        ∃ tbl : In₂ -> Out₂,
          path (n + 1) = .blockEnvR h word state minState tbl := hstep
    right
    rw [hnext]
    simp [stageRank]
  · obtain ⟨move, hnext⟩ :
        ∃ move : In₁ × In₂,
          path (n + 1) = .recvR h word state minState tbl move := hstep
    right
    rw [hnext]
    simp [stageRank]
  · obtain ⟨outTwo, hnext⟩ :
        ∃ outTwo : Out₂,
          path (n + 1) =
            .resolveR h word state minState tbl move outTwo := hstep
    right
    rw [hnext]
    simp [stageRank]
  · have hstep' :
        path (n + 1) =
            uContinueRTarget σ h word state minState move outTwo ∨
          path (n + 1) =
            .closeR h word state minState tbl move outTwo := hstep
    rcases hstep' with hnext | hnext
    · exact
        Or.inl
          (happend (rightEnvironment (move.2, move.1))
            (by rw [hnext]; rfl))
    · right
      rw [hnext]
      simp [stageRank]
  · obtain ⟨outOne, hnext⟩ :
        ∃ outOne : Out₁,
          path (n + 1) =
            .closeResolveR h word state minState tbl move outTwo
              outOne := hstep
    right
    rw [hnext]
    simp [stageRank]
  · have hstep' :
        path (n + 1) =
            uCloseTarget (A := A) state minState move outOne outTwo ∨
          path (n + 1) =
            uRevReverseLTarget (A := A) state minState move outOne
              (tbl move.2) := hstep
    left
    rcases hstep' with hnext | hnext
    · exact happend (bothEnvironment move) (by rw [hnext]; rfl)
    · exact happend (leftEnvironment move) (by rw [hnext]; rfl)
  · obtain ⟨hc, hnext⟩ :
        ∃ hc : History In₁ In₂ Graph Out₁ Out₂,
          path (n + 1) = .revBlockL hc word eqs ems eqs ems := hstep
    right
    rw [hnext]
    simp [stageRank]
  · obtain ⟨tbl, hnext⟩ :
        ∃ tbl : In₁ -> Out₁,
          path (n + 1) =
            .revEnvL hc word eqs ems state minState tbl := hstep
    right
    rw [hnext]
    simp [stageRank]
  · obtain ⟨move, hnext⟩ :
        ∃ move : In₁ × In₂,
          path (n + 1) =
            .revRecvL hc word eqs ems state minState tbl move := hstep
    right
    rw [hnext]
    simp [stageRank]
  · obtain ⟨o1r, o2r, hnext⟩ :
        ∃ (o1r : Out₁) (o2r : Out₂),
          path (n + 1) =
            .revResolveL hc word eqs ems state minState tbl move o1r
              o2r := hstep
    right
    rw [hnext]
    simp [stageRank]
  · have hstep' :
        path (n + 1) =
            uRevContinueLTarget σ hc word eqs ems state minState move
              o1r ∨
          path (n + 1) =
            uCloseTarget (A := A) state minState move o1r o2r ∨
          path (n + 1) =
            uRevReverseRTarget (A := A) state minState move
              (tbl move.1) o2r := hstep
    left
    rcases hstep' with hnext | hnext | hnext
    · exact happend (leftEnvironment move) (by rw [hnext]; rfl)
    · exact happend (bothEnvironment move) (by rw [hnext]; rfl)
    · exact happend (rightEnvironment (move.2, move.1)) (by rw [hnext]; rfl)
  · obtain ⟨hc, hnext⟩ :
        ∃ hc : History In₁ In₂ Graph Out₁ Out₂,
          path (n + 1) = .revBlockR hc word eqs ems eqs ems := hstep
    right
    rw [hnext]
    simp [stageRank]
  · obtain ⟨tbl, hnext⟩ :
        ∃ tbl : In₂ -> Out₂,
          path (n + 1) =
            .revEnvR hc word eqs ems state minState tbl := hstep
    right
    rw [hnext]
    simp [stageRank]
  · obtain ⟨move, hnext⟩ :
        ∃ move : In₁ × In₂,
          path (n + 1) =
            .revRecvR hc word eqs ems state minState tbl move := hstep
    right
    rw [hnext]
    simp [stageRank]
  · obtain ⟨o1r, o2r, hnext⟩ :
        ∃ (o1r : Out₁) (o2r : Out₂),
          path (n + 1) =
            .revResolveR hc word eqs ems state minState tbl move o1r
              o2r := hstep
    right
    rw [hnext]
    simp [stageRank]
  · have hstep' :
        path (n + 1) =
            uRevContinueRTarget σ hc word eqs ems state minState move
              o2r ∨
          path (n + 1) =
            uCloseTarget (A := A) state minState move o1r o2r ∨
          path (n + 1) =
            uRevReverseLTarget (A := A) state minState move o1r
              (tbl move.2) := hstep
    left
    rcases hstep' with hnext | hnext | hnext
    · exact happend (rightEnvironment (move.2, move.1)) (by rw [hnext]; rfl)
    · exact happend (bothEnvironment move) (by rw [hnext]; rfl)
    · exact happend (leftEnvironment move) (by rw [hnext]; rfl)

/-- A round completes at some step at or after every given step. -/
theorem exists_playClock_succ_ge
    (hplay : ∀ k, uniformizationStep σ (path k) (path (k + 1)))
    (n : Nat) :
    ∃ k : Nat,
      n ≤ k ∧ playClock σ path (k + 1) = playClock σ path k + 1 := by
  by_contra hnone
  push Not at hnone
  have hdesc :
      ∀ j : Nat,
        stageRank (path (n + j + 1)) < stageRank (path (n + j)) := by
    intro j
    rcases playClock_succ_or_rank_lt σ path hplay (n + j) with happ | hrank
    · exact absurd happ (hnone (n + j) (by omega))
    · exact hrank
  have hle : ∀ j : Nat, stageRank (path (n + j)) + j ≤ stageRank (path n) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have := hdesc j
        have hj1 : n + (j + 1) = n + j + 1 := by omega
        rw [hj1]
        omega
  have h8 := hle 8
  have hbound : stageRank (path (n + 8)) ≤ 7 := by
    cases path (n + 8) <;> simp [stageRank]
  have hbound' : stageRank (path n) ≤ 7 := by
    cases path n <;> simp [stageRank]
  omega

/-- The play completes infinitely many rounds. -/
theorem playClock_unbounded
    (hplay : ∀ k, uniformizationStep σ (path k) (path (k + 1))) :
    ∀ t : Nat, ∃ n : Nat, t < playClock σ path n := by
  intro t
  induction t with
  | zero =>
      obtain ⟨k, _, happ⟩ := exists_playClock_succ_ge σ path hplay 0
      exact ⟨k + 1, by omega⟩
  | succ t ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨k, hk, happ⟩ := exists_playClock_succ_ge σ path hplay n
      have hmono := playClock_mono σ path hk
      exact ⟨k + 1, by omega⟩

/-- Reconstructed histories are nested prefixes along the play. -/
theorem pathMemory_prefix (n m : Nat) (hnm : n ≤ m) :
    (pathMemory σ path n).1 <+: (pathMemory σ path m).1 := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst hn
      exact List.prefix_refl _
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · have hprev := ih (by omega)
        refine hprev.trans ?_
        have hcases :=
          trackUpdate_fst_cases σ (pathMemory σ path m) (path (m + 1))
        show (pathMemory σ path m).1 <+:
          (trackUpdate σ (pathMemory σ path m) (path (m + 1))).1
        rcases hcases with hsame | ⟨env, happ⟩
        · rw [hsame]
        · rw [happ]
          exact ⟨_, rfl⟩
      · have hn : n = m + 1 := by omega
        subst hn
        exact List.prefix_refl _

/-- Reads below the clock are stable along the play. -/
theorem pathMemory_getD_stable
    [Inhabited Out₁] [Inhabited Out₂]
    {t n m : Nat}
    (hn : t < playClock σ path n) (hnm : n ≤ m) :
    ((pathMemory σ path m).1).getD t default =
      ((pathMemory σ path n).1).getD t default := by
  obtain ⟨tail, htail⟩ := pathMemory_prefix σ path n m hnm
  rw [← htail, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hn]

variable [Inhabited Out₁] [Inhabited Out₂]

/-- The environment sequence read off the play. -/
noncomputable def playEnv
    (hgrow : ∀ t : Nat, ∃ n : Nat, t < playClock σ path n)
    (t : Nat) : EnvironmentRound In₁ In₂ :=
  (((pathMemory σ path (Nat.find (hgrow t))).1).getD t default).environment

/-- The environment sequence agrees with every late enough read. -/
theorem playEnv_eq
    (hgrow : ∀ t : Nat, ∃ n : Nat, t < playClock σ path n)
    {t n : Nat} (hn : t < playClock σ path n) :
    playEnv σ path hgrow t =
      (((pathMemory σ path n).1).getD t default).environment := by
  have hfind : t < playClock σ path (Nat.find (hgrow t)) :=
    Nat.find_spec (hgrow t)
  rcases Nat.le_total (Nat.find (hgrow t)) n with hle | hle
  · rw [playEnv, pathMemory_getD_stable σ path hfind hle]
  · rw [playEnv, pathMemory_getD_stable σ path hn hle]

/--
The reconstructed history is the execution prefix of the tracked
strategy against the environment sequence read off the play.
-/
theorem pathMemory_eq_executionPrefix
    (hgrow : ∀ t : Nat, ∃ n : Nat, t < playClock σ path n) :
    ∀ n : Nat,
      (pathMemory σ path n).1 =
        executionPrefix σ (playEnv σ path hgrow) (playClock σ path n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hcases :=
        trackUpdate_fst_cases σ (pathMemory σ path n) (path (n + 1))
      have hmem :
          (pathMemory σ path (n + 1)).1 =
            (trackUpdate σ (pathMemory σ path n) (path (n + 1))).1 := rfl
      rcases hcases with hsame | ⟨env, happ⟩
      · have hclock : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [hmem, hsame]
          rfl
        rw [hmem, hsame, hclock]
        exact ih
      · have hclock :
            playClock σ path (n + 1) = playClock σ path n + 1 := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [hmem, happ]
          simp [History.append, playClock]
        have henv : playEnv σ path hgrow (playClock σ path n) = env := by
          have hlt : playClock σ path n < playClock σ path (n + 1) := by
            omega
          rw [playEnv_eq σ path hgrow hlt, hmem, happ]
          have hget :
              (History.append (pathMemory σ path n).1
                    (nextRound σ (pathMemory σ path n).1 env)).getD
                  (playClock σ path n) default =
                nextRound σ (pathMemory σ path n).1 env := by
            show
              ((pathMemory σ path n).1 ++
                    [nextRound σ (pathMemory σ path n).1 env]).getD
                  ((pathMemory σ path n).1).length default =
                nextRound σ (pathMemory σ path n).1 env
            rw [List.getD_eq_getElem?_getD]
            rw [show ((pathMemory σ path n).1).length =
              List.length (pathMemory σ path n).1 from rfl,
              List.getElem?_append_right (le_refl _)]
            simp
          rw [hget]
          rfl
        rw [hmem, happ, hclock, executionPrefix_succ, ← ih, henv]

omit [Inhabited In₁] [Inhabited In₂] in
/-- The run of the induced word matches the reconstructed states. -/
theorem historyState_executionPrefix
    (env : EnvironmentSequence In₁ In₂) :
    ∀ t : Nat,
      A.historyState (executionPrefix σ env t) =
        A.run (execution σ env) t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [executionPrefix_succ, A.historyState_append, ih,
        ← execution_apply]
      rfl

/-! ### Memory updates by previous stage -/

theorem trackUpdate_fst_bnd (H : History In₁ In₂ Graph Out₁ Out₂)
    (atom : A.State × A.State)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ (H, .bnd atom) p).1 = H := by
  cases p <;> rfl

theorem trackUpdate_fst_committed (H : History In₁ In₂ Graph Out₁ Out₂)
    (atom : A.State × A.State) (h : History In₁ In₂ Graph Out₁ Out₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ (H, .committed atom h) p).1 = H := by
  cases p <;> rfl

theorem trackUpdate_fst_opening (H : History In₁ In₂ Graph Out₁ Out₂)
    (atom : A.State × A.State) (h : History In₁ In₂ Graph Out₁ Out₂)
    (move : In₁ × In₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ (H, .opening atom h move) p).1 = H := by
  cases p <;> rfl

theorem trackUpdate_fst_blockL (H : History In₁ In₂ Graph Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (state minState : A.State)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ (H, .blockL h word state minState) p).1 = H := by
  cases p <;> rfl

theorem trackUpdate_fst_blockEnvL (H : History In₁ In₂ Graph Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (state minState : A.State) (tbl : In₁ -> Out₁)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ (H, .blockEnvL h word state minState tbl) p).1 =
      H := by
  cases p <;> rfl

theorem trackUpdate_fst_recvL (H : History In₁ In₂ Graph Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (state minState : A.State) (tbl : In₁ -> Out₁) (move : In₁ × In₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ (H, .recvL h word state minState tbl move) p).1 =
      H := by
  cases p <;> rfl

theorem trackUpdate_fst_blockR (H : History In₁ In₂ Graph Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (state minState : A.State)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ (H, .blockR h word state minState) p).1 = H := by
  cases p <;> rfl

theorem trackUpdate_fst_blockEnvR (H : History In₁ In₂ Graph Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (state minState : A.State) (tbl : In₂ -> Out₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ (H, .blockEnvR h word state minState tbl) p).1 =
      H := by
  cases p <;> rfl

theorem trackUpdate_fst_recvR (H : History In₁ In₂ Graph Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (state minState : A.State) (tbl : In₂ -> Out₂) (move : In₁ × In₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ (H, .recvR h word state minState tbl move) p).1 =
      H := by
  cases p <;> rfl

theorem trackUpdate_fst_revCommitL (H : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₂) (entryState entryMin : A.State)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ (H, .revCommitL word entryState entryMin) p).1 =
      H := by
  cases p <;> rfl

theorem trackUpdate_fst_revBlockL (H : History In₁ In₂ Graph Out₁ Out₂)
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (entryState entryMin state minState : A.State)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ
        (H, .revBlockL hc word entryState entryMin state minState)
        p).1 = H := by
  cases p <;> rfl

theorem trackUpdate_fst_revEnvL (H : History In₁ In₂ Graph Out₁ Out₂)
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (entryState entryMin state minState : A.State) (tbl : In₁ -> Out₁)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ
        (H, .revEnvL hc word entryState entryMin state minState tbl)
        p).1 = H := by
  cases p <;> rfl

theorem trackUpdate_fst_revRecvL (H : History In₁ In₂ Graph Out₁ Out₂)
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (entryState entryMin state minState : A.State) (tbl : In₁ -> Out₁)
    (move : In₁ × In₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ
        (H, .revRecvL hc word entryState entryMin state minState tbl
          move) p).1 = H := by
  cases p <;> rfl

theorem trackUpdate_fst_revCommitR (H : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₁) (entryState entryMin : A.State)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ (H, .revCommitR word entryState entryMin) p).1 =
      H := by
  cases p <;> rfl

theorem trackUpdate_fst_revBlockR (H : History In₁ In₂ Graph Out₁ Out₂)
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (entryState entryMin state minState : A.State)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ
        (H, .revBlockR hc word entryState entryMin state minState)
        p).1 = H := by
  cases p <;> rfl

theorem trackUpdate_fst_revEnvR (H : History In₁ In₂ Graph Out₁ Out₂)
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (entryState entryMin state minState : A.State) (tbl : In₂ -> Out₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ
        (H, .revEnvR hc word entryState entryMin state minState tbl)
        p).1 = H := by
  cases p <;> rfl

theorem trackUpdate_fst_revRecvR (H : History In₁ In₂ Graph Out₁ Out₂)
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (entryState entryMin state minState : A.State) (tbl : In₂ -> Out₂)
    (move : In₁ × In₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ
        (H, .revRecvR hc word entryState entryMin state minState tbl
          move) p).1 = H := by
  cases p <;> rfl

theorem trackUpdate_fst_openingResolve
    (H : History In₁ In₂ Graph Out₁ Out₂)
    (atom : A.State × A.State) (h : History In₁ In₂ Graph Out₁ Out₂)
    (move : In₁ × In₂) (outOne : Out₁) (outTwo : Out₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ (H, .openingResolve atom h move outOne outTwo) p).1 =
        H ∨
      (trackUpdate σ (H, .openingResolve atom h move outOne outTwo) p).1 =
          History.append H (nextRound σ H (bothEnvironment move)) ∨
        (trackUpdate σ
              (H, .openingResolve atom h move outOne outTwo) p).1 =
            History.append H (nextRound σ H (leftEnvironment move)) ∨
          (trackUpdate σ
                (H, .openingResolve atom h move outOne outTwo) p).1 =
              History.append H
                (nextRound σ H (rightEnvironment (move.2, move.1))) := by
  cases p <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr rfl))

theorem trackUpdate_fst_resolveL (H : History In₁ In₂ Graph Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (state minState : A.State) (tbl : In₁ -> Out₁) (move : In₁ × In₂)
    (outOne : Out₁)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ
          (H, .resolveL h word state minState tbl move outOne) p).1 =
        H ∨
      (trackUpdate σ
            (H, .resolveL h word state minState tbl move outOne) p).1 =
          History.append H (nextRound σ H (leftEnvironment move)) := by
  cases p <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem trackUpdate_fst_closeL (H : History In₁ In₂ Graph Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (state minState : A.State) (tbl : In₁ -> Out₁) (move : In₁ × In₂)
    (outOne : Out₁)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ
        (H, .closeL h word state minState tbl move outOne) p).1 =
      H := by
  cases p <;> rfl

theorem trackUpdate_fst_closeResolveL
    (H : History In₁ In₂ Graph Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (state minState : A.State) (tbl : In₁ -> Out₁) (move : In₁ × In₂)
    (outOne : Out₁) (outTwo : Out₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ
          (H, .closeResolveL h word state minState tbl move outOne
            outTwo) p).1 =
        H ∨
      (trackUpdate σ
            (H, .closeResolveL h word state minState tbl move outOne
              outTwo) p).1 =
          History.append H (nextRound σ H (bothEnvironment move)) ∨
        (trackUpdate σ
              (H, .closeResolveL h word state minState tbl move outOne
                outTwo) p).1 =
            History.append H
              (nextRound σ H (rightEnvironment (move.2, move.1))) := by
  cases p <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr rfl)

theorem trackUpdate_fst_resolveR (H : History In₁ In₂ Graph Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (state minState : A.State) (tbl : In₂ -> Out₂) (move : In₁ × In₂)
    (outTwo : Out₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ
          (H, .resolveR h word state minState tbl move outTwo) p).1 =
        H ∨
      (trackUpdate σ
            (H, .resolveR h word state minState tbl move outTwo) p).1 =
          History.append H
            (nextRound σ H (rightEnvironment (move.2, move.1))) := by
  cases p <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem trackUpdate_fst_closeR (H : History In₁ In₂ Graph Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (state minState : A.State) (tbl : In₂ -> Out₂) (move : In₁ × In₂)
    (outTwo : Out₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ
        (H, .closeR h word state minState tbl move outTwo) p).1 =
      H := by
  cases p <;> rfl

theorem trackUpdate_fst_closeResolveR
    (H : History In₁ In₂ Graph Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (state minState : A.State) (tbl : In₂ -> Out₂) (move : In₁ × In₂)
    (outTwo : Out₂) (outOne : Out₁)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ
          (H, .closeResolveR h word state minState tbl move outTwo
            outOne) p).1 =
        H ∨
      (trackUpdate σ
            (H, .closeResolveR h word state minState tbl move outTwo
              outOne) p).1 =
          History.append H (nextRound σ H (bothEnvironment move)) ∨
        (trackUpdate σ
              (H, .closeResolveR h word state minState tbl move outTwo
                outOne) p).1 =
            History.append H (nextRound σ H (leftEnvironment move)) := by
  cases p <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr rfl)

theorem trackUpdate_fst_revResolveL
    (H : History In₁ In₂ Graph Out₁ Out₂)
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (entryState entryMin state minState : A.State) (tbl : In₁ -> Out₁)
    (move : In₁ × In₂) (o1r : Out₁) (o2r : Out₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ
          (H, .revResolveL hc word entryState entryMin state minState
            tbl move o1r o2r) p).1 =
        H ∨
      (trackUpdate σ
            (H, .revResolveL hc word entryState entryMin state minState
              tbl move o1r o2r) p).1 =
          History.append H (nextRound σ H (leftEnvironment move)) ∨
        (trackUpdate σ
              (H, .revResolveL hc word entryState entryMin state
                minState tbl move o1r o2r) p).1 =
            History.append H (nextRound σ H (bothEnvironment move)) ∨
          (trackUpdate σ
                (H, .revResolveL hc word entryState entryMin state
                  minState tbl move o1r o2r) p).1 =
              History.append H
                (nextRound σ H (rightEnvironment (move.2, move.1))) := by
  cases p <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr rfl))

theorem trackUpdate_fst_revResolveR
    (H : History In₁ In₂ Graph Out₁ Out₂)
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (entryState entryMin state minState : A.State) (tbl : In₂ -> Out₂)
    (move : In₁ × In₂) (o1r : Out₁) (o2r : Out₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ
          (H, .revResolveR hc word entryState entryMin state minState
            tbl move o1r o2r) p).1 =
        H ∨
      (trackUpdate σ
            (H, .revResolveR hc word entryState entryMin state minState
              tbl move o1r o2r) p).1 =
          History.append H (nextRound σ H (leftEnvironment move)) ∨
        (trackUpdate σ
              (H, .revResolveR hc word entryState entryMin state
                minState tbl move o1r o2r) p).1 =
            History.append H (nextRound σ H (bothEnvironment move)) ∨
          (trackUpdate σ
                (H, .revResolveR hc word entryState entryMin state
                  minState tbl move o1r o2r) p).1 =
              History.append H
                (nextRound σ H (rightEnvironment (move.2, move.1))) := by
  cases p <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr rfl))

/-! ### The play never reverses directly -/

/-- Consecutive records never reverse the orientation directly. -/
def NoDirectHistory (h : History In₁ In₂ Graph Out₁ Out₂) : Prop :=
  ∀ i : Nat, i + 1 < List.length h ->
    ((h.getD i default).graph = Graph.left ->
      (h.getD (i + 1) default).graph ≠ Graph.right) ∧
    ((h.getD i default).graph = Graph.right ->
      (h.getD (i + 1) default).graph ≠ Graph.left)

theorem noDirectHistory_nil :
    NoDirectHistory ([] : History In₁ In₂ Graph Out₁ Out₂) := by
  intro i hi
  simp at hi

theorem noDirectHistory_append
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hnd : NoDirectHistory h)
    (hcompat :
      ∀ r' ∈ h.getLast?,
        (r'.graph = Graph.left -> r.graph ≠ Graph.right) ∧
        (r'.graph = Graph.right -> r.graph ≠ Graph.left)) :
    NoDirectHistory (History.append h r) := by
  intro i hi
  rw [show History.append h r = h ++ [r] from rfl] at hi ⊢
  simp only [List.length_append, List.length_cons, List.length_nil] at hi
  by_cases hlt : i + 1 < List.length h
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show i < List.length h by omega),
      List.getElem?_append_left hlt,
      ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
    exact hnd i hlt
  · have hieq : i + 1 = List.length h := by omega
    have hilt : i < List.length h := by omega
    have hsnd : (h ++ [r]).getD (i + 1) default = r := by
      rw [List.getD_eq_getElem?_getD, hieq,
        List.getElem?_append_right (le_refl _)]
      simp
    have hfst : h.getLast? = some ((h ++ [r]).getD i default) := by
      have hread : (h ++ [r]).getD i default = h[i]'hilt := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_left hilt,
          List.getElem?_eq_getElem hilt]
        rfl
      rw [hread, List.getLast?_eq_getElem?,
        show List.length h - 1 = i by omega,
        List.getElem?_eq_getElem hilt]
    have hpair := hcompat ((h ++ [r]).getD i default) hfst
    rw [hsnd]
    exact hpair

theorem extendPrefix_getLast?_graph
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (envs : List (EnvironmentRound In₁ In₂)) (g : Graph)
    (hne : envs ≠ [])
    (hall : ∀ e ∈ envs, e.graph = g) :
    ∀ r ∈ (extendPrefix σ h envs).getLast?, r.graph = g := by
  induction envs using List.reverseRecOn with
  | nil => exact absurd rfl hne
  | append_singleton envs e _ =>
      intro r hr
      rw [extendPrefix_snoc,
        show
          History.append (extendPrefix σ h envs)
              (nextRound σ (extendPrefix σ h envs) e) =
            extendPrefix σ h envs ++
              [nextRound σ (extendPrefix σ h envs) e] from rfl,
        List.getLast?_concat] at hr
      simp at hr
      subst hr
      exact hall e (by simp)

/-! ### Attainment of the tracked minima -/

/-- The tracked block-minimum component of a position, if any. -/
def blockMin : UniformizationPosition (In₁ := In₁) A -> Option A.State
  | .blockL _ _ _ minState => some minState
  | .blockEnvL _ _ _ minState _ => some minState
  | .recvL _ _ _ minState _ _ => some minState
  | .resolveL _ _ _ minState _ _ _ => some minState
  | .closeL _ _ _ minState _ _ _ => some minState
  | .closeResolveL _ _ _ minState _ _ _ _ => some minState
  | .blockR _ _ _ minState => some minState
  | .blockEnvR _ _ _ minState _ => some minState
  | .recvR _ _ _ minState _ _ => some minState
  | .resolveR _ _ _ minState _ _ _ => some minState
  | .closeR _ _ _ minState _ _ _ => some minState
  | .closeResolveR _ _ _ minState _ _ _ _ => some minState
  | .revCommitL _ _ entryMin => some entryMin
  | .revBlockL _ _ _ _ _ minState => some minState
  | .revEnvL _ _ _ _ _ minState _ => some minState
  | .revRecvL _ _ _ _ _ minState _ _ => some minState
  | .revResolveL _ _ _ _ _ minState _ _ _ _ => some minState
  | .revCommitR _ _ entryMin => some entryMin
  | .revBlockR _ _ _ _ _ minState => some minState
  | .revEnvR _ _ _ _ _ minState _ => some minState
  | .revRecvR _ _ _ _ _ minState _ _ => some minState
  | .revResolveR _ _ _ _ _ minState _ _ _ _ => some minState
  | _ => none

/-- The play visits a boundary position at time `m`. -/
def IsBndAt (path : Nat -> UniformizationPosition (In₁ := In₁) A)
    (m : Nat) : Prop :=
  ∃ atom : A.State × A.State, path m = .bnd atom

variable [Fintype In₁] [Fintype In₂]
variable [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]

/-- The tracked states are the run states of the induced word. -/
theorem historyState_pathMemory_eq_run
    (hgrow : ∀ t : Nat, ∃ n : Nat, t < playClock σ path n) (k : Nat) :
    A.historyState (pathMemory σ path k).1 =
      A.run (execution σ (playEnv σ path hgrow)) (playClock σ path k) := by
  rw [pathMemory_eq_executionPrefix σ path hgrow k]
  exact historyState_executionPrefix σ _ (playClock σ path k)

/--
Attainment: every tracked minimum is a run state of the induced word
at an index dominating the clocks of all earlier boundary visits;
boundary emissions are attained strictly inside the closed block.
-/
theorem attainment
    (hplay :
      (uniformizationGame A σ).PlayFrom
        (.bnd (A.initial, A.initial)) path)
    (hcons :
      CountableParityGame.Strategy.Consistent
        (G := uniformizationGame A σ) (trackingStrategy σ) path)
    (hgrow : ∀ t : Nat, ∃ n : Nat, t < playClock σ path n) :
    ∀ n : Nat,
      (∀ atom : A.State × A.State, path n = .bnd atom -> 0 < n ->
        ∃ j : Nat, j < playClock σ path n ∧
          atom.2 = A.run (execution σ (playEnv σ path hgrow)) j ∧
          ∀ m : Nat, m < n -> IsBndAt path m -> playClock σ path m ≤ j) ∧
      (∀ minState : A.State, blockMin (path n) = some minState ->
        ∃ j : Nat, j ≤ playClock σ path n ∧
          minState = A.run (execution σ (playEnv σ path hgrow)) j ∧
          ∀ m : Nat, m < n -> IsBndAt path m -> playClock σ path m ≤ j) := by
  have htracks := tracks_of_consistent σ path hplay hcons
  have hrun := historyState_pathMemory_eq_run σ path hgrow
  intro n
  induction n with
  | zero =>
      constructor
      · intro atom _ h0
        omega
      · intro minState hmn
        rw [hplay.1] at hmn
        simp [blockMin] at hmn
  | succ n ih =>
      have hstep : uniformizationStep σ (path n) (path (n + 1)) :=
        hplay.2 n
      have htrack := htracks n
      rcases hpos : path n with
        atom | ⟨atom, h⟩ | ⟨atom, h, move⟩ | ⟨atom, h, move, outOne, outTwo⟩ |
        ⟨h, word, state, minState⟩ | ⟨h, word, state, minState, tbl⟩ |
        ⟨h, word, state, minState, tbl, move⟩ |
        ⟨h, word, state, minState, tbl, move, outOne⟩ |
        ⟨h, word, state, minState, tbl, move, outOne⟩ |
        ⟨h, word, state, minState, tbl, move, outOne, outTwo⟩ |
        ⟨h, word, state, minState⟩ | ⟨h, word, state, minState, tbl⟩ |
        ⟨h, word, state, minState, tbl, move⟩ |
        ⟨h, word, state, minState, tbl, move, outTwo⟩ |
        ⟨h, word, state, minState, tbl, move, outTwo⟩ |
        ⟨h, word, state, minState, tbl, move, outTwo, outOne⟩ |
        ⟨word, eqs, ems⟩ | ⟨hc, word, eqs, ems, state, minState⟩ |
        ⟨hc, word, eqs, ems, state, minState, tbl⟩ |
        ⟨hc, word, eqs, ems, state, minState, tbl, move⟩ |
        ⟨hc, word, eqs, ems, state, minState, tbl, move, o1r, o2r⟩ |
        ⟨word, eqs, ems⟩ | ⟨hc, word, eqs, ems, state, minState⟩ |
        ⟨hc, word, eqs, ems, state, minState, tbl⟩ |
        ⟨hc, word, eqs, ems, state, minState, tbl, move⟩ |
        ⟨hc, word, eqs, ems, state, minState, tbl, move, o1r, o2r⟩
      all_goals rw [hpos] at ih htrack hstep
      -- bnd: Even commits
      · have hnext : path (n + 1) = .committed atom (pathMemory σ path n).1 := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          simp [blockMin] at hmn
      -- committed: Odd reveals
      · obtain ⟨move, hnext⟩ :
            ∃ move : In₁ × In₂, path (n + 1) = .opening atom h move :=
          hstep
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          simp [blockMin] at hmn
      -- opening: Even answers
      · obtain ⟨hh, hgen, hready, hstate⟩ := htrack
        have hnext :
            path (n + 1) =
              .openingResolve atom (pathMemory σ path n).1 move
                (σ.one (nextView Proc.one (pathMemory σ path n).1 (bothEnvironment move)))
                (σ.two (nextView Proc.two (pathMemory σ path n).1 (bothEnvironment move))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          rw [hmove, hh]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          simp [blockMin] at hmn
      -- openingResolve: the round resolves
      · obtain ⟨hh, hgen, hready, hstate, hone, htwo⟩ := htrack
        subst hh
        have hstep' :
            path (n + 1) =
                uOpenBothTarget (A := A) atom move outOne outTwo ∨
              path (n + 1) =
                uOpenLeftTarget σ atom (pathMemory σ path n).1 move outOne ∨
              path (n + 1) =
                uOpenRightTarget σ atom (pathMemory σ path n).1 move outTwo :=
          hstep
        rcases hstep' with hnext | hnext | hnext
        · have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (bothEnvironment move)) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          rw [hnext]
          constructor
          · intro atom' heq _
            have heq' :
                atom' =
                  (A.step atom.1 (bothRoundRecord move outOne outTwo),
                    atom.1) := by
              have := heq.symm
              simpa [uOpenBothTarget] using this
            refine ⟨playClock σ path n, by omega, ?_, ?_⟩
            · rw [heq']
              show atom.1 = _
              rw [hstate]
              exact hrun n
            · intro m hm _
              have := playClock_mono σ path (show m ≤ n by omega)
              omega
          · intro minState hmn
            simp [uOpenBothTarget, blockMin] at hmn
        · rw [hnext]
          have htrack1 := htracks (n + 1)
          rw [hnext] at htrack1
          obtain ⟨_, _, _, _, _, _, hstate1⟩ := htrack1
          have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (leftEnvironment move)) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          constructor
          · intro atom' heq
            exact absurd heq (by simp [uOpenLeftTarget])
          · intro minState' hmn
            have hmn' :
                A.minPriorityState atom.1 (A.step atom.1 (leftRoundRecord move outOne (blockSenderTwo σ (pathMemory σ path n).1 [] move.2))) =
                  minState' := by
              simpa [uOpenLeftTarget, blockMin] using hmn
            rcases minPriorityState_eq_or (A := A) atom.1 _ with
              hcase | hcase
            · refine ⟨playClock σ path (n + 1), le_refl _, ?_, ?_⟩
              · rw [← hmn', hcase, hstate1]
                exact hrun (n + 1)
              · intro m hm _
                have := playClock_mono σ path (show m ≤ n by omega)
                omega
            · refine ⟨playClock σ path n, by omega, ?_, ?_⟩
              · rw [← hmn', hcase, hstate]
                exact hrun n
              · intro m hm _
                have := playClock_mono σ path (show m ≤ n by omega)
                omega

        · rw [hnext]
          have htrack1 := htracks (n + 1)
          rw [hnext] at htrack1
          obtain ⟨_, _, _, _, _, _, hstate1⟩ := htrack1
          have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (rightEnvironment (move.2, move.1))) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          constructor
          · intro atom' heq
            exact absurd heq (by simp [uOpenRightTarget])
          · intro minState' hmn
            have hmn' :
                A.minPriorityState atom.1 (A.step atom.1 (rightRoundRecord (move.2, move.1) (blockSenderOne σ (pathMemory σ path n).1 [] move.1) outTwo)) =
                  minState' := by
              simpa [uOpenRightTarget, blockMin] using hmn
            rcases minPriorityState_eq_or (A := A) atom.1 _ with
              hcase | hcase
            · refine ⟨playClock σ path (n + 1), le_refl _, ?_, ?_⟩
              · rw [← hmn', hcase, hstate1]
                exact hrun (n + 1)
              · intro m hm _
                have := playClock_mono σ path (show m ≤ n by omega)
                omega
            · refine ⟨playClock σ path n, by omega, ?_, ?_⟩
              · rw [← hmn', hcase, hstate]
                exact hrun n
              · intro m hm _
                have := playClock_mono σ path (show m ≤ n by omega)
                omega
      -- blockL: Even commits table
      · have hnext : path (n + 1) = .blockEnvL h word state minState (fun inputOne => σ.one (nextView Proc.one (pathMemory σ path n).1 (rightEnvironment (default, inputOne)))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_blockL]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : minState = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 minState (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- blockEnvL: Odd reveals move
      · obtain ⟨move, hnext⟩ : ∃ move : In₁ × In₂, path (n + 1) = .recvL h word state minState tbl move := hstep
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_blockEnvL]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : minState = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 minState (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- recvL: Even answers
      · have hnext : path (n + 1) = .resolveL h word state minState tbl move (σ.one (nextView Proc.one (pathMemory σ path n).1 (leftEnvironment move))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_recvL]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : minState = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 minState (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- resolveL: continue or close
      · have hstep' :
            path (n + 1) =
                uContinueLTarget σ h word state minState move outOne ∨
              path (n + 1) =
                .closeL h word state minState tbl move outOne :=
          hstep
        rcases hstep' with hnext | hnext
        · rw [hnext]
          have htrack1 := htracks (n + 1)
          rw [hnext] at htrack1
          obtain ⟨_, _, _, _, _, _, hstate1⟩ := htrack1
          have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (leftEnvironment move)) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          constructor
          · intro atom' heq
            exact absurd heq (by simp [uContinueLTarget])
          · intro minState' hmn
            have hmn' :
                A.minPriorityState minState (A.step state (leftRoundRecord move outOne (blockSenderTwo σ h word move.2))) =
                  minState' := by
              simpa [uContinueLTarget, blockMin] using hmn
            rcases minPriorityState_eq_or (A := A) minState _ with
              hcase | hcase
            · refine ⟨playClock σ path (n + 1), le_refl _, ?_, ?_⟩
              · rw [← hmn', hcase, hstate1]
                exact hrun (n + 1)
              · intro m hm _
                have := playClock_mono σ path (show m ≤ n by omega)
                omega
            · obtain ⟨j, hj, hrunj, hdom⟩ :=
                ih.2 minState (by simp [blockMin])
              refine ⟨j, by omega, by rw [← hmn', hcase]; exact hrunj, ?_⟩
              intro m hm hb
              rcases Nat.lt_or_ge m n with hlt | hge
              · exact hdom m hlt hb
              · have hmn2 : m = n := by omega
                subst hmn2
                rcases hb with ⟨a, ha⟩
                rw [hpos] at ha
                exact absurd ha (by simp)

        · have hclk : playClock σ path (n + 1) = playClock σ path n := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [pathMemory_fst_succ σ path n, hpos, hnext]
            rfl
          rw [hnext]
          constructor
          · intro atom' heq
            exact absurd heq (by simp)
          · intro minState' hmn
            have hmn' : minState = minState' := by
              simpa [blockMin] using hmn
            subst hmn'
            obtain ⟨j, hj, hrunj, hdom⟩ :=
              ih.2 minState (by simp [blockMin])
            refine ⟨j, by omega, hrunj, ?_⟩
            intro m hm hb
            rcases Nat.lt_or_ge m n with hlt | hge
            · exact hdom m hlt hb
            · have hmn2 : m = n := by omega
              subst hmn2
              rcases hb with ⟨a, ha⟩
              rw [hpos] at ha
              exact absurd ha (by simp)
      -- closeL: Even fixes close
      · have hnext : path (n + 1) = .closeResolveL h word state minState tbl move outOne (σ.two (nextView Proc.two (pathMemory σ path n).1 (bothEnvironment move))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_closeL]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : minState = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 minState (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- closeResolveL: sync or reverse
      · have hstep' :
            path (n + 1) =
                uCloseTarget (A := A) state minState move outOne outTwo ∨
              path (n + 1) =
                uRevReverseRTarget (A := A) state minState move
                  (tbl move.1) outTwo :=
          hstep
        rcases hstep' with hnext | hnext
        · have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (bothEnvironment move)) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          rw [hnext]
          constructor
          · intro atom' heq
            have heq' : atom'.2 = minState := by
              have h' := heq.symm
              simp [uCloseTarget] at h'
              rw [h']
            intro _
            obtain ⟨j, hj, hrunj, hdom⟩ :=
              ih.2 minState (by simp [blockMin])
            refine ⟨j, by omega, by rw [heq']; exact hrunj, ?_⟩
            intro m hm hb
            rcases Nat.lt_or_ge m n with hlt | hge
            · exact hdom m hlt hb
            · have hmn2 : m = n := by omega
              subst hmn2
              rcases hb with ⟨a, ha⟩
              rw [hpos] at ha
              exact absurd ha (by simp)
          · intro minState' hmn
            simp [uCloseTarget, blockMin] at hmn

        · rw [hnext]
          have htrack1 := htracks (n + 1)
          rw [hnext] at htrack1
          obtain ⟨⟨_, hstate1⟩, _⟩ := htrack1
          have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (rightEnvironment (move.2, move.1))) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          constructor
          · intro atom' heq
            exact absurd heq (by simp [uRevReverseRTarget])
          · intro minState' hmn
            have hmn' :
                A.minPriorityState minState (A.step state (rightRoundRecord (move.2, move.1) (tbl move.1) outTwo)) =
                  minState' := by
              simpa [uRevReverseRTarget, blockMin] using hmn
            rcases minPriorityState_eq_or (A := A) minState _ with
              hcase | hcase
            · refine ⟨playClock σ path (n + 1), le_refl _, ?_, ?_⟩
              · rw [← hmn', hcase, hstate1]
                exact hrun (n + 1)
              · intro m hm _
                have := playClock_mono σ path (show m ≤ n by omega)
                omega
            · obtain ⟨j, hj, hrunj, hdom⟩ :=
                ih.2 minState (by simp [blockMin])
              refine ⟨j, by omega, by rw [← hmn', hcase]; exact hrunj, ?_⟩
              intro m hm hb
              rcases Nat.lt_or_ge m n with hlt | hge
              · exact hdom m hlt hb
              · have hmn2 : m = n := by omega
                subst hmn2
                rcases hb with ⟨a, ha⟩
                rw [hpos] at ha
                exact absurd ha (by simp)
      -- blockR: Even commits table
      · have hnext : path (n + 1) = .blockEnvR h word state minState (fun inputTwo => σ.two (nextView Proc.two (pathMemory σ path n).1 (leftEnvironment (default, inputTwo)))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_blockR]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : minState = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 minState (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- blockEnvR: Odd reveals move
      · obtain ⟨move, hnext⟩ : ∃ move : In₁ × In₂, path (n + 1) = .recvR h word state minState tbl move := hstep
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_blockEnvR]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : minState = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 minState (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- recvR: Even answers
      · have hnext : path (n + 1) = .resolveR h word state minState tbl move (σ.two (nextView Proc.two (pathMemory σ path n).1 (rightEnvironment (move.2, move.1)))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_recvR]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : minState = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 minState (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- resolveR: continue or close
      · have hstep' :
            path (n + 1) =
                uContinueRTarget σ h word state minState move outTwo ∨
              path (n + 1) =
                .closeR h word state minState tbl move outTwo :=
          hstep
        rcases hstep' with hnext | hnext
        · rw [hnext]
          have htrack1 := htracks (n + 1)
          rw [hnext] at htrack1
          obtain ⟨_, _, _, _, _, _, hstate1⟩ := htrack1
          have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (rightEnvironment (move.2, move.1))) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          constructor
          · intro atom' heq
            exact absurd heq (by simp [uContinueRTarget])
          · intro minState' hmn
            have hmn' :
                A.minPriorityState minState (A.step state (rightRoundRecord (move.2, move.1) (blockSenderOne σ h word move.1) outTwo)) =
                  minState' := by
              simpa [uContinueRTarget, blockMin] using hmn
            rcases minPriorityState_eq_or (A := A) minState _ with
              hcase | hcase
            · refine ⟨playClock σ path (n + 1), le_refl _, ?_, ?_⟩
              · rw [← hmn', hcase, hstate1]
                exact hrun (n + 1)
              · intro m hm _
                have := playClock_mono σ path (show m ≤ n by omega)
                omega
            · obtain ⟨j, hj, hrunj, hdom⟩ :=
                ih.2 minState (by simp [blockMin])
              refine ⟨j, by omega, by rw [← hmn', hcase]; exact hrunj, ?_⟩
              intro m hm hb
              rcases Nat.lt_or_ge m n with hlt | hge
              · exact hdom m hlt hb
              · have hmn2 : m = n := by omega
                subst hmn2
                rcases hb with ⟨a, ha⟩
                rw [hpos] at ha
                exact absurd ha (by simp)

        · have hclk : playClock σ path (n + 1) = playClock σ path n := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [pathMemory_fst_succ σ path n, hpos, hnext]
            rfl
          rw [hnext]
          constructor
          · intro atom' heq
            exact absurd heq (by simp)
          · intro minState' hmn
            have hmn' : minState = minState' := by
              simpa [blockMin] using hmn
            subst hmn'
            obtain ⟨j, hj, hrunj, hdom⟩ :=
              ih.2 minState (by simp [blockMin])
            refine ⟨j, by omega, hrunj, ?_⟩
            intro m hm hb
            rcases Nat.lt_or_ge m n with hlt | hge
            · exact hdom m hlt hb
            · have hmn2 : m = n := by omega
              subst hmn2
              rcases hb with ⟨a, ha⟩
              rw [hpos] at ha
              exact absurd ha (by simp)
      -- closeR: Even fixes close
      · have hnext : path (n + 1) = .closeResolveR h word state minState tbl move outTwo (σ.one (nextView Proc.one (pathMemory σ path n).1 (bothEnvironment move))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_closeR]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : minState = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 minState (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- closeResolveR: sync or reverse
      · have hstep' :
            path (n + 1) =
                uCloseTarget (A := A) state minState move outOne outTwo ∨
              path (n + 1) =
                uRevReverseLTarget (A := A) state minState move outOne
                  (tbl move.2) :=
          hstep
        rcases hstep' with hnext | hnext
        · have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (bothEnvironment move)) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          rw [hnext]
          constructor
          · intro atom' heq
            have heq' : atom'.2 = minState := by
              have h' := heq.symm
              simp [uCloseTarget] at h'
              rw [h']
            intro _
            obtain ⟨j, hj, hrunj, hdom⟩ :=
              ih.2 minState (by simp [blockMin])
            refine ⟨j, by omega, by rw [heq']; exact hrunj, ?_⟩
            intro m hm hb
            rcases Nat.lt_or_ge m n with hlt | hge
            · exact hdom m hlt hb
            · have hmn2 : m = n := by omega
              subst hmn2
              rcases hb with ⟨a, ha⟩
              rw [hpos] at ha
              exact absurd ha (by simp)
          · intro minState' hmn
            simp [uCloseTarget, blockMin] at hmn

        · rw [hnext]
          have htrack1 := htracks (n + 1)
          rw [hnext] at htrack1
          obtain ⟨⟨_, hstate1⟩, _⟩ := htrack1
          have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (leftEnvironment move)) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          constructor
          · intro atom' heq
            exact absurd heq (by simp [uRevReverseLTarget])
          · intro minState' hmn
            have hmn' :
                A.minPriorityState minState (A.step state (leftRoundRecord move outOne (tbl move.2))) =
                  minState' := by
              simpa [uRevReverseLTarget, blockMin] using hmn
            rcases minPriorityState_eq_or (A := A) minState _ with
              hcase | hcase
            · refine ⟨playClock σ path (n + 1), le_refl _, ?_, ?_⟩
              · rw [← hmn', hcase, hstate1]
                exact hrun (n + 1)
              · intro m hm _
                have := playClock_mono σ path (show m ≤ n by omega)
                omega
            · obtain ⟨j, hj, hrunj, hdom⟩ :=
                ih.2 minState (by simp [blockMin])
              refine ⟨j, by omega, by rw [← hmn', hcase]; exact hrunj, ?_⟩
              intro m hm hb
              rcases Nat.lt_or_ge m n with hlt | hge
              · exact hdom m hlt hb
              · have hmn2 : m = n := by omega
                subst hmn2
                rcases hb with ⟨a, ha⟩
                rw [hpos] at ha
                exact absurd ha (by simp)
      -- revCommitL: Even commits view
      · have hnext : path (n + 1) = .revBlockL (pathMemory σ path n).1 word eqs ems eqs ems := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_revCommitL]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : ems = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 ems (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- revBlockL: Even commits send table
      · have hnext : path (n + 1) = .revEnvL hc word eqs ems state minState (fun inputOne => σ.one (nextView Proc.one (pathMemory σ path n).1 (rightEnvironment (default, inputOne)))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_revBlockL]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : minState = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 minState (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- revEnvL: Odd reveals move
      · obtain ⟨move, hnext⟩ : ∃ move : In₁ × In₂, path (n + 1) = .revRecvL hc word eqs ems state minState tbl move := hstep
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_revEnvL]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : minState = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 minState (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- revRecvL: Even stages
      · have hnext : path (n + 1) = .revResolveL hc word eqs ems state minState tbl move (σ.one (nextView Proc.one (pathMemory σ path n).1 (bothEnvironment move))) (σ.two (nextView Proc.two (pathMemory σ path n).1 (bothEnvironment move))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_revRecvL]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : minState = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 minState (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- revResolveL: continue, close, reverse
      · have hstep' :
            path (n + 1) =
                uRevContinueLTarget σ hc word eqs ems state minState
                  move o1r ∨
              path (n + 1) =
                uCloseTarget (A := A) state minState move o1r o2r ∨
              path (n + 1) =
                uRevReverseRTarget (A := A) state minState move
                  (tbl move.1) o2r :=
          hstep
        rcases hstep' with hnext | hnext | hnext
        · rw [hnext]
          have htrack1 := htracks (n + 1)
          rw [hnext] at htrack1
          obtain ⟨_, _, _, _, _, _, hstate1⟩ := htrack1
          have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (leftEnvironment move)) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          constructor
          · intro atom' heq
            exact absurd heq (by simp [uRevContinueLTarget])
          · intro minState' hmn
            have hmn' :
                A.minPriorityState minState (A.step state (leftRoundRecord move o1r (blockSenderTwo σ hc (word.drop 1) move.2))) =
                  minState' := by
              simpa [uRevContinueLTarget, blockMin] using hmn
            rcases minPriorityState_eq_or (A := A) minState _ with
              hcase | hcase
            · refine ⟨playClock σ path (n + 1), le_refl _, ?_, ?_⟩
              · rw [← hmn', hcase, hstate1]
                exact hrun (n + 1)
              · intro m hm _
                have := playClock_mono σ path (show m ≤ n by omega)
                omega
            · obtain ⟨j, hj, hrunj, hdom⟩ :=
                ih.2 minState (by simp [blockMin])
              refine ⟨j, by omega, by rw [← hmn', hcase]; exact hrunj, ?_⟩
              intro m hm hb
              rcases Nat.lt_or_ge m n with hlt | hge
              · exact hdom m hlt hb
              · have hmn2 : m = n := by omega
                subst hmn2
                rcases hb with ⟨a, ha⟩
                rw [hpos] at ha
                exact absurd ha (by simp)

        · have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (bothEnvironment move)) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          rw [hnext]
          constructor
          · intro atom' heq
            have heq' : atom'.2 = minState := by
              have h' := heq.symm
              simp [uCloseTarget] at h'
              rw [h']
            intro _
            obtain ⟨j, hj, hrunj, hdom⟩ :=
              ih.2 minState (by simp [blockMin])
            refine ⟨j, by omega, by rw [heq']; exact hrunj, ?_⟩
            intro m hm hb
            rcases Nat.lt_or_ge m n with hlt | hge
            · exact hdom m hlt hb
            · have hmn2 : m = n := by omega
              subst hmn2
              rcases hb with ⟨a, ha⟩
              rw [hpos] at ha
              exact absurd ha (by simp)
          · intro minState' hmn
            simp [uCloseTarget, blockMin] at hmn

        · rw [hnext]
          have htrack1 := htracks (n + 1)
          rw [hnext] at htrack1
          obtain ⟨⟨_, hstate1⟩, _⟩ := htrack1
          have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (rightEnvironment (move.2, move.1))) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          constructor
          · intro atom' heq
            exact absurd heq (by simp [uRevReverseRTarget])
          · intro minState' hmn
            have hmn' :
                A.minPriorityState minState (A.step state (rightRoundRecord (move.2, move.1) (tbl move.1) o2r)) =
                  minState' := by
              simpa [uRevReverseRTarget, blockMin] using hmn
            rcases minPriorityState_eq_or (A := A) minState _ with
              hcase | hcase
            · refine ⟨playClock σ path (n + 1), le_refl _, ?_, ?_⟩
              · rw [← hmn', hcase, hstate1]
                exact hrun (n + 1)
              · intro m hm _
                have := playClock_mono σ path (show m ≤ n by omega)
                omega
            · obtain ⟨j, hj, hrunj, hdom⟩ :=
                ih.2 minState (by simp [blockMin])
              refine ⟨j, by omega, by rw [← hmn', hcase]; exact hrunj, ?_⟩
              intro m hm hb
              rcases Nat.lt_or_ge m n with hlt | hge
              · exact hdom m hlt hb
              · have hmn2 : m = n := by omega
                subst hmn2
                rcases hb with ⟨a, ha⟩
                rw [hpos] at ha
                exact absurd ha (by simp)
      -- revCommitR: Even commits view
      · have hnext : path (n + 1) = .revBlockR (pathMemory σ path n).1 word eqs ems eqs ems := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_revCommitR]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : ems = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 ems (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- revBlockR: Even commits send table
      · have hnext : path (n + 1) = .revEnvR hc word eqs ems state minState (fun inputTwo => σ.two (nextView Proc.two (pathMemory σ path n).1 (leftEnvironment (default, inputTwo)))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_revBlockR]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : minState = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 minState (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- revEnvR: Odd reveals move
      · obtain ⟨move, hnext⟩ : ∃ move : In₁ × In₂, path (n + 1) = .revRecvR hc word eqs ems state minState tbl move := hstep
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_revEnvR]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : minState = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 minState (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- revRecvR: Even stages
      · have hnext : path (n + 1) = .revResolveR hc word eqs ems state minState tbl move (σ.one (nextView Proc.one (pathMemory σ path n).1 (bothEnvironment move))) (σ.two (nextView Proc.two (pathMemory σ path n).1 (bothEnvironment move))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        have hclk : playClock σ path (n + 1) = playClock σ path n := by
          show List.length (pathMemory σ path (n + 1)).1 = _
          rw [pathMemory_fst_succ σ path n, hpos, trackUpdate_fst_revRecvR]
          rfl
        rw [hnext]
        constructor
        · intro atom' heq
          exact absurd heq (by simp)
        · intro minState' hmn
          have hmn' : minState = minState' := by simpa [blockMin] using hmn
          subst hmn'
          obtain ⟨j, hj, hrunj, hdom⟩ :=
            ih.2 minState (by simp [blockMin])
          refine ⟨j, by omega, hrunj, ?_⟩
          intro m hm hb
          rcases Nat.lt_or_ge m n with hlt | hge
          · exact hdom m hlt hb
          · have hmn2 : m = n := by omega
            subst hmn2
            rcases hb with ⟨a, ha⟩
            rw [hpos] at ha
            exact absurd ha (by simp)
      -- revResolveR: continue, close, reverse
      · have hstep' :
            path (n + 1) =
                uRevContinueRTarget σ hc word eqs ems state minState
                  move o2r ∨
              path (n + 1) =
                uCloseTarget (A := A) state minState move o1r o2r ∨
              path (n + 1) =
                uRevReverseLTarget (A := A) state minState move o1r
                  (tbl move.2) :=
          hstep
        rcases hstep' with hnext | hnext | hnext
        · rw [hnext]
          have htrack1 := htracks (n + 1)
          rw [hnext] at htrack1
          obtain ⟨_, _, _, _, _, _, hstate1⟩ := htrack1
          have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (rightEnvironment (move.2, move.1))) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          constructor
          · intro atom' heq
            exact absurd heq (by simp [uRevContinueRTarget])
          · intro minState' hmn
            have hmn' :
                A.minPriorityState minState (A.step state (rightRoundRecord (move.2, move.1) (blockSenderOne σ hc (word.drop 1) move.1) o2r)) =
                  minState' := by
              simpa [uRevContinueRTarget, blockMin] using hmn
            rcases minPriorityState_eq_or (A := A) minState _ with
              hcase | hcase
            · refine ⟨playClock σ path (n + 1), le_refl _, ?_, ?_⟩
              · rw [← hmn', hcase, hstate1]
                exact hrun (n + 1)
              · intro m hm _
                have := playClock_mono σ path (show m ≤ n by omega)
                omega
            · obtain ⟨j, hj, hrunj, hdom⟩ :=
                ih.2 minState (by simp [blockMin])
              refine ⟨j, by omega, by rw [← hmn', hcase]; exact hrunj, ?_⟩
              intro m hm hb
              rcases Nat.lt_or_ge m n with hlt | hge
              · exact hdom m hlt hb
              · have hmn2 : m = n := by omega
                subst hmn2
                rcases hb with ⟨a, ha⟩
                rw [hpos] at ha
                exact absurd ha (by simp)

        · have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (bothEnvironment move)) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          rw [hnext]
          constructor
          · intro atom' heq
            have heq' : atom'.2 = minState := by
              have h' := heq.symm
              simp [uCloseTarget] at h'
              rw [h']
            intro _
            obtain ⟨j, hj, hrunj, hdom⟩ :=
              ih.2 minState (by simp [blockMin])
            refine ⟨j, by omega, by rw [heq']; exact hrunj, ?_⟩
            intro m hm hb
            rcases Nat.lt_or_ge m n with hlt | hge
            · exact hdom m hlt hb
            · have hmn2 : m = n := by omega
              subst hmn2
              rcases hb with ⟨a, ha⟩
              rw [hpos] at ha
              exact absurd ha (by simp)
          · intro minState' hmn
            simp [uCloseTarget, blockMin] at hmn

        · rw [hnext]
          have htrack1 := htracks (n + 1)
          rw [hnext] at htrack1
          obtain ⟨⟨_, hstate1⟩, _⟩ := htrack1
          have hclk :
              playClock σ path (n + 1) = playClock σ path n + 1 := by
            show List.length (pathMemory σ path (n + 1)).1 = _
            rw [show (pathMemory σ path (n + 1)).1 =
                History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1 (leftEnvironment move)) by
              rw [pathMemory_fst_succ σ path n, hpos, hnext]
              rfl]
            simp [History.append, playClock]
          constructor
          · intro atom' heq
            exact absurd heq (by simp [uRevReverseLTarget])
          · intro minState' hmn
            have hmn' :
                A.minPriorityState minState (A.step state (leftRoundRecord move o1r (tbl move.2))) =
                  minState' := by
              simpa [uRevReverseLTarget, blockMin] using hmn
            rcases minPriorityState_eq_or (A := A) minState _ with
              hcase | hcase
            · refine ⟨playClock σ path (n + 1), le_refl _, ?_, ?_⟩
              · rw [← hmn', hcase, hstate1]
                exact hrun (n + 1)
              · intro m hm _
                have := playClock_mono σ path (show m ≤ n by omega)
                omega
            · obtain ⟨j, hj, hrunj, hdom⟩ :=
                ih.2 minState (by simp [blockMin])
              refine ⟨j, by omega, by rw [← hmn', hcase]; exact hrunj, ?_⟩
              intro m hm hb
              rcases Nat.lt_or_ge m n with hlt | hge
              · exact hdom m hlt hb
              · have hmn2 : m = n := by omega
                subst hmn2
                rcases hb with ⟨a, ha⟩
                rw [hpos] at ha
                exact absurd ha (by simp)


/-! ### Emission of the run priorities -/

/-- Away from boundary positions, the play emits the current run
priority. -/
theorem uniformizationPriority_eq_run_of_not_bnd
    (hplay :
      (uniformizationGame A σ).PlayFrom
        (.bnd (A.initial, A.initial)) path)
    (hcons :
      CountableParityGame.Strategy.Consistent
        (G := uniformizationGame A σ) (trackingStrategy σ) path)
    (hgrow : ∀ t : Nat, ∃ n : Nat, t < playClock σ path n)
    (k : Nat) (hnb : ¬ IsBndAt path k) :
    uniformizationPriority (path k) =
      A.priority
        (A.run (execution σ (playEnv σ path hgrow))
          (playClock σ path k)) := by
  have htrack := tracks_of_consistent σ path hplay hcons k
  have hrun := historyState_pathMemory_eq_run σ path hgrow k
  rcases hpos : path k with
    atom | ⟨atom, h⟩ | ⟨atom, h, move⟩ | ⟨atom, h, move, outOne, outTwo⟩ |
    ⟨h, word, state, minState⟩ | ⟨h, word, state, minState, tbl⟩ |
    ⟨h, word, state, minState, tbl, move⟩ |
    ⟨h, word, state, minState, tbl, move, outOne⟩ |
    ⟨h, word, state, minState, tbl, move, outOne⟩ |
    ⟨h, word, state, minState, tbl, move, outOne, outTwo⟩ |
    ⟨h, word, state, minState⟩ | ⟨h, word, state, minState, tbl⟩ |
    ⟨h, word, state, minState, tbl, move⟩ |
    ⟨h, word, state, minState, tbl, move, outTwo⟩ |
    ⟨h, word, state, minState, tbl, move, outTwo⟩ |
    ⟨h, word, state, minState, tbl, move, outTwo, outOne⟩ |
    ⟨word, eqs, ems⟩ | ⟨hc, word, eqs, ems, state, minState⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl, move⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl, move, o1r, o2r⟩ |
    ⟨word, eqs, ems⟩ | ⟨hc, word, eqs, ems, state, minState⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl, move⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl, move, o1r, o2r⟩
  all_goals rw [hpos] at htrack
  · exact absurd ⟨atom, hpos⟩ hnb
  · show A.priority atom.1 = _
    rw [htrack.2.2.2, hrun]
  · show A.priority atom.1 = _
    rw [htrack.2.2.2, hrun]
  · show A.priority atom.1 = _
    rw [htrack.2.2.2.1, hrun]
  · obtain ⟨_, _, _, _, _, _, hstate⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _, _, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨_, _, _, _, _, _, hstate⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _, _, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, hstate⟩, _⟩ := htrack
    show A.priority eqs = _
    rw [hstate, hrun]
  · obtain ⟨_, _, _, _, _, _, hstate⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _, _, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, hstate⟩, _⟩ := htrack
    show A.priority eqs = _
    rw [hstate, hrun]
  · obtain ⟨_, _, _, _, _, _, hstate⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]
  · obtain ⟨⟨_, _, _, _, _, _, hstate⟩, _, _, _⟩ := htrack
    show A.priority state = _
    rw [hstate, hrun]

/-- Every run priority of the induced word is emitted by the play at
or after its round. -/
theorem exists_priority_emission
    (hplay :
      (uniformizationGame A σ).PlayFrom
        (.bnd (A.initial, A.initial)) path)
    (hcons :
      CountableParityGame.Strategy.Consistent
        (G := uniformizationGame A σ) (trackingStrategy σ) path)
    (hgrow : ∀ t : Nat, ∃ n : Nat, t < playClock σ path n)
    (t : Nat) :
    ∃ k : Nat, t ≤ k ∧
      uniformizationPriority (path k) =
        A.priority (A.run (execution σ (playEnv σ path hgrow)) t) := by
  have hfind := Nat.find_spec (hgrow t)
  have hne : Nat.find (hgrow t) ≠ 0 := by
    intro h0
    rw [h0] at hfind
    simp at hfind
  obtain ⟨k, hk⟩ : ∃ k : Nat, Nat.find (hgrow t) = k + 1 :=
    ⟨Nat.find (hgrow t) - 1, by omega⟩
  have hkmin : ¬ t < playClock σ path k :=
    Nat.find_min (hgrow t) (by omega)
  rw [hk] at hfind
  have hcases := playClock_succ_cases σ path k
  have hklt : playClock σ path k = t := by omega
  refine ⟨k, ?_, ?_⟩
  · have := playClock_le_self σ path k
    omega
  · by_cases hb : IsBndAt path k
    · exfalso
      rcases hb with ⟨a, ha⟩
      have hsame : playClock σ path (k + 1) = playClock σ path k := by
        show List.length (pathMemory σ path (k + 1)).1 = _
        rw [pathMemory_fst_succ σ path k, ha, trackUpdate_fst_bnd]
        rfl
      omega
    · rw [uniformizationPriority_eq_run_of_not_bnd σ path hplay hcons
        hgrow k hb, hklt]

end Clock

section Endpoint

variable (σ : StrategyPair In₁ In₂ Out₁ Out₂)
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂]
variable [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]

/--
Step W1: the tracking strategy wins the uniformization game from the
initial boundary whenever the tracked strategy wins the real
synthesis game on every environment sequence.
-/
theorem trackingStrategy_winningFrom
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution σ env)) :
    CountableParityGame.Strategy.WinningFrom
      (G := uniformizationGame A σ) (trackingStrategy σ)
      (.bnd (A.initial, A.initial)) := by
  refine ⟨trackingStrategy_legal σ, ?_⟩
  intro path hplay hcons
  have hsteps : ∀ k, uniformizationStep σ (path k) (path (k + 1)) :=
    hplay.2
  have hgrow := playClock_unbounded σ path hsteps
  have haccepts := hwin (playEnv σ path hgrow)
  have hrunparity :
      NatSeqMinEvenParity
        (fun t =>
          A.priority (A.run (execution σ (playEnv σ path hgrow)) t)) :=
    haccepts
  have hattain := attainment σ path hplay hcons hgrow
  have hup :
      ∀ w : Nat,
        NatSeqSeenInfinitelyOften
            (fun t =>
              A.priority
                (A.run (execution σ (playEnv σ path hgrow)) t)) w ->
          NatSeqSeenInfinitelyOften
            (fun k => uniformizationPriority (path k)) w := by
    intro w hw N
    obtain ⟨t, htN, hteq⟩ := hw N
    obtain ⟨k, htk, hkeq⟩ :=
      exists_priority_emission σ path hplay hcons hgrow t
    refine ⟨k, by omega, ?_⟩
    show uniformizationPriority (path k) = w
    rw [hkeq]
    exact hteq
  have hdown :
      ∀ v : Nat,
        NatSeqSeenInfinitelyOften
            (fun k => uniformizationPriority (path k)) v ->
          ∀ N : Nat,
            ∃ j : Nat, N ≤ j ∧
              A.priority
                  (A.run (execution σ (playEnv σ path hgrow)) j) ≤ v := by
    intro v hv N
    obtain ⟨n₀, hn₀⟩ := hgrow N
    obtain ⟨k₁, hk₁, hk₁eq⟩ := hv n₀
    by_cases hb₁ : IsBndAt path k₁
    · obtain ⟨k₂, hk₂, hk₂eq⟩ := hv (k₁ + 1)
      by_cases hb₂ : IsBndAt path k₂
      · rcases hb₂ with ⟨atom₂, ha₂⟩
        obtain ⟨j, hjlt, hjrun, hjdom⟩ :=
          (hattain k₂).1 atom₂ ha₂ (by omega)
        have hdomk₁ := hjdom k₁ (by omega) hb₁
        have hmono := playClock_mono σ path hk₁
        refine ⟨j, by omega, ?_⟩
        have hk₂eq' : uniformizationPriority (path k₂) = v := hk₂eq
        have hval : A.priority atom₂.2 = v := by
          rw [ha₂] at hk₂eq'
          exact hk₂eq'
        show
          A.priority (A.run (execution σ (playEnv σ path hgrow)) j) ≤ v
        rw [← hjrun]
        exact le_of_eq hval
      · refine ⟨playClock σ path k₂, ?_, ?_⟩
        · have := playClock_mono σ path (show n₀ ≤ k₂ by omega)
          omega
        · have hk₂eq' : uniformizationPriority (path k₂) = v := hk₂eq
          show
            A.priority
                (A.run (execution σ (playEnv σ path hgrow))
                  (playClock σ path k₂)) ≤ v
          rw [← uniformizationPriority_eq_run_of_not_bnd σ path hplay
            hcons hgrow k₂ hb₂]
          exact le_of_eq hk₂eq'
    · refine ⟨playClock σ path k₁, ?_, ?_⟩
      · have := playClock_mono σ path hk₁
        omega
      · have hk₁eq' : uniformizationPriority (path k₁) = v := hk₁eq
        show
          A.priority
              (A.run (execution σ (playEnv σ path hgrow))
                (playClock σ path k₁)) ≤ v
        rw [← uniformizationPriority_eq_run_of_not_bnd σ path hplay
          hcons hgrow k₁ hb₁]
        exact le_of_eq hk₁eq'
  exact
    (natSeqMinEvenParity_iff_of_recurring_transfer
        (fun t =>
          A.priority (A.run (execution σ (playEnv σ path hgrow)) t))
        (fun k => uniformizationPriority (path k)) hup hdown).mp
      hrunparity

/-- The initial boundary lies in Even's winning region. -/
theorem bnd_initial_mem_winningRegion
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution σ env)) :
    (UniformizationPosition.bnd (A.initial, A.initial) :
        UniformizationPosition (In₁ := In₁) A) ∈
      (uniformizationGame A σ).WinningRegion ParityPlayer.even :=
  ⟨trackingStrategy σ, trackingStrategy_winningFrom σ hwin⟩

/--
Step W2: positional determinacy hands Even a positional winner of the
uniformization game, whose boundary commitments are per atom: the
cross-boundary uniformization of `prop:journalgivesuniform`.
-/
theorem exists_positional_uniformization_winner
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution σ env)) :
    ∃ τ : (uniformizationGame A σ).PositionalStrategy ParityPlayer.even,
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := uniformizationGame A σ) τ (.bnd (A.initial, A.initial)) :=
  (uniformizationGame A σ).positionalDeterminacy ParityPlayer.even _
    (bnd_initial_mem_winningRegion σ hwin)

/-- A positional Even winner commits one virtual history per atom. -/
theorem exists_commitment_of_positional
    (τ : (uniformizationGame A σ).PositionalStrategy ParityPlayer.even)
    (atom : A.State × A.State) :
    ∃ h : History In₁ In₂ Graph Out₁ Out₂,
      τ.move (.bnd atom) = .committed atom h :=
  τ.legal (.bnd atom) rfl

end Endpoint

end DetParityAutomaton

end DistributedSynthesis
