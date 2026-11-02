/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmRootPinnedBlockNarrowing

/-!
# A reusable first-letter safety guard for block monitors

`rootPinned` fixes a complete first record.  At a local handoff one often
needs less: only a finite predicate on the informed receiver's first output
must be retained, while the blind output and all later records remain free.

This wrapper adds exactly that sticky one-shot test.  A failed test has
priority one forever, so unconditional narrowing preserves it.  The wrapper
does not expose the tested predicate, an orientation, or a leader bit to
either process; it is only part of the finite objective-monitor state.
-/

namespace DistributedSynthesis

universe u v x y w

namespace BlockRecordMonitor

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

/-- Product state of the underlying monitor and a sticky one-shot guard. -/
structure FirstLetterGuardState where
  base : M.State
  first : Bool
  safe : Bool

noncomputable instance : Fintype (FirstLetterGuardState M) := by
  classical
  exact Fintype.ofEquiv (M.State × Bool × Bool) {
    toFun := fun state => ⟨state.1, state.2.1, state.2.2⟩
    invFun := fun state => (state.base, state.first, state.safe)
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; cases state; rfl
  }

/-- Add a sticky Boolean test on the first realized record. -/
noncomputable def firstLetterGuard
    (allowed : RealizedBlockRound RIn SIn ROut SOut → Bool) :
    BlockRecordMonitor RIn SIn ROut SOut := by
  classical
  exact {
    State := FirstLetterGuardState M
    stateFinite := inferInstance
    initial := ⟨M.initial, true, true⟩
    step := fun state letter =>
      ⟨M.step state.base letter, false,
        state.safe && (!state.first || allowed letter)⟩
    priority := fun state => if state.safe then M.priority state.base + 2 else 1
  }

@[simp] theorem firstLetterGuard_initial
    (allowed : RealizedBlockRound RIn SIn ROut SOut → Bool) :
    (M.firstLetterGuard allowed).initial = ⟨M.initial, true, true⟩ := rfl

@[simp] theorem firstLetterGuard_step_base
    (allowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (state : FirstLetterGuardState M)
    (letter : RealizedBlockRound RIn SIn ROut SOut) :
    ((M.firstLetterGuard allowed).step state letter).base =
      M.step state.base letter := rfl

@[simp] theorem firstLetterGuard_step_first
    (allowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (state : FirstLetterGuardState M)
    (letter : RealizedBlockRound RIn SIn ROut SOut) :
    ((M.firstLetterGuard allowed).step state letter).first = false := rfl

/-- The base component is exactly the underlying monitor run. -/
theorem firstLetterGuard_run_base
    (allowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut)) : ∀ n,
    ((M.firstLetterGuard allowed).run word n).base = M.run word n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, BlockRecordMonitor.run]
      exact congrArg (fun state => M.step state (word n)) ih

theorem firstLetterGuard_run_first_succ
    (allowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut)) (n : Nat) :
    ((M.firstLetterGuard allowed).run word (n + 1)).first = false := by
  rw [BlockRecordMonitor.run]
  rfl

/-- Once the one-shot test fails, it remains failed forever. -/
theorem firstLetterGuard_safe_false_persists
    (allowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut))
    (n : Nat)
    (hfalse : ((M.firstLetterGuard allowed).run word n).safe = false) :
    ∀ k, ((M.firstLetterGuard allowed).run word (n + k)).safe = false := by
  intro k
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      change
        Bool.and ((M.firstLetterGuard allowed).run word (n + k)).safe _ = false
      rw [ih]
      rfl

/-- A successful first test keeps the sticky bit true forever. -/
theorem firstLetterGuard_run_safe_of_first_allowed
    (allowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut))
    (hroot : allowed (word 0) = true) : ∀ n,
    ((M.firstLetterGuard allowed).run word n).safe = true := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run]
      cases n with
      | zero =>
          change Bool.and true (Bool.or (!true) (allowed (word 0))) = true
          rw [hroot]
          rfl
      | succ n =>
          change
            Bool.and ((M.firstLetterGuard allowed).run word (n + 1)).safe
              (Bool.or
                (!((M.firstLetterGuard allowed).run word (n + 1)).first)
                (allowed (word (n + 1)))) = true
          rw [firstLetterGuard_run_first_succ M allowed word n]
          simp [ih]

/-- Winning forces the sticky one-shot safety bit to remain true. -/
theorem firstLetterGuard_safe_of_wins
    (allowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut))
    (hwins : (M.firstLetterGuard allowed).WinsPlay word) (n : Nat) :
    ((M.firstLetterGuard allowed).run word n).safe = true := by
  by_contra hnot
  have hfalse : ((M.firstLetterGuard allowed).run word n).safe = false :=
    Bool.eq_false_of_not_eq_true hnot
  have hpersist := M.firstLetterGuard_safe_false_persists allowed word n hfalse
  have heventual : ∀ k, n ≤ k →
      (M.firstLetterGuard allowed).priority
        ((M.firstLetterGuard allowed).run word k) = 1 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    change (if ((M.firstLetterGuard allowed).run word (n + j)).safe
      then _ else 1) = 1
    rw [hpersist j]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwins

/-- Forgetting the finite first-letter test preserves base winning. -/
theorem firstLetterGuard_base_wins_of_wins
    (allowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut))
    (hwins : (M.firstLetterGuard allowed).WinsPlay word) :
    M.WinsPlay word := by
  unfold BlockRecordMonitor.WinsPlay at hwins ⊢
  have heq :
      (fun n => (M.firstLetterGuard allowed).priority
        ((M.firstLetterGuard allowed).run word n)) =
        fun n => M.priority (M.run word n) + 2 := by
    funext n
    change (if ((M.firstLetterGuard allowed).run word n).safe
      then M.priority ((M.firstLetterGuard allowed).run word n).base + 2
      else 1) = M.priority (M.run word n) + 2
    rw [M.firstLetterGuard_safe_of_wins allowed word hwins n, if_pos rfl,
      M.firstLetterGuard_run_base allowed word n]
  rw [heq] at hwins
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hwins

/-- A base-winning local strategy whose first record passes the test realizes
the strengthened monitor. -/
theorem firstLetterGuard_realizable
    (allowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hbase : ∀ env : Nat → RIn × SIn,
      M.WinsPlay (pairPlay receiver sender env))
    (hroot : ∀ env : Nat → RIn × SIn,
      allowed (pairPlay receiver sender env 0) = true) :
    ∀ env : Nat → RIn × SIn,
      (M.firstLetterGuard allowed).WinsPlay
        (pairPlay receiver sender env) := by
  intro env
  let word := pairPlay receiver sender env
  have hsafe := M.firstLetterGuard_run_safe_of_first_allowed allowed word
    (hroot env)
  have hparity := hbase env
  unfold BlockRecordMonitor.WinsPlay at hparity ⊢
  have heq :
      (fun n => (M.firstLetterGuard allowed).priority
        ((M.firstLetterGuard allowed).run word n)) =
        fun n => M.priority (M.run word n) + 2 := by
    funext n
    change
      (if ((M.firstLetterGuard allowed).run word n).safe then
          M.priority ((M.firstLetterGuard allowed).run word n).base + 2
        else 1) = M.priority (M.run word n) + 2
    rw [hsafe n, if_pos rfl, M.firstLetterGuard_run_base allowed word n]
  rw [heq]
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hparity

/-- Every winning narrowed controller passes the finite predicate on its
first record, for every possible first input pair. -/
theorem firstLetterGuard_root_allowed
    [Inhabited RIn] [Inhabited SIn]
    (allowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (narrowed : LabeledTree SIn
      (NarrowedBlockLabel RIn SIn ROut SOut
        (M.firstLetterGuard allowed).State))
    (hthreads : NarrowedAllThreadsWin (M.firstLetterGuard allowed) narrowed)
    (move : RIn × SIn) :
    allowed
      (narrowedRecord (M.firstLetterGuard allowed) (narrowed [])
        (M.firstLetterGuard allowed).initial move) = true := by
  by_contra hnot
  have hallowed : allowed
      (narrowedRecord (M.firstLetterGuard allowed) (narrowed [])
        (M.firstLetterGuard allowed).initial move) = false :=
    Bool.eq_false_of_not_eq_true hnot
  let env : Nat → RIn × SIn
    | 0 => move
    | _ + 1 => (default, default)
  have hfalse :
      (narrowedThreadState (M.firstLetterGuard allowed) narrowed env 1).safe =
        false := by
    change
      (narrowedControl (M.firstLetterGuard allowed) narrowed
        (branchNode env 0 ++ [env 0])).safe = false
    rw [narrowedControl_append]
    change Bool.and true
      (Bool.or (!true)
        (allowed
          (narrowedRecord (M.firstLetterGuard allowed) (narrowed [])
            (M.firstLetterGuard allowed).initial move))) = false
    rw [hallowed]
    rfl
  have hpersist : ∀ k,
      (narrowedThreadState (M.firstLetterGuard allowed) narrowed env
        (1 + k)).safe = false := by
    intro k
    induction k with
    | zero => simpa using hfalse
    | succ k ih =>
        rw [Nat.add_succ]
        change
          (narrowedControl (M.firstLetterGuard allowed) narrowed
            (branchNode env (1 + k) ++ [env (1 + k)])).safe = false
        rw [narrowedControl_append]
        change Bool.and
          (narrowedThreadState (M.firstLetterGuard allowed) narrowed env
            (1 + k)).safe _ = false
        rw [ih]
        rfl
  have heventual : ∀ n, 1 ≤ n →
      (M.firstLetterGuard allowed).priority
        (narrowedThreadState (M.firstLetterGuard allowed) narrowed env n) =
        1 := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    change
      (if (narrowedThreadState (M.firstLetterGuard allowed) narrowed env
          (1 + k)).safe then _ else 1) = 1
    rw [hpersist k]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ 1 heventual
    (hthreads env)

end BlockRecordMonitor

end DistributedSynthesis
