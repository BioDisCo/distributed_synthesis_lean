/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSharedParityProgress

/-!
# Winning continuations are not closed under infinite restart

The objective asks for infinitely many `true` outputs. The two-state
continuation emits `false` once and then `true` forever, so it wins from
either objective state. Restarting it before its second output emits only
`false` and loses. Every restart occurs at the same literal objective state;
there is no state-projection error in this example.

This is a stress test for a general continuation-replacement argument, not a
counterexample to the concrete owner table. It isolates why separately
accepting blocks, exact DPA endpoints, and exact finite-block priorities are
not enough: the replacement edges must preserve one shared progress measure.
-/

namespace DistributedSynthesis

namespace AcceptingContinuationRestartObstruction

open DetParityAutomaton

/-- The DPA for infinitely many `true` letters. -/
def objective : DetParityAutomaton Bool where
  State := Bool
  stateFinite := inferInstance
  initial := false
  step _ letter := letter
  priority state := if state then 0 else 1

/-- The output of a two-state continuation: wait once, then grant forever. -/
def continuation (n : Nat) : Bool := decide (0 < n)

theorem continuation_wins_from_every_state (initial : objective.State) :
    objective.AcceptsFrom initial continuation := by
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro n
    refine ⟨n + 2, by omega, ?_⟩
    simp [runFrom, objective, continuation]
  · intro p _
    exact Nat.zero_le p

/-- Use only the initial output of each freshly restarted continuation. -/
def restarted : OmegaWord Bool := fun _ ↦ continuation 0

theorem restarted_run (n : Nat) :
    objective.runFrom false restarted n = false := by
  cases n <;> simp [runFrom, objective, restarted, continuation]

theorem restarted_rejects : ¬ objective.AcceptsFrom false restarted := by
  rintro ⟨p, heven, hseen, _⟩
  obtain ⟨n, _, hp⟩ := hseen 0
  have hone : p = 1 := by
    change objective.priority (objective.runFrom false restarted n) = p at hp
    rw [restarted_run] at hp
    exact hp.symm
  obtain ⟨k, hk⟩ := heven
  omega

/-- At every splice the literal DPA is back at the same state from which a
fresh continuation is winning. This does not make the infinite splice win. -/
theorem every_restart_has_winning_continuation :
    ∀ n, objective.AcceptsFrom (objective.runFrom false restarted n)
      continuation := by
  intro n
  exact continuation_wins_from_every_state _

/-- Even exact one-round state tracking cannot detect the postponed grant:
the actual executed prefix ends in `false` and sees only priority one. -/
theorem restart_prefix_exact :
    objective.step false (continuation 0) = false ∧
      objective.priority false = 1 ∧
      objective.priority (objective.step false (continuation 0)) = 1 := by
  simp [objective, continuation]

/-- A shared certificate rejects this reset immediately, since it would
require a rank to be strictly smaller than itself at odd priority one. -/
theorem no_shared_progress_for_restart
    {Rank : Type*} [LinearOrder Rank] :
    ¬ Nonempty (SharedParityProgress objective id
      (fun source target ↦ source = false ∧ target = false) Rank) := by
  rintro ⟨certificate⟩
  have hodd : ¬ NatEven 1 := by rintro ⟨k, hk⟩; omega
  exact (lt_irrefl _)
    (certificate.decrease 1 hodd false false ⟨rfl, rfl⟩ rfl)

end AcceptingContinuationRestartObstruction

end DistributedSynthesis
