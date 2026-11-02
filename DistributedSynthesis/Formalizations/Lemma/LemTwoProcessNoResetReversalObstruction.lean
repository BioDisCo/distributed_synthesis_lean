/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmStarReadback
import DistributedSynthesis.Formalizations.Lemma.LemSharedParityProgress

/-!
# Direct reversals can defeat finite local controllers without any reset

Both processes keep a Boolean clock, toggled on every round, independently
of receipt. Their output uses only that clock and their own receipt bit.
For each fixed graph direction the resulting word is accepting; this remains
true after any finite prefix. An alternating environment, however, selects
the losing clock phase of each strict direction and produces only rejecting
letters. No controller is restarted or loses its clock memory.

The objective itself has a one-state local winning implementation: both
processes always output `true`. Thus this is a counterexample to a proposed
composition rule, not to the synthesis theorem. It is a literal execution in
the two-process model, but is not claimed to instantiate the additional
descriptor/target constraints of `exactEffectTable`.
-/

namespace DistributedSynthesis
namespace TwoProcessNoResetReversalObstruction

open DetParityAutomaton

/-- The objective is `GF (both ∨ (outputOne ∧ outputTwo))`. -/
def grant (record : RoundRecord Unit Unit Graph Bool Bool) : Bool :=
  decide (record.graph = .both) || (record.outputOne && record.outputTwo)

def objective : DetParityAutomaton (RoundRecord Unit Unit Graph Bool Bool) where
  State := Bool
  stateFinite := inferInstance
  initial := false
  step _ record := grant record
  priority state := if state then 0 else 1

/-- The clock is representable by one bit; the count is used only to describe
the same controller as a full-view strategy. -/
def clock {p : Proc} (view : View Unit Unit p) : Bool :=
  decide (StarReadback.viewRounds view % 2 = 0)

theorem clock_noRecv {p : Proc} (view : View Unit Unit p)
    (input : PSum Unit Unit) : clock (.noRecv view input) = !clock view := by
  simp only [clock, StarReadback.viewRounds]
  by_cases h : StarReadback.viewRounds view % 2 = 0 <;>
    simp [h, show (StarReadback.viewRounds view + 1) % 2 = 0 ↔
      StarReadback.viewRounds view % 2 ≠ 0 by omega]

theorem clock_recv {p : Proc} (view : View Unit Unit p)
    (input : PSum Unit Unit) (other : View Unit Unit p.other)
    (otherInput : PSum Unit Unit) :
    clock (.recv view input other otherInput) = !clock view := by
  exact clock_noRecv view input

/-- Each output is a function only of the local clock and local receipt tag. -/
def replacement : StrategyPair Unit Unit Bool Bool where
  one := fun view ↦ if view.receiptTag = .recv then !clock view else clock view
  two := fun view ↦ if view.receiptTag = .recv then clock view else !clock view

/-- A winning replacement does exist for the very same objective. -/
def alwaysGrant : StrategyPair Unit Unit Bool Bool where
  one := fun _ ↦ true
  two := fun _ ↦ true

theorem alwaysGrant_wins (env : EnvironmentSequence Unit Unit) :
    objective.Accepts (execution alwaysGrant env) := by
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro n
    refine ⟨n + 1, by omega, ?_⟩
    simp [runFrom, objective, grant, execution_apply, nextRound, alwaysGrant]
  · intro p _
    exact Nat.zero_le p

/-- All finite histories are covered, not just an initial empty block. -/
theorem nextRound_grant
    (history : History Unit Unit Graph Bool Bool)
    (env : EnvironmentRound Unit Unit) :
    grant (nextRound replacement history env) =
      match env.graph with
      | .left => !decide ((history.length + 1) % 2 = 0)
      | .right => decide ((history.length + 1) % 2 = 0)
      | .both => true := by
  have hone : StarReadback.viewRounds (viewPair history).1 = history.length :=
    StarReadback.viewRounds_currentView .one history
  have htwo : StarReadback.viewRounds (viewPair history).2 = history.length :=
    StarReadback.viewRounds_currentView .two history
  cases hgraph : env.graph <;>
    simp [grant, nextRound, replacement, nextView, advanceViewsWithEnvironment,
      hgraph, View.receiptTag, clock, StarReadback.viewRounds, hone, htwo]

theorem execution_grant (env : EnvironmentSequence Unit Unit) (n : Nat) :
    grant (execution replacement env n) =
      match (env n).graph with
      | .left => !decide ((n + 1) % 2 = 0)
      | .right => decide ((n + 1) % 2 = 0)
      | .both => true := by
  rw [execution_apply, nextRound_grant]
  have hlen : (executionPrefix replacement env n).length = n :=
    executionPrefix_length replacement env n
  rw [hlen]

/-- Every eventually fixed graph direction wins, with the same clocks
retained across the preceding finite execution. -/
theorem replacement_wins_eventually_constant
    (env : EnvironmentSequence Unit Unit) (direction : Graph) (N : Nat)
    (hfixed : ∀ n, N ≤ n → (env n).graph = direction) :
    objective.Accepts (execution replacement env) := by
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro n
    cases direction with
    | left =>
      refine ⟨2 * (N + n) + 1, by omega, ?_⟩
      change objective.priority
        (grant (execution replacement env (2 * (N + n)))) = 0
      rw [execution_grant, hfixed _ (by omega)]
      simp [objective]
    | right =>
      refine ⟨2 * (N + n) + 2, by omega, ?_⟩
      change objective.priority
        (grant (execution replacement env (2 * (N + n) + 1))) = 0
      rw [execution_grant, hfixed _ (by omega)]
      simp [objective, show (2 * (N + n) + 1 + 1) % 2 = 0 by omega]
    | both =>
      refine ⟨N + n + 1, by omega, ?_⟩
      change objective.priority (grant (execution replacement env (N + n))) = 0
      rw [execution_grant, hfixed _ (by omega)]
      rfl
  · intro p _
    exact Nat.zero_le p

/-- Nature picks the strict direction whose current clock phase is losing. -/
def alternating : EnvironmentSequence Unit Unit := fun n ↦
  ⟨(), (), if n % 2 = 0 then .right else .left⟩

theorem alternating_direct_reversal (n : Nat) :
    (alternating n).graph ≠ (alternating (n + 1)).graph ∧
      (alternating n).graph ≠ .both := by
  by_cases h : n % 2 = 0 <;>
    simp [alternating, h, show (n + 1) % 2 = 0 ↔ n % 2 ≠ 0 by omega]

theorem alternating_no_grant (n : Nat) :
    grant (execution replacement alternating n) = false := by
  rw [execution_grant]
  by_cases h : n % 2 = 0 <;>
    simp [alternating, h, show (n + 1) % 2 = 0 ↔ n % 2 ≠ 0 by omega]

theorem alternating_run (n : Nat) :
    objective.run (execution replacement alternating) n = false := by
  cases n with
  | zero => rfl
  | succ n => exact alternating_no_grant n

theorem replacement_rejects_alternating :
    ¬ objective.Accepts (execution replacement alternating) := by
  rintro ⟨p, heven, hseen, _⟩
  obtain ⟨n, _, hp⟩ := hseen 0
  change objective.priority (objective.run (execution replacement alternating) n) = p at hp
  rw [alternating_run] at hp
  have hone : p = 1 := hp.symm
  obtain ⟨k, hk⟩ := heven
  omega

/-- The actual two-state rejecting cycle forbids any shared progress rank,
although each homogeneous direction is accepting. -/
theorem replacement_has_no_shared_progress
    {Rank : Type*} [LinearOrder Rank] [WellFoundedLT Rank]
    (rank : Nat → Nat → Rank)
    (hweak : ∀ p, ¬ NatEven p → ∀ n,
      p ≤ objective.priority (objective.run (execution replacement alternating) n) →
        rank p (n + 1) ≤ rank p n)
    (hstrict : ∀ p, ¬ NatEven p → ∀ n,
      objective.priority (objective.run (execution replacement alternating) n) = p →
        rank p (n + 1) < rank p n) : False := by
  exact replacement_rejects_alternating
    (objective.acceptsFrom_of_shared_wellFounded_progress objective.initial
      (execution replacement alternating) rank hweak hstrict)

end TwoProcessNoResetReversalObstruction
end DistributedSynthesis
