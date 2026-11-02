/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingLocalFront
import DistributedSynthesis.Formalizations.Theorem.ThmDPACombinators
import DistributedSynthesis.Formalizations.Theorem.ThmStarReadback

/-!
# Finite blind controllers need not reproduce the named winning strategy

Keeping exact semantic memory in the bank does not undo the rationalization
already performed inside each physical sibling move.  On a constant-input
blind tail, that move's owner follows a finite deterministic state machine.
Its output is therefore eventually periodic.  A winning perfect-recall
strategy need not have this property, even for the accept-all objective.

The example below outputs `true` exactly at power-of-two round counts.  No
suffix of its output is eventually periodic.  Consequently no finite blind
owner can reproduce any execution suffix of this particular winning strategy.
This refutes literal preservation of the named strategy as a general proof
target, not existence of a finite winning replacement or owner-kernel safety.
-/

namespace DistributedSynthesis

/-- Eventual periodicity with a strictly positive period. -/
def WordEventuallyPeriodic {α : Type*} (word : Nat → α) : Prop :=
  ∃ threshold period, 0 < period ∧
    ∀ n, threshold ≤ n → word (n + period) = word n

/-- On a fixed input, every deterministic finite-state output stream is
eventually periodic.  Two equal states on the orbit give the period, and
determinism propagates their equality to every later offset. -/
theorem finite_orbit_output_eventuallyPeriodic
    {State Output : Type*} [Finite State]
    (step : State → State) (label : State → Output) (initial : State) :
    WordEventuallyPeriodic (fun n ↦ label (step^[n] initial)) := by
  obtain ⟨i, j, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : Nat ↦ step^[n] initial)
  have ordered : ∃ i j, i < j ∧ step^[i] initial = step^[j] initial := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨i, j, hlt, heq⟩
    · exact ⟨j, i, hgt, heq.symm⟩
  obtain ⟨i, j, hlt, heq⟩ := ordered
  refine ⟨i, j - i, Nat.sub_pos_of_lt hlt, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  change label (step^[i + k + (j - i)] initial) = label (step^[i + k] initial)
  have hindices : i + k + (j - i) = k + j := by omega
  rw [hindices, Function.iterate_add_apply, ← heq,
    show i + k = k + i from Nat.add_comm _ _, Function.iterate_add_apply]

noncomputable section

/-- A deliberately unnecessary infinite-memory output schedule. -/
def powerOfTwoPulse (n : Nat) : Bool := by
  classical
  exact decide (∃ exponent : Nat, 2 ^ exponent = n)

@[simp] theorem powerOfTwoPulse_true (n : Nat) :
    powerOfTwoPulse n = true ↔ ∃ exponent : Nat, 2 ^ exponent = n := by
  classical
  simp [powerOfTwoPulse]

/-- A pulse beyond the proposed threshold and period would force another
pulse strictly between two consecutive powers of two. -/
theorem powerOfTwoPulse_suffix_not_eventuallyPeriodic (offset : Nat) :
    ¬ WordEventuallyPeriodic (fun n ↦ powerOfTwoPulse (offset + n)) := by
  rintro ⟨threshold, period, hperiod, hrepeat⟩
  let exponent := offset + threshold + period + 1
  let pulse := 2 ^ exponent
  have hlarge : exponent < pulse := Nat.lt_pow_self (by decide)
  have hoffset : offset ≤ pulse := by dsimp [exponent] at hlarge; omega
  have hthreshold : threshold ≤ pulse - offset := by
    dsimp [exponent] at hlarge
    omega
  have hperiodSmall : period < pulse := by
    dsimp [exponent] at hlarge
    omega
  have hfirst : powerOfTwoPulse pulse = true :=
    (powerOfTwoPulse_true pulse).mpr ⟨exponent, rfl⟩
  have hsecond := hrepeat (pulse - offset) hthreshold
  change powerOfTwoPulse (offset + (pulse - offset + period)) =
    powerOfTwoPulse (offset + (pulse - offset)) at hsecond
  have hcancel : offset + (pulse - offset) = pulse := by omega
  have hcancelNext : offset + (pulse - offset + period) = pulse + period := by
    omega
  rw [hcancelNext, hcancel, hfirst] at hsecond
  obtain ⟨nextExponent, hnext⟩ := (powerOfTwoPulse_true _).mp hsecond
  have hexponent : exponent < nextExponent := by
    by_contra h
    have hle := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt h)
    change 2 ^ nextExponent ≤ pulse at hle
    omega
  have hnextBound := Nat.pow_le_pow_right (by decide : 0 < 2) hexponent
  have hdouble : 2 ^ (exponent + 1) = pulse + pulse := by
    simp [pulse, pow_succ, Nat.mul_two]
  rw [hdouble, hnext] at hnextBound
  omega

/-- Both current receipt choices count one round, so this strategy's first
output depends only on elapsed time, not on the environment. -/
def powerOfTwoPulseStrategy : StrategyPair Unit Unit Bool Bool where
  one := fun view ↦ powerOfTwoPulse (DetParityAutomaton.StarReadback.viewRounds view)
  two := fun _ ↦ false

theorem powerOfTwoPulseStrategy_wins :
    ∀ env : EnvironmentSequence Unit Unit,
      (DetParityAutomaton.top :
        DetParityAutomaton (RoundRecord Unit Unit Graph Bool Bool)).Accepts
          (execution powerOfTwoPulseStrategy env) := by
  intro env
  exact DetParityAutomaton.top_accepts _

theorem powerOfTwoPulseStrategy_output
    (env : EnvironmentSequence Unit Unit) (n : Nat) :
    (execution powerOfTwoPulseStrategy env n).outputOne =
      powerOfTwoPulse (n + 1) := by
  rw [execution_apply]
  change powerOfTwoPulse
      (DetParityAutomaton.StarReadback.viewRounds
        (nextView .one (executionPrefix powerOfTwoPulseStrategy env n) (env n))) = _
  have hlength : (executionPrefix powerOfTwoPulseStrategy env n).length = n :=
    executionPrefix_length powerOfTwoPulseStrategy env n
  have hrounds : DetParityAutomaton.StarReadback.viewRounds
      (viewPair (executionPrefix powerOfTwoPulseStrategy env n)).1 = n := by
    change DetParityAutomaton.StarReadback.viewRounds
      (currentView .one (executionPrefix powerOfTwoPulseStrategy env n)) = n
    rw [DetParityAutomaton.StarReadback.viewRounds_currentView, hlength]
  cases hgraph : (env n).graph <;>
    simp only [nextView, advanceViewsWithEnvironment, hgraph,
      DetParityAutomaton.StarReadback.viewRounds, hrounds]

/-- No finite autonomous owner reproduces even a suffix of the named winning
strategy, regardless of which environment generated that suffix. -/
theorem powerOfTwoPulseStrategy_no_finite_literal_suffix
    {State : Type*} [Finite State]
    (step : State → State) (label : State → Bool) (initial : State)
    (env : EnvironmentSequence Unit Unit) (offset : Nat) :
    ¬ ∀ n, label (step^[n] initial) =
      (execution powerOfTwoPulseStrategy env (offset + n)).outputOne := by
  intro heq
  have hperiodic := finite_orbit_output_eventuallyPeriodic step label initial
  have hword : (fun n ↦ label (step^[n] initial)) =
      (fun n ↦ powerOfTwoPulse ((offset + 1) + n)) := by
    funext n
    rw [heq, powerOfTwoPulseStrategy_output]
    congr 1
    omega
  rw [hword] at hperiodic
  exact powerOfTwoPulse_suffix_not_eventuallyPeriodic (offset + 1) hperiodic

namespace DetParityAutomaton

/-- This applies to the actual physical sibling owner used by the exact
bank, not just to an abstract proposed finite quotient of semantic memory. -/
theorem rightPhysicalSiblingOwner_no_literal_powerOfTwoPulse_suffix
    (A : DetParityAutomaton (RoundRecord Unit Unit Graph Bool Bool))
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (env : EnvironmentSequence Unit Unit) (offset : Nat) :
    let controller := move.memberController A false
    ¬ ∀ n,
      ((controller.labelOf ((fun control ↦ controller.step control ())^[n]
        owner)).1 ()) =
      (execution powerOfTwoPulseStrategy env (offset + n)).outputOne := by
  exact powerOfTwoPulseStrategy_no_finite_literal_suffix
    (fun control ↦ (move.memberController A false).step control ())
    (fun control ↦ ((move.memberController A false).labelOf control).1 ())
    owner env offset

end DetParityAutomaton

end

end DistributedSynthesis
