/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemTwoProcessNoResetReversalObstruction

/-!
# Exact common-choice test for the two-process clock-controller family

This solves the replacement-choice question completely for a finite family
of genuinely distributed controllers and the objective of the no-reset test.
There are four local Boolean output tables, each reading only a one-bit clock;
the local receipt bit selects the appropriate table. Clocks never reset.

Winning against every graph sequence is equivalent to the existence of a
clock phase at which both strict directions grant. In contrast, winning each
fixed direction only requires a possibly different granting phase for each
direction. The two quantifier orders are not equivalent.

This is an exact restricted-family classification, not a classification of
the physical sibling moves or a completeness theorem for arbitrary DPAs.
-/

namespace DistributedSynthesis
namespace TwoProcessClockPolicyClassification

open DetParityAutomaton
open TwoProcessNoResetReversalObstruction (objective grant clock)

structure Policy where
  oneBlind : Bool → Bool
  oneRecv : Bool → Bool
  twoBlind : Bool → Bool
  twoRecv : Bool → Bool
deriving Fintype, DecidableEq

def leftGrant (policy : Policy) (phase : Bool) : Bool :=
  policy.oneRecv phase && policy.twoBlind phase

def rightGrant (policy : Policy) (phase : Bool) : Bool :=
  policy.oneBlind phase && policy.twoRecv phase

def strategy (policy : Policy) : StrategyPair Unit Unit Bool Bool where
  one := fun view ↦ if view.receiptTag = .recv
    then policy.oneRecv (clock view) else policy.oneBlind (clock view)
  two := fun view ↦ if view.receiptTag = .recv
    then policy.twoRecv (clock view) else policy.twoBlind (clock view)

def phaseAt (n : Nat) : Bool := decide ((n + 1) % 2 = 0)

def DirectionwiseGood (policy : Policy) : Prop :=
  (∃ phase, leftGrant policy phase = true) ∧
    (∃ phase, rightGrant policy phase = true)

def JointlyGood (policy : Policy) : Prop :=
  ∃ phase, leftGrant policy phase = true ∧ rightGrant policy phase = true

instance (policy : Policy) : Decidable (DirectionwiseGood policy) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop)))

instance (policy : Policy) : Decidable (JointlyGood policy) :=
  inferInstanceAs (Decidable (∃ _ : Bool, (_ : Prop)))

theorem execution_grant (policy : Policy)
    (env : EnvironmentSequence Unit Unit) (n : Nat) :
    grant (execution (strategy policy) env n) =
      match (env n).graph with
      | .left => leftGrant policy (phaseAt n)
      | .right => rightGrant policy (phaseAt n)
      | .both => true := by
  rw [execution_apply]
  let history := executionPrefix (strategy policy) env n
  have hlen : history.length = n := executionPrefix_length (strategy policy) env n
  have hone : StarReadback.viewRounds (viewPair history).1 = n :=
    (StarReadback.viewRounds_currentView .one history).trans hlen
  have htwo : StarReadback.viewRounds (viewPair history).2 = n :=
    (StarReadback.viewRounds_currentView .two history).trans hlen
  change grant (nextRound (strategy policy) history (env n)) = _
  cases hgraph : (env n).graph <;>
    simp [grant, nextRound, strategy, nextView, advanceViewsWithEnvironment,
      hgraph, View.receiptTag, clock, StarReadback.viewRounds, hone, htwo,
      leftGrant, rightGrant, phaseAt]

theorem phaseAt_seen (phase : Bool) (N : Nat) :
    ∃ n, N ≤ n ∧ phaseAt n = phase := by
  cases phase with
  | false => exact ⟨2 * N, by omega, by simp [phaseAt]⟩
  | true => exact ⟨2 * N + 1, by omega,
      by simp [phaseAt, show (2 * N + 1 + 1) % 2 = 0 by omega]⟩

/-- A shared good phase gives infinitely many grants regardless of how
Nature switches the graph. -/
theorem jointlyGood_wins (policy : Policy) (hjoint : JointlyGood policy)
    (env : EnvironmentSequence Unit Unit) :
    objective.Accepts (execution (strategy policy) env) := by
  obtain ⟨phase, hleft, hright⟩ := hjoint
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro N
    obtain ⟨n, hn, hphase⟩ := phaseAt_seen phase N
    refine ⟨n + 1, by omega, ?_⟩
    change objective.priority (grant (execution (strategy policy) env n)) = 0
    rw [execution_grant, hphase]
    cases (env n).graph <;> simp [hleft, hright, objective]
  · intro p _
    exact Nat.zero_le p

/-- When no phase works for both directions, Nature chooses a losing strict
direction at each phase. It never needs to observe a hidden local state: the
clock is determined by round number. -/
def spoilingEnvironment (policy : Policy) : EnvironmentSequence Unit Unit :=
  fun n ↦ ⟨(), (), if rightGrant policy (phaseAt n) = true then .left else .right⟩

theorem spoiling_no_grant (policy : Policy) (hjoint : ¬ JointlyGood policy)
    (n : Nat) :
    grant (execution (strategy policy) (spoilingEnvironment policy) n) = false := by
  rw [execution_grant]
  by_cases hright : rightGrant policy (phaseAt n) = true
  · have hleft : leftGrant policy (phaseAt n) = false := by
      cases h : leftGrant policy (phaseAt n) with
      | false => rfl
      | true => exact False.elim (hjoint ⟨phaseAt n, h, hright⟩)
    simp [spoilingEnvironment, hright, hleft]
  · simp [spoilingEnvironment, hright]

theorem spoiling_rejects (policy : Policy) (hjoint : ¬ JointlyGood policy) :
    ¬ objective.Accepts (execution (strategy policy) (spoilingEnvironment policy)) := by
  have hrun : ∀ n, objective.run
      (execution (strategy policy) (spoilingEnvironment policy)) n = false := by
    intro n
    cases n with
    | zero => rfl
    | succ n => exact spoiling_no_grant policy hjoint n
  rintro ⟨p, heven, hseen, _⟩
  obtain ⟨n, _, hp⟩ := hseen 0
  change objective.priority (objective.run _ n) = p at hp
  rw [hrun] at hp
  have hpone : p = 1 := hp.symm
  obtain ⟨k, hk⟩ := heven
  omega

/-- Complete full-model characterization for this finite local family. -/
theorem wins_iff_jointlyGood (policy : Policy) :
    (∀ env, objective.Accepts (execution (strategy policy) env)) ↔
      JointlyGood policy := by
  constructor
  · intro hwin
    by_contra hjoint
    exact spoiling_rejects policy hjoint (hwin (spoilingEnvironment policy))
  · exact jointlyGood_wins policy

/-- The full objective product for this local family. The first coordinate
is the current output-clock phase, the second the literal DPA state. -/
def runtimeStep (policy : Policy) (state : Bool × Bool) (direction : Graph) :
    Bool × Bool :=
  (!state.1, match direction with
    | .left => leftGrant policy state.1
    | .right => rightGrant policy state.1
    | .both => true)

def progressRank (goodPhase : Bool) (state : Bool × Bool) : Nat :=
  if state.2 then 0 else if state.1 = goodPhase then 1 else 2

/-- Joint feasibility gives a concrete rank bounded by two; it is not merely
an assumed acceptance certificate in this solved finite instance. -/
theorem progressRank_decreases (policy : Policy) (goodPhase : Bool)
    (hleft : leftGrant policy goodPhase = true)
    (hright : rightGrant policy goodPhase = true)
    (phase : Bool) (direction : Graph) :
    progressRank goodPhase (runtimeStep policy (phase, false) direction) <
      progressRank goodPhase (phase, false) := by
  by_cases heq : phase = goodPhase
  · subst phase
    cases direction <;> simp [runtimeStep, progressRank, hleft, hright]
  · have hnext : !phase = goodPhase := by cases phase <;> cases goodPhase <;> simp_all
    cases phase <;> cases goodPhase <;> cases direction <;>
      simp_all [runtimeStep, progressRank] <;> split <;> decide

/-- One explicit certificate for all strict/common transitions, constructed
from the joint condition. Direction-wise witnesses need not supply one. -/
def sharedProgress (policy : Policy) (goodPhase : Bool)
    (hleft : leftGrant policy goodPhase = true)
    (hright : rightGrant policy goodPhase = true) :
    SharedParityProgress objective Prod.snd
      (fun source target ↦ ∃ direction, target = runtimeStep policy source direction)
      Nat where
  rank := fun _ state ↦ progressRank goodPhase state
  nonincrease := by
    intro p hodd source target hedge hlower
    obtain ⟨direction, rfl⟩ := hedge
    rcases source with ⟨phase, q⟩
    have hzero : NatEven 0 := ⟨0, rfl⟩
    cases q with
    | false => exact (progressRank_decreases policy goodPhase hleft hright phase direction).le
    | true =>
      change p ≤ 0 at hlower
      have hp : p = 0 := by omega
      exact False.elim (hodd (hp ▸ hzero))
  decrease := by
    intro p hodd source target hedge hpriority
    obtain ⟨direction, rfl⟩ := hedge
    rcases source with ⟨phase, q⟩
    cases q with
    | false => exact progressRank_decreases policy goodPhase hleft hright phase direction
    | true =>
      change 0 = p at hpriority
      exact False.elim (hodd (hpriority ▸ (show NatEven 0 from ⟨0, rfl⟩)))

def constantEnvironment (direction : Graph) : EnvironmentSequence Unit Unit :=
  fun _ ↦ ⟨(), (), direction⟩

private theorem rejects_of_no_grant (word : OmegaWord
    (RoundRecord Unit Unit Graph Bool Bool)) (hgrant : ∀ n, grant (word n) = false) :
    ¬ objective.Accepts word := by
  have hrun : ∀ n, objective.run word n = false := by
    intro n
    cases n with
    | zero => rfl
    | succ n => exact hgrant n
  rintro ⟨p, heven, hseen, _⟩
  obtain ⟨n, _, hp⟩ := hseen 0
  change objective.priority (objective.run word n) = p at hp
  rw [hrun] at hp
  have hpone : p = 1 := hp.symm
  obtain ⟨k, hk⟩ := heven
  omega

/-- Each direction may use a different granting phase. -/
theorem directionwiseGood_wins_constant (policy : Policy)
    (hgood : DirectionwiseGood policy) (direction : Graph) :
    objective.Accepts (execution (strategy policy) (constantEnvironment direction)) := by
  have hphase : ∃ phase, match direction with
      | .left => leftGrant policy phase = true
      | .right => rightGrant policy phase = true
      | .both => True := by
    cases direction with
    | left => exact hgood.1
    | right => exact hgood.2
    | both => exact ⟨false, trivial⟩
  obtain ⟨phase, hphase⟩ := hphase
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro N
    obtain ⟨n, hn, hclock⟩ := phaseAt_seen phase N
    refine ⟨n + 1, by omega, ?_⟩
    change objective.priority (grant (execution (strategy policy)
      (constantEnvironment direction) n)) = 0
    rw [execution_grant, hclock]
    cases direction <;> simpa [constantEnvironment, objective] using hphase
  · intro p _
    exact Nat.zero_le p

/-- Exact fixed-direction characterization, for comparison with full-model
winning. In particular the exhaustive counts below refer to semantic wins. -/
theorem wins_constant_iff_directionwiseGood (policy : Policy) :
    (∀ direction, objective.Accepts
      (execution (strategy policy) (constantEnvironment direction))) ↔
      DirectionwiseGood policy := by
  constructor
  · intro hwin
    constructor
    · by_contra hleft
      apply rejects_of_no_grant _ ?_ (hwin .left)
      intro n
      rw [execution_grant]
      change leftGrant policy (phaseAt n) = false
      cases h : leftGrant policy (phaseAt n) with
      | false => rfl
      | true => exact False.elim (hleft ⟨phaseAt n, h⟩)
    · by_contra hright
      apply rejects_of_no_grant _ ?_ (hwin .right)
      intro n
      rw [execution_grant]
      change rightGrant policy (phaseAt n) = false
      cases h : rightGrant policy (phaseAt n) with
      | false => rfl
      | true => exact False.elim (hright ⟨phaseAt n, h⟩)
  · exact directionwiseGood_wins_constant policy

set_option maxRecDepth 4096 in
/-- Exhaustive counts in the 256-element local output-table family. -/
theorem policy_count : Fintype.card Policy = 256 := by decide

theorem directionwiseGood_count :
    (Finset.univ.filter DirectionwiseGood).card = 49 := by decide

theorem jointlyGood_count :
    (Finset.univ.filter JointlyGood).card = 31 := by decide

theorem directionwise_but_not_joint_count :
    (Finset.univ.filter (fun policy ↦ DirectionwiseGood policy ∧
      ¬ JointlyGood policy)).card = 18 := by decide

end TwoProcessClockPolicyClassification
end DistributedSynthesis
