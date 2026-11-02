/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemTwoProcessPhysicalTargetAudit
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonBothRestart

/-!
# Replacing pulsed-source block labels while retaining the full target contract

The source below is one concrete generated common world. Its two entry states
are `true`, and its initial informed profile is `false`. The two literal
semantic targets used below retain the full incidence codes, including their
profiles and block minima.

This file concerns the exact block contracts. A separate embedding into the
retained-owner runtime is needed before claiming a rejecting owner execution.
-/

namespace DistributedSynthesis
namespace PulsedSourceBlockFlexibility

open DetParityAutomaton TwoProcessNoResetReversalObstruction
open TwoProcessPhysicalTargetAudit (pulsedSource pulsedSource_wins)

noncomputable section

local instance : DecidableEq objective.State := inferInstanceAs (DecidableEq Bool)

def initialWorld : ProfiledRawJointCommonBaseWorld objective pulsedSource :=
  ⟨[], .empty, (), (), objective.initial⟩

def family := profiledRawJointCommonWorldFamily objective initialWorld
def direction := profiledRawJointBothRestartDirection ((), ())
def world := profiledRawJointCommonWorldAfterBoth objective initialWorld ((), ())
def rightMember := world.procOneMember objective
def leftMember := world.procTwoMember objective

theorem right_member : (family.semanticChild objective direction).right () =
    some rightMember :=
  profiledRawJointCommonWorld_semanticChild_right_bothRestart objective
    initialWorld ((), ())

theorem left_member : (family.semanticChild objective direction).left () =
    some leftMember :=
  profiledRawJointCommonWorld_semanticChild_left_bothRestart objective
    initialWorld ((), ())

def source : ProfiledRawRightSlot objective := (((true, true), true), fun _ ↦ false)

theorem right_source : profiledRawRightSlotOfSemanticPair objective rightMember =
    source := by
  apply Prod.ext
  · apply Prod.ext
    · decide
    · decide
  · funext input
    rcases input with ⟨⟨⟩, ⟨⟩⟩
    decide

theorem left_source : profiledRawLeftSlotOfSemanticPair objective leftMember =
    source := by
  apply Prod.ext
  · apply Prod.ext
    · decide
    · decide
  · funext input
    rcases input with ⟨⟨⟩, ⟨⟩⟩
    decide

def originalRight := profiledRawJointRightSiblingActivation objective
  pulsedSource_wins family direction rightMember right_member false

def originalLeft := profiledRawJointLeftSiblingActivation objective
  pulsedSource_wins family direction leftMember left_member false

/-- Select an actual source target, not just a DPA-code projection. -/
def rightTarget (granting : Bool) : ProfiledRawJointUnitTarget objective :=
  originalRight.target .first (if granting then [((), ())] else []) ((), ())

def leftTarget (granting : Bool) : ProfiledRawJointUnitTarget objective :=
  originalLeft.target .first (if granting then [((), ())] else []) ((), ())

theorem rightTarget_allowed (g : Bool) :
    ProfiledRawJointRightSiblingSharedAllowedTarget objective family direction
      (rightTarget g) := originalRight.target_allowed _ _ _

theorem leftTarget_allowed (g : Bool) :
    ProfiledRawJointLeftSiblingSharedAllowedTarget objective family direction
      (leftTarget g) := originalLeft.target_allowed _ _ _

theorem rightTarget_projection (g : Bool) :
    profiledRawJointUnitRightTargetProjection objective (rightTarget g) =
      .inr (.inr ((((g, true), true), fun _ ↦ !g))) := by
  rw [rightTarget, originalRight.target_state]
  dsimp only [originalRight, profiledRawJointRightSiblingActivation]
  rw [right_source]
  cases g <;> apply congrArg Sum.inr <;> apply congrArg Sum.inr <;> apply Prod.ext
  all_goals decide

theorem leftTarget_projection (g : Bool) :
    profiledRawJointUnitLeftTargetProjection objective (leftTarget g) =
      .inr (.inl ((((g, true), true), fun _ ↦ !g))) := by
  rw [leftTarget, originalLeft.target_state]
  dsimp only [originalLeft, profiledRawJointLeftSiblingActivation]
  rw [left_source]
  cases g <;> apply congrArg Sum.inr <;> apply congrArg Sum.inl <;> apply Prod.ext
  all_goals decide

/-- A chosen strict grant schedule. Closing outputs realize the profile
stored at the preceding target, even if the schedule is not alternating. -/
def rightLambda (g : Nat → Bool) : ProcOnePairedRightLambda
    (In₁ := Unit) (In₂ := Unit) (Out₁ := Bool) (Out₂ := Bool) where
  blind past _ := g past.length
  informedLeft past _ := g past.length
  informedBoth past _ := g past.length
  bothOneLeft past _ := !g (past.length - 1)
  bothOneBoth past _ := !g (past.length - 1)

def leftLambda (g : Nat → Bool) : ProcTwoPairedLeftLambda
    (In₁ := Unit) (In₂ := Unit) (Out₁ := Bool) (Out₂ := Bool) where
  blind past _ := g past.length
  informedRight past _ := g past.length
  informedBoth past _ := g past.length
  bothTwoRight past _ := !g (past.length - 1)
  bothTwoBoth past _ := !g (past.length - 1)

theorem blockMin_true (word : List (RoundRecord Unit Unit Graph Bool Bool)) :
    blockMinState objective true word = true := by
  have h : ∀ q : Bool, (word.foldl
      (fun pair record ↦ (objective.step pair.1 record,
        objective.minPriorityState pair.2 (objective.step pair.1 record)))
      (q, true)).2 = true := by
    induction word with
    | nil => intro q; rfl
    | cons record word ih =>
      intro q
      simpa [minPriorityState, objective] using ih (grant record)
  exact h true

theorem right_child (g : Nat → Bool) (row : PairedEntryRow)
    (past : List (Unit × Unit)) (input : Unit × Unit) :
    profiledRawRightChildSlot objective source (rightLambda g) row past input =
      (((g past.length, true), true), fun _ ↦ !g past.length) := by
  cases row <;>
    simp only [profiledRawRightChildSlot, source]
  all_goals apply Prod.ext
  all_goals first
    | (apply Prod.ext
       · simp [pairedRightFreshChildCodeLeft, pairedRightFreshChildCodeBoth,
           rightLambda, objective, grant, rightRoundRecord, bothRoundRecord, senderWord]
       · exact blockMin_true _)
    | (funext next; simp [rightClosingProfile, rightLambda])

theorem left_child (g : Nat → Bool) (row : PairedEntryRow)
    (past : List (Unit × Unit)) (input : Unit × Unit) :
    profiledRawLeftChildSlot objective source (leftLambda g) row past input =
      (((g past.length, true), true), fun _ ↦ !g past.length) := by
  cases row <;>
    simp only [profiledRawLeftChildSlot, source]
  all_goals apply Prod.ext
  all_goals first
    | (apply Prod.ext
       · simp [pairedLeftFreshChildCodeRight, pairedLeftFreshChildCodeBoth,
           leftLambda, objective, grant, leftRoundRecord, bothRoundRecord, senderWord]
       · exact blockMin_true _)
    | (funext next; simp [leftClosingProfile, leftLambda])

theorem right_forever (g : Nat → Bool)
    (hrec : ∀ N, ∃ n, N ≤ n ∧ g n = true) :
    PairedRightForeverAccepts objective source.1.1 (rightLambda g) := by
  constructor <;> intro env
  all_goals refine ⟨0, ⟨0, rfl⟩, ?_, fun p _ ↦ Nat.zero_le p⟩
  all_goals
    intro N
    obtain ⟨n, hn, hg⟩ := hrec N
    refine ⟨n + 1, by omega, ?_⟩
    rw [runFrom]
    simp [pairedRightOmegaWord, rightLambda, senderWord, omegaPrefix,
      objective, grant, rightRoundRecord, hg]

theorem left_forever (g : Nat → Bool)
    (hrec : ∀ N, ∃ n, N ≤ n ∧ g n = true) :
    PairedLeftForeverAccepts objective source.1.1 (leftLambda g) := by
  constructor <;> intro env
  all_goals refine ⟨0, ⟨0, rfl⟩, ?_, fun p _ ↦ Nat.zero_le p⟩
  all_goals
    intro N
    obtain ⟨n, hn, hg⟩ := hrec N
    refine ⟨n + 1, by omega, ?_⟩
    rw [runFrom]
    simp [pairedLeftOmegaWord, leftLambda, senderWord, omegaPrefix,
      objective, grant, leftRoundRecord, hg]

/-- The complete activation for the actual semantic descriptor. The only
schedule restrictions are the pinned first output and recurring grants. -/
def rightActivation (g : Nat → Bool) (hzero : g 0 = false)
    (hrec : ∀ N, ∃ n, N ≤ n ∧ g n = true) :
    ProfiledRawJointTargetRightBlockActivation objective
      (ProfiledRawJointUnitTarget objective)
      (profiledRawJointUnitRightTargetProjection objective)
      (profiledRawJointRightPhysicalSiblingAllowed objective
        (profiledRawJointRightPhysicalSiblingDescriptorOf objective family
          direction rightMember))
      (profiledRawRightSlotOfSemanticPair objective rightMember) where
  lambda := rightLambda g
  initial_profile := by rw [right_source]; funext input; exact hzero
  forever := by rw [right_source]; exact right_forever g hrec
  target := fun _ past _ ↦ rightTarget (g past.length)
  target_allowed := by
    intro row past input
    rw [profiledRawJointRightPhysicalSiblingDescriptorOf_allowed_iff]
    exact rightTarget_allowed _
  target_state := by
    intro row past input
    rw [right_source, rightTarget_projection, right_child]
    rfl

def leftActivation (g : Nat → Bool) (hzero : g 0 = false)
    (hrec : ∀ N, ∃ n, N ≤ n ∧ g n = true) :
    ProfiledRawJointTargetLeftBlockActivation objective
      (ProfiledRawJointUnitTarget objective)
      (profiledRawJointUnitLeftTargetProjection objective)
      (profiledRawJointLeftPhysicalSiblingAllowed objective
        (profiledRawJointLeftPhysicalSiblingDescriptorOf objective family
          direction leftMember))
      (profiledRawLeftSlotOfSemanticPair objective leftMember) where
  lambda := leftLambda g
  initial_profile := by rw [left_source]; funext input; exact hzero
  forever := by rw [left_source]; exact left_forever g hrec
  target := fun _ past _ ↦ leftTarget (g past.length)
  target_allowed := by
    intro row past input
    rw [profiledRawJointLeftPhysicalSiblingDescriptorOf_allowed_iff]
    exact leftTarget_allowed _
  target_state := by
    intro row past input
    rw [left_source, leftTarget_projection, left_child]
    rfl

theorem right_monitor_wins (g : Nat → Bool) (hzero : g 0 = false)
    (hrec : ∀ N, ∃ n, N ≤ n ∧ g n = true) (member : Bool)
    (env : Nat → Unit × Unit) :
    (profiledRawJointRightPhysicalSiblingMonitor objective
      (profiledRawJointRightPhysicalSiblingDescriptorOf objective family
        direction rightMember) member).WinsPlay
      (pairPlay
        (profiledRawJointTargetRightReceiverStrategy objective
          (rightActivation g hzero hrec))
        (pairedRightSenderStrategy (rightLambda g)) env) :=
  profiledRawJointTargetRightBlockMonitor_realizable objective _ _ _
    (rightActivation g hzero hrec) env

theorem left_monitor_wins (g : Nat → Bool) (hzero : g 0 = false)
    (hrec : ∀ N, ∃ n, N ≤ n ∧ g n = true) (member : Bool)
    (env : Nat → Unit × Unit) :
    (profiledRawJointLeftPhysicalSiblingMonitor objective
      (profiledRawJointLeftPhysicalSiblingDescriptorOf objective family
        direction leftMember) member).WinsPlay
      (pairPlay
        (profiledRawJointTargetLeftReceiverStrategy objective
          (leftActivation g hzero hrec))
        (pairedLeftSenderStrategy (leftLambda g)) env) :=
  profiledRawJointTargetLeftBlockMonitor_realizable objective _ _ _
    (leftActivation g hzero hrec) env

/-! ## Two disjoint schedules admitted by these full block contracts -/

def rightSchedule (n : Nat) : Bool := decide (n % 2 = 1)
def leftSchedule (n : Nat) : Bool := decide (0 < n ∧ n % 2 = 0)

theorem rightSchedule_recurs (N : Nat) :
    ∃ n, N ≤ n ∧ rightSchedule n = true :=
  ⟨2 * N + 1, by omega, by simp [rightSchedule]⟩

theorem leftSchedule_recurs (N : Nat) :
    ∃ n, N ≤ n ∧ leftSchedule n = true :=
  ⟨2 * N + 2, by omega, by simp [leftSchedule]⟩

theorem schedules_disjoint (n : Nat) :
    (rightSchedule n && leftSchedule n) = false := by
  by_cases h : n % 2 = 1
  · simp [rightSchedule, leftSchedule, h]
  · simp [rightSchedule, h]

/-- Both exact physical block monitors accept the chosen, disjoint schedules.
No projection or weakening of the target predicate occurs here. -/
theorem disjoint_schedules_monitors_win (member : Bool)
    (env : Nat → Unit × Unit) :
    (profiledRawJointRightPhysicalSiblingMonitor objective
      (profiledRawJointRightPhysicalSiblingDescriptorOf objective family
        direction rightMember) member).WinsPlay
      (pairPlay (profiledRawJointTargetRightReceiverStrategy objective
        (rightActivation rightSchedule (by decide) rightSchedule_recurs))
        (pairedRightSenderStrategy (rightLambda rightSchedule)) env) ∧
    (profiledRawJointLeftPhysicalSiblingMonitor objective
      (profiledRawJointLeftPhysicalSiblingDescriptorOf objective family
        direction leftMember) member).WinsPlay
      (pairPlay (profiledRawJointTargetLeftReceiverStrategy objective
        (leftActivation leftSchedule (by decide) leftSchedule_recurs))
        (pairedLeftSenderStrategy (leftLambda leftSchedule)) env) :=
  ⟨right_monitor_wins _ _ _ _ _, left_monitor_wins _ _ _ _ _⟩

/-- Three states generate both schedules, with no receipt-dependent reset. -/
inductive ScheduleState where
  | initial | odd | even
  deriving DecidableEq, Fintype

def scheduleStep : ScheduleState → ScheduleState
  | .initial => .odd
  | .odd => .even
  | .even => .odd

def scheduleState (n : Nat) : ScheduleState :=
  if n = 0 then .initial else if n % 2 = 1 then .odd else .even

theorem scheduleState_succ (n : Nat) :
    scheduleState (n + 1) = scheduleStep (scheduleState n) := by
  by_cases hz : n = 0
  · subst n; rfl
  · by_cases ho : n % 2 = 1
    · simp [scheduleState, scheduleStep, hz, ho,
        show (n + 1) % 2 ≠ 1 by omega]
    · simp [scheduleState, scheduleStep, hz, ho,
        show (n + 1) % 2 = 1 by omega]

theorem schedules_from_state (n : Nat) :
    (rightSchedule n, leftSchedule n) =
      match scheduleState n with
      | .initial => (false, false)
      | .odd => (true, false)
      | .even => (false, true) := by
  by_cases hz : n = 0
  · subst n; rfl
  · by_cases ho : n % 2 = 1
    · simp [scheduleState, rightSchedule, leftSchedule, hz, ho]
    · simp [scheduleState, rightSchedule, leftSchedule, hz,
        show 0 < n by omega, show n % 2 = 0 by omega]

/-- Finite memory for the complete certificate labels, including both
delayed closing outputs, not merely the strict grant bits. -/
abbrev CertificateState := ScheduleState × Bool × Bool

def scheduleOutputs : ScheduleState → Bool × Bool
  | .initial => (false, false)
  | .odd => (true, false)
  | .even => (false, true)

def certificateStep (state : CertificateState) : CertificateState :=
  (scheduleStep state.1, scheduleOutputs state.1)

def certificateState (n : Nat) : CertificateState :=
  (scheduleState n, rightSchedule (n - 1), leftSchedule (n - 1))

theorem certificateState_succ (n : Nat) :
    certificateState (n + 1) = certificateStep (certificateState n) := by
  change (scheduleState (n + 1), rightSchedule (n + 1 - 1),
    leftSchedule (n + 1 - 1)) =
      (scheduleStep (scheduleState n), scheduleOutputs (scheduleState n))
  rw [scheduleState_succ, Nat.add_sub_cancel]
  exact congrArg (Prod.mk _) (schedules_from_state n)

def rightLetter (state : CertificateState) : RealizedBlockRound Unit Unit
    (ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Bool) (Out₂ := Bool) (ProfiledRawJointUnitTarget objective)) Bool :=
  let g := (scheduleOutputs state.1).1
  (((), ()), ⟨⟨g, g, !state.2.1, !state.2.1⟩, fun _ ↦ rightTarget g⟩, g)

def leftLetter (state : CertificateState) : RealizedBlockRound Unit Unit
    (ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Bool) (Out₂ := Bool) (ProfiledRawJointUnitTarget objective)) Bool :=
  let g := (scheduleOutputs state.1).2
  (((), ()), ⟨⟨g, g, !state.2.2, !state.2.2⟩, fun _ ↦ leftTarget g⟩, g)

private theorem node_length (env : Nat → Unit × Unit) (n : Nat) :
    (branchNode env n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [branchNode, ih]

theorem right_full_letter_finite (env : Nat → Unit × Unit) (n : Nat) :
    pairPlay (profiledRawJointTargetRightReceiverStrategy objective
      (rightActivation rightSchedule (by decide) rightSchedule_recurs))
      (pairedRightSenderStrategy (rightLambda rightSchedule)) env n =
        rightLetter (certificateState n) := by
  have h := schedules_from_state n
  change (rightSchedule n, leftSchedule n) = scheduleOutputs (scheduleState n) at h
  simp only [rightLetter, certificateState, ← h]
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    profiledRawJointTargetRightReceiverStrategy,
    rightActivation, pairedRightReceiverStrategy, pairedRightSenderStrategy,
    rightLambda, senderWord, node_length]

theorem left_full_letter_finite (env : Nat → Unit × Unit) (n : Nat) :
    pairPlay (profiledRawJointTargetLeftReceiverStrategy objective
      (leftActivation leftSchedule (by decide) leftSchedule_recurs))
      (pairedLeftSenderStrategy (leftLambda leftSchedule)) env n =
        leftLetter (certificateState n) := by
  have h := schedules_from_state n
  change (rightSchedule n, leftSchedule n) = scheduleOutputs (scheduleState n) at h
  simp only [leftLetter, certificateState, ← h]
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    profiledRawJointTargetLeftReceiverStrategy,
    leftActivation, pairedLeftReceiverStrategy, pairedLeftSenderStrategy,
    leftLambda, senderWord, node_length]

/-- Literal distributed reuse of the two schedules. The first two rounds
agree with the pulsed source; afterwards the local receipt selects the
appropriate schedule. This is not defined through the owner-kernel decoder. -/
def scheduledStrategy : StrategyPair Unit Unit Bool Bool where
  one := fun view ↦
    let rounds := StarReadback.viewRounds view
    if rounds ≤ 2 then clock view else
      if view.receiptTag = .recv then leftSchedule (rounds - 3)
      else rightSchedule (rounds - 3)
  two := fun view ↦
    let rounds := StarReadback.viewRounds view
    if rounds ≤ 2 then clock view else
      if view.receiptTag = .recv then rightSchedule (rounds - 3)
      else leftSchedule (rounds - 3)

theorem scheduledStrategy_grant (env : EnvironmentSequence Unit Unit) (n : Nat) :
    grant (execution scheduledStrategy env (n + 2)) =
      match (env (n + 2)).graph with
      | .right => rightSchedule n
      | .left => leftSchedule n
      | .both => true := by
  rw [execution_apply]
  let history := executionPrefix scheduledStrategy env (n + 2)
  have hone : StarReadback.viewRounds (viewPair history).1 = n + 2 :=
    (StarReadback.viewRounds_currentView .one history).trans
      (executionPrefix_length scheduledStrategy env (n + 2))
  have htwo : StarReadback.viewRounds (viewPair history).2 = n + 2 :=
    (StarReadback.viewRounds_currentView .two history).trans
      (executionPrefix_length scheduledStrategy env (n + 2))
  change grant (nextRound scheduledStrategy history (env (n + 2))) = _
  cases hg : (env (n + 2)).graph <;>
    simp [grant, nextRound, scheduledStrategy, nextView,
      advanceViewsWithEnvironment, hg, View.receiptTag, StarReadback.viewRounds,
      hone, htwo, show ¬n + 2 + 1 ≤ 2 by omega]

def spoilingEnvironment (n : Nat) : EnvironmentRound Unit Unit :=
  ⟨(), (), if n < 2 then .both else
    if rightSchedule (n - 2) then .left else .right⟩

theorem spoiling_prefix_is_semantic_entry :
    executionPrefix scheduledStrategy spoilingEnvironment 2 =
      rightMember.1.bothHistory := by rfl

theorem spoiling_tail_no_grant (n : Nat) :
    grant (execution scheduledStrategy spoilingEnvironment (n + 2)) = false := by
  rw [scheduledStrategy_grant]
  simp only [spoilingEnvironment, show ¬n + 2 < 2 by omega, if_false,
    Nat.add_sub_cancel]
  cases hr : rightSchedule n with
  | false => simp
  | true =>
    simpa [hr] using schedules_disjoint n

theorem scheduledStrategy_rejects :
    ¬objective.Accepts (execution scheduledStrategy spoilingEnvironment) := by
  rintro ⟨p, heven, hinf, hmin⟩
  obtain ⟨n, hn, hp⟩ := hinf 3
  obtain ⟨k, rfl⟩ : ∃ k, n = (k + 2) + 1 := by
    exact ⟨n - 3, by omega⟩
  rw [runFrom] at hp
  change objective.priority
    (grant (execution scheduledStrategy spoilingEnvironment (k + 2))) = p at hp
  rw [spoiling_tail_no_grant] at hp
  have hpone : p = 1 := hp.symm
  rcases heven with ⟨a, ha⟩
  omega

/-- Full target-profile checks do not force an independently retained
opposite receiver to agree with the closing output at a later common depth. -/
theorem retained_receiver_disagrees_at_two :
    (rightLambda rightSchedule).bothOneLeft [((), ()), ((), ())] ((), ()) =
      false ∧
    (leftLambda leftSchedule).informedRight [((), ()), ((), ())] ((), ()) =
      true := by decide

end
end PulsedSourceBlockFlexibility
end DistributedSynthesis
