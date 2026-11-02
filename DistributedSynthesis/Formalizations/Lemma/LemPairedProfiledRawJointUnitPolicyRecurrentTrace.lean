/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyLeaderFreeKernel
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyPhysicalPriority
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointPersistentReversalRecut

/-!
# The recurrent leader-free carrier follows one fixed raw-joint thread

This module removes the policy-edge part of the remaining recurrent trace
obligation.  Every literal close of a finite right or left controller stages
an opposite macro which is simultaneously

* an `AlternatingStep` of the unchanged finite policy, and
* labelled by the minimum original-DPA priority of that literal block.

Iterating these closes therefore constructs one genuine infinite alternating
thread, not a mosaic of independently accepted controller fragments.  The
last two theorems expose the only operational premise still owed by the
physical carrier: its concrete cut block must be the literal controller block
named by the close schedule.  No side, graph, cut, or leader bit is supplied
to either local controller; the schedule is proof-side indexing data.
-/

namespace DistributedSynthesis

universe u v w x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
  (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (initial.code A))
  (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)

/-! ## A staged local target is an edge of the unchanged policy -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Invert the executable right receiver's successful branch.  This theorem
is deliberately stated for an arbitrary finite control: it can be used both
for ordinary matched blocks and for receiver controls retained in the cross.
-/
theorem profiledRawJointUnitRightPolicyReceiverFor_allowed_of_staged
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy)
    (ownerControl : ((bank.right source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).State)
    (move : In₂ × In₁)
    (target : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy)
    (hstage :
      (stepProfiledRawJointUnitRightPolicyReceiverFor A strategy initial policy
        bank source ownerControl row monitorState move).2.2 = some target) :
    ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
      (initial.code A) policy source.state target.state := by
  classical
  simp only [stepProfiledRawJointUnitRightPolicyReceiverFor] at hstage
  split at hstage
  · rename_i hsafe
    have htarget := Option.some.inj hstage
    subst target
    exact hsafe.2
  · simp at hstage

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left receiver mirror of
`profiledRawJointUnitRightPolicyReceiverFor_allowed_of_staged`. -/
theorem profiledRawJointUnitLeftPolicyReceiverFor_allowed_of_staged
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy)
    (ownerControl : ((bank.left source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).State)
    (move : In₁ × In₂)
    (target : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy)
    (hstage :
      (stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy initial policy
        bank source ownerControl row monitorState move).2.2 = some target) :
    ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
      (initial.code A) policy source.state target.state := by
  classical
  simp only [stepProfiledRawJointUnitLeftPolicyReceiverFor] at hstage
  split at hstage
  · rename_i hsafe
    have htarget := Option.some.inj hstage
    subst target
    exact hsafe.2
  · simp at hstage

/-! ## One real close supplies edge and priority together -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A literal right-controller close produces exactly one next left root of
the same policy, its executable staging equation, its alternating edge, and
its physical block-minimum equation. -/
theorem exists_profiledRawJointUnitLeft_step_priority_of_realRightClose
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ∃ target : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
        policy,
      (stepProfiledRawJointUnitRightPolicyReceiverFor A strategy initial policy
        bank source
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past).1 row
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past).2 move).2.2 = some target ∧
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep A policy
        (.inl source) (.inr target) ∧
      profiledRawJointThreadRootPriority A (.inr target.slot) =
        A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.slot.1.1)
            (profiledRawJointUnitRightPhysicalPrefixRecords A row
              (omegaPrefix
                (profiledRawJointUnitRightPolicyPlay A strategy initial policy
                  bank source past move)
                past.length))) := by
  obtain ⟨target, hstage, hpriority⟩ :=
    profiledRawJointUnitRightPolicy_real_close_priority_eq_blockMin A strategy
      initial policy bank source row past move
  have hallowed :=
    profiledRawJointUnitRightPolicyReceiverFor_allowed_of_staged A strategy
      initial policy bank source
        (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
          policy bank source past).1 row
        (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
          policy bank source past).2 move target hstage
  exact ⟨target, hstage,
    .rightToLeft source target hallowed, hpriority⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-to-right mirror of the combined real-close theorem. -/
theorem exists_profiledRawJointUnitRight_step_priority_of_realLeftClose
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ∃ target : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
        policy,
      (stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy initial policy
        bank source
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past).1 row
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past).2 move).2.2 = some target ∧
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep A policy
        (.inr source) (.inl target) ∧
      profiledRawJointThreadRootPriority A (.inl target.slot) =
        A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.slot.1.1)
            (profiledRawJointUnitLeftPhysicalPrefixRecords A row
              (omegaPrefix
                (profiledRawJointUnitLeftPolicyPlay A strategy initial policy
                  bank source past move)
                past.length))) := by
  obtain ⟨target, hstage, hpriority⟩ :=
    profiledRawJointUnitLeftPolicy_real_close_priority_eq_blockMin A strategy
      initial policy bank source row past move
  have hallowed :=
    profiledRawJointUnitLeftPolicyReceiverFor_allowed_of_staged A strategy
      initial policy bank source
        (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
          policy bank source past).1 row
        (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
          policy bank source past).2 move target hstage
  exact ⟨target, hstage,
    .leftToRight source target hallowed, hpriority⟩

/-! ## Canonical closed receiver controls of the physical carrier -/

/-- The exact left macro stored by a right-controller close. -/
noncomputable def profiledRawJointUnitRightPolicyCloseTarget
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A) policy :=
  Classical.choose
    (exists_profiledRawJointUnitLeft_step_priority_of_realRightClose A
      strategy initial policy bank source row past move)

/-- Mirror right macro stored by a left-controller close. -/
noncomputable def profiledRawJointUnitLeftPolicyCloseTarget
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A) policy :=
  Classical.choose
    (exists_profiledRawJointUnitRight_step_priority_of_realLeftClose A
      strategy initial policy bank source row past move)

/-- Canonical matched-right owner control at a finite physical prefix. -/
noncomputable def profiledRawJointUnitRightPolicyOwnerAt
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (past : List (In₂ × In₁)) :
    ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial policy bank :=
  ⟨source,
    (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial policy
      bank source past).1⟩

/-- Canonical matched-right receiver before its next physical round.  The
pending target does not affect an interior continuation, so it remains an
explicit argument. -/
noncomputable def profiledRawJointUnitRightPolicyReceiverAt
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁))
    (pending : Option (ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)) :
    ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial policy :=
  ⟨source, row,
    (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial policy
      bank source past).2, pending⟩

/-- Receiver control immediately after the literal right close. -/
noncomputable def profiledRawJointUnitRightPolicyClosedReceiver
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial policy :=
  let result := stepProfiledRawJointUnitRightPolicyReceiverFor A strategy
    initial policy bank source
      (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
        policy bank source past).1 row
      (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
        policy bank source past).2 move
  ⟨source, row, result.2.1, result.2.2⟩

/-- Left-oriented canonical owner. -/
noncomputable def profiledRawJointUnitLeftPolicyOwnerAt
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (past : List (In₁ × In₂)) :
    ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial policy bank :=
  ⟨source,
    (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial policy
      bank source past).1⟩

/-- Left-oriented canonical receiver before its next physical round. -/
noncomputable def profiledRawJointUnitLeftPolicyReceiverAt
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂))
    (pending : Option (ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)) :
    ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial policy :=
  ⟨source, row,
    (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial policy
      bank source past).2, pending⟩

/-- Receiver control immediately after the literal left close. -/
noncomputable def profiledRawJointUnitLeftPolicyClosedReceiver
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial policy :=
  let result := stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy
    initial policy bank source
      (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
        policy bank source past).1 row
      (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
        policy bank source past).2 move
  ⟨source, row, result.2.1, result.2.2⟩

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The actual matched-right continuation produces exactly the canonical
closed receiver; the previous pending target is overwritten, not accumulated.
-/
theorem continueProfiledRawJointUnitRightPolicyReceiverAt_eq_closed
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁))
    (pending : Option (ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)) (move : In₂ × In₁) :
    (continueProfiledRawJointUnitRightPolicyReceiver A strategy initial policy
      bank
        (profiledRawJointUnitRightPolicyReceiverAt A strategy initial policy
          bank source row past pending)
        (profiledRawJointUnitRightPolicyOwnerAt A strategy initial policy bank
          source past) move).2 =
      profiledRawJointUnitRightPolicyClosedReceiver A strategy initial policy
        bank source row past move := by
  simp [continueProfiledRawJointUnitRightPolicyReceiver,
    profiledRawJointUnitRightPolicyReceiverAt,
    profiledRawJointUnitRightPolicyOwnerAt,
    profiledRawJointUnitRightPolicyClosedReceiver,
    profiledRawJointUnitRightPolicyOwnerControlFor]

/-- Matched-left mirror: each close replaces the pending target. -/
theorem continueProfiledRawJointUnitLeftPolicyReceiverAt_eq_closed
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂))
    (pending : Option (ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)) (move : In₁ × In₂) :
    (continueProfiledRawJointUnitLeftPolicyReceiver A strategy initial policy
      bank
        (profiledRawJointUnitLeftPolicyReceiverAt A strategy initial policy
          bank source row past pending)
        (profiledRawJointUnitLeftPolicyOwnerAt A strategy initial policy bank
          source past) move).2 =
      profiledRawJointUnitLeftPolicyClosedReceiver A strategy initial policy
        bank source row past move := by
  simp [continueProfiledRawJointUnitLeftPolicyReceiver,
    profiledRawJointUnitLeftPolicyReceiverAt,
    profiledRawJointUnitLeftPolicyOwnerAt,
    profiledRawJointUnitLeftPolicyClosedReceiver,
    profiledRawJointUnitLeftPolicyOwnerControlFor]

/-- The actual right owner advances to the canonical next-prefix control. -/
theorem stepProfiledRawJointUnitRightPolicyOwnerAt_eq_append
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    (stepProfiledRawJointUnitRightPolicyOwner A strategy initial policy bank
      (profiledRawJointUnitRightPolicyOwnerAt A strategy initial policy bank
        source past) move.2).2 =
      profiledRawJointUnitRightPolicyOwnerAt A strategy initial policy bank
        source (past ++ [move]) := by
  simp [profiledRawJointUnitRightPolicyOwnerAt,
    stepProfiledRawJointUnitRightPolicyOwner,
    profiledRawJointUnitRightPolicyFiniteStateAfter, List.foldl_append,
    stepProfiledRawJointUnitRightPolicyFiniteState, narrowedRecord]

/-- Left owner mirror. -/
theorem stepProfiledRawJointUnitLeftPolicyOwnerAt_eq_append
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    (stepProfiledRawJointUnitLeftPolicyOwner A strategy initial policy bank
      (profiledRawJointUnitLeftPolicyOwnerAt A strategy initial policy bank
        source past) move.2).2 =
      profiledRawJointUnitLeftPolicyOwnerAt A strategy initial policy bank
        source (past ++ [move]) := by
  simp [profiledRawJointUnitLeftPolicyOwnerAt,
    stepProfiledRawJointUnitLeftPolicyOwner,
    profiledRawJointUnitLeftPolicyFiniteStateAfter, List.foldl_append,
    stepProfiledRawJointUnitLeftPolicyFiniteState, narrowedRecord]

/-- A canonical closed right receiver stores exactly the selected left macro,
not merely an equivalent policy state. -/
theorem profiledRawJointUnitRightPolicyClosedReceiver_pending
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    (profiledRawJointUnitRightPolicyClosedReceiver A strategy initial policy
      bank source row past move).2.2.2 =
        some (profiledRawJointUnitRightPolicyCloseTarget A strategy initial
          policy bank source row past move) := by
  exact (Classical.choose_spec
    (exists_profiledRawJointUnitLeft_step_priority_of_realRightClose A
      strategy initial policy bank source row past move)).1

/-- Closed left receiver mirror. -/
theorem profiledRawJointUnitLeftPolicyClosedReceiver_pending
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    (profiledRawJointUnitLeftPolicyClosedReceiver A strategy initial policy
      bank source row past move).2.2.2 =
        some (profiledRawJointUnitLeftPolicyCloseTarget A strategy initial
          policy bank source row past move) := by
  exact (Classical.choose_spec
    (exists_profiledRawJointUnitRight_step_priority_of_realLeftClose A
      strategy initial policy bank source row past move)).1

/-- After a right close, both finite coordinates are exactly those of the
extended physical prefix and the pending coordinate is the exact target. -/
theorem profiledRawJointUnitRightPolicyClosedReceiver_eq_receiverAt_append
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    profiledRawJointUnitRightPolicyClosedReceiver A strategy initial policy
        bank source row past move =
      profiledRawJointUnitRightPolicyReceiverAt A strategy initial policy bank
        source row (past ++ [move])
          (some (profiledRawJointUnitRightPolicyCloseTarget A strategy initial
            policy bank source row past move)) := by
  have hstage :=
    profiledRawJointUnitRightPolicyClosedReceiver_pending A strategy initial
      policy bank source row past move
  unfold profiledRawJointUnitRightPolicyClosedReceiver at hstage ⊢
  unfold profiledRawJointUnitRightPolicyReceiverAt
  dsimp only at hstage ⊢
  rw [hstage]
  congr 1
  simp [profiledRawJointUnitRightPolicyFiniteStateAfter, List.foldl_append,
    stepProfiledRawJointUnitRightPolicyFiniteState,
    stepProfiledRawJointUnitRightPolicyReceiverFor_monitor]

/-- Left closed receiver mirror. -/
theorem profiledRawJointUnitLeftPolicyClosedReceiver_eq_receiverAt_append
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    profiledRawJointUnitLeftPolicyClosedReceiver A strategy initial policy bank
        source row past move =
      profiledRawJointUnitLeftPolicyReceiverAt A strategy initial policy bank
        source row (past ++ [move])
          (some (profiledRawJointUnitLeftPolicyCloseTarget A strategy initial
            policy bank source row past move)) := by
  have hstage :=
    profiledRawJointUnitLeftPolicyClosedReceiver_pending A strategy initial
      policy bank source row past move
  unfold profiledRawJointUnitLeftPolicyClosedReceiver at hstage ⊢
  unfold profiledRawJointUnitLeftPolicyReceiverAt
  dsimp only at hstage ⊢
  rw [hstage]
  congr 1
  simp [profiledRawJointUnitLeftPolicyFiniteStateAfter, List.foldl_append,
    stepProfiledRawJointUnitLeftPolicyFiniteState,
    stepProfiledRawJointUnitLeftPolicyReceiverFor_monitor]

/-- A strict-left selection, or process one's half of a simultaneous cross
refresh, starts from the exact staged left target. -/
theorem profiledRawJointUnitPolicyStartLeftReceiver_closed_source
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (nextMove : In₁ × In₂) :
    (profiledRawJointUnitPolicyStartLeftReceiver A strategy initial policy bank
      (profiledRawJointUnitRightPolicyClosedReceiver A strategy initial policy
        bank source row past move) nextMove).2.1 =
      profiledRawJointUnitRightPolicyCloseTarget A strategy initial policy bank
        source row past move := by
  simp [profiledRawJointUnitPolicyStartLeftReceiver,
    profiledRawJointUnitPolicyRightReceiverTarget,
    profiledRawJointUnitRightPolicyClosedReceiver_pending,
    profiledRawJointUnitRestartLeft,
    initialProfiledRawJointUnitLeftPolicyReceiver,
    continueProfiledRawJointUnitLeftPolicyReceiver_source]

/-- Process two's honest non-receipt selects the same exact target. -/
theorem profiledRawJointUnitPolicyStartLeftOwner_closed_source
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (input : In₂) :
    (profiledRawJointUnitPolicyStartLeftOwner A strategy initial policy bank
      (profiledRawJointUnitRightPolicyClosedReceiver A strategy initial policy
        bank source row past move) input).2.1 =
      profiledRawJointUnitRightPolicyCloseTarget A strategy initial policy bank
        source row past move := by
  simp [profiledRawJointUnitPolicyStartLeftOwner,
    profiledRawJointUnitPolicyRightReceiverTarget,
    profiledRawJointUnitRightPolicyClosedReceiver_pending,
    profiledRawJointUnitRestartLeft,
    initialProfiledRawJointUnitLeftPolicyOwner,
    stepProfiledRawJointUnitLeftPolicyOwner_source]

/-- Right-selection mirror from a canonical closed left receiver. -/
theorem profiledRawJointUnitPolicyStartRightReceiver_closed_source
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (nextMove : In₂ × In₁) :
    (profiledRawJointUnitPolicyStartRightReceiver A strategy initial policy
      bank
        (profiledRawJointUnitLeftPolicyClosedReceiver A strategy initial policy
          bank source row past move) nextMove).2.1 =
      profiledRawJointUnitLeftPolicyCloseTarget A strategy initial policy bank
        source row past move := by
  simp [profiledRawJointUnitPolicyStartRightReceiver,
    profiledRawJointUnitPolicyLeftReceiverTarget,
    profiledRawJointUnitLeftPolicyClosedReceiver_pending,
    profiledRawJointUnitRestartRight,
    initialProfiledRawJointUnitRightPolicyReceiver,
    continueProfiledRawJointUnitRightPolicyReceiver_source]

/-- Process one's strict-right non-receipt selects that same target. -/
theorem profiledRawJointUnitPolicyStartRightOwner_closed_source
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (input : In₁) :
    (profiledRawJointUnitPolicyStartRightOwner A strategy initial policy bank
      (profiledRawJointUnitLeftPolicyClosedReceiver A strategy initial policy
        bank source row past move) input).2.1 =
      profiledRawJointUnitLeftPolicyCloseTarget A strategy initial policy bank
        source row past move := by
  simp [profiledRawJointUnitPolicyStartRightOwner,
    profiledRawJointUnitPolicyLeftReceiverTarget,
    profiledRawJointUnitLeftPolicyClosedReceiver_pending,
    profiledRawJointUnitRestartRight,
    initialProfiledRawJointUnitRightPolicyOwner,
    stepProfiledRawJointUnitRightPolicyOwner_source]

end

/-! ## Literal strict-round trace identification -/

/-- The physical record emitted by the actual matched-right carrier maps at
one canonical prefix.  This definition uses exactly the local owner and
receiver functions installed in the leader-free kernel. -/
noncomputable def profiledRawJointUnitRightPolicyCarrierRecordAt
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁))
    (pending : Option (ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)) (move : In₂ × In₁) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  let owner := profiledRawJointUnitRightPolicyOwnerAt A strategy initial policy
    bank source past
  let receiver := profiledRawJointUnitRightPolicyReceiverAt A strategy initial
    policy bank source row past pending
  let one := stepProfiledRawJointUnitRightPolicyOwner A strategy initial policy
    bank owner move.2
  let two := continueProfiledRawJointUnitRightPolicyReceiver A strategy initial
    policy bank receiver owner move
  rightRoundRecord move one.1 two.1

/-- Left-oriented actual carrier record. -/
noncomputable def profiledRawJointUnitLeftPolicyCarrierRecordAt
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂))
    (pending : Option (ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)) (move : In₁ × In₂) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  let receiver := profiledRawJointUnitLeftPolicyReceiverAt A strategy initial
    policy bank source row past pending
  let owner := profiledRawJointUnitLeftPolicyOwnerAt A strategy initial policy
    bank source past
  let one := continueProfiledRawJointUnitLeftPolicyReceiver A strategy initial
    policy bank receiver owner move
  let two := stepProfiledRawJointUnitLeftPolicyOwner A strategy initial policy
    bank owner move.2
  leftRoundRecord move one.1 two.1

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The matched-right carrier round is literally the certificate record read
by the physical-priority theorem.  In particular, no strategy replay or
post-hoc rationalization is used in the slice. -/
theorem profiledRawJointUnitRightPolicyCarrierRecordAt_eq_playRecord
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁))
    (pending : Option (ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)) (move : In₂ × In₁) :
    profiledRawJointUnitRightPolicyCarrierRecordAt A strategy initial policy
        bank source row past pending move =
      pairedRightRecordForRow row
        (profiledRawJointUnitRightPhysicalLetter A
          (profiledRawJointUnitRightPolicyPlay A strategy initial policy bank
            source past move past.length)) := by
  have hat := profiledRawJointUnitRightPolicy_treePlay_at_prefix A strategy
    initial policy bank source past move
  change profiledRawJointUnitRightPolicyPlay A strategy initial policy bank
    source past move past.length = _ at hat
  rw [hat]
  cases row <;>
    simp [profiledRawJointUnitRightPolicyCarrierRecordAt,
      profiledRawJointUnitRightPolicyOwnerAt,
      profiledRawJointUnitRightPolicyReceiverAt,
      profiledRawJointUnitRightPolicyFiniteStateAfter_eq,
      stepProfiledRawJointUnitRightPolicyOwner,
      continueProfiledRawJointUnitRightPolicyReceiver,
      profiledRawJointUnitRightPolicyOwnerControlFor,
      profiledRawJointUnitRightPhysicalLetter, indexedTargetPhysicalLetter,
      narrowedRecord, pairedRightRecordForRow, pairedRightInformedForRow]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Matched-left mirror of the literal one-round identification. -/
theorem profiledRawJointUnitLeftPolicyCarrierRecordAt_eq_playRecord
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂))
    (pending : Option (ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)) (move : In₁ × In₂) :
    profiledRawJointUnitLeftPolicyCarrierRecordAt A strategy initial policy bank
        source row past pending move =
      pairedLeftRecordForRow row
        (profiledRawJointUnitLeftPhysicalLetter A
          (profiledRawJointUnitLeftPolicyPlay A strategy initial policy bank
            source past move past.length)) := by
  have hat := profiledRawJointUnitLeftPolicy_treePlay_at_prefix A strategy
    initial policy bank source past move
  change profiledRawJointUnitLeftPolicyPlay A strategy initial policy bank
    source past move past.length = _ at hat
  rw [hat]
  cases row <;>
    simp [profiledRawJointUnitLeftPolicyCarrierRecordAt,
      profiledRawJointUnitLeftPolicyOwnerAt,
      profiledRawJointUnitLeftPolicyReceiverAt,
      profiledRawJointUnitLeftPolicyFiniteStateAfter_eq,
      stepProfiledRawJointUnitLeftPolicyOwner,
      continueProfiledRawJointUnitLeftPolicyReceiver,
      profiledRawJointUnitLeftPolicyOwnerControlFor,
      profiledRawJointUnitLeftPhysicalLetter, indexedTargetPhysicalLetter,
      narrowedRecord, pairedLeftRecordForRow, pairedLeftInformedForRow]

/-! ## Iterating literal closes -/

/-- Proof-side data identifying one literal close at the current actual
macro.  Its type forces the input order to agree with the macro orientation.
-/
inductive ProfiledRawJointUnitPolicyCloseQuery :
    ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A) policy →
      Type (max u v x y s) where
  | right
      (source : ProfiledRawJointUnitRightPolicyMacro A strategy
        (initial.code A) policy)
      (row : PairedEntryRow) (past : List (In₂ × In₁))
      (move : In₂ × In₁) :
      ProfiledRawJointUnitPolicyCloseQuery (.inl source)
  | left
      (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
        (initial.code A) policy)
      (row : PairedEntryRow) (past : List (In₁ × In₂))
      (move : In₁ × In₂) :
      ProfiledRawJointUnitPolicyCloseQuery (.inr source)

/-- The literal original-DPA block minimum named by one close query. -/
def ProfiledRawJointUnitPolicyCloseQuery.blockPriority
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) : Nat :=
  match query with
  | .right source row past move =>
      A.priority
        (blockMinState A
          (pairedCodeStateForRow A row source.slot.1.1)
          (profiledRawJointUnitRightPhysicalPrefixRecords A row
            (omegaPrefix
              (profiledRawJointUnitRightPolicyPlay A strategy initial policy
                bank source past move)
              past.length)))
  | .left source row past move =>
      A.priority
        (blockMinState A
          (pairedCodeStateForRow A row source.slot.1.1)
          (profiledRawJointUnitLeftPhysicalPrefixRecords A row
            (omegaPrefix
              (profiledRawJointUnitLeftPolicyPlay A strategy initial policy
                bank source past move)
              past.length)))

/-- Original-DPA state carried at the entry of the queried literal block. -/
def ProfiledRawJointUnitPolicyCloseQuery.entryState
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) : A.State :=
  match query with
  | .right source row _ _ =>
      pairedCodeStateForRow A row source.slot.1.1
  | .left source row _ _ =>
      pairedCodeStateForRow A row source.slot.1.1

/-- Literal finite strict-block record list named by a close query.  The
closing round itself installs the following entry and is therefore excluded,
exactly as in `cutBlockMin`. -/
def ProfiledRawJointUnitPolicyCloseQuery.records
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) : List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  match query with
  | .right source row past move =>
      profiledRawJointUnitRightPhysicalPrefixRecords A row
        (omegaPrefix
          (profiledRawJointUnitRightPolicyPlay A strategy initial policy bank
            source past move)
          past.length)
  | .left source row past move =>
      profiledRawJointUnitLeftPhysicalPrefixRecords A row
        (omegaPrefix
          (profiledRawJointUnitLeftPolicyPlay A strategy initial policy bank
            source past move)
          past.length)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem ProfiledRawJointUnitPolicyCloseQuery.blockPriority_eq
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) :
    query.blockPriority A strategy initial policy bank =
      A.priority
        (blockMinState A
          (query.entryState A strategy initial policy)
          (query.records A strategy initial policy bank)) := by
  cases query <;> rfl

/-- Exact trace-index information owed by the operational carrier at one
physical cut.  This is intentionally only state, length, and literal slice
alignment; no parity or policy coherence is assumed. -/
structure ProfiledRawJointUnitPolicyCloseQuery.PhysicalSlice
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) (cuts : Nat → Nat) (k : Nat) : Prop where
  entryState_eq : A.run word (start + cuts k) =
    query.entryState A strategy initial policy
  records_length :
    (query.records A strategy initial policy bank).length =
      cuts (k + 1) - cuts k - 1
  records_eq_slice :
    omegaPrefix (OmegaWord.drop word (start + cuts k))
        (query.records A strategy initial policy bank).length =
      query.records A strategy initial policy bank

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The exact cut-to-close bridge.  Once the carrier has identified its
entry state and literal finite slice, the `hphysical` equality required by
the scheduled epoch coupling follows with no further controller or parity
argument. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.cutBlockMin_eq_blockPriority
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) (cuts : Nat → Nat) (k : Nat)
    (slice : query.PhysicalSlice A strategy initial policy bank word start cuts
      k) :
    cutBlockMin (fun n ↦ A.priority (A.run word (start + n))) cuts k =
      query.blockPriority A strategy initial policy bank := by
  rw [query.blockPriority_eq A strategy initial policy bank]
  exact cutBlockMin_eq_priority_blockMinState_of_slice_alignment A word start
    cuts k (query.entryState A strategy initial policy)
      (query.records A strategy initial policy bank) slice.entryState_eq
        slice.records_length slice.records_eq_slice

/-- Choose the exact staged target of a literal close. -/
noncomputable def ProfiledRawJointUnitPolicyCloseQuery.target
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) :
    ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A) policy :=
  match query with
  | .right source row past move =>
      .inr (Classical.choose
        (exists_profiledRawJointUnitLeft_step_priority_of_realRightClose
          A strategy initial policy bank source row past move))
  | .left source row past move =>
      .inl (Classical.choose
        (exists_profiledRawJointUnitRight_step_priority_of_realLeftClose
          A strategy initial policy bank source row past move))

/-- Exact executable meaning of a query target.  The mismatched-orientation
cases are false, so a consumer cannot silently cast a right close into a
right target or a left close into a left target. -/
def ProfiledRawJointUnitPolicyCloseQuery.Stages
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (target : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) : Prop :=
  match query, target with
  | .right source row past move, .inr next =>
      (stepProfiledRawJointUnitRightPolicyReceiverFor A strategy initial policy
        bank source
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past).1 row
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past).2 move).2.2 = some next
  | .left source row past move, .inl next =>
      (stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy initial policy
        bank source
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past).1 row
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past).2 move).2.2 = some next
  | _, _ => False

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The chosen query target is literally the macro stored by the executable
receiver step. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.stages_target
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) :
    query.Stages A strategy initial policy bank
      (query.target A strategy initial policy bank) := by
  cases query with
  | right source row past move =>
      exact (Classical.choose_spec
        (exists_profiledRawJointUnitLeft_step_priority_of_realRightClose
          A strategy initial policy bank source row past move)).1
  | left source row past move =>
      exact (Classical.choose_spec
        (exists_profiledRawJointUnitRight_step_priority_of_realLeftClose
          A strategy initial policy bank source row past move)).1

/-- The selected target is an exact alternating edge. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.alternatingStep
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep A policy root
      (query.target A strategy initial policy bank) := by
  cases query with
  | right source row past move =>
      exact (Classical.choose_spec
        (exists_profiledRawJointUnitLeft_step_priority_of_realRightClose
          A strategy initial policy bank source row past move)).2.1
  | left source row past move =>
      exact (Classical.choose_spec
        (exists_profiledRawJointUnitRight_step_priority_of_realLeftClose
          A strategy initial policy bank source row past move)).2.1

/-- The selected target's live-slot priority is the literal block minimum. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.targetPriority
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) :
    profiledRawJointThreadRootPriority A
        (ProfiledRawJointUnitFixedPolicyRoot.threadRoot A policy
          (query.target A strategy initial policy bank)) =
      query.blockPriority A strategy initial policy bank := by
  cases query with
  | right source row past move =>
      exact (Classical.choose_spec
        (exists_profiledRawJointUnitLeft_step_priority_of_realRightClose
          A strategy initial policy bank source row past move)).2.2
  | left source row past move =>
      exact (Classical.choose_spec
        (exists_profiledRawJointUnitRight_step_priority_of_realLeftClose
          A strategy initial policy bank source row past move)).2.2

end

/-- An arbitrary proof-side close schedule.  It observes the actual root only
to select the correctly typed row, finite history, and closing move; it is not
runtime data of either process. -/
abbrev ProfiledRawJointUnitPolicyCloseSchedule :=
  (n : Nat) →
    (root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) →
      ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy root

/-- Roots obtained by repeatedly taking the exact staged target. -/
noncomputable def profiledRawJointUnitPolicyScheduledRoot
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) : Nat →
      ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A) policy
  | 0 => seed
  | n + 1 =>
      (schedule n
        (profiledRawJointUnitPolicyScheduledRoot seed schedule n)).target
          A strategy initial policy bank

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointUnitPolicyScheduledRoot_zero
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) :
    profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank seed
      schedule 0 = seed :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointUnitPolicyScheduledRoot_succ
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) (n : Nat) :
    profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank seed
        schedule (n + 1) =
      (schedule n
        (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          seed schedule n)).target A strategy initial policy bank :=
  rfl

/-- Literal closes assemble into one infinite alternating thread of the
unchanged policy. -/
noncomputable def profiledRawJointUnitPolicyScheduledAlternatingThread
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run []) :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingThread A policy where
  root := profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
    bank seed schedule
  initial := hseed
  step n := by
    rw [profiledRawJointUnitPolicyScheduledRoot_succ]
    exact (schedule n
      (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule n)).alternatingStep A strategy initial policy bank

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Pointwise target-priority law of the scheduled actual-macro thread. -/
theorem profiledRawJointUnitPolicyScheduledAlternatingThread_targetPriority
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run []) (n : Nat) :
    profiledRawJointThreadRootPriority A
        (ProfiledRawJointUnitFixedPolicyRoot.threadRoot A policy
          ((profiledRawJointUnitPolicyScheduledAlternatingThread A strategy
            initial policy bank seed schedule hseed).root (n + 1))) =
      (schedule n
        (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          seed schedule n)).blockPriority A strategy initial policy bank := by
  change
    profiledRawJointThreadRootPriority A
        (ProfiledRawJointUnitFixedPolicyRoot.threadRoot A policy
          (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
            bank seed schedule (n + 1))) = _
  rw [profiledRawJointUnitPolicyScheduledRoot_succ]
  exact (schedule n
    (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
      seed schedule n)).targetPriority A strategy initial policy bank

/-! ## The exact actual-trace residual -/

/-- All cut-index information needed from an actual global-machine trace.
The policy thread, staged-target adjacency, and parity proof are absent from
this structure because they have already been derived above. -/
structure ProfiledRawJointUnitPolicyScheduledPhysicalSlices
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (start : Nat) (cuts : Nat → Nat) : Prop where
  sliceAt : ∀ k : Nat,
    (schedule k
      (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k)).PhysicalSlice A strategy initial policy bank
          (G.globalMachineTraceWord outputOne outputTwo env) start cuts k

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The scheduled physical-slice invariant discharges the complete
`hphysical` family pointwise. -/
theorem ProfiledRawJointUnitPolicyScheduledPhysicalSlices.blockMin_eq
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy}
    {start : Nat} {cuts : Nat → Nat}
    (slices : ProfiledRawJointUnitPolicyScheduledPhysicalSlices A strategy
      initial policy bank G outputOne outputTwo env seed schedule start cuts)
    (k : Nat) :
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts k =
      (schedule k
        (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          seed schedule k)).blockPriority A strategy initial policy bank :=
  (schedule k
    (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank seed
      schedule k)).cutBlockMin_eq_blockPriority A strategy initial policy bank
        (G.globalMachineTraceWord outputOne outputTwo env) start cuts k
          (slices.sliceAt k)

/-! ## Direct recurrent and persistent acceptance joins -/

/-- The reusable exact endpoint of the scheduled-close construction.  It
returns the `FiniteGlobalMachineEpochCoupling` consumed by the physical
four-regime package, rather than only its acceptance consequence. -/
noncomputable def profiledRawJointUnitPolicyScheduledTraceEpochCoupling
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run [])
    (start : Nat) (cuts : Nat → Nat) (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (hphysical : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (start + n)))
          cuts k =
        (schedule k
          (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
            bank seed schedule k)).blockPriority A strategy initial policy
              bank) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env := by
  let thread := profiledRawJointUnitPolicyScheduledAlternatingThread A strategy
    initial policy bank seed schedule hseed
  let coupling := thread.toPolicyEpochCouplingOfThreadRootPriority A policy G
    outputOne outputTwo env 0 start cuts cuts_strictMono cuts_zero (fun k ↦ by
      have htarget :=
        profiledRawJointUnitPolicyScheduledAlternatingThread_targetPriority
          A strategy initial policy bank seed schedule hseed k
      simpa [thread] using (hphysical k).trans htarget.symm)
  exact coupling.toFiniteGlobalMachineEpochCoupling A

/-- Slice-indexed form of the generic endpoint.  This is the constructor used
by an operational carrier invariant: supplying `PhysicalSlice` at every cut
returns the exact recurrent package with no separately stated block-min law.
-/
noncomputable def profiledRawJointUnitPolicyScheduledSlicesEpochCoupling
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run [])
    (start : Nat) (cuts : Nat → Nat) (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (slices : ProfiledRawJointUnitPolicyScheduledPhysicalSlices A strategy
      initial policy bank G outputOne outputTwo env seed schedule start cuts) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env :=
  profiledRawJointUnitPolicyScheduledTraceEpochCoupling A strategy initial
    policy bank G outputOne outputTwo env seed schedule hseed start cuts
      cuts_strictMono cuts_zero slices.blockMin_eq

/-- Automatic recurrent cuts instantiate the exact generic coupling above.
The fixed policy is assumed to have been selected already; the heterogeneous
initial all-`both` seam is intentionally outside this statement. -/
noncomputable def profiledRawJointUnitPolicyScheduledTraceRecurrentCoupling
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph))
    (lower : Nat)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run [])
    (hphysical : ∀ k : Nat,
      let extraction :=
        recurrentEnvironmentEpochCutExtractionAfter env hboth lower
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (extraction.start + n)))
          extraction.cuts k =
        (schedule k
          (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
            bank seed schedule k)).blockPriority A strategy initial policy
              bank) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env :=
  let extraction :=
    recurrentEnvironmentEpochCutExtractionAfter env hboth lower
  profiledRawJointUnitPolicyScheduledTraceEpochCoupling A strategy initial
    policy bank G outputOne outputTwo env seed schedule hseed extraction.start
      extraction.cuts extraction.cuts_strictMono extraction.cuts_zero hphysical

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The persistent-reversal coupling yields precisely the physical tail
parity field consumed by `FiniteGlobalMachinePhysicalAcceptance`. -/
theorem profiledRawJointUnitPolicyScheduledTrace_persistentTailParity
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hpersistent : PersistentStrictReversalTail (fun n ↦ (env n).graph))
    (lower : Nat)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run [])
    (hphysical : ∀ k : Nat,
      let extraction :=
        persistentStrictReversalEpochCutExtractionAfter env hpersistent lower
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (extraction.start + n)))
          extraction.cuts k =
        (schedule k
          (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
            bank seed schedule k)).blockPriority A strategy initial policy
              bank) :
    ∃ start : Nat, NatSeqMinEvenParity
      (fun n ↦ A.priority
        (A.run (G.globalMachineTraceWord outputOne outputTwo env)
          (start + n))) := by
  let extraction :=
    persistentStrictReversalEpochCutExtractionAfter env hpersistent lower
  let coupling :=
    profiledRawJointUnitPolicyScheduledTraceEpochCoupling A strategy initial
      policy bank G outputOne outputTwo env seed schedule hseed extraction.start
        extraction.cuts extraction.cuts_strictMono extraction.cuts_zero
        hphysical
  let priorities : Nat → Nat := fun n ↦ A.priority
    (A.run (G.globalMachineTraceWord outputOne outputTwo env)
      (coupling.start + n))
  have hblocks : NatSeqMinEvenParity
      (cutBlockMin priorities coupling.cuts) := by
    convert coupling.epochParity using 1
    funext k
    exact coupling.blockMin_eq_epochPriority k
  exact ⟨coupling.start,
    (natSeqMinEvenParity_cutBlockMin priorities coupling.cuts_strictMono
      coupling.cuts_zero).mp hblocks⟩

/-- Once the actual leader-free trace identifies each automatic recurrent
cut with the literal close selected above, all policy coherence and parity
obligations are already discharged. -/
theorem profiledRawJointUnitPolicyScheduledTrace_accepts_of_recurrent
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph))
    (lower : Nat)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run [])
    (hphysical : ∀ k : Nat,
      let extraction :=
        recurrentEnvironmentEpochCutExtractionAfter env hboth lower
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (extraction.start + n)))
          extraction.cuts k =
        (schedule k
          (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
            bank seed schedule k)).blockPriority A strategy initial policy
              bank) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  exact A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling G outputOne
    outputTwo env
      (profiledRawJointUnitPolicyScheduledTraceRecurrentCoupling A strategy
        initial policy bank G outputOne outputTwo env hboth lower seed schedule
        hseed hphysical)

/-- Persistent strict reversals use the same scheduled thread and the same
single physical block identification; checker state is not restarted. -/
theorem profiledRawJointUnitPolicyScheduledTrace_accepts_of_persistentReversal
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hpersistent : PersistentStrictReversalTail (fun n ↦ (env n).graph))
    (lower : Nat)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run [])
    (hphysical : ∀ k : Nat,
      let extraction :=
        persistentStrictReversalEpochCutExtractionAfter env hpersistent lower
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (extraction.start + n)))
          extraction.cuts k =
        (schedule k
          (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
            bank seed schedule k)).blockPriority A strategy initial policy
              bank) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  rcases
      profiledRawJointUnitPolicyScheduledTrace_persistentTailParity A strategy
        initial policy bank G outputOne outputTwo env hpersistent lower seed
        schedule hseed hphysical with
    ⟨start, htail⟩
  exact A.finiteGlobalMachineTraceWord_accepts_of_tailParity G outputOne
    outputTwo env start htail

end

end

end DetParityAutomaton

end DistributedSynthesis
