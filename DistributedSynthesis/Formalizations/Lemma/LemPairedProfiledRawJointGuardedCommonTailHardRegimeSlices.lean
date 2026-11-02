/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailExecutionShapeSplit
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPolicyRecurrentTrace

/-!
# The kernel-independent automatic-cut seam for the two hard regimes

A checked common-tail close already contains a root of one fixed rational
one-sided policy.  The generic recurrent trace development turns any
proof-side schedule of literal closes of that policy into an accepting
alternating thread.  Thus the switching carrier does not owe a new parity or
policy-coherence argument.  At every automatic cut it owes only the existing
`PhysicalSlice` predicate:

* the actual DPA state is the scheduled block's entry state;
* the cut distance has the scheduled literal block length; and
* the actual emitted word slice is that literal block.

This file packages precisely that seam for recurrent `.both` and persistent
strict reversal.  Importantly, it is parameterized by an arbitrary finite
global round machine and its two output maps.  It therefore applies unchanged
to the eventual charged switching kernel; it does not specialize the result
back to the older common-tail core kernel whose mixed branches use a fallback.

All cuts, schedules, roots, and graph regimes are proof-side objects.  No
local transition receives a graph, orientation, side, or leader signal.
-/

namespace DistributedSynthesis

universe u v x y s w

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
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonControl :=
  ProfiledRawJointGuardedInitialCommonControl A strategy hwin

/-! ## A fixed-policy root already stored in a staged close -/

/-- The precise one-sided policy payload needed by the generic scheduled
trace theorem.  This is finite proof-relevant provenance, not a runtime side
test. -/
structure ProfiledRawJointGuardedCommonTailPolicyAnchor where
  initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)
  policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (initial.code A)
  bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy
  seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
    policy
  seed_state : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
    policy.run []

/-- A checked strict-right close already carries the initial left root of
its selected fixed recurrent policy. -/
noncomputable def profiledRawJointGuardedCommonTailPolicyAnchorOfRightClose
    (close : ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin) :
    ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy := by
  let key :=
    profiledRawJointGuardedCommonTargetOfRight A strategy hwin close.handoff
  let package :
      ProfiledRawJointGuardedCommonRightHandoffRootPackage A strategy hwin
        close.handoff :=
    Classical.choice close.root
  exact
    { initial := profiledRawJointGuardedCommonTargetSource A strategy hwin key
      policy := profiledRawJointGuardedCommonTargetPolicy A strategy hwin key
      bank :=
        profiledRawJointGuardedCommonTargetControllerBank A strategy hwin key
      seed := .inr package.seed
      seed_state := package.seed_state }

/-- Checked strict-left mirror: its staged package is already the initial
right root of one fixed policy. -/
noncomputable def profiledRawJointGuardedCommonTailPolicyAnchorOfLeftClose
    (close : ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin) :
    ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy := by
  let key :=
    profiledRawJointGuardedCommonTargetOfLeft A strategy hwin close.handoff
  let package :
      ProfiledRawJointGuardedCommonLeftHandoffRootPackage A strategy hwin
        close.handoff :=
    Classical.choice close.root
  exact
    { initial := profiledRawJointGuardedCommonTargetSource A strategy hwin key
      policy := profiledRawJointGuardedCommonTargetPolicy A strategy hwin key
      bank :=
        profiledRawJointGuardedCommonTargetControllerBank A strategy hwin key
      seed := .inl package.seed
      seed_state := package.seed_state }

namespace ProfiledRawJointGuardedCommonTailPolicyAnchor

/-- Proof-side literal-close schedules at the anchor's unchanged policy. -/
abbrev CloseSchedule
    (anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy) :=
  ProfiledRawJointUnitPolicyCloseSchedule A strategy anchor.initial
    anchor.policy

end ProfiledRawJointGuardedCommonTailPolicyAnchor

/-! ## Current-tail automatic-cut slice interfaces -/

/-- Exact operational invariant owed on recurrent-`.both` executions.
Everything except `slices` is already finite policy/cut data. -/
structure ProfiledRawJointGuardedCommonTailRecurrentAutomaticCutSlices
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph)) where
  lower : Nat
  anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy
  schedule : anchor.CloseSchedule A strategy
  slices :
    let extraction :=
      recurrentEnvironmentEpochCutExtractionAfter physicalEnv hboth lower
    ProfiledRawJointUnitPolicyScheduledPhysicalSlices A strategy
      anchor.initial anchor.policy anchor.bank
      G outputOne outputTwo physicalEnv anchor.seed schedule extraction.start
        extraction.cuts

/-- Persistent strict-reversal version of the identical pointwise seam. -/
structure ProfiledRawJointGuardedCommonTailReversalAutomaticCutSlices
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hreversal :
      PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph)) where
  lower : Nat
  anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy
  schedule : anchor.CloseSchedule A strategy
  slices :
    let extraction :=
      persistentStrictReversalEpochCutExtractionAfter physicalEnv hreversal
        lower
    ProfiledRawJointUnitPolicyScheduledPhysicalSlices A strategy
      anchor.initial anchor.policy anchor.bank
      G outputOne outputTwo physicalEnv anchor.seed schedule extraction.start
        extraction.cuts

/-! ## The generic parity machinery consumes the slice seam directly -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Recurrent automatic-cut slices imply acceptance of the actual current
tail-kernel trace; no additional policy or parity premise remains. -/
theorem ProfiledRawJointGuardedCommonTailRecurrentAutomaticCutSlices.accepts
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph)}
    (witness :
      ProfiledRawJointGuardedCommonTailRecurrentAutomaticCutSlices A strategy
        G outputOne outputTwo physicalEnv hboth) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo physicalEnv) := by
  apply profiledRawJointUnitPolicyScheduledTrace_accepts_of_recurrent A
    strategy witness.anchor.initial witness.anchor.policy witness.anchor.bank
      G outputOne outputTwo physicalEnv hboth witness.lower witness.anchor.seed
      witness.schedule witness.anchor.seed_state
  intro k
  exact witness.slices.blockMin_eq A strategy witness.anchor.initial
    witness.anchor.policy witness.anchor.bank k

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Persistent strict-reversal automatic-cut slices imply acceptance by the
same unchanged fixed-policy thread. -/
theorem
    ProfiledRawJointGuardedCommonTailReversalAutomaticCutSlices.accepts
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {hreversal :
      PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph)}
    (witness :
      ProfiledRawJointGuardedCommonTailReversalAutomaticCutSlices A strategy
        G outputOne outputTwo physicalEnv hreversal) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo physicalEnv) := by
  apply profiledRawJointUnitPolicyScheduledTrace_accepts_of_persistentReversal
    A strategy witness.anchor.initial witness.anchor.policy
      witness.anchor.bank G outputOne outputTwo physicalEnv hreversal
      witness.lower witness.anchor.seed witness.schedule witness.anchor.seed_state
  intro k
  exact witness.slices.blockMin_eq A strategy witness.anchor.initial
    witness.anchor.policy witness.anchor.bank k

/-! ## Kernel-independent join with the execution-shape split -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- All three nontrivial proof-side inputs are now operational reachability
invariants: fixed common cuts, recurrent automatic slices, and reversal
automatic slices.  Their acceptance consequences are fully discharged. -/
theorem
    finiteGlobalMachineTrace_accepts_of_fixedBranches_of_automaticSlices
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (fixedRight :
      EventuallyStrictRight (fun n ↦ (physicalEnv n).graph) →
        A.Accepts
          (G.globalMachineTraceWord outputOne outputTwo physicalEnv))
    (fixedLeft :
      EventuallyStrictLeft (fun n ↦ (physicalEnv n).graph) →
        A.Accepts
          (G.globalMachineTraceWord outputOne outputTwo physicalEnv))
    (recurrentSlices :
      ∀ hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph),
        ProfiledRawJointGuardedCommonTailRecurrentAutomaticCutSlices A
          strategy G outputOne outputTwo physicalEnv hboth)
    (reversalSlices :
      ∀ hreversal :
          PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph),
        ProfiledRawJointGuardedCommonTailReversalAutomaticCutSlices A strategy
          G outputOne outputTwo physicalEnv hreversal) :
    A.Accepts
      (G.globalMachineTraceWord outputOne outputTwo physicalEnv) := by
  rcases environment_physical_acceptance_regime physicalEnv with
    hboth | hreversal | hright | hleft
  · exact (recurrentSlices hboth).accepts A strategy
  · exact (reversalSlices hreversal).accepts A strategy
  · exact fixedRight hright
  · exact fixedLeft hleft

end

end DetParityAutomaton

end DistributedSynthesis
