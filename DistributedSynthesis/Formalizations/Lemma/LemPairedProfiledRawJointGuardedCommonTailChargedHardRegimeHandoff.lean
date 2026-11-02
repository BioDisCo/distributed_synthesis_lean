/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailChargedPhysicalSlices
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailHardRegimeSlices

/-!
# Charged cut alignment discharges the hard-regime acceptance seam

The charged local carrier is an operational construction.  At its automatic
cuts it owes the three equalities packaged by
`ProfiledRawJointGuardedCommonTailChargedScheduledCutAlignment`.  The generic
hard-regime development already proves all parity consequences of those
equalities.

This file is the lossless adapter between the two interfaces.  It is generic
in the finite global round machine and its output maps.  In particular it
does not inspect a graph, hierarchy direction, leader bit, or the internal
state type of the eventual charged kernel.
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

/-! ## Adapter-facing witnesses for the two hard regimes -/

/-- In the recurrent-`both` regime, pointwise alignment of every charged cut
with one scheduled fixed-policy thread is the complete operational premise
needed for acceptance. -/
structure
    ProfiledRawJointGuardedCommonTailChargedRecurrentAutomaticCutAlignment
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph)) where
  lower : Nat
  anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy
  schedule : anchor.CloseSchedule A strategy
  alignment :
    let extraction :=
      recurrentEnvironmentEpochCutExtractionAfter physicalEnv hboth lower
    ProfiledRawJointGuardedCommonTailChargedScheduledCutAlignment A strategy
      anchor.initial anchor.policy anchor.bank G outputOne outputTwo physicalEnv
      anchor.seed schedule extraction.start extraction.cuts

/-- Persistent strict reversal uses the same charged alignment interface and
only a different proof-side cut extraction. -/
structure
    ProfiledRawJointGuardedCommonTailChargedReversalAutomaticCutAlignment
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hreversal :
      PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph)) where
  lower : Nat
  anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy
  schedule : anchor.CloseSchedule A strategy
  alignment :
    let extraction :=
      persistentStrictReversalEpochCutExtractionAfter physicalEnv hreversal
        lower
    ProfiledRawJointGuardedCommonTailChargedScheduledCutAlignment A strategy
      anchor.initial anchor.policy anchor.bank G outputOne outputTwo physicalEnv
      anchor.seed schedule extraction.start extraction.cuts

/-! ## Exact conversion to the already proved hard-regime seam -/

/-- No parity reasoning occurs here: each charged cut is merely viewed as
the generic `PhysicalSlice` it already is. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailChargedRecurrentAutomaticCutAlignment.toAutomaticCutSlices
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph)}
    (witness :
      ProfiledRawJointGuardedCommonTailChargedRecurrentAutomaticCutAlignment A
        strategy G outputOne outputTwo physicalEnv hboth) :
    ProfiledRawJointGuardedCommonTailRecurrentAutomaticCutSlices A strategy G
      outputOne outputTwo physicalEnv hboth := by
  refine
    { lower := witness.lower
      anchor := witness.anchor
      schedule := witness.schedule
      slices := ?_ }
  exact witness.alignment.toScheduledPhysicalSlices A strategy
    witness.anchor.initial witness.anchor.policy witness.anchor.bank

noncomputable def
    ProfiledRawJointGuardedCommonTailChargedReversalAutomaticCutAlignment.toAutomaticCutSlices
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {hreversal :
      PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph)}
    (witness :
      ProfiledRawJointGuardedCommonTailChargedReversalAutomaticCutAlignment A
        strategy G outputOne outputTwo physicalEnv hreversal) :
    ProfiledRawJointGuardedCommonTailReversalAutomaticCutSlices A strategy G
      outputOne outputTwo physicalEnv hreversal := by
  refine
    { lower := witness.lower
      anchor := witness.anchor
      schedule := witness.schedule
      slices := ?_ }
  exact witness.alignment.toScheduledPhysicalSlices A strategy
    witness.anchor.initial witness.anchor.policy witness.anchor.bank

/-! ## Acceptance and the four-way environment split -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem
    ProfiledRawJointGuardedCommonTailChargedRecurrentAutomaticCutAlignment.accepts
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph)}
    (witness :
      ProfiledRawJointGuardedCommonTailChargedRecurrentAutomaticCutAlignment A
        strategy G outputOne outputTwo physicalEnv hboth) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo physicalEnv) := by
  exact (witness.toAutomaticCutSlices A strategy).accepts A strategy

theorem
    ProfiledRawJointGuardedCommonTailChargedReversalAutomaticCutAlignment.accepts
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {hreversal :
      PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph)}
    (witness :
      ProfiledRawJointGuardedCommonTailChargedReversalAutomaticCutAlignment A
        strategy G outputOne outputTwo physicalEnv hreversal) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo physicalEnv) := by
  exact (witness.toAutomaticCutSlices A strategy).accepts A strategy

/-- Final generic handoff: fixed one-way tails keep their existing proofs;
the two hard regimes now ask only for charged operational cut alignment. -/
theorem
    finiteGlobalMachineTrace_accepts_of_fixedBranches_of_chargedAlignments
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
    (recurrentAlignment :
      ∀ hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph),
        ProfiledRawJointGuardedCommonTailChargedRecurrentAutomaticCutAlignment
          A strategy G outputOne outputTwo physicalEnv hboth)
    (reversalAlignment :
      ∀ hreversal :
          PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph),
        ProfiledRawJointGuardedCommonTailChargedReversalAutomaticCutAlignment
          A strategy G outputOne outputTwo physicalEnv hreversal) :
    A.Accepts
      (G.globalMachineTraceWord outputOne outputTwo physicalEnv) := by
  apply finiteGlobalMachineTrace_accepts_of_fixedBranches_of_automaticSlices A
    strategy G outputOne outputTwo physicalEnv fixedRight fixedLeft
  · intro hboth
    exact (recurrentAlignment hboth).toAutomaticCutSlices A strategy
  · intro hreversal
    exact (reversalAlignment hreversal).toAutomaticCutSlices A strategy

end

end

end DetParityAutomaton

end DistributedSynthesis
