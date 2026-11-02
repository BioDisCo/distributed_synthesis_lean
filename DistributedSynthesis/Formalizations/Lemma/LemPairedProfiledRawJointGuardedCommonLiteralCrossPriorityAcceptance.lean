/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossCanonicalAcceptance

/-!
# Literal-cross acceptance from block priorities only

The former canonical handoff asks the operational controller to identify every
physical record in every scheduled block.  That statement is sufficient, but
stronger than parity needs and too rigid for the branch-aware heterogeneous
table: its active target is literal and sound even when no independently
chosen canonical record word is definitionally equal to the table play.

This file exposes the exact weaker interface.  At every canonical close the
controller owes only the minimum priority of the actual physical block.  The
scheduled target already belongs to one alternating thread of one fixed
rational policy, so the existing thread-parity and block-pasting theorems turn
those equalities directly into an epoch coupling and acceptance.

The old record alignment maps into this interface, but the converse is neither
required nor claimed.  All schedules, cuts, rows, and priorities below are
proof-side; executable endpoints still receive no graph, orientation, leader
bit, hierarchy side, history, or semantic view.
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

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)

/-- Exact parity-facing alignment for the canonical literal-close schedule.
Unlike `ProfiledRawJointGuardedCommonLiteralCrossCanonicalTraceAlignment`,
this structure contains no entry-state or record-list equality. -/
structure ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow) : Prop where
  blockMinAt : ∀ k : Nat,
    let schedule :=
      profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
        bank physicalEnv base hterm seed rowAt
    let cuts :=
      profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
        physicalEnv base hterm seed schedule
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k
    let query := schedule k root
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo physicalEnv)
            (base + n)))
        cuts k =
      query.blockPriority A strategy initial policy bank

namespace ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment

/-- Block-priority alignment is exactly enough for the existing scheduled
alternating-thread construction to yield the physical epoch coupling. -/
noncomputable def epochCoupling
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)}
    {bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂} {base : Nat}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {rowAt : Nat → PairedEntryRow}
    (alignment :
      ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment A
        strategy initial policy bank G outputOne outputTwo physicalEnv base
          hterm seed rowAt)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run []) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo physicalEnv := by
  let schedule :=
    profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
      bank physicalEnv base hterm seed rowAt
  let cuts :=
    profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
      physicalEnv base hterm seed schedule
  apply profiledRawJointUnitPolicyScheduledTraceEpochCoupling A strategy
    initial policy bank G outputOne outputTwo physicalEnv seed schedule hseed
      base cuts
  · exact rootOrientedCloseCuts_strictMono
      (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
      (profiledRawJointUnitPolicyScheduledGraph A strategy initial policy bank
        seed schedule)
  · rfl
  · intro k
    exact alignment.blockMinAt k

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Hence no record-word comparison is needed to prove acceptance. -/
theorem accepts
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)}
    {bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂} {base : Nat}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {rowAt : Nat → PairedEntryRow}
    (alignment :
      ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment A
        strategy initial policy bank G outputOne outputTwo physicalEnv base
          hterm seed rowAt)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run []) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo physicalEnv) := by
  exact A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling G outputOne
    outputTwo physicalEnv (alignment.epochCoupling A strategy hseed)

/-- Compatibility: the old record-level alignment implies the new, weaker
priority alignment.  New constructions may target the latter directly. -/
noncomputable def ofTraceAlignment
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)}
    {bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂} {base : Nat}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {rowAt : Nat → PairedEntryRow}
    (alignment :
      ProfiledRawJointGuardedCommonLiteralCrossCanonicalTraceAlignment A
        strategy initial policy bank G outputOne outputTwo physicalEnv base
          hterm seed rowAt) :
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment A
      strategy initial policy bank G outputOne outputTwo physicalEnv base hterm
        seed rowAt where
  blockMinAt k := by
    let schedule :=
      profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
        bank physicalEnv base hterm seed rowAt
    let cuts :=
      profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
        physicalEnv base hterm seed schedule
    have charged := alignment.toChargedScheduledCutAlignment A strategy initial
      policy bank
    have slices := charged.toScheduledPhysicalSlices A strategy initial policy
      bank
    exact slices.blockMin_eq A strategy initial policy bank k

/-! ## Acceptance-facing packaging

The remainder of the readback stack used to be phrased only for the stronger
record-level alignment.  The following parallel packaging carries the weaker
priority law to the same final endpoint. -/

/-- One proof-side tail anchor together with the pointwise physical block
minima of its canonical close schedule. -/
structure CanonicalAcceptanceWitness
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂) where
  base : Nat
  anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy
  hterm : OperationalStrictRunsTerminate
    (profiledRawJointPhysicalGraphTail physicalEnv base)
  rowAt : Nat → PairedEntryRow
  alignment :
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment A
      strategy anchor.initial anchor.policy anchor.bank G outputOne outputTwo
        physicalEnv base hterm anchor.seed rowAt

namespace CanonicalAcceptanceWitness

/-- A priority witness is already the complete epoch coupling. -/
noncomputable def epochCoupling
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (witness : CanonicalAcceptanceWitness A strategy G outputOne outputTwo
      physicalEnv) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo physicalEnv :=
  witness.alignment.epochCoupling A strategy witness.anchor.seed_state

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Hence it accepts the actual finite-machine word. -/
theorem accepts
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (witness : CanonicalAcceptanceWitness A strategy G outputOne outputTwo
      physicalEnv) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo physicalEnv) := by
  exact witness.alignment.accepts A strategy witness.anchor.seed_state

end CanonicalAcceptanceWitness

/-! ## Direct finite-controller readback endpoint -/

/-- The four physical regimes for one genuinely local paired controller,
with only priority alignment in the two hard regimes. -/
structure FinitePairedPhysicalControllerPriorityAcceptance
    (controller :
      FinitePairedPhysicalController.{u, v, x, y, w, w}
        In₁ In₂ Out₁ Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂) where
  fixedRight :
    EventuallyStrictRight (fun n ↦ (physicalEnv n).graph) →
      ∃ start : Nat, NatSeqMinEvenParity
        (fun n ↦ A.priority
          (A.run
            (controller.globalMachine.globalMachineTraceWord
              controller.globalOutputOne controller.globalOutputTwo
                physicalEnv)
            (start + n)))
  fixedLeft :
    EventuallyStrictLeft (fun n ↦ (physicalEnv n).graph) →
      ∃ start : Nat, NatSeqMinEvenParity
        (fun n ↦ A.priority
          (A.run
            (controller.globalMachine.globalMachineTraceWord
              controller.globalOutputOne controller.globalOutputTwo
                physicalEnv)
            (start + n)))
  recurrentAlignment :
    ∀ _hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph),
      CanonicalAcceptanceWitness A strategy controller.globalMachine
        controller.globalOutputOne controller.globalOutputTwo physicalEnv
  reversalAlignment :
    ∀ _hreversal :
        PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph),
      CanonicalAcceptanceWitness A strategy controller.globalMachine
        controller.globalOutputOne controller.globalOutputTwo physicalEnv

namespace FinitePairedPhysicalControllerPriorityAcceptance

/-- Priority-only hard-regime witnesses supply the standard four-regime
physical-acceptance package. -/
noncomputable def physicalAcceptance
    {controller :
      FinitePairedPhysicalController.{u, v, x, y, w, w}
        In₁ In₂ Out₁ Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (acceptance : FinitePairedPhysicalControllerPriorityAcceptance A strategy
      controller physicalEnv) :
    A.FiniteGlobalMachinePhysicalAcceptance controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo physicalEnv where
  recurrent hboth :=
    (acceptance.recurrentAlignment hboth).epochCoupling A strategy
  alternatingTail hreversal := by
    have haccepts :=
      (acceptance.reversalAlignment hreversal).accepts A strategy
    exact ⟨0, by simpa using haccepts⟩
  strictRightTail := acceptance.fixedRight
  strictLeftTail := acceptance.fixedLeft

end FinitePairedPhysicalControllerPriorityAcceptance

/-- Strategy-indexed positive target for the final local construction. -/
def PerStrategyWinningFinitePairedPhysicalControllerPriorityAcceptance : Prop :=
  ∀ suppliedStrategy : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution suppliedStrategy env)) →
      ∃ controller :
          FinitePairedPhysicalController.{u, v, x, y, w, w}
            In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          Nonempty
            (FinitePairedPhysicalControllerPriorityAcceptance A
              suppliedStrategy controller env)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The priority-only extraction is exactly the physical-acceptance endpoint
consumed by direct readback. -/
theorem
    perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_priority
    (hextract :
      PerStrategyWinningFinitePairedPhysicalControllerPriorityAcceptance.{u,
        v, x, y, s, w} A) :
    PerStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance.{u, v,
      x, y, s, w} A := by
  intro suppliedStrategy hsuppliedWin
  obtain ⟨controller, hpriority⟩ := hextract suppliedStrategy hsuppliedWin
  refine ⟨controller, fun env ↦ ?_⟩
  obtain ⟨acceptance⟩ := hpriority env
  exact ⟨acceptance.physicalAcceptance A suppliedStrategy⟩

/-- Final one-arrow consumer: no record-level canonical alignment is present
in the hypothesis. -/
theorem exists_readbackUpgrade_of_finitePairedPhysicalControllerPriority
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hextract :
      PerStrategyWinningFinitePairedPhysicalControllerPriorityAcceptance.{u,
        v, x, y, s, w} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact
    exists_readbackUpgrade_of_finitePairedPhysicalControllerPhysicalAcceptance
      A fallback
        (perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_priority
          A hextract)

end ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment

end

end DetParityAutomaton

end DistributedSynthesis
