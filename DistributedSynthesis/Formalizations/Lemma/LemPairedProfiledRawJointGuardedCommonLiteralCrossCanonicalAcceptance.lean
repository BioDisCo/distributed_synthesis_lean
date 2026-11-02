/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossPhysicalCutHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailHardRegimeSlices
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedPhysicalControllerReadback

/-!
# Canonical literal-cross alignment implies physical acceptance

The canonical literal-cross interface already supplies exact physical slices
at the root-oriented close cuts.  Those cuts are productive and start at
zero, so the existing scheduled-policy epoch coupling applies directly.  No
second hard-regime recut, controller invariant, or parity argument is needed.

The final witness packages one fresh staged-close policy anchor together with
its canonical entry/record alignment.  The four-way environment theorem then
combines such witnesses in the recurrent regimes with the existing two fixed
strict-tail branches.

All regime tests and cuts below are proof-side.  No local transition receives
a graph, orientation, hierarchy side, leader bit, or semantic history.
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

/-! ## One fixed canonical alignment -/

/-- Canonical entry-state and emitted-record alignment produces the exact
epoch-coupling field consumed by `FiniteGlobalMachinePhysicalAcceptance`.
The proof simply composes the two structural adapters with the established
scheduled-slice coupling. -/
noncomputable def
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalTraceAlignment.epochCoupling
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
  have hcharged :=
    alignment.toChargedScheduledCutAlignment A strategy initial policy bank
  have hslices := hcharged.toScheduledPhysicalSlices A strategy initial policy
    bank
  have hmono : StrictMono cuts := by
    exact rootOrientedCloseCuts_strictMono
      (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
      (profiledRawJointUnitPolicyScheduledGraph A strategy initial policy bank
        seed schedule)
  have hzero : cuts 0 = 0 := by
    rfl
  exact profiledRawJointUnitPolicyScheduledSlicesEpochCoupling A strategy
    initial policy bank G outputOne outputTwo physicalEnv seed schedule hseed
      base cuts hmono hzero hslices

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Consequently the complete finite-machine trace is accepting. -/
theorem
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalTraceAlignment.accepts
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
          hterm seed rowAt)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run []) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo physicalEnv) := by
  exact A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling G outputOne
    outputTwo physicalEnv (alignment.epochCoupling A strategy hseed)

/-! ## A staged-close anchor plus its canonical operational trace -/

/-- Complete acceptance-facing witness selected after one fresh staged close.
The staged-close constructors already provide `anchor.seed_state`; the
operational carrier therefore owes only the canonical `entryStateAt` and
`emittedRoundAt` fields contained in `alignment`. -/
structure
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalAcceptanceWitness
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂) where
  base : Nat
  anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy
  hterm : OperationalStrictRunsTerminate
    (profiledRawJointPhysicalGraphTail physicalEnv base)
  rowAt : Nat → PairedEntryRow
  alignment :
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalTraceAlignment A
      strategy anchor.initial anchor.policy anchor.bank G outputOne outputTwo
        physicalEnv base hterm anchor.seed rowAt

/-- A canonical witness is already a proof of acceptance; no hard-regime
information remains in the conclusion. -/
noncomputable def
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalAcceptanceWitness.epochCoupling
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (witness :
      ProfiledRawJointGuardedCommonLiteralCrossCanonicalAcceptanceWitness A
        strategy G outputOne outputTwo physicalEnv) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo physicalEnv :=
  witness.alignment.epochCoupling A strategy witness.anchor.seed_state

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalAcceptanceWitness.accepts
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (witness :
      ProfiledRawJointGuardedCommonLiteralCrossCanonicalAcceptanceWitness A
        strategy G outputOne outputTwo physicalEnv) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo physicalEnv) := by
  exact witness.alignment.accepts A strategy witness.anchor.seed_state

/-! ## The four physical regimes -/

/-- Model-facing four-regime package.  Canonical witnesses supply the exact
recurrent epoch coupling and the persistent-reversal parity tail.  The two
eventually fixed strict directions retain their existing tail proofs. -/
noncomputable def
    finiteGlobalMachinePhysicalAcceptance_of_fixedTails_of_canonicalLiteralCrossAlignments
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (fixedRight :
      EventuallyStrictRight (fun n ↦ (physicalEnv n).graph) →
        ∃ start : Nat, NatSeqMinEvenParity
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo physicalEnv)
              (start + n))))
    (fixedLeft :
      EventuallyStrictLeft (fun n ↦ (physicalEnv n).graph) →
        ∃ start : Nat, NatSeqMinEvenParity
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo physicalEnv)
              (start + n))))
    (recurrentAlignment :
      ∀ _hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph),
        ProfiledRawJointGuardedCommonLiteralCrossCanonicalAcceptanceWitness A
          strategy G outputOne outputTwo physicalEnv)
    (reversalAlignment :
      ∀ _hreversal :
          PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph),
        ProfiledRawJointGuardedCommonLiteralCrossCanonicalAcceptanceWitness A
          strategy G outputOne outputTwo physicalEnv) :
    A.FiniteGlobalMachinePhysicalAcceptance G outputOne outputTwo physicalEnv
    where
  recurrent hboth :=
    (recurrentAlignment hboth).epochCoupling A strategy
  alternatingTail hreversal := by
    let witness := reversalAlignment hreversal
    have haccepts := witness.accepts A strategy
    exact ⟨0, by simpa using haccepts⟩
  strictRightTail := fixedRight
  strictLeftTail := fixedLeft

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Final generic acceptance adapter for the eventual literal-cross carrier.
The two fixed one-way tails retain their existing proofs.  In the recurrent
simultaneous and persistent-reversal regimes the caller supplies only a
canonical trace-alignment witness, possibly based at any later fresh close. -/
theorem
    finiteGlobalMachineTrace_accepts_of_fixedBranches_of_canonicalLiteralCrossAlignments
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
      ∀ _hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph),
        ProfiledRawJointGuardedCommonLiteralCrossCanonicalAcceptanceWitness A
          strategy G outputOne outputTwo physicalEnv)
    (reversalAlignment :
      ∀ _hreversal :
          PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph),
        ProfiledRawJointGuardedCommonLiteralCrossCanonicalAcceptanceWitness A
          strategy G outputOne outputTwo physicalEnv) :
    A.Accepts
      (G.globalMachineTraceWord outputOne outputTwo physicalEnv) := by
  rcases environment_physical_acceptance_regime physicalEnv with
    hboth | hreversal | hright | hleft
  · exact (recurrentAlignment hboth).accepts A strategy
  · exact (reversalAlignment hreversal).accepts A strategy
  · exact fixedRight hright
  · exact fixedLeft hleft

/-! ## Direct finite-controller extraction endpoint -/

/-- Acceptance data owed by one genuinely local paired controller in one
environment.  The two easy fields are the established eventually-fixed tail
arguments.  The two hard fields contain only canonical entry-state and
emitted-record alignments for the same controller trace.

In particular this package does not expose an orientation, hierarchy side,
strict-leader bit, or semantic history to either executable endpoint. -/
structure
    FinitePairedPhysicalControllerCanonicalLiteralCrossAcceptance
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
      ProfiledRawJointGuardedCommonLiteralCrossCanonicalAcceptanceWitness A
        strategy controller.globalMachine controller.globalOutputOne
          controller.globalOutputTwo physicalEnv
  reversalAlignment :
    ∀ _hreversal :
        PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph),
      ProfiledRawJointGuardedCommonLiteralCrossCanonicalAcceptanceWitness A
        strategy controller.globalMachine controller.globalOutputOne
          controller.globalOutputTwo physicalEnv

/-- The controller-facing canonical package is exactly the model-facing
four-regime physical-acceptance package consumed by direct readback. -/
noncomputable def
    FinitePairedPhysicalControllerCanonicalLiteralCrossAcceptance.physicalAcceptance
    {controller :
      FinitePairedPhysicalController.{u, v, x, y, w, w}
        In₁ In₂ Out₁ Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (acceptance :
      FinitePairedPhysicalControllerCanonicalLiteralCrossAcceptance A strategy
        controller physicalEnv) :
    A.FiniteGlobalMachinePhysicalAcceptance controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo physicalEnv :=
  finiteGlobalMachinePhysicalAcceptance_of_fixedTails_of_canonicalLiteralCrossAlignments
    A strategy controller.globalMachine controller.globalOutputOne
      controller.globalOutputTwo physicalEnv acceptance.fixedRight
        acceptance.fixedLeft acceptance.recurrentAlignment
          acceptance.reversalAlignment

/-- Positive extraction target for the remaining operational construction:
for each winning strategy, choose one finite paired controller once; each
environment then owes the four canonical fields above for that same trace. -/
def
    PerStrategyWinningFinitePairedPhysicalControllerCanonicalLiteralCrossAcceptance :
    Prop :=
  ∀ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) →
      ∃ controller :
          FinitePairedPhysicalController.{u, v, x, y, w, w}
            In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          Nonempty
            (FinitePairedPhysicalControllerCanonicalLiteralCrossAcceptance A
              strategy controller env)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Canonical literal-cross extraction supplies the exact strategy-indexed
physical-acceptance endpoint, without an epoch/query dummy adapter. -/
theorem
    perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_canonicalLiteralCross
    (hextract :
      PerStrategyWinningFinitePairedPhysicalControllerCanonicalLiteralCrossAcceptance.{u,
        v, x, y, s, w} A) :
    PerStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance.{u, v,
      x, y, s, w} A := by
  intro suppliedStrategy hsuppliedWin
  obtain ⟨controller, hcanonical⟩ :=
    hextract suppliedStrategy hsuppliedWin
  refine ⟨controller, fun env ↦ ?_⟩
  obtain ⟨acceptance⟩ := hcanonical env
  exact ⟨acceptance.physicalAcceptance A suppliedStrategy⟩

/-- Final direct consumer.  Once the remaining local product carrier supplies
the canonical extraction target, an unconditional readback-upgrade summary
automaton follows in one theorem application. -/
theorem
    exists_readbackUpgrade_of_finitePairedPhysicalControllerCanonicalLiteralCross
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hextract :
      PerStrategyWinningFinitePairedPhysicalControllerCanonicalLiteralCrossAcceptance.{u,
        v, x, y, s, w} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact
    exists_readbackUpgrade_of_finitePairedPhysicalControllerPhysicalAcceptance
      A fallback
        (perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_canonicalLiteralCross
          A hextract)

end


end DetParityAutomaton

end DistributedSynthesis
