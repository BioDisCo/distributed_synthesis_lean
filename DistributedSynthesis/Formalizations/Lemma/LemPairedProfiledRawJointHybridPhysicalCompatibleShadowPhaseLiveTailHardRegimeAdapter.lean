/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailRootAlignedCutStream
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOperationalCloseCuts

/-!
# Operational hard-regime adapter for root-aligned cut streams

The recurrent-synchronization and persistent strict-reversal branches use the
same canonical operational-close clock.  Once a concrete controller trace has
been organized into a root-aligned physical cut stream, the remaining passage
to the final controller bookkeeping is independent of the controller's
internal construction.

This file records that passage in one arrow.  A regime witness contains only

* its proof-side delayed tag and physical start time;
* a stream indexed by the canonical operational-close cuts; and
* a total decoding of controller states into tail states, together with its
  equality to the stream at every close cut.

Cut monotonicity and the zero equation are deliberately not additional
hypotheses: they are inherited from `OperationalCloseCutPackage`.  The fixed
strict-tail field remains explicit, since it is logically independent of the
two productive hard regimes.
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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev TailState (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag

private abbrev PhysicalController :=
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂

/-- Public spelling of the dependent hard-certificate bundle consumed by the
final controller bookkeeping.  The original spelling is private to the
physical-acceptance module; this equivalent interface lets later construction
files assemble and inspect the data without depending on a private name. -/
abbrev ProfiledRawJointHybridShadowPhaseLivePublicHardCertificateBundle
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) :=
  Σ tag : Tag A strategy hwin, Σ start : Nat, Σ cuts : Nat → Nat,
    ProfiledRawJointHybridShadowPhaseLivePhysicalAcceptanceCertificate A
      strategy hwin tag controller.globalMachine controller.globalOutputOne
        controller.globalOutputTwo env start cuts

/-- The smallest controller-independent witness over one already chosen
operational-close package.  In particular, `cuts` is not stored independently:
the stream is indexed by `cutPackage.cuts` definitionally. -/
structure
    ProfiledRawJointHybridShadowPhaseLiveOperationalCutStreamWitness
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂)
    (cutPackage : OperationalCloseCutPackage (fun n ↦ (env n).graph)) where
  tag : Tag A strategy hwin
  start : Nat
  stream :
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutStream A
      strategy hwin tag controller.globalMachine controller.globalOutputOne
        controller.globalOutputTwo env start cutPackage.cuts
  closeState : controller.globalMachine.State →
    TailState A strategy hwin tag
  closeState_eq : ∀ n : Nat,
    closeState
        (controller.globalMachine.globalStateTrace env
          (start + cutPackage.cuts n)) =
      stream.state n

namespace
  ProfiledRawJointHybridShadowPhaseLiveOperationalCutStreamWitness

/-- A stream over an operational-close package already contains a complete
hard-regime physical-acceptance certificate. -/
noncomputable def publicHardCertificateBundle
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    {cutPackage : OperationalCloseCutPackage (fun n ↦ (env n).graph)}
    (witness :
      ProfiledRawJointHybridShadowPhaseLiveOperationalCutStreamWitness A
        strategy hwin controller env cutPackage) :
    ProfiledRawJointHybridShadowPhaseLivePublicHardCertificateBundle A
      strategy hwin controller env :=
  ⟨witness.tag, witness.start, cutPackage.cuts,
    witness.stream.physicalAcceptanceCertificate A strategy hwin
      cutPackage.cuts_strictMono cutPackage.cuts_zero witness.closeState
        witness.closeState_eq⟩

end
  ProfiledRawJointHybridShadowPhaseLiveOperationalCutStreamWitness

/-- The exact regime split immediately before the final shadow-phase-live
controller bookkeeping.  Both hard fields use their canonical graph-derived
operational-close package.  The installed fixed-tail witness is retained as a
separate explicit field. -/
structure
    ProfiledRawJointHybridShadowPhaseLiveOperationalHardRegimeBookkeeping
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) : Prop where
  recurrent :
    ∀ hboth : GraphBothRecurrent (fun n ↦ (env n).graph),
      Nonempty
        (ProfiledRawJointHybridShadowPhaseLiveOperationalCutStreamWitness A
          strategy hwin controller env
            (operationalCloseCutPackageOfGraphBothRecurrent
              (fun n ↦ (env n).graph) hboth))
  reversal :
    ∀ hreversal : PersistentStrictReversalTail (fun n ↦ (env n).graph),
      Nonempty
        (ProfiledRawJointHybridShadowPhaseLiveOperationalCutStreamWitness A
          strategy hwin controller env
            (operationalCloseCutPackageOfPersistentStrictReversalTail
              (fun n ↦ (env n).graph) hreversal))
  fixed : EventuallyInstalledOutputTailBookkeeping A controller env

namespace
  ProfiledRawJointHybridShadowPhaseLiveOperationalHardRegimeBookkeeping

/-- The two canonical operational clocks and their root-aligned streams
discharge both hard fields of the final controller bookkeeping. -/
noncomputable def controllerBookkeeping
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridShadowPhaseLiveOperationalHardRegimeBookkeeping A
        strategy hwin controller env) :
    ProfiledRawJointHybridShadowPhaseLiveControllerBookkeeping A strategy hwin
      controller env where
  recurrent hboth := by
    let cutPackage := operationalCloseCutPackageOfGraphBothRecurrent
      (fun n ↦ (env n).graph) hboth
    let witness := Classical.choice (bookkeeping.recurrent hboth)
    exact ⟨witness.publicHardCertificateBundle A strategy hwin⟩
  reversal hreversal := by
    let cutPackage := operationalCloseCutPackageOfPersistentStrictReversalTail
      (fun n ↦ (env n).graph) hreversal
    let witness := Classical.choice (bookkeeping.reversal hreversal)
    exact ⟨witness.publicHardCertificateBundle A strategy hwin⟩
  fixed := bookkeeping.fixed

/-- Acceptance of the actual finite-controller trace is now immediate from
the operational hard-regime bookkeeping. -/
noncomputable def physicalAcceptance
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridShadowPhaseLiveOperationalHardRegimeBookkeeping A
        strategy hwin controller env) :
    A.FiniteGlobalMachinePhysicalAcceptance controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo env :=
  (bookkeeping.controllerBookkeeping A strategy hwin).physicalAcceptance A
    strategy hwin

end
  ProfiledRawJointHybridShadowPhaseLiveOperationalHardRegimeBookkeeping

end

end DetParityAutomaton

end DistributedSynthesis
