/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedExtraPathAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorInstalledOutputTail
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalMachinePhysicalAcceptanceOfAccepts
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedPhysicalControllerReadback

/-!
# Operational acceptance from a jointly annotated policy path

This file is the acceptance-only adapter for the shared visible-fibre Tail
construction.  It replaces the old delayed-tag acceptance handoff, whose hard
path lived in a separately root-pinned policy, by a path through one
current-valid joint policy.  The policy is weakened only proof-theoretically
to reuse the established path-acceptance theorem; its run and successor table
stay literally unchanged.

Once that path is supplied, the controller owes only one physical equation:
the minimum priority of each actual cut block is the priority of one hidden
lineage of the path's accepted bare-code word, at a fixed proof-side offset.
The offset absorbs any finite common/shadow bootstrap.  Everything after this
equation is generic parity composition, the standard four-regime split, and
the existing finite-controller readback.

In particular no runtime map is assumed to receive a direction, hierarchy
side, leader bit, strict-leader bit, semantic history, or policy witness.
-/

namespace DistributedSynthesis

universe u v x y s b w

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

variable {Extra : Type b} [Fintype Extra]

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev ExtraPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra) :=
  ProfiledRawJointHybridPhysicalCompatibleExtraRationalPolicy A strategy hwin
    initial initialExtra extraAdvance

private abbrev ExtraPath
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {initialExtra : Extra}
    {extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra}
    (policy : ExtraPolicy A strategy hwin initial initialExtra extraAdvance) :=
  ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath A strategy hwin
    policy

private abbrev ValidatedExtraPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (ExtraValid : HybridState A strategy → Extra → Prop)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraRationalPolicy A
    strategy hwin initial initialExtra ExtraValid extraAdvance

private abbrev ValidatedExtraPath
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {initialExtra : Extra}
    {ExtraValid : HybridState A strategy → Extra → Prop}
    {extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra}
    (policy : ValidatedExtraPolicy A strategy hwin initial initialExtra
      ExtraValid extraAdvance) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraAllowedPath A
    strategy hwin policy

private abbrev PhysicalController :=
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂

namespace ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {initialExtra : Extra}
variable {extraAdvance : HybridState A strategy → Extra →
  HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra}
variable {policy : ExtraPolicy A strategy hwin initial initialExtra
  extraAdvance}

/-- Acceptance of the joint path implies parity of every initially selected
hidden lineage. -/
theorem threadPriority_parity
    (path : ExtraPath A strategy hwin policy)
    (initialSide : IndexedLineageSide) :
    NatSeqMinEvenParity (fun n ↦
      (codedAlternatingIndexedLineageCodeThreadSystem
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun
          (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
            A))
          (profiledRawJointHybridCurrentSlots A)
          (path.bareCodeWord A strategy hwin) initialSide () n)) := by
  have haccepts := path.bareCodeWord_accepts A strategy hwin
  have hcoded :
      (codedAlternatingIndexedLineageCodeDPA
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).Accepts
          (path.bareCodeWord A strategy hwin) := by
    simpa only [profiledRawJointHybridCodeParityDPA] using haccepts
  exact
    (codedAlternatingIndexedLineageCodeDPA_accepts_iff
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A)
      (path.bareCodeWord A strategy hwin)).mp hcoded initialSide ()

end ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath

/-! ## The smallest hard-regime physical alignment -/

/-- Acceptance-facing contract for an actual finite controller trace.

The joint path already contains its initial state and all same-policy allowed
edges.  Therefore the only controller-specific mathematical field is
`blockMin_eq_threadPriority`.  `offset` is proof-side and may skip the finite
bootstrap before the shared visible-fibre Tail becomes fully active. -/
structure ProfiledRawJointHybridPhysicalCompatibleExtraPhysicalCutAlignment
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {initialExtra : Extra}
    {extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra}
    {policy : ExtraPolicy A strategy hwin initial initialExtra extraAdvance}
    (path : ExtraPath A strategy hwin policy)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat) where
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  initialSide : IndexedLineageSide
  offset : Nat
  blockMin_eq_threadPriority : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts k =
      (codedAlternatingIndexedLineageCodeThreadSystem
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun
          (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
            A))
          (profiledRawJointHybridCurrentSlots A)
          (path.bareCodeWord A strategy hwin) initialSide () (offset + k))

namespace
  ProfiledRawJointHybridPhysicalCompatibleExtraPhysicalCutAlignment

/-- The single block-minimum equation turns the accepted joint path into the
ordinary epoch coupling of the actual controller trace. -/
noncomputable def epochCoupling
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {initialExtra : Extra}
    {extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra}
    {policy : ExtraPolicy A strategy hwin initial initialExtra extraAdvance}
    {path : ExtraPath A strategy hwin policy}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (alignment :
      ProfiledRawJointHybridPhysicalCompatibleExtraPhysicalCutAlignment A
        strategy hwin path G outputOne outputTwo env start cuts) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env := by
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  let priorities := fun n ↦
    (codedAlternatingIndexedLineageCodeThreadSystem initialCode
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun initialCode
        (profiledRawJointHybridCurrentSlots A)
        (path.bareCodeWord A strategy hwin) alignment.initialSide () n)
  have hfull : NatSeqMinEvenParity priorities := by
    simpa only [priorities, initialCode] using
      path.threadPriority_parity A strategy hwin alignment.initialSide
  have hshift :
      NatSeqMinEvenParity (fun k ↦ priorities (alignment.offset + k)) :=
    (natSeqMinEvenParity_shift priorities alignment.offset).mpr hfull
  exact {
    start := start
    cuts := cuts
    cuts_strictMono := alignment.cuts_strictMono
    cuts_zero := alignment.cuts_zero
    epochPriority := fun k ↦ priorities (alignment.offset + k)
    epochParity := hshift
    blockMin_eq_epochPriority := fun k ↦ by
      simpa only [priorities, initialCode] using
        alignment.blockMin_eq_threadPriority k }

/-- Hence the complete actual controller trace is accepted; an arbitrary
finite physical prefix before `start` is harmless. -/
theorem accepts
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {initialExtra : Extra}
    {extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra}
    {policy : ExtraPolicy A strategy hwin initial initialExtra extraAdvance}
    {path : ExtraPath A strategy hwin policy}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (alignment :
      ProfiledRawJointHybridPhysicalCompatibleExtraPhysicalCutAlignment A
        strategy hwin path G outputOne outputTwo env start cuts) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling G outputOne outputTwo
    env (alignment.epochCoupling A strategy hwin)

end
  ProfiledRawJointHybridPhysicalCompatibleExtraPhysicalCutAlignment

/-- Current-valid presentation of the cut alignment.  Internally it reuses
the existing accepted-path consumer through the literal policy weakening;
there is no independently selected unvalidated policy. -/
abbrev
    ProfiledRawJointHybridPhysicalCompatibleValidatedExtraPhysicalCutAlignment
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {initialExtra : Extra}
    {ExtraValid : HybridState A strategy → Extra → Prop}
    {extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra}
    {policy : ValidatedExtraPolicy A strategy hwin initial initialExtra
      ExtraValid extraAdvance}
    (path : ValidatedExtraPath A strategy hwin policy)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat) :=
  ProfiledRawJointHybridPhysicalCompatibleExtraPhysicalCutAlignment A
    strategy hwin (path.toExtraAllowedPath A strategy hwin) G outputOne
      outputTwo env start cuts

/-! ## Four regimes and `ReadbackUpgrade` -/

/-- One hard-regime witness.  The common root, the jointly rationalized
policy, and its allowed path are proof-side data; only the physical controller
is executable. -/
abbrev ProfiledRawJointHybridPhysicalCompatibleExtraHardCertificateBundle
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) :=
  Σ initial : ProfiledRawJointCommonBaseWorld A strategy,
    Σ initialExtra : Extra,
      Σ ExtraValid : HybridState A strategy → Extra → Prop,
        Σ extraAdvance : HybridState A strategy → Extra →
            HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra,
          Σ policy : ValidatedExtraPolicy A strategy hwin initial initialExtra
            ExtraValid extraAdvance,
            Σ path : ValidatedExtraPath A strategy hwin policy,
              Σ start : Nat, Σ cuts : Nat → Nat,
                ProfiledRawJointHybridPhysicalCompatibleValidatedExtraPhysicalCutAlignment
                  A strategy hwin path controller.globalMachine
                    controller.globalOutputOne controller.globalOutputTwo env
                      start cuts

/-- Exact per-environment residual for the joint-policy route.  The two hard
regimes need only the bundle above; the homogeneous regimes reuse the already
proved installed-output tails. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleExtraControllerBookkeeping
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) : Prop where
  recurrent : GraphBothRecurrent (fun n ↦ (env n).graph) →
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleExtraHardCertificateBundle A
        strategy hwin (Extra := Extra) controller env)
  reversal : PersistentStrictReversalTail (fun n ↦ (env n).graph) →
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleExtraHardCertificateBundle A
        strategy hwin (Extra := Extra) controller env)
  fixed : EventuallyInstalledOutputTailBookkeeping A controller env

namespace
  ProfiledRawJointHybridPhysicalCompatibleExtraControllerBookkeeping

/-- Joint-policy hard witnesses plus the existing fixed tails give the
standard physical-acceptance package. -/
noncomputable def physicalAcceptance
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridPhysicalCompatibleExtraControllerBookkeeping A
        strategy hwin (Extra := Extra) controller env) :
    A.FiniteGlobalMachinePhysicalAcceptance controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo env := by
  let fixed := bookkeeping.fixed.toEventuallyInstalledFixedTailBookkeeping A
  exact {
    recurrent := fun hboth ↦ by
      let bundle := Classical.choice (bookkeeping.recurrent hboth)
      let alignment := bundle.2.2.2.2.2.2.2.2
      exact alignment.epochCoupling A strategy hwin
    alternatingTail := fun hreversal ↦ by
      let bundle := Classical.choice (bookkeeping.reversal hreversal)
      let alignment := bundle.2.2.2.2.2.2.2.2
      let direct := A.finiteGlobalMachinePhysicalAcceptance_of_accepts
        controller.globalMachine controller.globalOutputOne
          controller.globalOutputTwo env
            (alignment.accepts A strategy hwin)
      exact direct.alternatingTail hreversal
    strictRightTail := fixed.rightTailParity A
    strictLeftTail := fixed.leftTailParity A }

end
  ProfiledRawJointHybridPhysicalCompatibleExtraControllerBookkeeping

/-- Strategy-indexed construction premise left to the shared visible-fibre
Tail.  Only the executable finite controller is selected before the
environment.  The common semantic root and all annotation-policy witnesses
are proof-side data local to each hard-regime execution. -/
def PerStrategyWinningPhysicalCompatibleExtraControllerBookkeeping : Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
      ∃ controller :
        FinitePairedPhysicalController.{u, v, x, y, w, w}
          In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        ProfiledRawJointHybridPhysicalCompatibleExtraControllerBookkeeping A
          strategy hwin (Extra := Extra) controller env

/-- The shared-fibre construction premise is exactly sufficient for the
existing finite paired physical-controller extraction. -/
theorem
    perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_extraBookkeeping
    (hbookkeeping :
      PerStrategyWinningPhysicalCompatibleExtraControllerBookkeeping.{u, v,
        x, y, s, b, w} A
        (Extra := Extra)) :
    PerStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance.{u, v,
      x, y, s, w} A := by
  intro strategy hwin
  obtain ⟨controller, hcontroller⟩ :=
    hbookkeeping strategy hwin
  refine ⟨controller, fun env ↦ ?_⟩
  exact ⟨(hcontroller env).physicalAcceptance A strategy hwin⟩

/-- One-arrow `ReadbackUpgrade` consumer.  There is no occurrence of the old
separately rationalized root-pinned Tail policy in this statement. -/
theorem exists_readbackUpgrade_of_physicalCompatibleExtraBookkeeping
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hbookkeeping :
      PerStrategyWinningPhysicalCompatibleExtraControllerBookkeeping.{u, v,
        x, y, s, b, w} A
        (Extra := Extra)) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact
    exists_readbackUpgrade_of_finitePairedPhysicalControllerPhysicalAcceptance
      A fallback
        (perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_extraBookkeeping
          A hbookkeeping)

end

end DetParityAutomaton

end DistributedSynthesis
