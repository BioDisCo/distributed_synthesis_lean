/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPhysicalPriorityBridge
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorInstalledOutputTail
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalMachinePhysicalAcceptanceOfAccepts
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedPhysicalControllerReadback

/-!
# Physical acceptance from one delayed root-pinned tail tag

The ordinary compatible-policy bookkeeping is rooted at one common code.  A
tail selected after the first strict shadow is honestly rooted at the exact
strict child instead.  This file avoids coercing that tail into the wrong
interface.  It combines

* the accepting ordinary tail projected from the preselected root-pinned
  package bank;
* exact close-state image edges of that same tail; and
* the usual physical-block-minimum/hidden-lineage equality.

The result is acceptance of the actual finite controller word, after which
the tag and policy can be forgotten.  The tag, cuts, and lineage side are
proof-side witnesses only.
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

/-- Complete hard-regime certificate below one delayed strict-child tag.
Every close state is a state of the ordinary tail selected by that tag. -/
structure
    ProfiledRawJointHybridShadowPhaseLivePhysicalAcceptanceCertificate
    (tag : Tag A strategy hwin)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat) where
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  closeState : G.State → TailState A strategy hwin tag
  close_zero :
    closeState (G.globalStateTrace env (start + cuts 0)) =
      (tag.tailCodePolicy A strategy hwin).run []
  close_step : ∀ n,
    tag.TailAllowedTarget A strategy hwin
      (closeState (G.globalStateTrace env (start + cuts n)))
      (closeState (G.globalStateTrace env (start + cuts (n + 1))))
  initialSide : IndexedLineageSide
  offset : Nat
  blockMin_eq_threadPriority : ∀ k : Nat,
    let installed :=
      profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    let initialCode : ProfiledRawJointHybridCode A :=
      .common ((profiledRawJointCommonWorldFamily A installed.world
        ).incidenceCode A)
    let firstChild := (tag.childCode A strategy hwin).1
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts k =
      (codedAlternatingIndexedLineageCodeThreadSystem initialCode
          (profiledRawJointHybridCurrentSlots A)
          (profiledRawJointThreadRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun initialCode
          (profiledRawJointHybridCurrentSlots A)
          (profiledRawJointHybridFirstChildCodeWord A firstChild
            (fun n ↦
              (closeState
                (G.globalStateTrace env
                  (start + cuts (n + 1)))).1.1))
          initialSide () (offset + k))

namespace
    ProfiledRawJointHybridShadowPhaseLivePhysicalAcceptanceCertificate

/-- The tagged certificate first proves acceptance from the actual physical
DPA state at its proof-side start cut. -/
theorem acceptsFrom
    {tag : Tag A strategy hwin}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (certificate :
      ProfiledRawJointHybridShadowPhaseLivePhysicalAcceptanceCertificate A
        strategy hwin tag G outputOne outputTwo env start cuts) :
    A.AcceptsFrom
      (A.run (G.globalMachineTraceWord outputOne outputTwo env) start)
      (OmegaWord.drop
        (G.globalMachineTraceWord outputOne outputTwo env) start) := by
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
  let package :=
    profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
      tag.origin
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A installed.world
      ).incidenceCode A)
  let firstChild := (tag.childCode A strategy hwin).1
  let states : Nat → TailState A strategy hwin tag := fun n ↦
    certificate.closeState
      (G.globalStateTrace env (start + cuts n))
  have hcode := tag.acceptsFrom_of_tailAllowedPath A strategy hwin states
    certificate.close_zero certificate.close_step
  have hcontrol :
      (package.policy.run [tag.childCode A strategy hwin]).2.2 =
        (profiledRawJointHybridCodeParityDPA A initialCode).step
          (profiledRawJointHybridCodeParityDPA A initialCode).initial
          firstChild :=
    tag.childControl A strategy hwin
  let word := G.globalMachineTraceWord outputOne outputTwo env
  let codeTail : OmegaWord (ProfiledRawJointHybridCode A) := fun n ↦
    (states (n + 1)).1.1
  apply profiledRawJointHybridPhysicalTail_acceptsFrom_of_codeAcceptsFrom A
    initialCode firstChild
    (package.policy.run [tag.childCode A strategy hwin]).2.2
    codeTail hcontrol hcode (A.run word start) (OmegaWord.drop word start)
    cuts certificate.cuts_strictMono certificate.cuts_zero
    certificate.initialSide certificate.offset
  intro k
  have hrun :
      (fun n ↦ A.priority
        (A.runFrom (A.run word start) (OmegaWord.drop word start) n)) =
      (fun n ↦ A.priority (A.run word (start + n))) := by
    funext n
    exact congrArg A.priority (A.runFrom_drop A.initial word start n)
  rw [hrun]
  exact certificate.blockMin_eq_threadPriority k

/-- Finite-prefix invariance upgrades the state-relative result to acceptance
of the complete actual controller trace. -/
theorem accepts
    {tag : Tag A strategy hwin}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (certificate :
      ProfiledRawJointHybridShadowPhaseLivePhysicalAcceptanceCertificate A
        strategy hwin tag G outputOne outputTwo env start cuts) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  let word := G.globalMachineTraceWord outputOne outputTwo env
  have htail : A.AcceptsFrom (A.run word start) (OmegaWord.drop word start) :=
    certificate.acceptsFrom A strategy hwin
  exact (A.acceptsFrom_runFrom_drop_iff A.initial word start).mp htail

end
  ProfiledRawJointHybridShadowPhaseLivePhysicalAcceptanceCertificate

/-! ## Policy-free final controller endpoint -/

private abbrev PhysicalController :=
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂

/-- One proof-side hard-regime witness with its dependent tag and cut indices
kept in `Type`.  `Nonempty` of this bundle can be selected while constructing
the physical-acceptance record, unlike a nested existential in `Prop`. -/
private abbrev ShadowPhaseLiveHardCertificateBundle
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) :=
  Σ tag : Tag A strategy hwin, Σ start : Nat, Σ cuts : Nat → Nat,
    ProfiledRawJointHybridShadowPhaseLivePhysicalAcceptanceCertificate A
      strategy hwin tag controller.globalMachine controller.globalOutputOne
        controller.globalOutputTwo env start cuts

/-- The exact per-environment obligations after the delayed tag has been
installed.  The productive regimes may select a proof-side finite tag and
cuts.  The controller itself is already fixed, and the two homogeneous
regimes use the output-only installed-tail interface for that same trace. -/
structure
    ProfiledRawJointHybridShadowPhaseLiveControllerBookkeeping
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) : Prop where
  recurrent : GraphBothRecurrent (fun n ↦ (env n).graph) →
    Nonempty
      (ShadowPhaseLiveHardCertificateBundle A strategy hwin controller env)
  reversal : PersistentStrictReversalTail (fun n ↦ (env n).graph) →
    Nonempty
      (ShadowPhaseLiveHardCertificateBundle A strategy hwin controller env)
  fixed : EventuallyInstalledOutputTailBookkeeping A controller env

namespace ProfiledRawJointHybridShadowPhaseLiveControllerBookkeeping

/-- Forget the root-pinned tail witness after it proves the corresponding
hard regime.  This is the precise adapter that avoids pretending a re-rooted
tail is an ordinary common-root compatible policy. -/
noncomputable def physicalAcceptance
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridShadowPhaseLiveControllerBookkeeping A strategy
        hwin controller env) :
    A.FiniteGlobalMachinePhysicalAcceptance controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo env := by
  let fixed := bookkeeping.fixed.toEventuallyInstalledFixedTailBookkeeping A
  exact {
    recurrent := fun hboth ↦ by
      let bundle := Classical.choice (bookkeeping.recurrent hboth)
      let certificate := bundle.2.2.2
      let direct := A.finiteGlobalMachinePhysicalAcceptance_of_accepts
        controller.globalMachine controller.globalOutputOne
          controller.globalOutputTwo env
            (certificate.accepts A strategy hwin)
      exact direct.recurrent hboth
    alternatingTail := fun hreversal ↦ by
      let bundle := Classical.choice (bookkeeping.reversal hreversal)
      let certificate := bundle.2.2.2
      let direct := A.finiteGlobalMachinePhysicalAcceptance_of_accepts
        controller.globalMachine controller.globalOutputOne
          controller.globalOutputTwo env
            (certificate.accepts A strategy hwin)
      exact direct.alternatingTail hreversal
    strictRightTail := fixed.rightTailParity A
    strictLeftTail := fixed.leftTailParity A }

end ProfiledRawJointHybridShadowPhaseLiveControllerBookkeeping

/-- Final strategy-indexed target for the delayed root-pinned-bank route.
The finite controller is outside the environment quantifier; only tags and
cut witnesses vary with the environment. -/
def PerStrategyWinningShadowPhaseLiveRootPinnedControllerBookkeeping : Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    ∃ controller :
        FinitePairedPhysicalController.{u, v, x, y, w, w}
          In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        ProfiledRawJointHybridShadowPhaseLiveControllerBookkeeping A strategy
          hwin controller env

/-- The policy-free tagged endpoint is already the generic finite physical
controller acceptance premise. -/
theorem
    perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_shadowPhaseLiveRootPinned
    (hbookkeeping :
      PerStrategyWinningShadowPhaseLiveRootPinnedControllerBookkeeping.{u, v,
        x, y, s, w} A) :
    PerStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance.{u, v,
      x, y, s, w} A := by
  intro strategy hwin
  obtain ⟨controller, hcontroller⟩ := hbookkeeping strategy hwin
  refine ⟨controller, fun env ↦ ?_⟩
  exact ⟨(hcontroller env).physicalAcceptance A strategy hwin⟩

/-- Consequently this route reaches the ordinary unconditional readback
endpoint without an ordinary common-root policy witness. -/
theorem exists_readbackUpgrade_of_shadowPhaseLiveRootPinnedController
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hbookkeeping :
      PerStrategyWinningShadowPhaseLiveRootPinnedControllerBookkeeping.{u, v,
        x, y, s, w} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact
    exists_readbackUpgrade_of_finitePairedPhysicalControllerPhysicalAcceptance
      A fallback
        (perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_shadowPhaseLiveRootPinned
          A hbookkeeping)

end

end DetParityAutomaton

end DistributedSynthesis
