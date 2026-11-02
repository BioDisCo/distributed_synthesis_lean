/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridClosedDirectRegimeEndpoint
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredFixedTailBridge

/-!
# Accepted output tails for payload-linked tables

The older installed-tail interface is intentionally typed by an ordinary
physical sibling move.  The full-restart controller instead executes a
payload-linked literal-prefix table.  Those two finite tables arise from the
same semantic occurrence, but they are different finite values and their
omega words must not be identified.

This file gives the type-neutral adapter required by the linked construction.
An accepted table word is related to the actual controller suffix by its DPA
entry state, environment coordinates, and output pair.  These local facts
recover equality of the complete suffix and therefore acceptance of the
actual word.  No graph direction, hierarchy side, leader bit, or semantic
witness is added to an executable controller.
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

private abbrev Letter := RoundRecord In₁ In₂ Graph Out₁ Out₂

private abbrev PhysicalController :=
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂

private abbrev TraceWord
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) :=
  controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
    controller.globalOutputTwo env

/-! ## One accepted output tail -/

/-- Type-neutral alignment of an accepted proof-side word with an actual
physical suffix.  Separating environment and output equality makes this the
exact consumer of a local output calculation: the graph and input coordinates
normally follow from the proof-side regime and the chosen environment tail. -/
structure AcceptedOutputTailAligned
    (source : A.State) (acceptedWord actualWord : OmegaWord (Letter (In₁ := In₁)
      (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (acceptedCut actualCut : Nat) : Prop where
  accepted : A.AcceptsFrom source acceptedWord
  state : A.run actualWord actualCut =
    A.runFrom source acceptedWord acceptedCut
  environment : ∀ n : Nat,
    (actualWord (actualCut + n)).environment =
      (acceptedWord (acceptedCut + n)).environment
  outputPair : ∀ n : Nat,
    (actualWord (actualCut + n)).outputPair =
      (acceptedWord (acceptedCut + n)).outputPair

namespace AcceptedOutputTailAligned

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Environment and output alignment are equality of the complete suffix. -/
theorem drop_eq
    {source : A.State}
    {acceptedWord actualWord : OmegaWord (Letter (In₁ := In₁)
      (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))}
    {acceptedCut actualCut : Nat}
    (aligned : AcceptedOutputTailAligned A source acceptedWord actualWord
      acceptedCut actualCut) :
    OmegaWord.drop actualWord actualCut =
      OmegaWord.drop acceptedWord acceptedCut := by
  funext n
  apply RoundRecord.eq_of_environment_eq_of_outputPair_eq
  · simpa only [OmegaWord.drop_apply] using aligned.environment n
  · simpa only [OmegaWord.drop_apply] using aligned.outputPair n

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- An accepted aligned suffix makes the complete actual physical word
accepted; parity is insensitive to the discarded finite prefix. -/
theorem accepts
    {source : A.State}
    {acceptedWord actualWord : OmegaWord (Letter (In₁ := In₁)
      (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))}
    {acceptedCut actualCut : Nat}
    (aligned : AcceptedOutputTailAligned A source acceptedWord actualWord
      acceptedCut actualCut) :
    A.Accepts actualWord := by
  have htail :
      A.AcceptsFrom (A.runFrom source acceptedWord acceptedCut)
        (OmegaWord.drop acceptedWord acceptedCut) :=
    (A.acceptsFrom_runFrom_drop_iff source acceptedWord acceptedCut).mpr
      aligned.accepted
  have hactual :
      A.AcceptsFrom (A.run actualWord actualCut)
        (OmegaWord.drop actualWord actualCut) := by
    rw [aligned.state, aligned.drop_eq A]
    exact htail
  exact
    (A.acceptsFrom_runFrom_drop_iff A.initial actualWord actualCut).mp hactual

end AcceptedOutputTailAligned

/-! ## Eventual homogeneous regimes -/

/-- The fixed-regime boundary appropriate for payload-linked tables.

Unlike `EventuallyInstalledOutputTailBookkeeping`, the proof-side accepted
word is not required to come from the older ordinary-sibling table type.  In
the full-restart application it is exactly the linked word returned by
`PairAtPrefix.physicalTail_exists` (or its mixed-sender variant). -/
structure EventuallyAcceptedOutputTailBookkeeping
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) : Prop where
  strictRight : EventuallyStrictRight (fun n ↦ (env n).graph) →
    ∃ (source : A.State) (acceptedWord : OmegaWord (Letter (In₁ := In₁)
        (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
      (acceptedCut actualCut : Nat),
      AcceptedOutputTailAligned A source acceptedWord (TraceWord controller env)
        acceptedCut actualCut
  strictLeft : EventuallyStrictLeft (fun n ↦ (env n).graph) →
    ∃ (source : A.State) (acceptedWord : OmegaWord (Letter (In₁ := In₁)
        (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
      (acceptedCut actualCut : Nat),
      AcceptedOutputTailAligned A source acceptedWord (TraceWord controller env)
        acceptedCut actualCut

namespace EventuallyAcceptedOutputTailBookkeeping

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem accepts_of_strictRight
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping : EventuallyAcceptedOutputTailBookkeeping A controller env)
    (hstrict : EventuallyStrictRight (fun n ↦ (env n).graph)) :
    A.Accepts (TraceWord controller env) := by
  rcases bookkeeping.strictRight hstrict with
    ⟨source, acceptedWord, acceptedCut, actualCut, aligned⟩
  exact aligned.accepts A

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem accepts_of_strictLeft
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping : EventuallyAcceptedOutputTailBookkeeping A controller env)
    (hstrict : EventuallyStrictLeft (fun n ↦ (env n).graph)) :
    A.Accepts (TraceWord controller env) := by
  rcases bookkeeping.strictLeft hstrict with
    ⟨source, acceptedWord, acceptedCut, actualCut, aligned⟩
  exact aligned.accepts A

end EventuallyAcceptedOutputTailBookkeeping

/-! ## Direct hard-regime endpoint -/

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

/-- Closed hard regimes with a type-neutral linked fixed-tail witness. -/
structure ProfiledRawJointHybridLinkedClosedHardRegimeAcceptanceBookkeeping
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) : Prop where
  recurrent : GraphBothRecurrent (fun n ↦ (env n).graph) →
    A.Accepts (TraceWord controller env)
  reversal : PersistentStrictReversalTail (fun n ↦ (env n).graph) →
    A.Accepts (TraceWord controller env)
  fixed : EventuallyAcceptedOutputTailBookkeeping A controller env

namespace ProfiledRawJointHybridLinkedClosedHardRegimeAcceptanceBookkeeping

/-- Forget the proof-side linked tail witness after it has supplied direct
acceptance of the two fixed regimes.  This is the exact handoff to the
repository's shortest unconditional endpoint. -/
noncomputable def toClosedDirect
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridLinkedClosedHardRegimeAcceptanceBookkeeping A
        controller env) :
    ProfiledRawJointHybridClosedDirectRegimeAcceptanceBookkeeping A controller
      env where
  recurrent := bookkeeping.recurrent
  reversal := bookkeeping.reversal
  strictRight := bookkeeping.fixed.accepts_of_strictRight A
  strictLeft := bookkeeping.fixed.accepts_of_strictLeft A

/-- Direct acceptance in the productive regimes and accepted linked suffixes
in the homogeneous regimes fill the standard four-way physical package. -/
noncomputable def physicalAcceptance
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridLinkedClosedHardRegimeAcceptanceBookkeeping A
        controller env) :
    A.FiniteGlobalMachinePhysicalAcceptance controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo env :=
  (bookkeeping.toClosedDirect A).physicalAcceptance A

end ProfiledRawJointHybridLinkedClosedHardRegimeAcceptanceBookkeeping

end

end DetParityAutomaton

end DistributedSynthesis
