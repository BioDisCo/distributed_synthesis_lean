/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPhysicalPolicyClose
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefEpochAcceptance

/-!
# Physical epoch acceptance from one raw-joint policy path

The recurrent physical construction and the finite raw-joint policy use two
different clocks.  This file records the exact acceptance seam between them.
At policy clock `n`, `state n` is one state of a *single* rational policy; an
edge may choose any member of that policy state's finite `AllowedTarget`
image.  Consequently the positive-time code word is accepted by the
raw-joint code DPA.  This is the anti-mosaic fact needed after local block
narrowing.

The only remaining physical obligation is pointwise: the minimum original
DPA priority in physical epoch `k` must equal the priority of one fixed hidden
alternating thread at the corresponding code time.  Once that equality is
available, ordinary parity pasting proves acceptance of the emitted physical
trace.

The hidden side is proof data of the objective monitor.  It is not an input
to either process and does not reveal a strict leader or graph orientation.
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

private abbrev RawCode :=
  ProfiledRawJointIncidenceCode A (I := Unit)

private abbrev RawPolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : RawCode A) :=
  ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy initialCode

private abbrev RawPolicyState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : RawCode A) :=
  ProfiledRawJointOneSidedProvenancePolicyState A strategy initialCode

private abbrev RawThreadSystem (initialCode : RawCode A) :=
  codedAlternatingIndexedLineageCodeThreadSystem initialCode
    (profiledRawJointOneSidedCurrentSlots A)
    (profiledRawJointThreadRootPriority A)

/-- Exact coupling between a root-started path in one raw-joint policy and
the physical epochs emitted by a finite global machine.  `offset` removes a
finite prefix of the hidden code thread; `start` independently removes a
finite prefix of the physical trace (in particular, the exceptional guarded
first block may live before `start`). -/
structure ProfiledRawJointUnitPolicyEpochCoupling
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : RawCode A)
    (policy : RawPolicy A strategy initialCode)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) where
  state : Nat → RawPolicyState A strategy initialCode
  initial : state 0 = policy.run []
  allowed : ∀ n : Nat,
    ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy initialCode
      policy (state n) (state (n + 1))
  initialSide : IndexedLineageSide
  offset : Nat
  start : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  blockMin_eq_threadPriority : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts k =
      (RawThreadSystem A initialCode).priority
        (codedAlternatingIndexedLineageCodeRun initialCode
          (profiledRawJointOneSidedCurrentSlots A)
          (fun n ↦ (state (n + 1)).1)
          initialSide () (offset + k))

namespace ProfiledRawJointUnitPolicyEpochCoupling

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every root-started `AllowedTarget` path in the fixed raw policy supplies
parity of the exact hidden alternating thread selected by the coupling. -/
theorem threadParity
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : RawCode A}
    {policy : RawPolicy A strategy initialCode}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    (coupling : ProfiledRawJointUnitPolicyEpochCoupling A strategy
      initialCode policy G outputOne outputTwo env) :
    NatSeqMinEvenParity (fun k ↦
      (RawThreadSystem A initialCode).priority
        (codedAlternatingIndexedLineageCodeRun initialCode
          (profiledRawJointOneSidedCurrentSlots A)
          (fun n ↦ (coupling.state (n + 1)).1)
          coupling.initialSide () (coupling.offset + k))) := by
  have hcode :
      (profiledRawJointOneSidedCodeParityDPA A initialCode).Accepts
        (fun n ↦ (coupling.state (n + 1)).1) :=
    SourceFreeBeliefFiniteCodePolicyImage.accepts_of_allowedTarget_path
      (profiledRawJointOneSidedCodeParityDPA A initialCode)
      initialCode
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedNext A)
      policy coupling.state coupling.initial coupling.allowed
  have hall : ∀ initialSide lineage,
      NatSeqMinEvenParity (fun n ↦
        (RawThreadSystem A initialCode).priority
          (codedAlternatingIndexedLineageCodeRun initialCode
            (profiledRawJointOneSidedCurrentSlots A)
            (fun k ↦ (coupling.state (k + 1)).1)
            initialSide lineage n)) := by
    exact (codedAlternatingIndexedLineageCodeDPA_accepts_iff initialCode
      (profiledRawJointOneSidedCurrentSlots A)
      (profiledRawJointThreadRootPriority A)
      (fun n ↦ (coupling.state (n + 1)).1)).mp hcode
  exact (natSeqMinEvenParity_shift
    (fun n ↦
      (RawThreadSystem A initialCode).priority
        (codedAlternatingIndexedLineageCodeRun initialCode
          (profiledRawJointOneSidedCurrentSlots A)
          (fun k ↦ (coupling.state (k + 1)).1)
          coupling.initialSide () n)) coupling.offset).mpr
      (hall coupling.initialSide ())

/-- Forget the raw policy presentation and expose the generic physical epoch
coupling consumed by parity pasting. -/
noncomputable def toFiniteGlobalMachineEpochCoupling
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : RawCode A}
    {policy : RawPolicy A strategy initialCode}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    (coupling : ProfiledRawJointUnitPolicyEpochCoupling A strategy
      initialCode policy G outputOne outputTwo env) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env where
  start := coupling.start
  cuts := coupling.cuts
  cuts_strictMono := coupling.cuts_strictMono
  cuts_zero := coupling.cuts_zero
  epochPriority := fun k ↦
    (RawThreadSystem A initialCode).priority
      (codedAlternatingIndexedLineageCodeRun initialCode
        (profiledRawJointOneSidedCurrentSlots A)
        (fun n ↦ (coupling.state (n + 1)).1)
        coupling.initialSide () (coupling.offset + k))
  epochParity := coupling.threadParity A
  blockMin_eq_epochPriority := coupling.blockMin_eq_threadPriority

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A coherent fixed-policy path plus the pointwise physical block-minimum
law proves acceptance of the finite global machine's actual trace. -/
theorem physicalTrace_accepts
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : RawCode A}
    {policy : RawPolicy A strategy initialCode}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    (coupling : ProfiledRawJointUnitPolicyEpochCoupling A strategy
      initialCode policy G outputOne outputTwo env) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling G outputOne
    outputTwo env (coupling.toFiniteGlobalMachineEpochCoupling A)

end ProfiledRawJointUnitPolicyEpochCoupling

end

end DetParityAutomaton

end DistributedSynthesis
