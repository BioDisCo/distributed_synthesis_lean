/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodePolicyPathAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceCodePolicyInstall
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefEpochAcceptance

/-!
# Physical epoch acceptance from one indexed-code policy path

The indexed-code rational policy and the physical round machine live at two
different clocks.  This file gives their exact safe acceptance handoff.

The policy contribution is anti-mosaic: one sequence of finite policy states
must start at the rational-policy root and follow its literal successor at
every epoch.  Its positive-time code word is therefore accepted by the
code-observable DPA.  That DPA checks every fixed alternating side/lineage
thread.

The physical contribution is deliberately only the pointwise pasting law:
the minimum original-DPA priority of physical epoch `k` must equal the
priority of one fixed code thread at the corresponding policy time.  No
unrelated fixed-policy root monitor can discharge this equation.  Conversely,
once the equation is proved, ordinary parity pasting closes acceptance.

All sides, lineages, and offsets below are proof data.  They are never passed
to a process and do not provide a leader, orientation, or hidden-bit signal.
-/

namespace DistributedSynthesis

universe i u v w x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

private abbrev CodeDPA
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  profiledOpenIndexedBiBeliefCodeParityDPA A initialCode

private abbrev CodePolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin basis
    initialCode

private abbrev CodePolicyPath
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : CodePolicy A strategy hwin basis initialCode) :=
  SourceFreeBeliefCodeParityPolicyPath
    (CodeDPA A initialCode) initialCode
    (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
    (profiledOpenIndexedBiBeliefNextFiniteTag A) policy

private abbrev CodeThreadSystem
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  codedAlternatingIndexedLineageCodeThreadSystem initialCode
    (profiledOpenIndexedBiBeliefCurrentSlots A)
    (profiledOpenIndexedRootPriority A)

/-- Exact coupling between one coherent indexed-code policy path and the
physical epochs emitted by a finite global machine.  `offset` discards the
harmless finite prefix of the hidden code thread (normally its initial
state); `start` independently discards a finite physical prefix. -/
structure ProfiledOpenIndexedCodePolicyEpochCoupling
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : CodePolicy A strategy hwin basis initialCode)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) where
  path : CodePolicyPath A strategy hwin basis initialCode policy
  initialSide : IndexedLineageSide
  lineage : I
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
      (CodeThreadSystem A initialCode).priority
        (profiledOpenIndexedBiBeliefCodeParityRun A initialCode
          (path.childCodeWord (CodeDPA A initialCode) initialCode
            (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
            (profiledOpenIndexedBiBeliefNextFiniteTag A) policy)
          initialSide lineage (offset + k))

namespace ProfiledOpenIndexedCodePolicyEpochCoupling

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The coherent rational-policy path supplies parity of the exact hidden
code thread named by the coupling. -/
theorem threadParity
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    {policy : CodePolicy A strategy hwin basis initialCode}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    (coupling : ProfiledOpenIndexedCodePolicyEpochCoupling A strategy hwin
      basis initialCode policy G outputOne outputTwo env) :
    NatSeqMinEvenParity (fun k ↦
      (CodeThreadSystem A initialCode).priority
        (profiledOpenIndexedBiBeliefCodeParityRun A initialCode
          (coupling.path.childCodeWord (CodeDPA A initialCode) initialCode
            (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
            (profiledOpenIndexedBiBeliefNextFiniteTag A) policy)
          coupling.initialSide coupling.lineage (coupling.offset + k))) := by
  have hcode :
      (CodeDPA A initialCode).Accepts
        (coupling.path.childCodeWord (CodeDPA A initialCode) initialCode
          (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
          (profiledOpenIndexedBiBeliefNextFiniteTag A) policy) :=
    coupling.path.accepts (CodeDPA A initialCode) initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) policy
  have hall :=
    (profiledOpenIndexedBiBeliefCodeParityDPA_accepts_iff A initialCode
      (coupling.path.childCodeWord (CodeDPA A initialCode) initialCode
        (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
        (profiledOpenIndexedBiBeliefNextFiniteTag A) policy)).mp hcode
  exact (natSeqMinEvenParity_shift
    (fun n ↦
      (CodeThreadSystem A initialCode).priority
        (profiledOpenIndexedBiBeliefCodeParityRun A initialCode
          (coupling.path.childCodeWord (CodeDPA A initialCode) initialCode
            (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
            (profiledOpenIndexedBiBeliefNextFiniteTag A) policy)
          coupling.initialSide coupling.lineage n)) coupling.offset).mpr
      (hall coupling.initialSide coupling.lineage)

/-- Forget the code-policy presentation and expose the ordinary physical
epoch coupling consumed by parity pasting. -/
noncomputable def toFiniteGlobalMachineEpochCoupling
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    {policy : CodePolicy A strategy hwin basis initialCode}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    (coupling : ProfiledOpenIndexedCodePolicyEpochCoupling A strategy hwin
      basis initialCode policy G outputOne outputTwo env) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env where
  start := coupling.start
  cuts := coupling.cuts
  cuts_strictMono := coupling.cuts_strictMono
  cuts_zero := coupling.cuts_zero
  epochPriority := fun k ↦
    (CodeThreadSystem A initialCode).priority
      (profiledOpenIndexedBiBeliefCodeParityRun A initialCode
        (coupling.path.childCodeWord (CodeDPA A initialCode) initialCode
          (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
          (profiledOpenIndexedBiBeliefNextFiniteTag A) policy)
        coupling.initialSide coupling.lineage (coupling.offset + k))
  epochParity := coupling.threadParity A
  blockMin_eq_epochPriority := coupling.blockMin_eq_threadPriority

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- One coherent policy path plus the pointwise physical block-minimum law is
sufficient for acceptance of the finite global machine's actual trace. -/
theorem physicalTrace_accepts
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    {policy : CodePolicy A strategy hwin basis initialCode}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    (coupling : ProfiledOpenIndexedCodePolicyEpochCoupling A strategy hwin
      basis initialCode policy G outputOne outputTwo env) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling G outputOne
    outputTwo env (coupling.toFiniteGlobalMachineEpochCoupling A)

end ProfiledOpenIndexedCodePolicyEpochCoupling

end

end DetParityAutomaton

end DistributedSynthesis
