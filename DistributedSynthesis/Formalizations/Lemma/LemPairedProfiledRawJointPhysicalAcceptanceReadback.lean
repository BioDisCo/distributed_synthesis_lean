/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefPhysicalAcceptanceSplit
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointLeaderFreeReadback

/-!
# Physical acceptance closes the leader-free readback

This is the final generic consumer of the raw-joint carrier.  The carrier is
already a pair of finite local machines.  Consequently an all-environment
`FiniteGlobalMachinePhysicalAcceptance` proof gives a winning distributed
readback, and hence `ReadbackUpgrade`, directly.  No reachable-belief
uniformity, hierarchy detector, or further finite retraction is required.
-/

namespace DistributedSynthesis

universe u v x y s i₁ i₂ e₁ e₂ k ro lr rr lo

namespace ProfiledRawJointLeaderFreeKernel

variable
  {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
  {InitialOne : Type i₁} {InitialTwo : Type i₂}
  {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
  {ChildCode : Type k}
  {RightOwner : ChildCode → Type ro}
  {LeftReceiver : ChildCode → Type lr}
  {RightReceiver : ChildCode → Type rr}
  {LeftOwner : ChildCode → Type lo}

variable (kernel : ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂
  InitialOne InitialTwo ExceptionalOne ExceptionalTwo ChildCode RightOwner
  LeftReceiver RightReceiver LeftOwner)

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [Fintype InitialOne] [Fintype InitialTwo]
variable [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
variable [Fintype ChildCode]
variable [∀ key, Fintype (RightOwner key)]
variable [∀ key, Fintype (LeftReceiver key)]
variable [∀ key, Fintype (RightReceiver key)]
variable [∀ key, Fintype (LeftOwner key)]

variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- The exact remaining model-facing obligation for a completed leader-free
carrier: its physical global trace satisfies one of the four verified
acceptance packages for every environment. -/
def AllEnvironmentPhysicalAcceptance : Prop :=
  ∀ env : EnvironmentSequence In₁ In₂,
    Nonempty
      (A.FiniteGlobalMachinePhysicalAcceptance kernel.globalMachine
        kernel.globalOutputOne kernel.globalOutputTwo env)

section
omit [Fintype In₁] [Fintype In₂]

/-- The four-way physical regime theorem turns the packaged obligation into
acceptance of every explicit global-machine trace. -/
theorem globalMachine_accepts_of_physicalAcceptance
    (hphysical : kernel.AllEnvironmentPhysicalAcceptance A) :
    ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts
        (kernel.globalMachine.globalMachineTraceWord kernel.globalOutputOne
          kernel.globalOutputTwo env) := by
  intro env
  obtain ⟨physical⟩ := hphysical env
  exact A.finiteGlobalMachineTraceWord_accepts_of_physicalAcceptance
    kernel.globalMachine kernel.globalOutputOne kernel.globalOutputTwo env
      physical

/-- The same handoff in the exact existential shape consumed by
`PerStrategyWinningReadback`.  This is useful when the carrier itself was
constructed after fixing one original winning strategy. -/
theorem exists_winningReadback_of_physicalAcceptance
    (hphysical : kernel.AllEnvironmentPhysicalAcceptance A) :
    ∃ (M : LocalSummaryAutomaton.{u, v,
          max i₁ i₂ e₁ e₂ k ro lr rr lo x y} In₁ In₂)
        (outputOne : M.Summary Proc.one → Out₁)
        (outputTwo : M.Summary Proc.two → Out₂),
      ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts
          (execution (M.readbackStrategy outputOne outputTwo) env) := by
  refine ⟨kernel.summaryAutomaton, kernel.summaryOutputOne,
    kernel.summaryOutputTwo, ?_⟩
  exact kernel.readback_accepts_of_globalMachine A
    (kernel.globalMachine_accepts_of_physicalAcceptance A hphysical)

/-- Final generic handoff: physical acceptance of the actual leader-free
carrier supplies its local-summary `ReadbackUpgrade` in one arrow. -/
theorem summaryAutomaton_readbackUpgrade_of_physicalAcceptance
    (hphysical : kernel.AllEnvironmentPhysicalAcceptance A) :
    kernel.summaryAutomaton.ReadbackUpgrade A :=
  kernel.summaryAutomaton_readbackUpgrade_of_globalMachine A
    (kernel.globalMachine_accepts_of_physicalAcceptance A hphysical)

end

end ProfiledRawJointLeaderFreeKernel

end DistributedSynthesis
