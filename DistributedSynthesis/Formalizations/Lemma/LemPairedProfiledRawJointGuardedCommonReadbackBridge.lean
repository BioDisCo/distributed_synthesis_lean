/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTargetFamily
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointPhysicalRegimeReadback

/-!
# The exact readback endpoint below the guarded-common target family

The guarded common construction now supplies a finite global target alphabet,
one fixed rational recurrent policy at every target, and literal oriented root
installers at every checked strict close.  The generic indexed kernel consumes
that data once its finite front transition table is supplied.

This file records the shortest remaining chain without hiding any premise:

1. a `ProfiledRawJointGuardedCommonTargetExceptionalAdapter` supplies the six
   genuinely local front maps (`initialNoRecvOne/Two`,
   `exceptionalNoRecvOne/Two`, and `otherRecvOne/Two`);
2. the already constructed indexed recurrent table completes the leader-free
   physical kernel;
3. acceptance of its actual trace in the five exhaustive proof-side regimes
   yields `ReadbackUpgrade` for its finite local-summary automaton.

The regime split is used only in proofs.  Neither the adapter nor the kernel
receives a graph, orientation, hierarchy side, leader bit, semantic world, or
history as executable input.
-/

namespace DistributedSynthesis

universe u v x y s i₁ i₂ e₁ e₂

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

/-! ## The exact remaining finite-front and acceptance package -/

/-- A concise package for the two inputs still required after the global
guarded target family has been constructed.  `adapter` is executable local
data.  `detailedAcceptance` is a proof about the resulting physical trace;
its graph regimes are not available to either process at runtime. -/
structure ProfiledRawJointGuardedCommonReadbackCompletion
    (InitialOne : Type i₁) (InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂)
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo] where
  adapter : ProfiledRawJointGuardedCommonTargetExceptionalAdapter A strategy
    hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo
  detailedAcceptance :
    (profiledRawJointGuardedCommonTargetLeaderFreeKernel A strategy hwin
      adapter).AllEnvironmentDetailedRegimeAcceptance A

namespace ProfiledRawJointGuardedCommonReadbackCompletion

variable {InitialOne : Type i₁} {InitialTwo : Type i₂}
  {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
variable [Fintype InitialOne] [Fintype InitialTwo]
  [Fintype ExceptionalOne] [Fintype ExceptionalTwo]

/-- The concrete leader-free kernel selected by a completed guarded front. -/
noncomputable abbrev kernel
    (completion : ProfiledRawJointGuardedCommonReadbackCompletion A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :=
  profiledRawJointGuardedCommonTargetLeaderFreeKernel A strategy hwin
    completion.adapter

/-- The shortest exact bridge to the existing local-summary readback API. -/
theorem readbackUpgrade
    (completion : ProfiledRawJointGuardedCommonReadbackCompletion A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :
    completion.kernel A strategy hwin |>.summaryAutomaton.ReadbackUpgrade A :=
  (completion.kernel A strategy hwin
    ).summaryAutomaton_readbackUpgrade_of_detailedRegimeAcceptance A
      completion.detailedAcceptance

/-- Outer-existential form consumed by the star-summary and synthesis endpoint
reductions.  The witness is the finite summary automaton of the completed
leader-free kernel. -/
theorem exists_readbackUpgrade
    (completion : ProfiledRawJointGuardedCommonReadbackCompletion A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :
    ∃ M : LocalSummaryAutomaton.{u, v,
        max s u v x y i₁ i₂ e₁ e₂} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact ⟨(completion.kernel A strategy hwin).summaryAutomaton,
    completion.readbackUpgrade A strategy hwin⟩

end ProfiledRawJointGuardedCommonReadbackCompletion

/-! ## Unbundled one-arrow forms -/

variable {InitialOne : Type i₁} {InitialTwo : Type i₂}
  {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
variable [Fintype InitialOne] [Fintype InitialTwo]
  [Fintype ExceptionalOne] [Fintype ExceptionalTwo]

/-- Direct form for callers that already have the concrete front adapter and
the five physical regime proofs. -/
theorem profiledRawJointGuardedCommonTarget_readbackUpgrade
    (adapter : ProfiledRawJointGuardedCommonTargetExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (hdetailed :
      (profiledRawJointGuardedCommonTargetLeaderFreeKernel A strategy hwin
        adapter).AllEnvironmentDetailedRegimeAcceptance A) :
    (profiledRawJointGuardedCommonTargetLeaderFreeKernel A strategy hwin
      adapter).summaryAutomaton.ReadbackUpgrade A :=
  (profiledRawJointGuardedCommonTargetLeaderFreeKernel A strategy hwin adapter
    ).summaryAutomaton_readbackUpgrade_of_detailedRegimeAcceptance A hdetailed

/-- Direct outer-existential endpoint for the unconditional main reduction. -/
theorem exists_profiledRawJointGuardedCommonTarget_readbackUpgrade
    (adapter : ProfiledRawJointGuardedCommonTargetExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (hdetailed :
      (profiledRawJointGuardedCommonTargetLeaderFreeKernel A strategy hwin
        adapter).AllEnvironmentDetailedRegimeAcceptance A) :
    ∃ M : LocalSummaryAutomaton.{u, v,
        max s u v x y i₁ i₂ e₁ e₂} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact ⟨_, profiledRawJointGuardedCommonTarget_readbackUpgrade A strategy
    hwin adapter hdetailed⟩

end

end DetParityAutomaton

end DistributedSynthesis
