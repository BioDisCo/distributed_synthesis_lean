/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedHybridCombinedFamily
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointPhysicalRegimeReadback

/-!
# Readback below the combined old-front and guarded-common recurrent family

The combined family contains both the five established hybrid mega entry
classes and every target generated after a guarded common strict close.  The
generic indexed kernel supplies all recurrent transitions uniformly over this
sum.  This file records the exact conditional endpoint left to the finite
front:

* its genuinely local exceptional adapter supplies the six front maps;
* acceptance of the resulting actual physical trace is proved in the five
  exhaustive proof-side graph regimes;
* the existing physical readback theorem yields `ReadbackUpgrade`, and hence
  the outer existential consumed by the star and synthesis endpoint reductions.

The regime split is proof-only.  No executable map introduced or consumed
here receives a graph, orientation, hierarchy side, leader bit, semantic
world, or history.
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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

/-! ## Bundled exact completion premise -/

/-- Exactly the two objects still owed above the combined recurrent family:
the finite local front table and proof that the resulting actual trace accepts
in every exhaustive regime. -/
structure ProfiledRawJointGuardedHybridCombinedReadbackCompletion
    (InitialOne : Type i₁) (InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂)
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo] where
  adapter : ProfiledRawJointGuardedHybridCombinedExceptionalAdapter A strategy
    hwin initialBank InitialOne InitialTwo ExceptionalOne ExceptionalTwo
  detailedAcceptance :
    (profiledRawJointGuardedHybridCombinedLeaderFreeKernel A strategy hwin
      initialBank adapter).AllEnvironmentDetailedRegimeAcceptance A

namespace ProfiledRawJointGuardedHybridCombinedReadbackCompletion

variable {InitialOne : Type i₁} {InitialTwo : Type i₂}
  {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
variable [Fintype InitialOne] [Fintype InitialTwo]
  [Fintype ExceptionalOne] [Fintype ExceptionalTwo]

/-- The concrete leader-free kernel determined by this completion package. -/
noncomputable abbrev kernel
    (completion :
      ProfiledRawJointGuardedHybridCombinedReadbackCompletion A strategy hwin
        initialBank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :=
  profiledRawJointGuardedHybridCombinedLeaderFreeKernel A strategy hwin
    initialBank completion.adapter

/-- One-arrow endpoint at the fixed finite local-summary automaton. -/
theorem readbackUpgrade
    (completion :
      ProfiledRawJointGuardedHybridCombinedReadbackCompletion A strategy hwin
        initialBank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :
    (completion.kernel A strategy hwin initialBank
      ).summaryAutomaton.ReadbackUpgrade A :=
  (completion.kernel A strategy hwin initialBank
    ).summaryAutomaton_readbackUpgrade_of_detailedRegimeAcceptance A
      completion.detailedAcceptance

/-- Outer-existential endpoint used directly by the star-summary and synthesis endpoint
reductions. -/
theorem exists_readbackUpgrade
    (completion :
      ProfiledRawJointGuardedHybridCombinedReadbackCompletion A strategy hwin
        initialBank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :
    ∃ M : LocalSummaryAutomaton.{u, v,
        max s u v x y i₁ i₂ e₁ e₂} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact ⟨(completion.kernel A strategy hwin initialBank).summaryAutomaton,
    completion.readbackUpgrade A strategy hwin initialBank⟩

end ProfiledRawJointGuardedHybridCombinedReadbackCompletion

/-! ## Unbundled forms for the eventual concrete front -/

variable {InitialOne : Type i₁} {InitialTwo : Type i₂}
  {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
variable [Fintype InitialOne] [Fintype InitialTwo]
  [Fintype ExceptionalOne] [Fintype ExceptionalTwo]

/-- Direct fixed-summary endpoint from a concrete front and its five regime
proofs. -/
theorem profiledRawJointGuardedHybridCombined_readbackUpgrade
    (adapter : ProfiledRawJointGuardedHybridCombinedExceptionalAdapter A
      strategy hwin initialBank InitialOne InitialTwo ExceptionalOne
      ExceptionalTwo)
    (hdetailed :
      (profiledRawJointGuardedHybridCombinedLeaderFreeKernel A strategy hwin
        initialBank adapter).AllEnvironmentDetailedRegimeAcceptance A) :
    (profiledRawJointGuardedHybridCombinedLeaderFreeKernel A strategy hwin
      initialBank adapter).summaryAutomaton.ReadbackUpgrade A :=
  (profiledRawJointGuardedHybridCombinedLeaderFreeKernel A strategy hwin
    initialBank adapter
    ).summaryAutomaton_readbackUpgrade_of_detailedRegimeAcceptance A hdetailed

/-- Direct outer-existential endpoint for the unconditional main reduction. -/
theorem exists_profiledRawJointGuardedHybridCombined_readbackUpgrade
    (adapter : ProfiledRawJointGuardedHybridCombinedExceptionalAdapter A
      strategy hwin initialBank InitialOne InitialTwo ExceptionalOne
      ExceptionalTwo)
    (hdetailed :
      (profiledRawJointGuardedHybridCombinedLeaderFreeKernel A strategy hwin
        initialBank adapter).AllEnvironmentDetailedRegimeAcceptance A) :
    ∃ M : LocalSummaryAutomaton.{u, v,
        max s u v x y i₁ i₂ e₁ e₂} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact ⟨_, profiledRawJointGuardedHybridCombined_readbackUpgrade A strategy
    hwin initialBank adapter hdetailed⟩

end

end DetParityAutomaton

end DistributedSynthesis
