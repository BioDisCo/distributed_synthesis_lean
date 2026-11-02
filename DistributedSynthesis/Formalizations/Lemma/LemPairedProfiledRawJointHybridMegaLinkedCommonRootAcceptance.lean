/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedCommonRootTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartCutPhysicalPacket

/-!
# Acceptance bookkeeping for the mega-linked common-root branch

The simultaneous front handoff is locally indistinguishable from either
one-sided handoff.  Its two endpoint controls therefore resolve to a common
root whose receiver-anchor metadata can differ from the ordinary
`FullRestart` initialization.  This file shows that the semantic run still
has the same authoritative-parent and fresh-restart structure at every strict
orientation switch.  These facts are the input to the parity cut splice.
-/

namespace DistributedSynthesis

universe u v x y s

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

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev LinkedOne :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
    A strategy hwin

private abbrev LinkedTwo :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
    A strategy hwin

/-- Process one's receive-normalized linked state in the common-root semantic
run. -/
noncomputable def profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    LinkedOne A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin tag
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
    A strategy hwin fallback.1
      (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
        tag env n).1

/-- Process-two mirror. -/
noncomputable def profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    LinkedTwo A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin tag
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
    A strategy hwin fallback.2
      (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
        tag env n).2

/-- Authoritative bank parent selected at time `n`. -/
noncomputable def profiledRawJointHybridMegaLinkedCommonRootParentAt
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    BankControl A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
    A strategy hwin
      (profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt A strategy hwin
        tag env n)
      (profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt A strategy hwin
        tag env n)

/-- Receiver-selected right relay at time `n`. -/
noncomputable def profiledRawJointHybridMegaLinkedCommonRootRightBaseAt
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
    A strategy hwin
      (profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt A strategy hwin
        tag env n)
      (profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt A strategy hwin
        tag env n)

/-- Receiver-selected left relay at time `n`. -/
noncomputable def profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
    A strategy hwin
      (profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt A strategy hwin
        tag env n)
      (profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt A strategy hwin
        tag env n)

@[simp] theorem profiledRawJointHybridMegaLinkedCommonRootParentAt_zero
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag env
        0 = tag.1 := by
  rfl

/-- After a left round, the common-root run selects a fresh right relay at
its authoritative parent. -/
theorem profiledRawJointHybridMegaLinkedCommonRootRightBaseAt_succ_of_left
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .left) :
    profiledRawJointHybridMegaLinkedCommonRootRightBaseAt A strategy hwin tag
        env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin
          (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin
            tag env (n + 1)) false false := by
  have hbits :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt_succ_selected_lastRecv
      A strategy hwin tag env n
  rw [hgraph] at hbits
  have hone :
      (profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt A strategy hwin
        tag env (n + 1)).2.1 = true := by
    simpa [profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt,
      profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt] using hbits.1
  have htwo :
      (profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt A strategy hwin
        tag env (n + 1)).2.1 = false := by
    simpa [profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt,
      profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt] using hbits.2
  simp [profiledRawJointHybridMegaLinkedCommonRootRightBaseAt,
    profiledRawJointHybridMegaLinkedCommonRootParentAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
    hone, htwo]

/-- After a right round, left mirror. -/
theorem profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt_succ_of_right
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .right) :
    profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin
          (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin
            tag env (n + 1)) false false := by
  have hbits :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt_succ_selected_lastRecv
      A strategy hwin tag env n
  rw [hgraph] at hbits
  have hone :
      (profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt A strategy hwin
        tag env (n + 1)).2.1 = false := by
    simpa [profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt,
      profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt] using hbits.1
  have htwo :
      (profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt A strategy hwin
        tag env (n + 1)).2.1 = true := by
    simpa [profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt,
      profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt] using hbits.2
  simp [profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt,
    profiledRawJointHybridMegaLinkedCommonRootParentAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
    hone, htwo]

end


end DetParityAutomaton

end DistributedSynthesis
