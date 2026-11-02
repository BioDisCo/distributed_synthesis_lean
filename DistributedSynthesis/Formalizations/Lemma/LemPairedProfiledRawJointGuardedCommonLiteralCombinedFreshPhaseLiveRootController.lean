/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveCanonicalTwo
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPendingOnlyInitial

/-!
# The rooted corrected phase-live controller

This file specializes the corrected two-endpoint carrier to its common finite
root.  It exposes the exact-closing law bundle, the finite Mealy controller,
and its Moore presentation used by the readback socket.  The old
`PendingOnly` name below refers only to the reusable root data; the retired
reset-on-every-receive transition is not used.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

/-- Complete exact-closing blind-fork laws at the common root. -/
noncomputable def literalCombinedFreshPhaseLiveRootBlindForkLaws
    (package : Package A strategy hwin (initial := initial)) :=
  (package.literalCombinedFreshPhaseLiveForkLaws A strategy hwin
    (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
    (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
  ).toExactClosingBlindForkLaws

/-- The rooted finite Mealy controller with retained live tables. -/
noncomputable def literalCombinedFreshPhaseLiveRootController
    (package : Package A strategy hwin (initial := initial)) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  package.literalCombinedFreshPhaseLiveController A strategy hwin
    (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
    (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)

/-- Moore-facing finite physical controller consumed by trace extraction. -/
noncomputable def literalCombinedFreshPhaseLiveRootPhysicalController
    (package : Package A strategy hwin (initial := initial)) :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ :=
  (package.literalCombinedFreshPhaseLiveRootController A strategy hwin
    ).mooreize

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end


end DetParityAutomaton

end DistributedSynthesis
