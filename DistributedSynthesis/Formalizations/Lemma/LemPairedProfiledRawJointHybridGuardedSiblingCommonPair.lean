/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridGuardedSiblingLocalInstallation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonPairCarrier

/-!
# One represented common pair behind every hybrid guarded installation

The finite hybrid installation alphabet distinguishes the exceptional table
below the first common root from tables below recurrent root-pinned common
controls.  Semantically, however, both cases are obtained by extracting the
right and left guarded sibling moves from one literal common world.

This file records that common representation.  It lets the generic guarded
common-pair front and its strict-reachability theorems consume the newer
root-pinned installation without selecting another representative or policy.
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

private abbrev Installation :=
  ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin

/-! ## Literal represented pair -/

/-- The one guarded common pair whose projections are the two moves stored by
the hybrid installation. -/
noncomputable def profiledRawJointHybridGuardedCommonPairAt
    (installation : Installation A strategy hwin) :
    ProfiledRawJointGuardedCommonPair A strategy hwin :=
  match installation with
  | .inl initial =>
      profiledRawJointGuardedCommonPairOfWorld A strategy hwin
        (ProfiledRawJointHybridInitialRootPinnedWorld A strategy
          initial.first)
        initial.current
  | .inr recurrent =>
      profiledRawJointGuardedCommonPairOfWorld A strategy hwin
        (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin
          recurrent.1).world
        recurrent.2

/-- Its right projection is exactly the move selected by the installation. -/
theorem profiledRawJointHybridGuardedCommonPairAt_right
    (installation : Installation A strategy hwin) :
    (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation).1.1 =
      profiledRawJointHybridGuardedRightMoveAt A strategy hwin
        installation := by
  cases installation with
  | inl initial =>
      rfl
  | inr recurrent =>
      rfl

/-- Left-projection mirror. -/
theorem profiledRawJointHybridGuardedCommonPairAt_left
    (installation : Installation A strategy hwin) :
    (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation).1.2 =
      profiledRawJointHybridGuardedLeftMoveAt A strategy hwin
        installation := by
  cases installation with
  | inl initial =>
      rfl
  | inr recurrent =>
      rfl

end

end DetParityAutomaton

end DistributedSynthesis
