/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedStrictRecurrentHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshRightActivationReduction

/-!
# What the fixed-first persistent bank does, and does not, synchronize

The old root-pinned construction selects one guarded policy for a fixed first
input pair and keeps every later strict macro inside that policy.  Its local
switch maps have an unconditional useful property: at one reversal, the two
endpoints restart at literally the same complete guarded child.  The first
two theorems below expose this fact in the existential shape used by a joint
representation.

This does not by itself identify the blind output of the table retained by the
combined pending control with the blind output of the recurrent controller.
Those controllers were rationalized by two different choices.  Equality of
their guarded child index therefore removes policy-state mosaic, but not the
cross-rationalization output seam.

`LiteralCombinedFreshRightActivationPhysicalMoveJointPreselection` names the
remaining one-reversal datum without asking for equality of policies,
complete lambdas, receiver alphabets, or controller types.  It asks only that
the two policy-state roots project their blind outputs through one already
finite `ProfiledRawJointRightPhysicalSiblingMove`.  The final theorem proves
that this joint preselection discharges the exact live-stage bridge.

Thus enriching the pre-rational move label by the existing physical sibling
move is sufficient for this equality, provided the two sibling policy states
retain the same enrichment.  Merely attaching independently chosen physical
moves after rationalization is not such a preselection.

No definition in this file receives a graph, orientation, hierarchy side,
leader bit, history, or semantic view as executable input.
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

/-! ## The old bank already gives one joint guarded state at a reversal -/

/-- At a right-to-left reversal, the independently executable fixed-first
restart maps admit one common complete guarded child.  In particular, the
per-state controller-bank choice does not split the owner and receiver child
indices at the restart itself. -/
theorem
    exists_profiledRawJointHybridRootPinnedStrictStartLeft_jointPolicyState
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver :
      ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy hwin child)
    (move : In₁ × In₂) :
    ∃ next : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin,
      (profiledRawJointHybridRootPinnedStrictStartLeftReceiver A strategy hwin
          child receiver move).2.1 = next ∧
        (profiledRawJointHybridRootPinnedStrictStartLeftOwner A strategy hwin
          child receiver move.2).2.1 = next := by
  let next :=
    (profiledRawJointHybridRootPinnedStrictStartLeftReceiver A strategy hwin
      child receiver move).2.1
  refine ⟨next, rfl, ?_⟩
  exact
    (profiledRawJointHybridRootPinnedStrictStartLeft_commonChild A strategy
      hwin child receiver move).symm

/-- Left-to-right mirror of the joint policy-state restart. -/
theorem
    exists_profiledRawJointHybridRootPinnedStrictStartRight_jointPolicyState
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver :
      ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin child)
    (move : In₂ × In₁) :
    ∃ next : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin,
      (profiledRawJointHybridRootPinnedStrictStartRightOwner A strategy hwin
          child receiver move.2).2.1 = next ∧
        (profiledRawJointHybridRootPinnedStrictStartRightReceiver A strategy
          hwin child receiver move).2.1 = next := by
  let next :=
    (profiledRawJointHybridRootPinnedStrictStartRightOwner A strategy hwin
      child receiver move.2).2.1
  refine ⟨next, rfl, ?_⟩
  exact
    (profiledRawJointHybridRootPinnedStrictStartRight_commonChild A strategy
      hwin child receiver move).symm

/-! ## One physical move is enough to synchronize the two blind roots -/

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev Key {initial : CommonPoint A strategy}
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin package

/-- The exact remaining positive datum at a blind right activation.

The pending root and the recurrent root may have different receiver alphabets
and need not be equal controls.  Joint preselection asks only that their
process-one sender projections are the two hidden-member projections of one
finite right physical sibling move at its common root control.  Since those
two projections are definitionally the same controller, this is exactly the
finite table ID which must be retained before the two policy states are
rationalized. -/
structure LiteralCombinedFreshRightActivationPhysicalMoveJointPreselection
    {initial : CommonPoint A strategy}
    (package : Package A strategy hwin initial)
    (freshKey : Key A strategy hwin package)
    (stageKey : Key A strategy hwin package) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (recordInput : In₁ × In₂) where
  physicalMove : ProfiledRawJointRightPhysicalSiblingMove A
  pending_root : ∀ input : In₁,
    (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
        (package.literalLeftSeamStagedSenderInitial A strategy hwin freshKey)
        input).1 =
      (((physicalMove.memberController A false).labelOf
        (physicalMove.memberController A false).initial).1 input)
  recurrent_root : ∀ input : In₁,
    (package.literalRightSeamTaggedNoRecvOne A strategy hwin
        (package.literalRightSeamTaggedMatched A strategy hwin stageKey row
          past recordInput).1 input).2 =
      (((physicalMove.memberController A true).labelOf
        (physicalMove.memberController A true).initial).1 input)

/-- A single preselected finite physical move closes the exact live-stage
root bridge.  The middle equality is definitional: the hidden member is not
consulted by `memberController`. -/
theorem
    LiteralCombinedFreshRightActivationPhysicalMoveJointPreselection.toRootBridge
    {initial : CommonPoint A strategy}
    {package : Package A strategy hwin initial}
    {freshKey : Key A strategy hwin package}
    {stageKey : Key A strategy hwin package} {row : PairedEntryRow}
    {past : List (In₁ × In₂)} {recordInput : In₁ × In₂}
    (preselection :
      LiteralCombinedFreshRightActivationPhysicalMoveJointPreselection A
        strategy hwin package freshKey stageKey row past recordInput) :
    package.LiteralCombinedFreshRightActivationRootBridge A strategy hwin
      freshKey stageKey row past recordInput := by
  intro input
  calc
    (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
        (package.literalLeftSeamStagedSenderInitial A strategy hwin freshKey)
        input).1 =
        (((preselection.physicalMove.memberController A false).labelOf
          (preselection.physicalMove.memberController A false).initial).1
            input) := preselection.pending_root input
    _ = (((preselection.physicalMove.memberController A true).labelOf
          (preselection.physicalMove.memberController A true).initial).1
            input) := rfl
    _ = (package.literalRightSeamTaggedNoRecvOne A strategy hwin
          (package.literalRightSeamTaggedMatched A strategy hwin stageKey row
            past recordInput).1 input).2 :=
      (preselection.recurrent_root input).symm

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
