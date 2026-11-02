/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenInitialOverlayWinningExtension

/-!
# Physical priority of a zero-open installed overlay

A witnessed overlay whose query is reset to the empty-word controller and
monitor state follows, for every finite physical input prefix, the retained
member play stored in its pinned family.  Consequently the advertised closing
root of that literal overlay carries exactly the original-DPA minimum of the
records emitted during the prefix.

This is the maximal per-epoch consequence of the current re-anchoring
interface.  It deliberately does not identify the closing root with the raw
child root computed by a separately extracted finite direction table.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

set_option maxHeartbeats 1600000

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-! ## Exact member-play trace -/

/-- At an empty-word query, the retained right member play is exactly the
finite overlay execution, at every position. -/
theorem profiledOpenWitnessedRightMemberBasePlay_eq_overlayRun
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (hquery : overlay.query =
      profiledOpenFixedRightInitialReachableQuery A initialCode overlay.value)
    (env : Nat → In₁ × In₂) : ∀ n,
    profiledOpenWitnessedRightMemberBasePlay A initialCode overlay
        (fun k ↦ ((env k).2, (env k).1)) n =
      profiledOpenWitnessedRightOverlayBaseRecord A initialCode
        (profiledOpenWitnessedRightRoundRecord A initialCode
          (profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay
            (List.ofFn fun k : Fin n ↦ env k))
          (env n).1 (env n).2) := by
  classical
  intro n
  simp [profiledOpenWitnessedRightMemberBasePlay,
    profiledOpenWitnessedRightMemberClassifiedPlay, treePlay,
    narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, hquery,
    profiledOpenFixedRightInitialReachableQuery,
    profiledOpenWitnessedRightOverlayBaseRecord,
    profiledOpenWitnessedRightRoundRecord,
    profiledOpenWitnessedRightRoundOverlayRun,
    ProfiledOpenWitnessedRightRoundOverlay.step,
    profiledOpenFixedRightQueryStep,
    FiniteDescriptorFamilyPinnedAllowedMove.memberController,
    FiniteDescriptorFamilyAllowedMove.controllerFor,
    reindexFiniteRootFamilyController, finiteRootMemberController,
    branchNode, senderWord, narrowedControl, narrowedControlAux,
    ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor]

end

end DetParityAutomaton

end DistributedSynthesis
