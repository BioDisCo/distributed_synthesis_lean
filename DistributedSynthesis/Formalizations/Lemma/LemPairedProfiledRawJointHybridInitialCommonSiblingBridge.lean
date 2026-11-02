/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialCommonAmbiguityShadow
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPersistentKeys

/-!
# The initial common ambiguity lives in the root-pinned sibling keys

The second simultaneous round and either indistinguishable strict round are
sibling transitions of the one exact root-pinned hybrid policy.  This file
identifies only their finite incidence data.  It does not identify the sibling
states, select a fresh policy, or expose a graph orientation to either process.
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
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)

/-! ## The two proof-side strict directions -/

/-- The strict-left sibling of the second simultaneous move.  The side is a
proof-tree tag; it is not part of either process's local control. -/
def profiledRawJointHybridInitialSecondStrictLeftDirection
    (first current : In₁ × In₂) :
    ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) where
  side := .left
  direction := profiledRawJointInitialCommonBothDirection (first, current)

/-- Strict-right mirror. -/
def profiledRawJointHybridInitialSecondStrictRightDirection
    (first current : In₁ × In₂) :
    ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) where
  side := .right
  direction := profiledRawJointInitialCommonBothDirection (first, current)

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointHybridInitialSecondStrictLeftDirection_normalized
    (first current : In₁ × In₂) :
    profiledRawJointCommonActualDirection
        (profiledRawJointHybridInitialSecondStrictLeftDirection first current) =
      profiledRawJointHybridInitialSecondStrictLeftDirection first current :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointHybridInitialSecondStrictRightDirection_normalized
    (first current : In₁ × In₂) :
    profiledRawJointCommonActualDirection
        (profiledRawJointHybridInitialSecondStrictRightDirection first current) =
      profiledRawJointHybridInitialSecondStrictRightDirection first current :=
  rfl

/-! ## Full incidence-code identification -/

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The recursively common finite code is exactly the incidence payload of
the root-pinned simultaneous sibling key. -/
theorem
    profiledRawJointHybridInitialRootPinnedSimultaneousKey_incidence_eq_secondCommon
    (first current : In₁ × In₂) :
    (profiledRawJointHybridInitialRootPinnedSimultaneousKey A strategy hwin
      first current).incidenceCode =
      (profiledRawJointCommonWorldFamily A
        (ProfiledRawJointHybridInitialSecondCommonWorld A strategy
          (first, current))).incidenceCode A := by
  symm
  exact profiledRawJointCommonWorldAfterBoth_incidenceCode A
    (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first) current

/-- The pinned-left strict child is exactly the incidence payload of the
strict-left sibling key in the same root-pinned policy. -/
theorem
    profiledRawJointHybridInitialSecondOneShadow_child_eq_strictSibling
    (first current : In₁ × In₂) :
    let shadow :=
      (profiledRawJointHybridInitialToSecondOneShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
          first).2 current.1 current.2).2
    shadow.strictStage.child.1 =
      (profiledRawJointHybridInitialRootPinnedStrictKey A strategy hwin first
        (profiledRawJointHybridInitialSecondStrictLeftDirection first current)
        ).incidenceCode := by
  dsimp only
  rw [profiledRawJointHybridInitialSecondOneShadow_child_eq_leftActual A
    strategy hwin controllers first current]
  let family := profiledRawJointInitialCommonBothFamily A strategy
    (first, current)
  let direction := profiledRawJointInitialCommonBothDirection (first, current)
  let common := Classical.choice
    (nonempty_profiledRawJointCommonWorldBothRestartSource A
      (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first) current)
  rw [family.leftActualChild_incidenceCode_eq A direction common]
  rfl

/-- Pinned-right mirror. -/
theorem
    profiledRawJointHybridInitialSecondTwoShadow_child_eq_strictSibling
    (first current : In₁ × In₂) :
    let shadow :=
      (profiledRawJointHybridInitialToSecondTwoShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
          first).2 current.2 current.1).2
    shadow.strictStage.child.1 =
      (profiledRawJointHybridInitialRootPinnedStrictKey A strategy hwin first
        (profiledRawJointHybridInitialSecondStrictRightDirection first current)
        ).incidenceCode := by
  dsimp only
  rw [profiledRawJointHybridInitialSecondTwoShadow_child_eq_rightActual A
    strategy hwin controllers first current]
  let family := profiledRawJointInitialCommonBothFamily A strategy
    (first, current)
  let direction := profiledRawJointInitialCommonBothDirection (first, current)
  let common := Classical.choice
    (nonempty_profiledRawJointCommonWorldBothRestartSource A
      (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first) current)
  rw [family.rightActualChild_incidenceCode_eq A direction common]
  rfl

/-! ## The local live-slot facade -/

/-- Process one's locally retained slot is the process-two slot of the
simultaneous sibling. -/
theorem
    profiledRawJointHybridInitialSecondOneShadow_liveRight_eq_simultaneousSibling
    (first current : In₁ × In₂) :
    let shadow :=
      (profiledRawJointHybridInitialToSecondOneShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
          first).2 current.1 current.2).2
    shadow.strictStage.child.1.family.right =
      (profiledRawJointHybridInitialRootPinnedSimultaneousKey A strategy hwin
        first current).incidenceCode.family.right := by
  dsimp only
  calc
    _ = ((profiledRawJointCommonWorldFamily A
          (ProfiledRawJointHybridInitialSecondCommonWorld A strategy
            (first, current))).incidenceCode A).family.right :=
      profiledRawJointHybridInitialSecondOneShadow_liveRight_eq_common A
        strategy hwin controllers first current
    _ = _ := congrArg (fun code ↦ code.family.right)
      (profiledRawJointHybridInitialRootPinnedSimultaneousKey_incidence_eq_secondCommon
        A strategy hwin first current).symm

/-- The same local slot is also the process-two slot of its strict-left
sibling.  The two sibling states themselves remain distinct. -/
theorem
    profiledRawJointHybridInitialSecondOneShadow_liveRight_eq_strictSibling
    (first current : In₁ × In₂) :
    let shadow :=
      (profiledRawJointHybridInitialToSecondOneShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
          first).2 current.1 current.2).2
    shadow.strictStage.child.1.family.right =
      (profiledRawJointHybridInitialRootPinnedStrictKey A strategy hwin first
        (profiledRawJointHybridInitialSecondStrictLeftDirection first current)
        ).incidenceCode.family.right := by
  dsimp only
  exact congrArg (fun code ↦ code.family.right)
    (profiledRawJointHybridInitialSecondOneShadow_child_eq_strictSibling A
      strategy hwin controllers first current)

/-- Process-two/common sibling mirror. -/
theorem
    profiledRawJointHybridInitialSecondTwoShadow_liveLeft_eq_simultaneousSibling
    (first current : In₁ × In₂) :
    let shadow :=
      (profiledRawJointHybridInitialToSecondTwoShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
          first).2 current.2 current.1).2
    shadow.strictStage.child.1.family.left =
      (profiledRawJointHybridInitialRootPinnedSimultaneousKey A strategy hwin
        first current).incidenceCode.family.left := by
  dsimp only
  calc
    _ = ((profiledRawJointCommonWorldFamily A
          (ProfiledRawJointHybridInitialSecondCommonWorld A strategy
            (first, current))).incidenceCode A).family.left :=
      profiledRawJointHybridInitialSecondTwoShadow_liveLeft_eq_common A
        strategy hwin controllers first current
    _ = _ := congrArg (fun code ↦ code.family.left)
      (profiledRawJointHybridInitialRootPinnedSimultaneousKey_incidence_eq_secondCommon
        A strategy hwin first current).symm

/-- Process-two/strict sibling mirror. -/
theorem
    profiledRawJointHybridInitialSecondTwoShadow_liveLeft_eq_strictSibling
    (first current : In₁ × In₂) :
    let shadow :=
      (profiledRawJointHybridInitialToSecondTwoShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
          first).2 current.2 current.1).2
    shadow.strictStage.child.1.family.left =
      (profiledRawJointHybridInitialRootPinnedStrictKey A strategy hwin first
        (profiledRawJointHybridInitialSecondStrictRightDirection first current)
        ).incidenceCode.family.left := by
  dsimp only
  exact congrArg (fun code ↦ code.family.left)
    (profiledRawJointHybridInitialSecondTwoShadow_child_eq_strictSibling A
      strategy hwin controllers first current)

/-- Slot-only bridge consumed by the leader-free carrier.  It records the
two local simultaneous/strict ambiguities inside the single guarded sibling
family, and intentionally contains no policy-state equality. -/
theorem
    profiledRawJointHybridInitialSecond_siblingLiveSlotCertificate
    (first current : In₁ × In₂) :
    let one :=
      (profiledRawJointHybridInitialToSecondOneShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
          first).2 current.1 current.2).2
    let two :=
      (profiledRawJointHybridInitialToSecondTwoShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
          first).2 current.2 current.1).2
    let simultaneous :=
      profiledRawJointHybridInitialRootPinnedSimultaneousKey A strategy hwin
        first current
    let strictLeft :=
      profiledRawJointHybridInitialRootPinnedStrictKey A strategy hwin first
        (profiledRawJointHybridInitialSecondStrictLeftDirection first current)
    let strictRight :=
      profiledRawJointHybridInitialRootPinnedStrictKey A strategy hwin first
        (profiledRawJointHybridInitialSecondStrictRightDirection first current)
    one.strictStage.child.1.family.right =
        simultaneous.incidenceCode.family.right ∧
      one.strictStage.child.1.family.right =
        strictLeft.incidenceCode.family.right ∧
      two.strictStage.child.1.family.left =
        simultaneous.incidenceCode.family.left ∧
      two.strictStage.child.1.family.left =
        strictRight.incidenceCode.family.left := by
  dsimp only
  exact ⟨
    profiledRawJointHybridInitialSecondOneShadow_liveRight_eq_simultaneousSibling
      A strategy hwin controllers first current,
    profiledRawJointHybridInitialSecondOneShadow_liveRight_eq_strictSibling A
      strategy hwin controllers first current,
    profiledRawJointHybridInitialSecondTwoShadow_liveLeft_eq_simultaneousSibling
      A strategy hwin controllers first current,
    profiledRawJointHybridInitialSecondTwoShadow_liveLeft_eq_strictSibling A
      strategy hwin controllers first current⟩

end

end DetParityAutomaton

end DistributedSynthesis
