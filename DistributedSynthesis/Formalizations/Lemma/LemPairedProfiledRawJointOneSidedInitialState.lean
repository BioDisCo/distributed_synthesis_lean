/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonBaseWorld
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedSemanticParity

/-!
# Initial one-sided raw joint semantic states

The recursive one-sided construction starts from one live semantic lane.  A
single paired entry is already enough: put it in the unique lineage and leave
the opposite lane empty.  The exact-fibre condition is then vacuous, while the
live lane retains the literal strategy histories.

The common-base world supplies exactly such an entry on either side.  At the
model root, taking the empty generated base, the first input pair, and
`A.initial` gives the familiar `left`/`both` process-one pair or its
`right`/`both` process-two mirror after round zero.  The selected side below is
proof-tree data; it is not revealed to either process.

This file closes only the recurrent-tree entrance.  It does not claim that one
chosen round-zero pair regularizes an arbitrarily long initial homogeneous
block.  That finite initial-block controller must still hand every possible
closing prefix to the corresponding common-base state constructed here.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

/-! ## Singleton semantic families -/

/-- One live process-one/right lane in the unique lineage. -/
def profiledRawJointRightSingletonFamily
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcOnePairedEntryRep strategy × A.State) :
    ProfiledRawJointSemanticFamily A strategy (I := Unit) where
  right := fun _ => some member
  left := fun _ => none
  right_view_shared := by
    intro _ _ leftMember rightMember hleft hright
    have hleft' : member = leftMember := Option.some.inj hleft
    have hright' : member = rightMember := Option.some.inj hright
    subst leftMember
    subst rightMember
    rfl
  left_view_shared := by
    intro _ _ _ _ hleft _
    simp at hleft

/-- One live process-two/left lane in the unique lineage. -/
def profiledRawJointLeftSingletonFamily
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcTwoPairedEntryRep strategy × A.State) :
    ProfiledRawJointSemanticFamily A strategy (I := Unit) where
  right := fun _ => none
  left := fun _ => some member
  right_view_shared := by
    intro _ _ _ _ hright _
    simp at hright
  left_view_shared := by
    intro _ _ leftMember rightMember hleft hright
    have hleft' : member = leftMember := Option.some.inj hleft
    have hright' : member = rightMember := Option.some.inj hright
    subst leftMember
    subst rightMember
    rfl

@[simp] theorem profiledRawJointRightSingletonFamily_right
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcOnePairedEntryRep strategy × A.State) :
    (profiledRawJointRightSingletonFamily A member).right () = some member :=
  rfl

@[simp] theorem profiledRawJointRightSingletonFamily_left
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcOnePairedEntryRep strategy × A.State) :
    (profiledRawJointRightSingletonFamily A member).left () = none :=
  rfl

@[simp] theorem profiledRawJointLeftSingletonFamily_right
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcTwoPairedEntryRep strategy × A.State) :
    (profiledRawJointLeftSingletonFamily A member).right () = none :=
  rfl

@[simp] theorem profiledRawJointLeftSingletonFamily_left
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcTwoPairedEntryRep strategy × A.State) :
    (profiledRawJointLeftSingletonFamily A member).left () = some member :=
  rfl

/-- A singleton right family is recursively exact because its opposite lane
is empty. -/
theorem profiledRawJointRightSingletonFamily_exactFibreAt
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcOnePairedEntryRep strategy × A.State)
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointRightSingletonFamily A member).ExactFibreAt A
      direction := by
  constructor
  · intro _ _ _ _ hleft
    simp [profiledRawJointRightSingletonFamily] at hleft
  · intro _ _ _ hleft _
    simp [profiledRawJointRightSingletonFamily] at hleft

/-- Singleton left-family mirror. -/
theorem profiledRawJointLeftSingletonFamily_exactFibreAt
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcTwoPairedEntryRep strategy × A.State)
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointLeftSingletonFamily A member).ExactFibreAt A
      direction := by
  constructor
  · intro _ _ _ hright _
    simp [profiledRawJointLeftSingletonFamily] at hright
  · intro _ _ _ _ hright
    simp [profiledRawJointLeftSingletonFamily] at hright

/-! ## Exact one-sided state wrappers -/

/-- Turn one literal process-one paired entry into a recursively closed raw
semantic state. -/
def profiledRawJointRightSingletonState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcOnePairedEntryRep strategy × A.State) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) where
  family := profiledRawJointRightSingletonFamily A member
  exactFibre := profiledRawJointRightSingletonFamily_exactFibreAt A member

/-- Process-two singleton-state mirror. -/
def profiledRawJointLeftSingletonState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcTwoPairedEntryRep strategy × A.State) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) where
  family := profiledRawJointLeftSingletonFamily A member
  exactFibre := profiledRawJointLeftSingletonFamily_exactFibreAt A member

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-- Select one recurrent orientation of a literal common-base world. -/
def ProfiledRawJointCommonBaseWorld.oneSidedState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (side : IndexedLineageSide) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  match side with
  | .right => profiledRawJointRightSingletonState A (world.procOneMember A)
  | .left => profiledRawJointLeftSingletonState A (world.procTwoMember A)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The chosen common-base root really has a live slot; no empty semantic
tree is smuggled into the rationalization. -/
theorem ProfiledRawJointCommonBaseWorld.oneSidedState_live
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (side : IndexedLineageSide) :
    ∃ root : ProfiledRawJointThreadRoot A,
      profiledRawJointOneSidedCurrentSlots A side
          ((world.oneSidedState A side).code A) () = some root := by
  cases side with
  | right => exact ⟨Sum.inl (world.procOneSlot A), rfl⟩
  | left => exact ⟨Sum.inr (world.procTwoSlot A), rfl⟩

/-! ## The genuine round-zero common base -/

/-- Empty generated base plus the first input pair.  Its two projections are
the standard first process-one and process-two paired memories. -/
def profiledRawJointInitialCommonBaseWorld
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointCommonBaseWorld A strategy where
  base := []
  base_generated := StrategyGeneratedPrefix.empty
  inputOne := inputOne
  inputTwo := inputTwo
  root := A.initial

/-- The smallest nonempty recurrent semantic root after the finite first
round, with Nature's orientation retained only as proof-tree data. -/
def profiledRawJointInitialOneSidedState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (side : IndexedLineageSide) (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  ProfiledRawJointCommonBaseWorld.oneSidedState A
    (profiledRawJointInitialCommonBaseWorld A strategy inputOne inputTwo) side

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
theorem profiledRawJointInitialOneSidedState_live
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (side : IndexedLineageSide) (inputOne : In₁) (inputTwo : In₂) :
    ∃ root : ProfiledRawJointThreadRoot A,
      profiledRawJointOneSidedCurrentSlots A side
          ((profiledRawJointInitialOneSidedState A strategy side inputOne
            inputTwo).code A) () = some root :=
  ProfiledRawJointCommonBaseWorld.oneSidedState_live A
    (profiledRawJointInitialCommonBaseWorld A strategy inputOne inputTwo) side

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- From a winning strategy, every first-input/orientation root immediately
inherits the unconditional code-parity semantic certificate. -/
theorem profiledRawJointInitialOneSidedState_codeParityCertificate
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (side : IndexedLineageSide) (inputOne : In₁) (inputTwo : In₂) :
    let initial := profiledRawJointInitialOneSidedState A strategy side
      inputOne inputTwo
    let raw := profiledRawJointOneSidedSemanticTree A initial
    SourceFreeBeliefCodeParityCertificate
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
      (initial.code A)
      (ProfiledRawJointIncidenceMoveValid A)
      (profiledRawJointOneSidedNext A)
      raw := by
  exact profiledRawJointOneSidedSemanticTree_codeParityCertificate A strategy
    hwin _

end

end DetParityAutomaton

end DistributedSynthesis
