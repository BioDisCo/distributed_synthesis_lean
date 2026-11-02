/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWinningMonitorPhysicalPriority
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceFiniteActivePivotStep

/-!
# Winning extensions of zero-open witnessed overlays

The root-pinned family value contains a winning projected controller for every
stored descriptor/root member.  That guarantee starts at the genuine initial
controller and monitor states.  The zero-open provenance query used by the
physical recurrence resets every bank coordinate to exactly those states.

This file records that alignment explicitly and turns it into the concrete
winning extension consumed by the physical block-minimum theorem.
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

/-! ## The zero-open query really starts every pinned coordinate -/

@[simp] theorem profiledOpenWitnessedInitialQueryForMove_rightQuery
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (value : ProfiledOpenFixedRightPinnedValue A initialCode) :
    (profiledOpenWitnessedInitialQueryForMove A initialCode move).1.1.2.1
        value =
      profiledOpenFixedRightInitialReachableQuery A initialCode value :=
  rfl

@[simp] theorem profiledOpenWitnessedInitialQueryForMove_leftQuery
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode) :
    (profiledOpenWitnessedInitialQueryForMove A initialCode move).1.1.2.2
        value =
      profiledOpenFixedLeftInitialReachableQuery A initialCode value :=
  rfl

/-! ## The winning projected member play -/

/-- The right member controller selected by a witnessed overlay, run on an
ordinary physical right-block input word. -/
noncomputable def profiledOpenWitnessedRightMemberClassifiedPlay
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (env : Nat → In₂ × In₁) :
    Nat → RealizedBlockRound In₂ In₁
      (ProfiledOpenRightClassifiedOutput A) Out₁ :=
  let Root := fun descriptor :
      ProfiledOpenHiddenDescriptorRightCarrier A overlay.value.1 ↦
    ProfiledOpenHiddenDescriptorRightRoot A descriptor.1
  let M : (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      overlay.value.1) → Root descriptor →
      BlockRecordMonitor In₂ In₁ (ProfiledOpenRightClassifiedOutput A)
        Out₁ := fun descriptor root ↦
    profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root
  let Allowed : (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      overlay.value.1) →
      (((Root descriptor × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses
  let expected := overlay.value.2.1
  let monitor := (M overlay.member overlay.root).rootPinned
    (expected ⟨overlay.member, overlay.root⟩)
  let controller := overlay.value.2.2.memberController Root M Allowed expected
    overlay.member overlay.root
  treePlay (narrowedInducedTree monitor controller.labeledTree) env

/-- Left projected member play. -/
noncomputable def profiledOpenWitnessedLeftMemberClassifiedPlay
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (env : Nat → In₁ × In₂) :
    Nat → RealizedBlockRound In₁ In₂
      (ProfiledOpenLeftClassifiedOutput A) Out₂ :=
  let Root := fun descriptor :
      ProfiledOpenHiddenDescriptorLeftCarrier A overlay.value.1 ↦
    ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1
  let M : (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      overlay.value.1) → Root descriptor →
      BlockRecordMonitor In₁ In₂ (ProfiledOpenLeftClassifiedOutput A)
        Out₂ := fun descriptor root ↦
    profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root
  let Allowed : (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      overlay.value.1) →
      (((Root descriptor × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses
  let expected := overlay.value.2.1
  let monitor := (M overlay.member overlay.root).rootPinned
    (expected ⟨overlay.member, overlay.root⟩)
  let controller := overlay.value.2.2.memberController Root M Allowed expected
    overlay.member overlay.root
  treePlay (narrowedInducedTree monitor controller.labeledTree) env

/-- Erase the classified target annotation from the right member play. -/
noncomputable def profiledOpenWitnessedRightMemberBasePlay
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (env : Nat → In₂ × In₁) :
    Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁ := fun n ↦
  let record := profiledOpenWitnessedRightMemberClassifiedPlay A initialCode
    overlay env n
  (record.1, record.2.1.1, record.2.2)

/-- Erase the classified target annotation from the left member play. -/
noncomputable def profiledOpenWitnessedLeftMemberBasePlay
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (env : Nat → In₁ × In₂) :
    Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂ := fun n ↦
  let record := profiledOpenWitnessedLeftMemberClassifiedPlay A initialCode
    overlay env n
  (record.1, record.2.1.1, record.2.2)

/-- Literal simultaneous pinned-union play used before projecting to one
right descriptor/root member. -/
noncomputable def profiledOpenWitnessedRightUnionClassifiedPlay
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (env : Nat →
      ((Sigma fun member : ProfiledOpenHiddenDescriptorRightCarrier A
        overlay.value.1 ↦
          ProfiledOpenHiddenDescriptorRightRoot A member.1) × In₂) × In₁) :
    Nat → RealizedBlockRound
      ((Sigma fun member : ProfiledOpenHiddenDescriptorRightCarrier A
        overlay.value.1 ↦
          ProfiledOpenHiddenDescriptorRightRoot A member.1) × In₂)
      In₁ (ProfiledOpenRightClassifiedOutput A) Out₁ :=
  treePlay
    (narrowedInducedTree
      (ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A overlay.value.1
        overlay.value.2.1)
      overlay.value.2.2.1.toTransitionRationalTree.labeledTree) env

/-- The nested descriptor/root projection is literally the corresponding
fixed-tag branch of the one simultaneous right union controller. -/
theorem profiledOpenWitnessedRightMemberClassifiedPlay_tagged
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (env : Nat → In₂ × In₁) (n : Nat) :
    tagFiniteRootPlay ⟨overlay.member, overlay.root⟩
        (profiledOpenWitnessedRightMemberClassifiedPlay A initialCode overlay
          env) n =
      profiledOpenWitnessedRightUnionClassifiedPlay A initialCode overlay
        (tagFiniteRootEnvironment ⟨overlay.member, overlay.root⟩ env) n := by
  let Root := fun descriptor :
      ProfiledOpenHiddenDescriptorRightCarrier A overlay.value.1 ↦
    ProfiledOpenHiddenDescriptorRightRoot A descriptor.1
  let baseM : (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      overlay.value.1) → Root descriptor →
      BlockRecordMonitor In₂ In₁ (ProfiledOpenRightClassifiedOutput A)
        Out₁ := fun descriptor root ↦
    profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root
  letI : Fintype (Sigma Root) := Sigma.instFintype
  let pinnedM := descriptorRootPinnedMonitor Root baseM overlay.value.2.1
  let unionM := descriptorRootUnionMonitor Root pinnedM
  let family := overlay.value.2.2.1.toTransitionRationalTree
  have htag := finiteRootMemberController_treePlay_tagged unionM family
    ⟨overlay.member, overlay.root⟩ env n
  have htree := finiteRootMemberController_reindex_labeledTree unionM
    (fun root : Root overlay.member ↦ Sigma.mk overlay.member root) family
      overlay.root
  simp only [profiledOpenWitnessedRightMemberClassifiedPlay,
    profiledOpenWitnessedRightUnionClassifiedPlay, Root, baseM, pinnedM,
    unionM, family,
    FiniteDescriptorFamilyPinnedAllowedMove.memberController,
    FiniteDescriptorFamilyAllowedMove.controllerFor,
    ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor] at htag ⊢
  rw [htree]
  exact htag

/-- Every right overlay member/root stored in the pinned value has a winning
base play.  This is the direct public projection of `member_base_wins`. -/
theorem profiledOpenWitnessedRightMemberBasePlay_wins
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (hmove : overlay.member.1.moveIdentity.1 =
      ProfiledOpenClassifiedMove.right source table)
    (env : Nat → In₂ × In₁) :
    (profiledOpenRightRootMonitor.{u, v, x, y, s, max i u v x y s} A
      (profiledOpenHiddenDescriptorRightRootToEq A overlay.member.1 source
        table hmove overlay.root).1).WinsPlay
      (profiledOpenWitnessedRightMemberBasePlay A initialCode overlay env) := by
  let Root := fun descriptor :
      ProfiledOpenHiddenDescriptorRightCarrier A overlay.value.1 ↦
    ProfiledOpenHiddenDescriptorRightRoot A descriptor.1
  let M : (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      overlay.value.1) → Root descriptor →
      BlockRecordMonitor In₂ In₁ (ProfiledOpenRightClassifiedOutput A)
        Out₁ := fun descriptor root ↦
    profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root
  let Allowed : (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      overlay.value.1) →
      (((Root descriptor × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses
  let expected := overlay.value.2.1
  have hclassified :=
    overlay.value.2.2.member_base_wins Root M Allowed expected overlay.member
      overlay.root env
  dsimp only [M] at hclassified
  simp only [profiledOpenHiddenDescriptorRightMonitor_eq_ofEq A
    overlay.member.1 source table hmove overlay.root] at hclassified
  have hbase := (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledOpenRightRootMonitor.{u, v, x, y, s, max i u v x y s} A
      (profiledOpenHiddenDescriptorRightRootToEq A overlay.member.1 source
        table hmove overlay.root).1)
    (fun output : ProfiledOpenRightClassifiedOutput A ↦ output.1)
    (profiledOpenWitnessedRightMemberClassifiedPlay A initialCode overlay env)
    ).mp (by
      simpa only [profiledOpenWitnessedRightMemberClassifiedPlay, Root, M,
        Allowed, expected] using hclassified)
  simpa only [profiledOpenWitnessedRightMemberBasePlay,
    BlockRecordMonitor.projectReceiverPlay] using hbase

/-- Left mirror. -/
theorem profiledOpenWitnessedLeftMemberBasePlay_wins
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (hmove : overlay.member.1.moveIdentity.2 =
      ProfiledOpenClassifiedMove.left source table)
    (env : Nat → In₁ × In₂) :
    (profiledOpenLeftRootMonitor.{u, v, x, y, s, max i u v x y s} A
      (profiledOpenHiddenDescriptorLeftRootToEq A overlay.member.1 source table
        hmove overlay.root).1).WinsPlay
      (profiledOpenWitnessedLeftMemberBasePlay A initialCode overlay env) := by
  let Root := fun descriptor :
      ProfiledOpenHiddenDescriptorLeftCarrier A overlay.value.1 ↦
    ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1
  let M : (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      overlay.value.1) → Root descriptor →
      BlockRecordMonitor In₁ In₂ (ProfiledOpenLeftClassifiedOutput A)
        Out₂ := fun descriptor root ↦
    profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root
  let Allowed : (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      overlay.value.1) →
      (((Root descriptor × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses
  let expected := overlay.value.2.1
  have hclassified :=
    overlay.value.2.2.member_base_wins Root M Allowed expected overlay.member
      overlay.root env
  dsimp only [M] at hclassified
  simp only [profiledOpenHiddenDescriptorLeftMonitor_eq_ofEq A
    overlay.member.1 source table hmove overlay.root] at hclassified
  have hbase := (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledOpenLeftRootMonitor.{u, v, x, y, s, max i u v x y s} A
      (profiledOpenHiddenDescriptorLeftRootToEq A overlay.member.1 source table
        hmove overlay.root).1)
    (fun output : ProfiledOpenLeftClassifiedOutput A ↦ output.1)
    (profiledOpenWitnessedLeftMemberClassifiedPlay A initialCode overlay env)
    ).mp (by
      simpa only [profiledOpenWitnessedLeftMemberClassifiedPlay, Root, M,
        Allowed, expected] using hclassified)
  simpa only [profiledOpenWitnessedLeftMemberBasePlay,
    BlockRecordMonitor.projectReceiverPlay] using hbase

/-! ## Initial-query trace agreement -/

theorem profiledOpenWitnessedRightMemberBasePlay_zero_eq_overlay
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (hquery : overlay.query =
      profiledOpenFixedRightInitialReachableQuery A initialCode overlay.value)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedRightMemberBasePlay A initialCode overlay
        (fun _ ↦ (inputTwo, inputOne)) 0 =
      profiledOpenWitnessedRightOverlayBaseRecord A initialCode
        (profiledOpenWitnessedRightRoundRecord A initialCode overlay inputOne
          inputTwo) := by
  simp [profiledOpenWitnessedRightMemberBasePlay,
    profiledOpenWitnessedRightMemberClassifiedPlay, treePlay,
    narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, hquery,
    profiledOpenFixedRightInitialReachableQuery,
    profiledOpenWitnessedRightOverlayBaseRecord,
    profiledOpenWitnessedRightRoundRecord,
    FiniteDescriptorFamilyPinnedAllowedMove.memberController,
    FiniteDescriptorFamilyAllowedMove.controllerFor,
    reindexFiniteRootFamilyController, finiteRootMemberController,
    branchNode, senderWord, narrowedControl, narrowedControlAux,
    TransitionRationalTree.controlAt, reindexFiniteRootFamilyState,
    ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor,
    finiteRootFamilyMonitor]

end

end DetParityAutomaton

end DistributedSynthesis
