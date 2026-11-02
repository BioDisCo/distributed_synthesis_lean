/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemNarrowedReceiverOutputDecoration
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLocalCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTransitionRootAlignment
import DistributedSynthesis.Formalizations.Lemma.LemRowExactIndexedTargetReceiverOutput

/-!
# Finite receiver decoration below a delayed strict-child tag

The delayed handoff fixes one finite tag before the recurrent tail begins.
Inside that fibre, a checked physical receiver-table cell is decorated by an
exact successor of the tag's re-rooted policy.  The construction is the
tail-relative counterpart of the older common-root successor decoration; it
never coerces the re-rooted policy back to the common root.

The decoration is finite and executable.  It receives only a current finite
tail state and a finite receiver output.  Reachability, target liveness, and
the graph orientation occur only in specification theorems.
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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev TailState (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag

/-! ## Exact finite target keys -/

/-- A bare physical target, its queried row, and the exact tail state retained
for the following block. -/
abbrev ProfiledRawJointHybridShadowPhaseLiveTailSuccessorTarget
    (tag : Tag A strategy hwin) :=
  ProfiledRawJointIncidenceCode A (I := Unit) ×
    (PairedEntryRow × TailState A strategy hwin tag)

noncomputable instance (tag : Tag A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridShadowPhaseLiveTailSuccessorTarget A strategy hwin
        tag) := by
  classical
  infer_instance

def profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetRow
    {tag : Tag A strategy hwin}
    (target : ProfiledRawJointHybridShadowPhaseLiveTailSuccessorTarget A
      strategy hwin tag) : PairedEntryRow :=
  target.2.1

def profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey
    {tag : Tag A strategy hwin}
    (target : ProfiledRawJointHybridShadowPhaseLiveTailSuccessorTarget A
      strategy hwin tag) : TailState A strategy hwin tag :=
  target.2.2

/-- A right receiver-table target is paired with an exact crossed left-live
successor of the same tagged tail. -/
def ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt
    {tag : Tag A strategy hwin}
    (state next : TailState A strategy hwin tag)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) : Prop :=
  ∃ slot : ProfiledRawLeftSlot A,
    target.family.left () = some slot ∧
      Nonempty
        (ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt A
          strategy hwin tag state next .left (.inr slot))

/-- Left receiver-table mirror. -/
def ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt
    {tag : Tag A strategy hwin}
    (state next : TailState A strategy hwin tag)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) : Prop :=
  ∃ slot : ProfiledRawRightSlot A,
    target.family.right () = some slot ∧
      Nonempty
        (ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt A
          strategy hwin tag state next .right (.inl slot))

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt.allowed
    {tag : Tag A strategy hwin}
    {state next : TailState A strategy hwin tag}
    {target : ProfiledRawJointIncidenceCode A (I := Unit)}
    (hkey : ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A
      strategy hwin state next target) :
    tag.TailAllowedTarget A strategy hwin state next := by
  rcases hkey with ⟨_slot, _hlive, ⟨transition⟩⟩
  exact transition.allowed A strategy hwin

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt.allowed
    {tag : Tag A strategy hwin}
    {state next : TailState A strategy hwin tag}
    {target : ProfiledRawJointIncidenceCode A (I := Unit)}
    (hkey : ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A
      strategy hwin state next target) :
    tag.TailAllowedTarget A strategy hwin state next := by
  rcases hkey with ⟨_slot, _hlive, ⟨transition⟩⟩
  exact transition.allowed A strategy hwin

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt.reachable
    {tag : Tag A strategy hwin}
    {state next : TailState A strategy hwin tag}
    {target : ProfiledRawJointIncidenceCode A (I := Unit)}
    (hkey : ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A
      strategy hwin state next target)
    (hstate : tag.TailReachable A strategy hwin state) :
    tag.TailReachable A strategy hwin next := by
  rcases hkey with ⟨_slot, _hlive, ⟨transition⟩⟩
  exact transition.reachable A strategy hwin hstate

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt.reachable
    {tag : Tag A strategy hwin}
    {state next : TailState A strategy hwin tag}
    {target : ProfiledRawJointIncidenceCode A (I := Unit)}
    (hkey : ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A
      strategy hwin state next target)
    (hstate : tag.TailReachable A strategy hwin state) :
    tag.TailReachable A strategy hwin next := by
  rcases hkey with ⟨_slot, _hlive, ⟨transition⟩⟩
  exact transition.reachable A strategy hwin hstate

/-- Every checked live right cell admits an exact finite next key in the same
tag fibre. -/
theorem
    exists_profiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (hreachable : tag.TailReachable A strategy hwin state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .right state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (move_eq : state.1.2.1 = some move)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (target_allowed :
      profiledRawJointRightPhysicalSiblingAllowed A move.1 target)
    (slot : ProfiledRawLeftSlot A)
    (target_live : target.family.left () = some slot) :
    ∃ next : TailState A strategy hwin tag,
      ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
        hwin state next target := by
  let targetAt :
      ProfiledRawJointHybridShadowPhaseLiveTailTableTargetAt A strategy hwin
        tag state .left (.inr slot) :=
    .right currentCode current_code currentRoot current_live move move_eq
      target target_allowed slot target_live
  rcases targetAt.exists_rootAlignedTransition A strategy hwin state hreachable with
    ⟨next, hnext⟩
  exact ⟨next, slot, target_live, hnext⟩

/-- Left-cell mirror. -/
theorem
    exists_profiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (hreachable : tag.TailReachable A strategy hwin state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .left state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (move_eq : state.1.2.2 = some move)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (target_allowed :
      profiledRawJointLeftPhysicalSiblingAllowed A move.1 target)
    (slot : ProfiledRawRightSlot A)
    (target_live : target.family.right () = some slot) :
    ∃ next : TailState A strategy hwin tag,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy
        hwin state next target := by
  let targetAt :
      ProfiledRawJointHybridShadowPhaseLiveTailTableTargetAt A strategy hwin
        tag state .right (.inl slot) :=
    .left currentCode current_code currentRoot current_live move move_eq
      target target_allowed slot target_live
  rcases targetAt.exists_rootAlignedTransition A strategy hwin state hreachable with
    ⟨next, hnext⟩
  exact ⟨next, slot, target_live, hnext⟩

/-- Total finite choice; unchecked cells retain the current key. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveTailRightSuccessorKey
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    TailState A strategy hwin tag := by
  classical
  exact if h : ∃ next,
      ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
        hwin state next target then h.choose else state

theorem
    profiledRawJointHybridShadowPhaseLiveTailRightSuccessorKey_spec
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hex : ∃ next,
      ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
        hwin state next target) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
      hwin state
        (profiledRawJointHybridShadowPhaseLiveTailRightSuccessorKey A strategy
          hwin state target) target := by
  classical
  rw [profiledRawJointHybridShadowPhaseLiveTailRightSuccessorKey]
  split
  · exact Classical.choose_spec ‹∃ next, _›
  · contradiction

noncomputable def profiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKey
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    TailState A strategy hwin tag := by
  classical
  exact if h : ∃ next,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy
        hwin state next target then h.choose else state

theorem
    profiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKey_spec
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hex : ∃ next,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy
        hwin state next target) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy
      hwin state
        (profiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKey A strategy
          hwin state target) target := by
  classical
  rw [profiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKey]
  split
  · exact Classical.choose_spec ‹∃ next, _›
  · contradiction

/-! ## Row-exact receiver decoration -/

abbrev ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput
    (tag : Tag A strategy hwin) :=
  RowExactIndexedTargetReceiverOutput
    (PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    PairedEntryRow
    (ProfiledRawJointHybridShadowPhaseLiveTailSuccessorTarget A strategy hwin
      tag)
    (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetRow A strategy
      hwin)

abbrev ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput
    (tag : Tag A strategy hwin) :=
  RowExactIndexedTargetReceiverOutput
    (PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    PairedEntryRow
    (ProfiledRawJointHybridShadowPhaseLiveTailSuccessorTarget A strategy hwin
      tag)
    (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetRow A strategy
      hwin)

def profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection
    {tag : Tag A strategy hwin}
    (output : ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A
      strategy hwin tag) :
    ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)) :=
  { physical := output.physical
    target := fun row ↦ (output.target row).1.1 }

def profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection
    {tag : Tag A strategy hwin}
    (output : ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A
      strategy hwin tag) :
    ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)) :=
  { physical := output.physical
    target := fun row ↦ (output.target row).1.1 }

def profiledRawJointHybridShadowPhaseLiveTailDecorateRightReceiverOutput
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (output : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit))) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin
      tag :=
  RowExactIndexedTargetReceiverOutput.ofTarget output.physical
    (fun row ↦
      (output.target row,
        (row,
          profiledRawJointHybridShadowPhaseLiveTailRightSuccessorKey A strategy
            hwin state (output.target row))))
    (fun _ ↦ rfl)

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailDecorateRightReceiverOutput_project
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (output : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit))) :
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection A strategy
        hwin
        (profiledRawJointHybridShadowPhaseLiveTailDecorateRightReceiverOutput A
          strategy hwin state output) = output :=
  rfl

def profiledRawJointHybridShadowPhaseLiveTailDecorateLeftReceiverOutput
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (output : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit))) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin
      tag :=
  RowExactIndexedTargetReceiverOutput.ofTarget output.physical
    (fun row ↦
      (output.target row,
        (row,
          profiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKey A strategy
            hwin state (output.target row))))
    (fun _ ↦ rfl)

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailDecorateLeftReceiverOutput_project
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (output : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit))) :
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection A strategy
        hwin
        (profiledRawJointHybridShadowPhaseLiveTailDecorateLeftReceiverOutput A
          strategy hwin state output) = output :=
  rfl

/-- The finite right decoration stores an exact allowed next tail key on every
checked live cell. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailDecorateRightReceiverOutput_key
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (hreachable : tag.TailReachable A strategy hwin state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .right state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (move_eq : state.1.2.1 = some move)
    (output : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow)
    (target_allowed : profiledRawJointRightPhysicalSiblingAllowed A move.1
      (output.target row))
    (slot : ProfiledRawLeftSlot A)
    (target_live : (output.target row).family.left () = some slot) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
      hwin state
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A strategy
        hwin
        ((profiledRawJointHybridShadowPhaseLiveTailDecorateRightReceiverOutput
          A strategy hwin state output).target row).1)
      (output.target row) := by
  apply profiledRawJointHybridShadowPhaseLiveTailRightSuccessorKey_spec A
    strategy hwin state
  exact
    exists_profiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A
      strategy hwin state hreachable currentCode current_code currentRoot
      current_live move move_eq (output.target row) target_allowed slot
        target_live

/-- Left decoration mirror. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailDecorateLeftReceiverOutput_key
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (hreachable : tag.TailReachable A strategy hwin state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .left state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (move_eq : state.1.2.2 = some move)
    (output : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow)
    (target_allowed : profiledRawJointLeftPhysicalSiblingAllowed A move.1
      (output.target row))
    (slot : ProfiledRawRightSlot A)
    (target_live : (output.target row).family.right () = some slot) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy hwin
      state
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A strategy
        hwin
        ((profiledRawJointHybridShadowPhaseLiveTailDecorateLeftReceiverOutput A
          strategy hwin state output).target row).1)
      (output.target row) := by
  apply profiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKey_spec A
    strategy hwin state
  exact
    exists_profiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A
      strategy hwin state hreachable currentCode current_code currentRoot
      current_live move move_eq (output.target row) target_allowed slot
        target_live

/-! ## Decoration of the finite physical table controllers -/

/-- The old right monitor, with only the finite tail key erased from receiver
outputs. -/
noncomputable abbrev
    profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor
    {tag : Tag A strategy hwin}
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool) :=
  (profiledRawJointRightPhysicalSiblingMonitor A move.1 member
    ).comapReceiverOutput
      (profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection A
        strategy hwin (tag := tag))

/-- Retain an exact tail key in every cell of an already finite right member
controller.  Sender control and sender output are unchanged. -/
noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool) :=
  (move.memberController A member).decorateReceiverOutput
    (profiledRawJointRightPhysicalSiblingMonitor A move.1 member)
    (profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection A
      strategy hwin)
    (fun _ _ output ↦
      profiledRawJointHybridShadowPhaseLiveTailDecorateRightReceiverOutput A
        strategy hwin state output)

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController_controlAt
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool)
    (word : List In₁) :
    (profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController A
      strategy hwin state move member).controlAt word =
        (move.memberController A member).controlAt word :=
  rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController_sender
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool)
    (word : List In₁) :
    ((profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController A
      strategy hwin state move member).labeledTree word).1 =
        ((move.memberController A member).labeledTree word).1 :=
  rfl

theorem
    profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController_wins
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool) :
    NarrowedAllThreadsWin
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
        strategy hwin (tag := tag) move member)
      (profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController A
        strategy hwin state move member).labeledTree := by
  apply TransitionRationalTree.decorateReceiverOutput_allThreadsWin
    (profiledRawJointRightPhysicalSiblingMonitor A move.1 member)
    (profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection A
      strategy hwin)
    (fun _ _ output ↦
      profiledRawJointHybridShadowPhaseLiveTailDecorateRightReceiverOutput A
        strategy hwin state output)
    (fun _ _ _ ↦ rfl)
  exact move.memberController_wins A member

/-- On a live cell, the key stored by the decorated controller is the exact
same-tag successor proved by the table inversion. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController_key
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (hreachable : tag.TailReachable A strategy hwin state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .right state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (move_eq : state.1.2.1 = some move) (member : Bool)
    (word : List In₁)
    (monitorState :
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 member).State)
    (input : In₂ × In₁) (row : PairedEntryRow)
    (target_allowed : profiledRawJointRightPhysicalSiblingAllowed A move.1
      (((move.memberController A member).labeledTree word).2 monitorState
        input |>.target row))
    (slot : ProfiledRawLeftSlot A)
    (target_live :
      (((move.memberController A member).labeledTree word).2 monitorState
        input |>.target row).family.left () = some slot) :
    let decorated :=
      profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController A
        strategy hwin state move member
    let target := ((decorated.labeledTree word).2 monitorState input).target row
    ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
      hwin state
        (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A strategy
          hwin target.1)
        target.1.1 := by
  dsimp only
  exact
    profiledRawJointHybridShadowPhaseLiveTailDecorateRightReceiverOutput_key A
      strategy hwin state hreachable currentCode current_code currentRoot
      current_live move move_eq
      (((move.memberController A member).labeledTree word).2 monitorState input)
      row target_allowed slot target_live

/-! ### Left mirror -/

noncomputable abbrev
    profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor
    {tag : Tag A strategy hwin}
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool) :=
  (profiledRawJointLeftPhysicalSiblingMonitor A move.1 member
    ).comapReceiverOutput
      (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection A
        strategy hwin (tag := tag))

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool) :=
  (move.memberController A member).decorateReceiverOutput
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1 member)
    (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection A
      strategy hwin)
    (fun _ _ output ↦
      profiledRawJointHybridShadowPhaseLiveTailDecorateLeftReceiverOutput A
        strategy hwin state output)

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController_controlAt
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool)
    (word : List In₂) :
    (profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
      strategy hwin state move member).controlAt word =
        (move.memberController A member).controlAt word :=
  rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController_sender
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool)
    (word : List In₂) :
    ((profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
      strategy hwin state move member).labeledTree word).1 =
        ((move.memberController A member).labeledTree word).1 :=
  rfl

theorem
    profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController_wins
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool) :
    NarrowedAllThreadsWin
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move member)
      (profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
        strategy hwin state move member).labeledTree := by
  apply TransitionRationalTree.decorateReceiverOutput_allThreadsWin
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1 member)
    (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection A strategy
      hwin)
    (fun _ _ output ↦
      profiledRawJointHybridShadowPhaseLiveTailDecorateLeftReceiverOutput A
        strategy hwin state output)
    (fun _ _ _ ↦ rfl)
  exact move.memberController_wins A member

theorem
    profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController_key
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (hreachable : tag.TailReachable A strategy hwin state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .left state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (move_eq : state.1.2.2 = some move) (member : Bool)
    (word : List In₂)
    (monitorState :
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 member).State)
    (input : In₁ × In₂) (row : PairedEntryRow)
    (target_allowed : profiledRawJointLeftPhysicalSiblingAllowed A move.1
      (((move.memberController A member).labeledTree word).2 monitorState
        input |>.target row))
    (slot : ProfiledRawRightSlot A)
    (target_live :
      (((move.memberController A member).labeledTree word).2 monitorState
        input |>.target row).family.right () = some slot) :
    let decorated :=
      profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
        strategy hwin state move member
    let target := ((decorated.labeledTree word).2 monitorState input).target row
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy hwin
      state
        (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A strategy
          hwin target.1)
        target.1.1 := by
  dsimp only
  exact
    profiledRawJointHybridShadowPhaseLiveTailDecorateLeftReceiverOutput_key A
      strategy hwin state hreachable currentCode current_code currentRoot
      current_live move move_eq
      (((move.memberController A member).labeledTree word).2 monitorState input)
      row target_allowed slot target_live

end

end DetParityAutomaton

end DistributedSynthesis
