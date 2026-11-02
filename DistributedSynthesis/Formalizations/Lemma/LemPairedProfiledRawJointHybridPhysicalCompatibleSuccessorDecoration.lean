/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemNarrowedReceiverOutputDecoration
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLocalCarrier
import DistributedSynthesis.Formalizations.Lemma.LemRowExactIndexedTargetReceiverOutput

/-!
# Decorating a physical close with its same-policy successor key

The finite physical table emits a bare one-sided incidence code.  Compatibility
already proves that every checked target of that table is a child of the same
outer rational policy, but choosing that child only after the close would lose
the annotation needed by the following block.

This file makes the choice at the finite close itself.  The receiver target is
decorated by its literal row and by one finite successor state of the fixed
compatible policy.  Projection is definitionally the old physical target.
For every allowed live target, the retained state comes with an exact
`ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt` witness.

The dynamic state is intended as the key of the sigma-packed acknowledged
carrier.  It is not an endpoint observation: the executable decoration takes
no graph, orientation, side, leader bit, strict-leader bit, history, or view.
The outer strategy/package key remains fixed.
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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatibleState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin initial

/-! ## Finite target and proof-erasing projections -/

/-- A bare physical target together with its queried row and the finite key
to install after the acknowledged close. -/
abbrev ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointIncidenceCode A (I := Unit) ×
    (PairedEntryRow × CompatibleState A strategy hwin initial)

noncomputable instance
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A strategy hwin
        initial) := by
  classical
  infer_instance

/-- The right physical monitor sees only the old bare target. -/
def profiledRawJointHybridPhysicalCompatibleSuccessorRightTargetProjection
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (target : ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A
      strategy hwin initial) : PairedProfiledTreeState A :=
  profiledRawJointUnitRightTargetProjection A target.1

/-- Left mirror. -/
def profiledRawJointHybridPhysicalCompatibleSuccessorLeftTargetProjection
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (target : ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A
      strategy hwin initial) : PairedProfiledTreeState A :=
  profiledRawJointUnitLeftTargetProjection A target.1

def profiledRawJointHybridPhysicalCompatibleSuccessorTargetRow
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (target : ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A
      strategy hwin initial) : PairedEntryRow :=
  target.2.1

def profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (target : ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A
      strategy hwin initial) : CompatibleState A strategy hwin initial :=
  target.2.2

/-! ## Choosing the same-policy key -/

/-- A right bare target and a candidate finite key are related precisely when
the target's crossed live slot is witnessed by a transition of the same
compatible policy. -/
def ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state next : CompatibleState A strategy hwin initial)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) : Prop :=
  ∃ slot : ProfiledRawLeftSlot A,
    target.family.left () = some slot ∧
      Nonempty
        (ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A
          strategy hwin policy state next .left (.inr slot))

/-- Left mirror. -/
def ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state next : CompatibleState A strategy hwin initial)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) : Prop :=
  ∃ slot : ProfiledRawRightSlot A,
    target.family.right () = some slot ∧
      Nonempty
        (ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A
          strategy hwin policy state next .right (.inl slot))

/-- Root-aligned refinement of a right successor key.  Besides the literal
live target and same-policy transition it retains that the move installed in
the child annotation is based at that very target slot. -/
def ProfiledRawJointHybridPhysicalCompatibleRightRootAlignedSuccessorKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state next : CompatibleState A strategy hwin initial)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) : Prop :=
  ∃ slot : ProfiledRawLeftSlot A,
    target.family.left () = some slot ∧
      Nonempty
        (ProfiledRawJointHybridPhysicalCompatibleRootAlignedTargetTransitionAt
          A strategy hwin policy state next .left (.inr slot))

/-- Root-aligned left successor key. -/
def ProfiledRawJointHybridPhysicalCompatibleLeftRootAlignedSuccessorKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state next : CompatibleState A strategy hwin initial)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) : Prop :=
  ∃ slot : ProfiledRawRightSlot A,
    target.family.right () = some slot ∧
      Nonempty
        (ProfiledRawJointHybridPhysicalCompatibleRootAlignedTargetTransitionAt
          A strategy hwin policy state next .right (.inl slot))

theorem
    ProfiledRawJointHybridPhysicalCompatibleRightRootAlignedSuccessorKeyAt.toSuccessorKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state next : CompatibleState A strategy hwin initial}
    {target : ProfiledRawJointIncidenceCode A (I := Unit)}
    (aligned :
      ProfiledRawJointHybridPhysicalCompatibleRightRootAlignedSuccessorKeyAt A
        strategy hwin policy state next target) :
    ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A strategy hwin
      policy state next target := by
  rcases aligned with ⟨slot, hlive, ⟨transition⟩⟩
  exact ⟨slot, hlive, ⟨transition.transition⟩⟩

theorem
    ProfiledRawJointHybridPhysicalCompatibleLeftRootAlignedSuccessorKeyAt.toSuccessorKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state next : CompatibleState A strategy hwin initial}
    {target : ProfiledRawJointIncidenceCode A (I := Unit)}
    (aligned :
      ProfiledRawJointHybridPhysicalCompatibleLeftRootAlignedSuccessorKeyAt A
        strategy hwin policy state next target) :
    ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A strategy hwin
      policy state next target := by
  rcases aligned with ⟨slot, hlive, ⟨transition⟩⟩
  exact ⟨slot, hlive, ⟨transition.transition⟩⟩

/-! ### Reachability carried by successor keys -/

/-- The fixed compatible policy starts at a reachable key. -/
theorem profiledRawJointHybridPhysicalCompatiblePolicy_root_reachable
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    ProfiledRawJointHybridPhysicalCompatibleReachable A strategy hwin initial
      policy (policy.run []) :=
  ⟨[], rfl⟩

/-- An exact retained transition preserves reachability in the same selected
rational policy. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt.reachable
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state next : CompatibleState A strategy hwin initial}
    {side : IndexedLineageSide} {root : ProfiledRawJointThreadRoot A}
    (transition :
      ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A strategy
        hwin policy state next side root)
    (hstate : ProfiledRawJointHybridPhysicalCompatibleReachable A strategy
      hwin initial policy state) :
    ProfiledRawJointHybridPhysicalCompatibleReachable A strategy hwin initial
      policy next := by
  rcases hstate with ⟨node, hnode⟩
  refine ⟨node ++ [transition.childCode], ?_⟩
  calc
    policy.run (node ++ [transition.childCode]) =
        policy.successor (policy.run node) transition.childCode :=
      (policy.successor_at node transition.childCode).symm
    _ = policy.successor state transition.childCode := by rw [hnode]
    _ = next := transition.successor.symm

/-- Hence a retained right key carries the reachability invariant needed by
the next finite-table decoration. -/
theorem ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt.reachable
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state next : CompatibleState A strategy hwin initial}
    {target : ProfiledRawJointIncidenceCode A (I := Unit)}
    (hkey : ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A
      strategy hwin policy state next target)
    (hstate : ProfiledRawJointHybridPhysicalCompatibleReachable A strategy
      hwin initial policy state) :
    ProfiledRawJointHybridPhysicalCompatibleReachable A strategy hwin initial
      policy next := by
  rcases hkey with ⟨_slot, _hlive, ⟨transition⟩⟩
  exact transition.reachable A strategy hwin hstate

/-- Left mirror. -/
theorem ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt.reachable
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state next : CompatibleState A strategy hwin initial}
    {target : ProfiledRawJointIncidenceCode A (I := Unit)}
    (hkey : ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A
      strategy hwin policy state next target)
    (hstate : ProfiledRawJointHybridPhysicalCompatibleReachable A strategy
      hwin initial policy state) :
    ProfiledRawJointHybridPhysicalCompatibleReachable A strategy hwin initial
      policy next := by
  rcases hkey with ⟨_slot, _hlive, ⟨transition⟩⟩
  exact transition.reachable A strategy hwin hstate

/-- A checked right target has at least one exact finite successor key. -/
theorem exists_profiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
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
    ∃ next : CompatibleState A strategy hwin initial,
      ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A strategy
        hwin policy state next target := by
  let targetAt :
      ProfiledRawJointHybridPhysicalCompatibleTableTargetAt A strategy hwin
        state .left (.inr slot) :=
    .right currentCode current_code currentRoot current_live move move_eq
      target target_allowed slot target_live
  rcases targetAt.exists_transition A strategy hwin policy state hreachable with
    ⟨next, hnext⟩
  exact ⟨next, slot, target_live, hnext⟩

/-- Left mirror. -/
theorem exists_profiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
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
    ∃ next : CompatibleState A strategy hwin initial,
      ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A strategy
        hwin policy state next target := by
  let targetAt :
      ProfiledRawJointHybridPhysicalCompatibleTableTargetAt A strategy hwin
        state .right (.inl slot) :=
    .left currentCode current_code currentRoot current_live move move_eq
      target target_allowed slot target_live
  rcases targetAt.exists_transition A strategy hwin policy state hreachable with
    ⟨next, hnext⟩
  exact ⟨next, slot, target_live, hnext⟩

/-- A checked right target admits a successor key whose installed physical
move is based at the crossed live slot. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleRightRootAlignedSuccessorKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
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
    ∃ next : CompatibleState A strategy hwin initial,
      ProfiledRawJointHybridPhysicalCompatibleRightRootAlignedSuccessorKeyAt A
        strategy hwin policy state next target := by
  let targetAt :
      ProfiledRawJointHybridPhysicalCompatibleTableTargetAt A strategy hwin
        state .left (.inr slot) :=
    .right currentCode current_code currentRoot current_live move move_eq
      target target_allowed slot target_live
  rcases
      targetAt.exists_rootAlignedTransition A strategy hwin policy state
        hreachable with
    ⟨next, hnext⟩
  exact ⟨next, slot, target_live, hnext⟩

/-- Left root-aligned mirror. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleLeftRootAlignedSuccessorKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
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
    ∃ next : CompatibleState A strategy hwin initial,
      ProfiledRawJointHybridPhysicalCompatibleLeftRootAlignedSuccessorKeyAt A
        strategy hwin policy state next target := by
  let targetAt :
      ProfiledRawJointHybridPhysicalCompatibleTableTargetAt A strategy hwin
        state .right (.inl slot) :=
    .left currentCode current_code currentRoot current_live move move_eq
      target target_allowed slot target_live
  rcases
      targetAt.exists_rootAlignedTransition A strategy hwin policy state
        hreachable with
    ⟨next, hnext⟩
  exact ⟨next, slot, target_live, hnext⟩

/-- Choose the finite right successor key whenever one exists, retaining the
current key only on irrelevant unchecked table entries. -/
noncomputable def profiledRawJointHybridPhysicalCompatibleRightSuccessorKey
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    CompatibleState A strategy hwin initial := by
  classical
  exact if h : ∃ next,
      ProfiledRawJointHybridPhysicalCompatibleRightRootAlignedSuccessorKeyAt A
        strategy hwin policy state next target then h.choose else state

theorem
    profiledRawJointHybridPhysicalCompatibleRightSuccessorKey_rootAligned_spec
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hex : ∃ next,
      ProfiledRawJointHybridPhysicalCompatibleRightRootAlignedSuccessorKeyAt A
        strategy hwin policy state next target) :
    ProfiledRawJointHybridPhysicalCompatibleRightRootAlignedSuccessorKeyAt A
      strategy hwin policy state
        (profiledRawJointHybridPhysicalCompatibleRightSuccessorKey A strategy
          hwin policy state target) target := by
  classical
  rw [profiledRawJointHybridPhysicalCompatibleRightSuccessorKey]
  split
  · exact Classical.choose_spec ‹∃ next, _›
  · contradiction

theorem profiledRawJointHybridPhysicalCompatibleRightSuccessorKey_spec
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hex : ∃ next,
      ProfiledRawJointHybridPhysicalCompatibleRightRootAlignedSuccessorKeyAt A
        strategy hwin policy state next target) :
    ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A strategy
      hwin policy state
        (profiledRawJointHybridPhysicalCompatibleRightSuccessorKey A strategy
          hwin policy state target) target := by
  exact
    (profiledRawJointHybridPhysicalCompatibleRightSuccessorKey_rootAligned_spec
      A strategy hwin policy state target hex).toSuccessorKeyAt

/-- Left key choice. -/
noncomputable def profiledRawJointHybridPhysicalCompatibleLeftSuccessorKey
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    CompatibleState A strategy hwin initial := by
  classical
  exact if h : ∃ next,
      ProfiledRawJointHybridPhysicalCompatibleLeftRootAlignedSuccessorKeyAt A
        strategy hwin policy state next target then h.choose else state

theorem
    profiledRawJointHybridPhysicalCompatibleLeftSuccessorKey_rootAligned_spec
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hex : ∃ next,
      ProfiledRawJointHybridPhysicalCompatibleLeftRootAlignedSuccessorKeyAt A
        strategy hwin policy state next target) :
    ProfiledRawJointHybridPhysicalCompatibleLeftRootAlignedSuccessorKeyAt A
      strategy hwin policy state
        (profiledRawJointHybridPhysicalCompatibleLeftSuccessorKey A strategy
          hwin policy state target) target := by
  classical
  rw [profiledRawJointHybridPhysicalCompatibleLeftSuccessorKey]
  split
  · exact Classical.choose_spec ‹∃ next, _›
  · contradiction

theorem profiledRawJointHybridPhysicalCompatibleLeftSuccessorKey_spec
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hex : ∃ next,
      ProfiledRawJointHybridPhysicalCompatibleLeftRootAlignedSuccessorKeyAt A
        strategy hwin policy state next target) :
    ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A strategy
      hwin policy state
        (profiledRawJointHybridPhysicalCompatibleLeftSuccessorKey A strategy
          hwin policy state target) target := by
  exact
    (profiledRawJointHybridPhysicalCompatibleLeftSuccessorKey_rootAligned_spec
      A strategy hwin policy state target hex).toSuccessorKeyAt

/-! ## Row-exact finite receiver decoration -/

abbrev ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  RowExactIndexedTargetReceiverOutput
    (PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    PairedEntryRow
    (ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A strategy hwin
      initial)
    (profiledRawJointHybridPhysicalCompatibleSuccessorTargetRow A strategy
      hwin)

abbrev ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  RowExactIndexedTargetReceiverOutput
    (PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    PairedEntryRow
    (ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A strategy hwin
      initial)
    (profiledRawJointHybridPhysicalCompatibleSuccessorTargetRow A strategy
      hwin)

/-- Forget the successor key and its row proof. -/
def profiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverProjection
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
        strategy hwin initial) :
    ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)) :=
  { physical := output.physical
    target := fun row ↦ (output.target row).1.1 }

def profiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverProjection
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
        strategy hwin initial) :
    ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)) :=
  { physical := output.physical
    target := fun row ↦ (output.target row).1.1 }

/-- Decorate all cells of one old right receiver table. -/
def profiledRawJointHybridPhysicalCompatibleDecorateRightReceiverOutput
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (output : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit))) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
      strategy hwin initial :=
  RowExactIndexedTargetReceiverOutput.ofTarget output.physical
    (fun row ↦
      (output.target row,
        (row,
          profiledRawJointHybridPhysicalCompatibleRightSuccessorKey A
            strategy hwin policy state (output.target row))))
    (fun _ ↦ rfl)

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleDecorateRightReceiverOutput_project
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (output : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit))) :
    profiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverProjection A
        strategy hwin
        (profiledRawJointHybridPhysicalCompatibleDecorateRightReceiverOutput A
          strategy hwin policy state output) = output :=
  rfl

/-- Left decoration. -/
def profiledRawJointHybridPhysicalCompatibleDecorateLeftReceiverOutput
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (output : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit))) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
      strategy hwin initial :=
  RowExactIndexedTargetReceiverOutput.ofTarget output.physical
    (fun row ↦
      (output.target row,
        (row,
          profiledRawJointHybridPhysicalCompatibleLeftSuccessorKey A
            strategy hwin policy state (output.target row))))
    (fun _ ↦ rfl)

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleDecorateLeftReceiverOutput_project
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (output : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit))) :
    profiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverProjection A
        strategy hwin
        (profiledRawJointHybridPhysicalCompatibleDecorateLeftReceiverOutput A
          strategy hwin policy state output) = output :=
  rfl

/-! ## The fail-fast exact equations -/

/-- On an allowed live right cell, the key physically retained by the
decoration is an exact root-aligned successor of the same compatible policy. -/
theorem
    profiledRawJointHybridPhysicalCompatibleDecorateRightReceiverOutput_key
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
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
    ProfiledRawJointHybridPhysicalCompatibleRightRootAlignedSuccessorKeyAt A
      strategy hwin policy state
      (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin
        ((profiledRawJointHybridPhysicalCompatibleDecorateRightReceiverOutput
          A strategy hwin policy state output).target row).1)
      (output.target row) := by
  apply
    profiledRawJointHybridPhysicalCompatibleRightSuccessorKey_rootAligned_spec
      A strategy hwin policy state
  exact
    exists_profiledRawJointHybridPhysicalCompatibleRightRootAlignedSuccessorKeyAt
      A strategy hwin policy state hreachable currentCode current_code
        currentRoot current_live move move_eq (output.target row) target_allowed
        slot target_live

/-- Left fail-fast equation. -/
theorem
    profiledRawJointHybridPhysicalCompatibleDecorateLeftReceiverOutput_key
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
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
    ProfiledRawJointHybridPhysicalCompatibleLeftRootAlignedSuccessorKeyAt A
      strategy hwin policy state
      (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin
        ((profiledRawJointHybridPhysicalCompatibleDecorateLeftReceiverOutput
          A strategy hwin policy state output).target row).1)
      (output.target row) := by
  apply
    profiledRawJointHybridPhysicalCompatibleLeftSuccessorKey_rootAligned_spec A
      strategy hwin policy state
  exact
    exists_profiledRawJointHybridPhysicalCompatibleLeftRootAlignedSuccessorKeyAt
      A strategy hwin policy state hreachable currentCode current_code
        currentRoot current_live move move_eq (output.target row) target_allowed
        slot target_live

/-! ## Decoration of the already finite member controllers -/

/-- The old right monitor comapped through successor-key erasure. -/
noncomputable abbrev
    profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool) :=
  (profiledRawJointRightPhysicalSiblingMonitor A move.1 member
    ).comapReceiverOutput
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverProjection
        A strategy hwin (initial := initial))

/-- Retain a same-policy key in every receiver cell of an already finite
right member controller.  Its finite control, blind sender output, and blind
sender step are copied literally. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool) :=
  (move.memberController A member).decorateReceiverOutput
    (profiledRawJointRightPhysicalSiblingMonitor A move.1 member)
    (profiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverProjection
      A strategy hwin)
    (fun _ _ output ↦
      profiledRawJointHybridPhysicalCompatibleDecorateRightReceiverOutput A
        strategy hwin policy state output)

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController_controlAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool)
    (word : List In₁) :
    (profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController A
      strategy hwin policy state move member).controlAt word =
        (move.memberController A member).controlAt word :=
  rfl

/-- The sender cannot distinguish the successor-key decoration. -/
@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController_sender
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool)
    (word : List In₁) :
    ((profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController A
      strategy hwin policy state move member).labeledTree word).1 =
        ((move.memberController A member).labeledTree word).1 :=
  rfl

/-- Universal block acceptance survives the right key decoration. -/
theorem
    profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController_wins
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool) :
    NarrowedAllThreadsWin
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
        strategy hwin (initial := initial) move member)
      (profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController A
        strategy hwin policy state move member).labeledTree := by
  apply TransitionRationalTree.decorateReceiverOutput_allThreadsWin
    (profiledRawJointRightPhysicalSiblingMonitor A move.1 member)
    (profiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverProjection
      A strategy hwin)
    (fun _ _ output ↦
      profiledRawJointHybridPhysicalCompatibleDecorateRightReceiverOutput A
        strategy hwin policy state output)
    (fun _ _ _ ↦ rfl)
  exact move.memberController_wins A member

/-- Fail-fast label equation for the decorated finite right controller.  Once
the old physical monitor supplies `target_allowed` and `target_live`, the
target key stored in the very same finite table cell is an exact child of the
same outer policy. -/
theorem
    profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController_key
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
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
      profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController A
        strategy hwin policy state move member
    let target := ((decorated.labeledTree word).2 monitorState input).target row
    ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A strategy
      hwin policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target.1)
        target.1.1 := by
  dsimp only
  exact
    (profiledRawJointHybridPhysicalCompatibleDecorateRightReceiverOutput_key A
      strategy hwin policy state hreachable currentCode current_code
        currentRoot current_live move move_eq
        (((move.memberController A member).labeledTree word).2 monitorState input)
        row target_allowed slot target_live).toSuccessorKeyAt

/-! ### Left mirror -/

noncomputable abbrev
    profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool) :=
  (profiledRawJointLeftPhysicalSiblingMonitor A move.1 member
    ).comapReceiverOutput
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverProjection
        A strategy hwin (initial := initial))

noncomputable def
    profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool) :=
  (move.memberController A member).decorateReceiverOutput
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1 member)
    (profiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverProjection
      A strategy hwin)
    (fun _ _ output ↦
      profiledRawJointHybridPhysicalCompatibleDecorateLeftReceiverOutput A
        strategy hwin policy state output)

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController_controlAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool)
    (word : List In₂) :
    (profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
      strategy hwin policy state move member).controlAt word =
        (move.memberController A member).controlAt word :=
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController_sender
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool)
    (word : List In₂) :
    ((profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
      strategy hwin policy state move member).labeledTree word).1 =
        ((move.memberController A member).labeledTree word).1 :=
  rfl

theorem
    profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController_wins
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool) :
    NarrowedAllThreadsWin
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move member)
      (profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
        strategy hwin policy state move member).labeledTree := by
  apply TransitionRationalTree.decorateReceiverOutput_allThreadsWin
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1 member)
    (profiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverProjection A
      strategy hwin)
    (fun _ _ output ↦
      profiledRawJointHybridPhysicalCompatibleDecorateLeftReceiverOutput A
        strategy hwin policy state output)
    (fun _ _ _ ↦ rfl)
  exact move.memberController_wins A member

theorem
    profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController_key
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
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
      profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
        strategy hwin policy state move member
    let target := ((decorated.labeledTree word).2 monitorState input).target row
    ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A strategy hwin
      policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target.1)
        target.1.1 := by
  dsimp only
  exact
    (profiledRawJointHybridPhysicalCompatibleDecorateLeftReceiverOutput_key A
      strategy hwin policy state hreachable currentCode current_code
        currentRoot current_live move move_eq
        (((move.memberController A member).labeledTree word).2 monitorState input)
        row target_allowed slot target_live).toSuccessorKeyAt

end

end DetParityAutomaton

end DistributedSynthesis
