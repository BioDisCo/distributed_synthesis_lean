/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionPostResolveFreshTargetBank

/-!
# Staging the selected post-resolve recurrent target

The informed endpoint of a post-resolve block stores the strict/common member
selected at the resolving receive.  After every subsequent block round it can
therefore select the corresponding row of the dispatcher's finite target
table and retain the resulting orientation-tagged recurrent root.

Only this selected finite root is staged.  No history, semantic occurrence,
policy, graph, orientation, or unobserved input is added to a local control.
On every state reachable from the concrete installation, the checked target
lookup succeeds.  The staged owner used by a later local non-receive and the
staged receiver read from the delivered control are definitionally indexed by
the same recurrent key.
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

private abbrev LeftSenderState :=
  ProfiledRawJointStrictLeftPostResolveFiniteSenderState A

private abbrev LeftReceiverState :=
  ProfiledRawJointStrictLeftPostResolveFiniteReceiverState A

private abbrev RightSenderState :=
  ProfiledRawJointStrictRightPostResolveFiniteSenderState A

private abbrev RightReceiverState :=
  ProfiledRawJointStrictRightPostResolveFiniteReceiverState A

/-! ## The finite selected row -/

/-- The strict member uses the first row and the simultaneous member uses the
both row.  The member is already finite local data of the informed endpoint. -/
def profiledRawJointPostResolveRowOfBranch (branch : Bool) : PairedEntryRow :=
  if branch then .both else .first

@[simp] theorem profiledRawJointPostResolveRowOfBranch_false :
    profiledRawJointPostResolveRowOfBranch false = .first :=
  rfl

@[simp] theorem profiledRawJointPostResolveRowOfBranch_true :
    profiledRawJointPostResolveRowOfBranch true = .both :=
  rfl

/-! ## Finite staged receiver states -/

/-- Process two's informed state during a right block, together with the
left-oriented recurrent root selected by its latest receive. -/
abbrev ProfiledRawJointStrictLeftPostResolveStagedReceiverState :=
  LeftReceiverState A ×
    Option (ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)

/-- Process one's informed state during a left block, with the mirrored
right-oriented recurrent root. -/
abbrev ProfiledRawJointStrictRightPostResolveStagedReceiverState :=
  RightReceiverState A ×
    Option (ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)

noncomputable instance :
    Fintype (ProfiledRawJointStrictLeftPostResolveStagedReceiverState A
      strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointStrictRightPostResolveStagedReceiverState A
      strategy) := by
  classical
  infer_instance

/-- Installation precedes the first round of the new right block, so no
target from that block has yet been emitted. -/
noncomputable def profiledRawJointStrictLeftPostResolveStagedReceiverInitial
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) :
    ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy :=
  (profiledRawJointStrictLeftPostResolveFiniteReceiverInitial A strategy hwin
    initial entry input branch, none)

/-- Mirrored initial staged state. -/
noncomputable def profiledRawJointStrictRightPostResolveStagedReceiverInitial
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) :
    ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy :=
  (profiledRawJointStrictRightPostResolveFiniteReceiverInitial A strategy hwin
    initial entry input branch, none)

/-! ## One block round and target replacement -/

/-- A right-block result retains the ordinary finite dispatch record and
replaces the previously staged target by the target emitted in the selected
row of this round. -/
structure ProfiledRawJointStrictLeftPostResolveStagedDispatchResult where
  dispatch : ProfiledRawJointStrictLeftPostResolveFiniteDispatchResult A
  nextReceiver :
    ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy

/-- Mirrored left-block result. -/
structure ProfiledRawJointStrictRightPostResolveStagedDispatchResult where
  dispatch : ProfiledRawJointStrictRightPostResolveFiniteDispatchResult A
  nextReceiver :
    ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy

/-- Execute one right-block round and stage exactly the member-selected
left-oriented root.  A failed checked lookup is retained as `none`; the
reachability theorem below excludes that branch on every real execution. -/
noncomputable def profiledRawJointStrictLeftPostResolveStagedDispatch
    (state : LeftSenderState A ×
      ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy)
    (own : In₂) (delivered : In₁) :
    ProfiledRawJointStrictLeftPostResolveStagedDispatchResult A strategy :=
  let dispatch := profiledRawJointStrictLeftPostResolveFiniteDispatch A
    (state.1, state.2.1) own delivered
  let row := profiledRawJointPostResolveRowOfBranch
    dispatch.nextReceiver.2.1
  let staged := profiledRawJointPostResolveRightFreshInstalledRoot? A strategy
    (dispatch.receiverOutput.target row) row
  ⟨dispatch, (dispatch.nextReceiver, staged)⟩

/-- Mirrored execute-and-stage map. -/
noncomputable def profiledRawJointStrictRightPostResolveStagedDispatch
    (state : RightSenderState A ×
      ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy)
    (own : In₁) (delivered : In₂) :
    ProfiledRawJointStrictRightPostResolveStagedDispatchResult A strategy :=
  let dispatch := profiledRawJointStrictRightPostResolveFiniteDispatch A
    (state.1, state.2.1) own delivered
  let row := profiledRawJointPostResolveRowOfBranch
    dispatch.nextReceiver.2.1
  let staged := profiledRawJointPostResolveLeftFreshInstalledRoot? A strategy
    (dispatch.receiverOutput.target row) row
  ⟨dispatch, (dispatch.nextReceiver, staged)⟩

@[simp] theorem profiledRawJointStrictLeftPostResolveStagedDispatch_descriptor
    (state : LeftSenderState A ×
      ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy)
    (own : In₂) (delivered : In₁) :
    (profiledRawJointStrictLeftPostResolveStagedDispatch A strategy state own
      delivered).nextReceiver.1 =
      (profiledRawJointStrictLeftPostResolveFiniteDispatch A
        (state.1, state.2.1) own delivered).nextReceiver :=
  rfl

@[simp] theorem profiledRawJointStrictRightPostResolveStagedDispatch_descriptor
    (state : RightSenderState A ×
      ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy)
    (own : In₁) (delivered : In₂) :
    (profiledRawJointStrictRightPostResolveStagedDispatch A strategy state own
      delivered).nextReceiver.1 =
      (profiledRawJointStrictRightPostResolveFiniteDispatch A
        (state.1, state.2.1) own delivered).nextReceiver :=
  rfl

/-! ## Reachable staging cannot fail -/

/-- Every reachable right-block step replaces the staged cell by a genuine
left-rooted recurrent package at the selected row. -/
theorem profiledRawJointStrictLeftPostResolveStagedDispatch_isSome
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool)
    (state : LeftSenderState A ×
      ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy)
    (hstate : ProfiledRawJointStrictLeftPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch (state.1, state.2.1))
    (current : In₂ × In₁) :
    ∃ root :
        ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy,
      (profiledRawJointStrictLeftPostResolveStagedDispatch A strategy state
        current.1 current.2).nextReceiver.2 = some root := by
  let dispatch := profiledRawJointStrictLeftPostResolveFiniteDispatch A
    (state.1, state.2.1) current.1 current.2
  let row := profiledRawJointPostResolveRowOfBranch
    dispatch.nextReceiver.2.1
  obtain ⟨root, hroot⟩ :=
    profiledRawJointStrictLeftPostResolveFiniteDispatch_rightFreshInstalledRoot?
      A strategy hwin initial entry input branch (state.1, state.2.1) hstate
        current row
  exact ⟨root, hroot⟩

/-- Mirrored reachable lookup success. -/
theorem profiledRawJointStrictRightPostResolveStagedDispatch_isSome
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool)
    (state : RightSenderState A ×
      ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy)
    (hstate : ProfiledRawJointStrictRightPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch (state.1, state.2.1))
    (current : In₁ × In₂) :
    ∃ root :
        ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy,
      (profiledRawJointStrictRightPostResolveStagedDispatch A strategy state
        current.1 current.2).nextReceiver.2 = some root := by
  let dispatch := profiledRawJointStrictRightPostResolveFiniteDispatch A
    (state.1, state.2.1) current.1 current.2
  let row := profiledRawJointPostResolveRowOfBranch
    dispatch.nextReceiver.2.1
  obtain ⟨root, hroot⟩ :=
    profiledRawJointStrictRightPostResolveFiniteDispatch_leftFreshInstalledRoot?
      A strategy hwin initial entry input branch (state.1, state.2.1) hstate
        current row
  exact ⟨root, hroot⟩

/-- The source of a successfully staged right-block root has exactly the
target emitted in the selected row of that round. -/
theorem profiledRawJointStrictLeftPostResolveStagedDispatch_source_code
    (state : LeftSenderState A ×
      ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy)
    (own : In₂) (delivered : In₁)
    (root : ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (hroot :
      (profiledRawJointStrictLeftPostResolveStagedDispatch A strategy state own
        delivered).nextReceiver.2 = some root) :
    let dispatch := profiledRawJointStrictLeftPostResolveFiniteDispatch A
      (state.1, state.2.1) own delivered
    let row := profiledRawJointPostResolveRowOfBranch
      dispatch.nextReceiver.2.1
    (profiledRawJointPostResolveFreshTargetSource A strategy (.inl root.1)
      ).code A = dispatch.receiverOutput.target row := by
  dsimp only
  apply profiledRawJointPostResolveRightFreshInstalledRoot?_source_code A
    strategy _ _ root
  exact hroot

/-- Mirrored exact source-code theorem. -/
theorem profiledRawJointStrictRightPostResolveStagedDispatch_source_code
    (state : RightSenderState A ×
      ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy)
    (own : In₁) (delivered : In₂)
    (root : ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (hroot :
      (profiledRawJointStrictRightPostResolveStagedDispatch A strategy state own
        delivered).nextReceiver.2 = some root) :
    let dispatch := profiledRawJointStrictRightPostResolveFiniteDispatch A
      (state.1, state.2.1) own delivered
    let row := profiledRawJointPostResolveRowOfBranch
      dispatch.nextReceiver.2.1
    (profiledRawJointPostResolveFreshTargetSource A strategy (.inr root.1)
      ).code A = dispatch.receiverOutput.target row := by
  dsimp only
  apply profiledRawJointPostResolveLeftFreshInstalledRoot?_source_code A
    strategy _ _ root
  exact hroot

/-! ## Two local projections of one staged recurrent root -/

/-- The blind process-two activation reads the owner projection of the root
that it staged while it was the informed endpoint. -/
def profiledRawJointStrictLeftPostResolveStagedLeftOwner?
    (state :
      ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy) :
    Option
      (ProfiledRawJointPostResolveFreshTargetLeftOwnerControl A strategy) :=
  state.2.map fun root ↦ ⟨.inl root.1, root.2.1⟩

/-- A process-one receive reads the receiver projection from the delivered
copy of exactly the same staged root. -/
def profiledRawJointStrictLeftPostResolveStagedLeftReceiver?
    (state :
      ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy) :
    Option
      (ProfiledRawJointPostResolveFreshTargetLeftReceiverControl A strategy) :=
  state.2.map fun root ↦ ⟨.inl root.1, root.2.2⟩

/-- Mirrored process-one owner activation. -/
def profiledRawJointStrictRightPostResolveStagedRightOwner?
    (state :
      ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy) :
    Option
      (ProfiledRawJointPostResolveFreshTargetRightOwnerControl A strategy) :=
  state.2.map fun root ↦ ⟨.inr root.1, root.2.1⟩

/-- Mirrored delivered receiver projection. -/
def profiledRawJointStrictRightPostResolveStagedRightReceiver?
    (state :
      ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy) :
    Option
      (ProfiledRawJointPostResolveFreshTargetRightReceiverControl A strategy) :=
  state.2.map fun root ↦ ⟨.inr root.1, root.2.2⟩

/-- Both local activations of a staged right-block target carry one literal
common key. -/
theorem profiledRawJointStrictLeftPostResolveStaged_common_key
    (state :
      ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy)
    (root : ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (hroot : state.2 = some root) :
    profiledRawJointStrictLeftPostResolveStagedLeftOwner? A strategy state =
        some ⟨.inl root.1, root.2.1⟩ ∧
      profiledRawJointStrictLeftPostResolveStagedLeftReceiver? A strategy
        state = some ⟨.inl root.1, root.2.2⟩ := by
  simp [profiledRawJointStrictLeftPostResolveStagedLeftOwner?,
    profiledRawJointStrictLeftPostResolveStagedLeftReceiver?, hroot]

/-- Mirrored common-key activation. -/
theorem profiledRawJointStrictRightPostResolveStaged_common_key
    (state :
      ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy)
    (root : ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (hroot : state.2 = some root) :
    profiledRawJointStrictRightPostResolveStagedRightOwner? A strategy state =
        some ⟨.inr root.1, root.2.1⟩ ∧
      profiledRawJointStrictRightPostResolveStagedRightReceiver? A strategy
        state = some ⟨.inr root.1, root.2.2⟩ := by
  simp [profiledRawJointStrictRightPostResolveStagedRightOwner?,
    profiledRawJointStrictRightPostResolveStagedRightReceiver?, hroot]

/-- A reachable right-block step supplies both local recurrent projections
at one orientation-refined key. -/
theorem profiledRawJointStrictLeftPostResolveStagedDispatch_activates
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool)
    (state : LeftSenderState A ×
      ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy)
    (hstate : ProfiledRawJointStrictLeftPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch (state.1, state.2.1))
    (current : In₂ × In₁) :
    let next := (profiledRawJointStrictLeftPostResolveStagedDispatch A strategy
      state current.1 current.2).nextReceiver
    ∃ root :
        ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy,
      profiledRawJointStrictLeftPostResolveStagedLeftOwner? A strategy next =
          some ⟨.inl root.1, root.2.1⟩ ∧
        profiledRawJointStrictLeftPostResolveStagedLeftReceiver? A strategy
          next = some ⟨.inl root.1, root.2.2⟩ := by
  dsimp only
  obtain ⟨root, hroot⟩ :=
    profiledRawJointStrictLeftPostResolveStagedDispatch_isSome A strategy hwin
      initial entry input branch state hstate current
  exact ⟨root,
    profiledRawJointStrictLeftPostResolveStaged_common_key A strategy _ root
      hroot⟩

/-- Mirrored reachable two-projection activation. -/
theorem profiledRawJointStrictRightPostResolveStagedDispatch_activates
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool)
    (state : RightSenderState A ×
      ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy)
    (hstate : ProfiledRawJointStrictRightPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch (state.1, state.2.1))
    (current : In₁ × In₂) :
    let next :=
      (profiledRawJointStrictRightPostResolveStagedDispatch A strategy state
        current.1 current.2).nextReceiver
    ∃ root :
        ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy,
      profiledRawJointStrictRightPostResolveStagedRightOwner? A strategy next =
          some ⟨.inr root.1, root.2.1⟩ ∧
        profiledRawJointStrictRightPostResolveStagedRightReceiver? A strategy
          next = some ⟨.inr root.1, root.2.2⟩ := by
  dsimp only
  obtain ⟨root, hroot⟩ :=
    profiledRawJointStrictRightPostResolveStagedDispatch_isSome A strategy hwin
      initial entry input branch state hstate current
  exact ⟨root,
    profiledRawJointStrictRightPostResolveStaged_common_key A strategy _ root
      hroot⟩

end

end DetParityAutomaton

end DistributedSynthesis
