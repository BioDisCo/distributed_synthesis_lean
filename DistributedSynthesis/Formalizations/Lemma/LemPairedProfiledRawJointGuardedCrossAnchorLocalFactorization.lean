/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLocalStrictInstallation

/-!
# Local factorization of a finite cross-anchor joint move

At a simultaneous receive following a strict round, the two processes hold
opposite halves of one pending state: the old blind owner and the ambiguity
receiver.  After messages are delivered, both processes possess the same two
finite values.  Therefore one finite joint move indexed by that pending pair
can be projected locally by both processes.

This file proves only that distribution/factorization fact.  It is independent
of how the joint move is obtained or why its physical word is accepting.  The
total local projections use a fallback outside the pending invariant.  No
projection accepts a graph, orientation, hierarchy side, leader bit, semantic
world, or history.
-/

namespace DistributedSynthesis

universe u v x y s a b

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

/-! ## Finite joint-move alphabets -/

/-- One finite right-pending joint table.  `NextOne` and `NextTwo` are the
local states installed after the cross anchor. -/
abbrev ProfiledRawJointGuardedRightCrossAnchorLocalFactorizationMove
    (NextOne : Type a) (NextTwo : Type b) :=
  ProfiledRawJointGuardedCommonRightPending A strategy hwin →
    (In₁ × In₂) →
      (Out₁ × NextOne) × (Out₂ × NextTwo)

/-- Left-pending mirror. -/
abbrev ProfiledRawJointGuardedLeftCrossAnchorLocalFactorizationMove
    (NextOne : Type a) (NextTwo : Type b) :=
  ProfiledRawJointGuardedCommonLeftPending A strategy hwin →
    (In₁ × In₂) →
      (Out₁ × NextOne) × (Out₂ × NextTwo)

noncomputable instance
    profiledRawJointGuardedRightCrossAnchorLocalFactorizationMoveFintype
    {NextOne : Type a} {NextTwo : Type b}
    [Fintype NextOne] [Fintype NextTwo] :
    Fintype
      (ProfiledRawJointGuardedRightCrossAnchorLocalFactorizationMove A strategy hwin
        NextOne NextTwo) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointGuardedLeftCrossAnchorLocalFactorizationMoveFintype
    {NextOne : Type a} {NextTwo : Type b}
    [Fintype NextOne] [Fintype NextTwo] :
    Fintype
      (ProfiledRawJointGuardedLeftCrossAnchorLocalFactorizationMove A strategy hwin
        NextOne NextTwo) := by
  classical
  infer_instance

/-! ## Reconstructing the shared pending key -/

/-- Both receive projections use this same finite check and constructor. -/
noncomputable def profiledRawJointGuardedRightLocalFactorizationPendingOf?
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (receiver : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin) :
    Option (ProfiledRawJointGuardedCommonRightPending A strategy hwin) := by
  classical
  exact if h : owner.1 = receiver.shadow.source then
    some ⟨owner, receiver, h⟩
  else none

/-- Left mirror. -/
noncomputable def profiledRawJointGuardedLeftLocalFactorizationPendingOf?
    (receiver : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin) :
    Option (ProfiledRawJointGuardedCommonLeftPending A strategy hwin) := by
  classical
  exact if h : owner.1 = receiver.shadow.source then
    some ⟨receiver, owner, h⟩
  else none

@[simp] theorem profiledRawJointGuardedRightLocalFactorizationPendingOf?_components
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin) :
    profiledRawJointGuardedRightLocalFactorizationPendingOf? A strategy hwin pending.owner
      pending.receiver = some pending := by
  rcases pending with ⟨owner, receiver, hsource⟩
  simp [profiledRawJointGuardedRightLocalFactorizationPendingOf?, hsource]

@[simp] theorem profiledRawJointGuardedLeftLocalFactorizationPendingOf?_components
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin) :
    profiledRawJointGuardedLeftLocalFactorizationPendingOf? A strategy hwin pending.receiver
      pending.owner = some pending := by
  rcases pending with ⟨receiver, owner, hsource⟩
  simp [profiledRawJointGuardedLeftLocalFactorizationPendingOf?, hsource]

/-! ## Total graph-blind local projections -/

/-- Process one reconstructs the right-pending key from its stored owner and
the delivered receiver, then takes the first projection of the joint move. -/
noncomputable def profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecvOne
    {NextOne : Type a} {NextTwo : Type b}
    (move : ProfiledRawJointGuardedRightCrossAnchorLocalFactorizationMove A strategy hwin
      NextOne NextTwo)
    (fallback : Out₁ × NextOne)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (receiver : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (own : In₁) (delivered : In₂) : Out₁ × NextOne :=
  match profiledRawJointGuardedRightLocalFactorizationPendingOf? A strategy hwin owner receiver
    with
  | some pending => (move pending (own, delivered)).1
  | none => fallback

/-- Process two has the same two values in the opposite local/received order
and takes the second projection of the same table. -/
noncomputable def profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecvTwo
    {NextOne : Type a} {NextTwo : Type b}
    (move : ProfiledRawJointGuardedRightCrossAnchorLocalFactorizationMove A strategy hwin
      NextOne NextTwo)
    (fallback : Out₂ × NextTwo)
    (receiver : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (own : In₂) (delivered : In₁) : Out₂ × NextTwo :=
  match profiledRawJointGuardedRightLocalFactorizationPendingOf? A strategy hwin owner receiver
    with
  | some pending => (move pending (delivered, own)).2
  | none => fallback

noncomputable def profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecvOne
    {NextOne : Type a} {NextTwo : Type b}
    (move : ProfiledRawJointGuardedLeftCrossAnchorLocalFactorizationMove A strategy hwin
      NextOne NextTwo)
    (fallback : Out₁ × NextOne)
    (receiver : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (own : In₁) (delivered : In₂) : Out₁ × NextOne :=
  match profiledRawJointGuardedLeftLocalFactorizationPendingOf? A strategy hwin receiver owner
    with
  | some pending => (move pending (own, delivered)).1
  | none => fallback

noncomputable def profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecvTwo
    {NextOne : Type a} {NextTwo : Type b}
    (move : ProfiledRawJointGuardedLeftCrossAnchorLocalFactorizationMove A strategy hwin
      NextOne NextTwo)
    (fallback : Out₂ × NextTwo)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (receiver : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (own : In₂) (delivered : In₁) : Out₂ × NextTwo :=
  match profiledRawJointGuardedLeftLocalFactorizationPendingOf? A strategy hwin receiver owner
    with
  | some pending => (move pending (delivered, own)).2
  | none => fallback

/-! ## Exact reconstruction on represented pending states -/

/-- The two independently executable receive projections reconstruct exactly
one right-pending joint step. -/
theorem profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecv_pair
    {NextOne : Type a} {NextTwo : Type b}
    (move : ProfiledRawJointGuardedRightCrossAnchorLocalFactorizationMove A strategy hwin
      NextOne NextTwo)
    (fallbackOne : Out₁ × NextOne) (fallbackTwo : Out₂ × NextTwo)
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecvOne A strategy hwin move
        fallbackOne pending.owner pending.receiver input.1 input.2,
      profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecvTwo A strategy hwin move
        fallbackTwo pending.receiver pending.owner input.2 input.1) =
      move pending input := by
  simp [profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecvOne,
    profiledRawJointGuardedRightCrossAnchorLocalFactorizationRecvTwo]

/-- Left-pending mirror. -/
theorem profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecv_pair
    {NextOne : Type a} {NextTwo : Type b}
    (move : ProfiledRawJointGuardedLeftCrossAnchorLocalFactorizationMove A strategy hwin
      NextOne NextTwo)
    (fallbackOne : Out₁ × NextOne) (fallbackTwo : Out₂ × NextTwo)
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecvOne A strategy hwin move
        fallbackOne pending.receiver pending.owner input.1 input.2,
      profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecvTwo A strategy hwin move
        fallbackTwo pending.owner pending.receiver input.2 input.1) =
      move pending input := by
  simp [profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecvOne,
    profiledRawJointGuardedLeftCrossAnchorLocalFactorizationRecvTwo]

end


end DetParityAutomaton

end DistributedSynthesis
