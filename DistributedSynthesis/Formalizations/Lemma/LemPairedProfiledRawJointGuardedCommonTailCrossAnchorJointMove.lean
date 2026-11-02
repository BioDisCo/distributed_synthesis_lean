/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemCodedObservablePostPolicyMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailPendingRebase

/-!
# One jointly selected move at a pending common/strict cross anchor

The old right-table continuation and the successor all-common continuation
are different semantic histories.  They therefore must not be rationalized
independently and compared afterwards.  At the actual receive, however, both
processes possess the same finite composite key: the blind owner's old
source/controller state and the delivered receiver shadow, which contains the
next common-policy control.  The left-pending case is symmetric.

This file gives the local interface for selecting one response table at that
shared key.  Each process receives only the projection it can execute.  The
global one-step equations are definitional, so no cross-history equality and
no leader/orientation test is needed.  `CodedObservablePostPolicy.SelectedMoveAt`
can later supply these tables from one exact-observation rational policy.
-/

namespace DistributedSynthesis

universe a b c d e k u v x y s

/-! ## Reading a finite move bank from one post-policy package -/

namespace CodedObservablePostPolicy

variable {Observation : Type a} {Move : Type b} {Code : Type c}
variable [Fintype Code]
variable
  (S : FiniteThreadSystem.{max a b, d, e} (Move × Observation))
  (initialObservation : Observation) (code : Observation → Code)
  (Valid : Code → Move → Prop)

/-- Choose the raw move exposed by the package at one reachable state. -/
noncomputable def Package.selectedMove
    (package : Package S initialObservation code Valid)
    (state : CodedObservableInputFreeState (Code := Code) S)
    (hreachable : Reachable S initialObservation code Valid package.policy
      state) : Move :=
  (Classical.choice (package.selected state hreachable)).move

theorem Package.selectedMove_valid
    (package : Package S initialObservation code Valid)
    (state : CodedObservableInputFreeState (Code := Code) S)
    (hreachable : Reachable S initialObservation code Valid package.policy
      state) :
    Valid state.1
      (package.selectedMove S initialObservation code Valid state
        hreachable) :=
  (Classical.choice (package.selected state hreachable)).valid

/-- The chosen move determines all exact-observation successors at once. -/
theorem Package.selectedMove_successor_eq
    (package : Package S initialObservation code Valid)
    (state : CodedObservableInputFreeState (Code := Code) S)
    (hreachable : Reachable S initialObservation code Valid package.policy
      state)
    (observation : Observation) :
    package.policy.successor state observation =
      (code observation,
        S.universalRunDPA.step state.2
          (package.selectedMove S initialObservation code Valid state
            hreachable, observation)) :=
  (Classical.choice (package.selected state hreachable)).successor_eq
    observation

/-- Any finite runtime key carrying a reachable outer-policy state obtains a
total finite move bank.  Exact observations remain arguments only of the
proof-side successor theorem below. -/
noncomputable def Package.moveBank
    {Key : Type k}
    (package : Package S initialObservation code Valid)
    (stateAt : Key → CodedObservableInputFreeState (Code := Code) S)
    (reachableAt : ∀ key,
      Reachable S initialObservation code Valid package.policy (stateAt key)) :
    Key → Move :=
  fun key ↦ package.selectedMove S initialObservation code Valid
    (stateAt key) (reachableAt key)

theorem Package.moveBank_successor_eq
    {Key : Type k}
    (package : Package S initialObservation code Valid)
    (stateAt : Key → CodedObservableInputFreeState (Code := Code) S)
    (reachableAt : ∀ key,
      Reachable S initialObservation code Valid package.policy (stateAt key))
    (key : Key) (observation : Observation) :
    package.policy.successor (stateAt key) observation =
      (code observation,
        S.universalRunDPA.step (stateAt key).2
          (package.moveBank S initialObservation code Valid stateAt reachableAt
            key, observation)) :=
  package.selectedMove_successor_eq S initialObservation code Valid
    (stateAt key) (reachableAt key) observation

end CodedObservablePostPolicy

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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

private abbrev InitialOne :=
  ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin

private abbrev InitialTwo :=
  ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin

private abbrev ExceptionalOne :=
  ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin

private abbrev ExceptionalTwo :=
  ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin

private abbrev OneControl :=
  ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin initialBank
    (InitialOne A strategy hwin) (ExceptionalOne A strategy hwin)

private abbrev TwoControl :=
  ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin initialBank
    (InitialTwo A strategy hwin) (ExceptionalTwo A strategy hwin)

/-! ## Finite shared keys -/

/-- The plain runtime data jointly available when a right-pending owner and
receiver are exchanged.  Compatibility is a global reachability invariant,
not a field needed by the executable lookup. -/
structure ProfiledRawJointGuardedRightCrossAnchorKey where
  owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin
  receiver : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin

/-- Left-pending mirror. -/
structure ProfiledRawJointGuardedLeftCrossAnchorKey where
  receiver : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin
  owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin

noncomputable instance profiledRawJointGuardedRightCrossAnchorKeyFintype :
    Fintype
      (ProfiledRawJointGuardedRightCrossAnchorKey A strategy hwin) := by
  classical
  let Rep :=
    ProfiledRawJointGuardedCommonRightOwner A strategy hwin ×
      ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin
  let equiv :
      ProfiledRawJointGuardedRightCrossAnchorKey A strategy hwin ≃ Rep :=
    { toFun := fun key ↦ (key.owner, key.receiver)
      invFun := fun key ↦ ⟨key.1, key.2⟩
      left_inv := by intro key; cases key; rfl
      right_inv := by intro key; cases key; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance profiledRawJointGuardedLeftCrossAnchorKeyFintype :
    Fintype
      (ProfiledRawJointGuardedLeftCrossAnchorKey A strategy hwin) := by
  classical
  let Rep :=
    ProfiledRawJointGuardedInitialCommonOneState A strategy hwin ×
      ProfiledRawJointGuardedCommonLeftOwner A strategy hwin
  let equiv :
      ProfiledRawJointGuardedLeftCrossAnchorKey A strategy hwin ≃ Rep :=
    { toFun := fun key ↦ (key.receiver, key.owner)
      invFun := fun key ↦ ⟨key.1, key.2⟩
      left_inv := by intro key; cases key; rfl
      right_inv := by intro key; cases key; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Forget the proof-only compatibility field of a reachable right-pending
state. -/
def ProfiledRawJointGuardedCommonRightPending.crossAnchorKey
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin) :
    ProfiledRawJointGuardedRightCrossAnchorKey A strategy hwin :=
  ⟨pending.owner, pending.receiver⟩

/-- Left-pending mirror. -/
def ProfiledRawJointGuardedCommonLeftPending.crossAnchorKey
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin) :
    ProfiledRawJointGuardedLeftCrossAnchorKey A strategy hwin :=
  ⟨pending.receiver, pending.owner⟩

/-! ## One jointly chosen response table -/

/-- Both local next states selected by one outer move. -/
structure ProfiledRawJointGuardedCrossAnchorCarrier where
  one : OneControl A strategy hwin initialBank
  two : TwoControl A strategy hwin initialBank

noncomputable instance profiledRawJointGuardedCrossAnchorCarrierFintype :
    Fintype
      (ProfiledRawJointGuardedCrossAnchorCarrier A strategy hwin
        initialBank) := by
  classical
  let Rep := OneControl A strategy hwin initialBank ×
    TwoControl A strategy hwin initialBank
  let equiv :
      ProfiledRawJointGuardedCrossAnchorCarrier A strategy hwin initialBank ≃
        Rep :=
    { toFun := fun carrier ↦ (carrier.one, carrier.two)
      invFun := fun carrier ↦ ⟨carrier.1, carrier.2⟩
      left_inv := by intro carrier; cases carrier; rfl
      right_inv := by intro carrier; cases carrier; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- One physical output pair and its single jointly selected continuation. -/
structure ProfiledRawJointGuardedCrossAnchorResponse where
  outputOne : Out₁
  outputTwo : Out₂
  carrier : ProfiledRawJointGuardedCrossAnchorCarrier A strategy hwin
    initialBank

noncomputable instance profiledRawJointGuardedCrossAnchorResponseFintype :
    Fintype
      (ProfiledRawJointGuardedCrossAnchorResponse A strategy hwin
        initialBank) := by
  classical
  let Rep := Out₁ × Out₂ ×
    ProfiledRawJointGuardedCrossAnchorCarrier A strategy hwin initialBank
  let equiv :
      ProfiledRawJointGuardedCrossAnchorResponse A strategy hwin initialBank ≃
        Rep :=
    { toFun := fun response ↦
        (response.outputOne, response.outputTwo, response.carrier)
      invFun := fun response ↦ ⟨response.1, response.2.1, response.2.2⟩
      left_inv := by intro response; cases response; rfl
      right_inv := by intro response; cases response; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- A move selected once at a right-pending outer-policy key.  Its response
is simultaneous over every possible current input pair. -/
structure ProfiledRawJointGuardedRightCrossAnchorJointMove where
  response : In₁ × In₂ →
    ProfiledRawJointGuardedCrossAnchorResponse A strategy hwin initialBank

/-- Left-pending mirror. -/
structure ProfiledRawJointGuardedLeftCrossAnchorJointMove where
  response : In₁ × In₂ →
    ProfiledRawJointGuardedCrossAnchorResponse A strategy hwin initialBank

noncomputable instance profiledRawJointGuardedRightCrossAnchorJointMoveFintype :
    Fintype
      (ProfiledRawJointGuardedRightCrossAnchorJointMove A strategy hwin
        initialBank) := by
  classical
  let Rep := (In₁ × In₂) →
    ProfiledRawJointGuardedCrossAnchorResponse A strategy hwin initialBank
  let equiv :
      ProfiledRawJointGuardedRightCrossAnchorJointMove A strategy hwin
          initialBank ≃ Rep :=
    { toFun := fun move ↦ move.response
      invFun := fun response ↦ ⟨response⟩
      left_inv := by intro move; cases move; rfl
      right_inv := by intro response; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance profiledRawJointGuardedLeftCrossAnchorJointMoveFintype :
    Fintype
      (ProfiledRawJointGuardedLeftCrossAnchorJointMove A strategy hwin
        initialBank) := by
  classical
  let Rep := (In₁ × In₂) →
    ProfiledRawJointGuardedCrossAnchorResponse A strategy hwin initialBank
  let equiv :
      ProfiledRawJointGuardedLeftCrossAnchorJointMove A strategy hwin
          initialBank ≃ Rep :=
    { toFun := fun move ↦ move.response
      invFun := fun response ↦ ⟨response⟩
      left_inv := by intro move; cases move; rfl
      right_inv := by intro response; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Finite lookup tables supplied by the outer rational policy. -/
abbrev ProfiledRawJointGuardedRightCrossAnchorBank :=
  ProfiledRawJointGuardedRightCrossAnchorKey A strategy hwin →
    ProfiledRawJointGuardedRightCrossAnchorJointMove A strategy hwin
      initialBank

abbrev ProfiledRawJointGuardedLeftCrossAnchorBank :=
  ProfiledRawJointGuardedLeftCrossAnchorKey A strategy hwin →
    ProfiledRawJointGuardedLeftCrossAnchorJointMove A strategy hwin initialBank

/-! ## Installation from one outer exact-observation policy -/

/-- Read the right-pending bank from one globally rationalized outer policy.
Only the finite state lookup survives in the executable bank. -/
noncomputable def
    profiledRawJointGuardedRightCrossAnchorBankOfPostPolicy
    {Observation : Type a} {Code : Type c} [Fintype Code]
    (S : FiniteThreadSystem.{max a
      (max u v x y s), d, e}
      (ProfiledRawJointGuardedRightCrossAnchorJointMove A strategy hwin
        initialBank × Observation))
    (initialObservation : Observation) (code : Observation → Code)
    (Valid : Code →
      ProfiledRawJointGuardedRightCrossAnchorJointMove A strategy hwin
        initialBank → Prop)
    (package : CodedObservablePostPolicy.Package S initialObservation code
      Valid)
    (stateAt : ProfiledRawJointGuardedRightCrossAnchorKey A strategy hwin →
      CodedObservableInputFreeState (Code := Code) S)
    (reachableAt : ∀ key,
      CodedObservablePostPolicy.Reachable S initialObservation code Valid
        package.policy (stateAt key)) :
    ProfiledRawJointGuardedRightCrossAnchorBank A strategy hwin initialBank :=
  package.moveBank S initialObservation code Valid stateAt reachableAt

/-- Left-pending mirror. -/
noncomputable def
    profiledRawJointGuardedLeftCrossAnchorBankOfPostPolicy
    {Observation : Type a} {Code : Type c} [Fintype Code]
    (S : FiniteThreadSystem.{max a
      (max u v x y s), d, e}
      (ProfiledRawJointGuardedLeftCrossAnchorJointMove A strategy hwin
        initialBank × Observation))
    (initialObservation : Observation) (code : Observation → Code)
    (Valid : Code →
      ProfiledRawJointGuardedLeftCrossAnchorJointMove A strategy hwin
        initialBank → Prop)
    (package : CodedObservablePostPolicy.Package S initialObservation code
      Valid)
    (stateAt : ProfiledRawJointGuardedLeftCrossAnchorKey A strategy hwin →
      CodedObservableInputFreeState (Code := Code) S)
    (reachableAt : ∀ key,
      CodedObservablePostPolicy.Reachable S initialObservation code Valid
        package.policy (stateAt key)) :
    ProfiledRawJointGuardedLeftCrossAnchorBank A strategy hwin initialBank :=
  package.moveBank S initialObservation code Valid stateAt reachableAt

/-! ## Genuinely local projections -/

/-- Process one receives the current common shadow and reads only the first
projection of the joint right-pending table. -/
noncomputable def profiledRawJointGuardedRightCrossAnchorRecvOne
    (bank : ProfiledRawJointGuardedRightCrossAnchorBank A strategy hwin
      initialBank)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (receiver : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × OneControl A strategy hwin initialBank :=
  let response := (bank ⟨owner, receiver⟩).response (own, delivered)
  (response.outputOne, response.carrier.one)

/-- Process two receives the old owner and reads the second projection of the
same joint table. -/
noncomputable def profiledRawJointGuardedRightCrossAnchorRecvTwo
    (bank : ProfiledRawJointGuardedRightCrossAnchorBank A strategy hwin
      initialBank)
    (receiver : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × TwoControl A strategy hwin initialBank :=
  let response := (bank ⟨owner, receiver⟩).response (delivered, own)
  (response.outputTwo, response.carrier.two)

/-- Left-pending process-one projection. -/
noncomputable def profiledRawJointGuardedLeftCrossAnchorRecvOne
    (bank : ProfiledRawJointGuardedLeftCrossAnchorBank A strategy hwin
      initialBank)
    (receiver : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × OneControl A strategy hwin initialBank :=
  let response := (bank ⟨receiver, owner⟩).response (own, delivered)
  (response.outputOne, response.carrier.one)

/-- Left-pending process-two projection. -/
noncomputable def profiledRawJointGuardedLeftCrossAnchorRecvTwo
    (bank : ProfiledRawJointGuardedLeftCrossAnchorBank A strategy hwin
      initialBank)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (receiver : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × TwoControl A strategy hwin initialBank :=
  let response := (bank ⟨receiver, owner⟩).response (delivered, own)
  (response.outputTwo, response.carrier.two)

/-! ## The first cross-anchor pair tests -/

/-- Both local right-pending receive maps are projections of literally the
same finite response. -/
theorem profiledRawJointGuardedRightCrossAnchor_local_pair
    (bank : ProfiledRawJointGuardedRightCrossAnchorBank A strategy hwin
      initialBank)
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    let response :=
      (bank (pending.crossAnchorKey A strategy hwin)).response input
    (profiledRawJointGuardedRightCrossAnchorRecvOne A strategy hwin
        initialBank bank pending.owner pending.receiver input.1 input.2,
      profiledRawJointGuardedRightCrossAnchorRecvTwo A strategy hwin
        initialBank bank pending.receiver pending.owner input.2 input.1) =
      ((response.outputOne, response.carrier.one),
        (response.outputTwo, response.carrier.two)) := by
  rfl

/-- Left-pending mirror. -/
theorem profiledRawJointGuardedLeftCrossAnchor_local_pair
    (bank : ProfiledRawJointGuardedLeftCrossAnchorBank A strategy hwin
      initialBank)
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    let response :=
      (bank (pending.crossAnchorKey A strategy hwin)).response input
    (profiledRawJointGuardedLeftCrossAnchorRecvOne A strategy hwin initialBank
        bank pending.receiver pending.owner input.1 input.2,
      profiledRawJointGuardedLeftCrossAnchorRecvTwo A strategy hwin initialBank
        bank pending.owner pending.receiver input.2 input.1) =
      ((response.outputOne, response.carrier.one),
        (response.outputTwo, response.carrier.two)) := by
  rfl

/-- Output-only form consumed by the physical global machine. -/
theorem profiledRawJointGuardedRightCrossAnchor_output_pair
    (bank : ProfiledRawJointGuardedRightCrossAnchorBank A strategy hwin
      initialBank)
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedRightCrossAnchorRecvOne A strategy hwin
        initialBank bank pending.owner pending.receiver input.1 input.2).1,
      (profiledRawJointGuardedRightCrossAnchorRecvTwo A strategy hwin
        initialBank bank pending.receiver pending.owner input.2 input.1).1) =
      let response :=
        (bank (pending.crossAnchorKey A strategy hwin)).response input
      (response.outputOne, response.outputTwo) := by
  rfl

/-- Left-pending output mirror. -/
theorem profiledRawJointGuardedLeftCrossAnchor_output_pair
    (bank : ProfiledRawJointGuardedLeftCrossAnchorBank A strategy hwin
      initialBank)
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedLeftCrossAnchorRecvOne A strategy hwin initialBank
        bank pending.receiver pending.owner input.1 input.2).1,
      (profiledRawJointGuardedLeftCrossAnchorRecvTwo A strategy hwin initialBank
        bank pending.owner pending.receiver input.2 input.1).1) =
      let response :=
        (bank (pending.crossAnchorKey A strategy hwin)).response input
      (response.outputOne, response.outputTwo) := by
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
