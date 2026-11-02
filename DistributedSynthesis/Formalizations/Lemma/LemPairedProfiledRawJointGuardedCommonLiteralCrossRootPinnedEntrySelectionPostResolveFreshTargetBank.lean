/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionPostResolveFiniteDispatcher
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointIndexedPolicyLeaderFreeKernel

/-!
# A finite oriented recurrent bank below the post-resolve dispatcher

The post-resolve dispatcher emits a finite public incidence code.  That code
alone does not record which recurrent root orientation has just been closed:
a code may have both a left and a right live slot.  We therefore split valid
targets into right-close and left-close subtypes.  The subtype proof contains
only the propositional existence of an orientation-refined fresh package.
For each finite key, classical choice selects the semantic source and rational
policy once and for all; neither object is stored in a runtime control.

The checked lookup functions are total on every public target.  A reachable
right-block dispatch succeeds in the right-close lookup, and a reachable
left-block dispatch succeeds in the left-close lookup.  Thus the later global
receive map may use `none` only as an unreachable totalization branch.
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

/-! ## Finite oriented target keys -/

/-- Public targets for which a right-block close has an explicitly left-rooted
fresh policy package. -/
abbrev ProfiledRawJointPostResolveRightFreshTarget :=
  { target : ProfiledRawJointUnitTarget A //
    Nonempty
      (ProfiledRawJointRightCloseFreshPolicyPackage A strategy target) }

/-- Public targets for which a left-block close has an explicitly right-rooted
fresh policy package. -/
abbrev ProfiledRawJointPostResolveLeftFreshTarget :=
  { target : ProfiledRawJointUnitTarget A //
    Nonempty
      (ProfiledRawJointLeftCloseFreshPolicyPackage A strategy target) }

noncomputable instance :
    Fintype (ProfiledRawJointPostResolveRightFreshTarget A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointPostResolveLeftFreshTarget A strategy) := by
  classical
  infer_instance

noncomputable instance :
    DecidableEq (ProfiledRawJointPostResolveRightFreshTarget A strategy) :=
  Classical.decEq _

noncomputable instance :
    DecidableEq (ProfiledRawJointPostResolveLeftFreshTarget A strategy) :=
  Classical.decEq _

/-- The finite disjoint union keeps only close orientation and public target.
No semantic occurrence or policy is part of the key's data. -/
abbrev ProfiledRawJointPostResolveFreshTargetKey :=
  ProfiledRawJointPostResolveRightFreshTarget A strategy ⊕
    ProfiledRawJointPostResolveLeftFreshTarget A strategy

noncomputable instance :
    Fintype (ProfiledRawJointPostResolveFreshTargetKey A strategy) := by
  classical
  infer_instance

noncomputable instance :
    DecidableEq (ProfiledRawJointPostResolveFreshTargetKey A strategy) :=
  Classical.decEq _

/-- Erase the orientation tag and proof field. -/
def profiledRawJointPostResolveFreshTargetCode
    (key : ProfiledRawJointPostResolveFreshTargetKey A strategy) :
    ProfiledRawJointUnitTarget A :=
  match key with
  | .inl right => right.1
  | .inr left => left.1

/-! ## Once-for-all choice of semantic source and policy -/

/-- Canonical orientation-refined package selected for a right-close key. -/
noncomputable def profiledRawJointPostResolveRightFreshPackage
    (key : ProfiledRawJointPostResolveRightFreshTarget A strategy) :
    ProfiledRawJointRightCloseFreshPolicyPackage A strategy key.1 :=
  Classical.choice key.2

/-- Canonical package selected for a left-close key. -/
noncomputable def profiledRawJointPostResolveLeftFreshPackage
    (key : ProfiledRawJointPostResolveLeftFreshTarget A strategy) :
    ProfiledRawJointLeftCloseFreshPolicyPackage A strategy key.1 :=
  Classical.choice key.2

/-- One semantic source is fixed proof-side for every finite oriented key. -/
noncomputable def profiledRawJointPostResolveFreshTargetSource
    (key : ProfiledRawJointPostResolveFreshTargetKey A strategy) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  match key with
  | .inl right =>
      (profiledRawJointPostResolveRightFreshPackage A strategy right).initial
  | .inr left =>
      (profiledRawJointPostResolveLeftFreshPackage A strategy left).initial

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The chosen source has exactly the public code carried by the finite key. -/
@[simp] theorem profiledRawJointPostResolveFreshTargetSource_code
    (key : ProfiledRawJointPostResolveFreshTargetKey A strategy) :
    (profiledRawJointPostResolveFreshTargetSource A strategy key).code A =
      profiledRawJointPostResolveFreshTargetCode A strategy key := by
  cases key with
  | inl right =>
      exact (profiledRawJointPostResolveRightFreshPackage A strategy right
        ).initial_code
  | inr left =>
      exact (profiledRawJointPostResolveLeftFreshPackage A strategy left
        ).initial_code

/-- One rational policy is fixed once for every finite oriented key. -/
noncomputable def profiledRawJointPostResolveFreshTargetPolicy
    (key : ProfiledRawJointPostResolveFreshTargetKey A strategy) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointPostResolveFreshTargetSource A strategy key).code A) :=
  match key with
  | .inl right =>
      (profiledRawJointPostResolveRightFreshPackage A strategy right).policy
  | .inr left =>
      (profiledRawJointPostResolveLeftFreshPackage A strategy left).policy

/-- The ordinary finite controller bank of the selected policy. -/
noncomputable def profiledRawJointPostResolveFreshTargetControllerBank
    (key : ProfiledRawJointPostResolveFreshTargetKey A strategy) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (profiledRawJointPostResolveFreshTargetSource A strategy key)
      (profiledRawJointPostResolveFreshTargetPolicy A strategy key) :=
  profiledRawJointUnitPolicyControllerBank A strategy
    (profiledRawJointPostResolveFreshTargetSource A strategy key)
    (profiledRawJointPostResolveFreshTargetPolicy A strategy key)

/-! ## Total checked lookup -/

/-- Total finite test for membership in the right-close target bank. -/
noncomputable def profiledRawJointPostResolveRightFreshTarget?
    (target : ProfiledRawJointUnitTarget A) :
    Option (ProfiledRawJointPostResolveRightFreshTarget A strategy) := by
  classical
  exact if h : Nonempty
      (ProfiledRawJointRightCloseFreshPolicyPackage A strategy target) then
    some ⟨target, h⟩
  else none

/-- Total finite test for membership in the left-close target bank. -/
noncomputable def profiledRawJointPostResolveLeftFreshTarget?
    (target : ProfiledRawJointUnitTarget A) :
    Option (ProfiledRawJointPostResolveLeftFreshTarget A strategy) := by
  classical
  exact if h : Nonempty
      (ProfiledRawJointLeftCloseFreshPolicyPackage A strategy target) then
    some ⟨target, h⟩
  else none

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointPostResolveRightFreshTarget?_eq_some
    (target : ProfiledRawJointUnitTarget A)
    (hpackage : Nonempty
      (ProfiledRawJointRightCloseFreshPolicyPackage A strategy target)) :
    ∃ key, profiledRawJointPostResolveRightFreshTarget? A strategy target =
        some key ∧ key.1 = target := by
  classical
  let key : ProfiledRawJointPostResolveRightFreshTarget A strategy :=
    ⟨target, hpackage⟩
  refine ⟨key, ?_, rfl⟩
  simp [profiledRawJointPostResolveRightFreshTarget?, hpackage, key]

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointPostResolveLeftFreshTarget?_eq_some
    (target : ProfiledRawJointUnitTarget A)
    (hpackage : Nonempty
      (ProfiledRawJointLeftCloseFreshPolicyPackage A strategy target)) :
    ∃ key, profiledRawJointPostResolveLeftFreshTarget? A strategy target =
        some key ∧ key.1 = target := by
  classical
  let key : ProfiledRawJointPostResolveLeftFreshTarget A strategy :=
    ⟨target, hpackage⟩
  refine ⟨key, ?_, rfl⟩
  simp [profiledRawJointPostResolveLeftFreshTarget?, hpackage, key]

/-! ## Recurrent root controls at the selected key -/

abbrev ProfiledRawJointPostResolveFreshTargetLeftOwner
    (key : ProfiledRawJointPostResolveFreshTargetKey A strategy) :=
  ProfiledRawJointIndexedPolicyLeftOwner A strategy
    (ProfiledRawJointPostResolveFreshTargetKey A strategy)
    (profiledRawJointPostResolveFreshTargetSource A strategy)
    (profiledRawJointPostResolveFreshTargetPolicy A strategy)
    (profiledRawJointPostResolveFreshTargetControllerBank A strategy) key

abbrev ProfiledRawJointPostResolveFreshTargetLeftReceiver
    (key : ProfiledRawJointPostResolveFreshTargetKey A strategy) :=
  ProfiledRawJointIndexedPolicyLeftReceiver A strategy
    (ProfiledRawJointPostResolveFreshTargetKey A strategy)
    (profiledRawJointPostResolveFreshTargetSource A strategy)
    (profiledRawJointPostResolveFreshTargetPolicy A strategy) key

abbrev ProfiledRawJointPostResolveFreshTargetRightOwner
    (key : ProfiledRawJointPostResolveFreshTargetKey A strategy) :=
  ProfiledRawJointIndexedPolicyRightOwner A strategy
    (ProfiledRawJointPostResolveFreshTargetKey A strategy)
    (profiledRawJointPostResolveFreshTargetSource A strategy)
    (profiledRawJointPostResolveFreshTargetPolicy A strategy)
    (profiledRawJointPostResolveFreshTargetControllerBank A strategy) key

abbrev ProfiledRawJointPostResolveFreshTargetRightReceiver
    (key : ProfiledRawJointPostResolveFreshTargetKey A strategy) :=
  ProfiledRawJointIndexedPolicyRightReceiver A strategy
    (ProfiledRawJointPostResolveFreshTargetKey A strategy)
    (profiledRawJointPostResolveFreshTargetSource A strategy)
    (profiledRawJointPostResolveFreshTargetPolicy A strategy) key

/-- The chosen right-close package installs a left owner at its root. -/
noncomputable def profiledRawJointPostResolveRightFreshInitialLeftOwner
    (key : ProfiledRawJointPostResolveRightFreshTarget A strategy) :
    ProfiledRawJointPostResolveFreshTargetLeftOwner A strategy (.inl key) :=
  initialProfiledRawJointUnitLeftPolicyOwner A strategy
    (profiledRawJointPostResolveFreshTargetSource A strategy (.inl key))
    (profiledRawJointPostResolveFreshTargetPolicy A strategy (.inl key))
    (profiledRawJointPostResolveFreshTargetControllerBank A strategy (.inl key))
    (profiledRawJointPostResolveRightFreshPackage A strategy key).seed

/-- Receiver-side root at the same right-close key. -/
noncomputable def profiledRawJointPostResolveRightFreshInitialLeftReceiver
    (key : ProfiledRawJointPostResolveRightFreshTarget A strategy)
    (row : PairedEntryRow) :
    ProfiledRawJointPostResolveFreshTargetLeftReceiver A strategy (.inl key) :=
  initialProfiledRawJointUnitLeftPolicyReceiver A strategy
    (profiledRawJointPostResolveFreshTargetSource A strategy (.inl key))
    (profiledRawJointPostResolveFreshTargetPolicy A strategy (.inl key))
    (profiledRawJointPostResolveRightFreshPackage A strategy key).seed row

/-- The chosen left-close package installs a right owner at its root. -/
noncomputable def profiledRawJointPostResolveLeftFreshInitialRightOwner
    (key : ProfiledRawJointPostResolveLeftFreshTarget A strategy) :
    ProfiledRawJointPostResolveFreshTargetRightOwner A strategy (.inr key) :=
  initialProfiledRawJointUnitRightPolicyOwner A strategy
    (profiledRawJointPostResolveFreshTargetSource A strategy (.inr key))
    (profiledRawJointPostResolveFreshTargetPolicy A strategy (.inr key))
    (profiledRawJointPostResolveFreshTargetControllerBank A strategy (.inr key))
    (profiledRawJointPostResolveLeftFreshPackage A strategy key).seed

/-- Receiver-side root at the same left-close key. -/
noncomputable def profiledRawJointPostResolveLeftFreshInitialRightReceiver
    (key : ProfiledRawJointPostResolveLeftFreshTarget A strategy)
    (row : PairedEntryRow) :
    ProfiledRawJointPostResolveFreshTargetRightReceiver A strategy (.inr key) :=
  initialProfiledRawJointUnitRightPolicyReceiver A strategy
    (profiledRawJointPostResolveFreshTargetSource A strategy (.inr key))
    (profiledRawJointPostResolveFreshTargetPolicy A strategy (.inr key))
    (profiledRawJointPostResolveLeftFreshPackage A strategy key).seed row

/-! ## Finite bank carriers and total root lookup -/

/-- All left-owner fibres of the oriented target bank. -/
abbrev ProfiledRawJointPostResolveFreshTargetLeftOwnerControl :=
  Σ key : ProfiledRawJointPostResolveFreshTargetKey A strategy,
    ProfiledRawJointPostResolveFreshTargetLeftOwner A strategy key

/-- All left-receiver fibres of the oriented target bank. -/
abbrev ProfiledRawJointPostResolveFreshTargetLeftReceiverControl :=
  Σ key : ProfiledRawJointPostResolveFreshTargetKey A strategy,
    ProfiledRawJointPostResolveFreshTargetLeftReceiver A strategy key

/-- All right-owner fibres of the oriented target bank. -/
abbrev ProfiledRawJointPostResolveFreshTargetRightOwnerControl :=
  Σ key : ProfiledRawJointPostResolveFreshTargetKey A strategy,
    ProfiledRawJointPostResolveFreshTargetRightOwner A strategy key

/-- All right-receiver fibres of the oriented target bank. -/
abbrev ProfiledRawJointPostResolveFreshTargetRightReceiverControl :=
  Σ key : ProfiledRawJointPostResolveFreshTargetKey A strategy,
    ProfiledRawJointPostResolveFreshTargetRightReceiver A strategy key

noncomputable instance :
    Fintype (ProfiledRawJointPostResolveFreshTargetLeftOwnerControl A
      strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointPostResolveFreshTargetLeftReceiverControl A
      strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointPostResolveFreshTargetRightOwnerControl A
      strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointPostResolveFreshTargetRightReceiverControl A
      strategy) := by
  classical
  infer_instance

/-- A successful right-close lookup returns both recurrent endpoints at one
definitionally shared key. -/
abbrev ProfiledRawJointPostResolveRightFreshInstalledRoot :=
  Σ key : ProfiledRawJointPostResolveRightFreshTarget A strategy,
    ProfiledRawJointPostResolveFreshTargetLeftOwner A strategy (.inl key) ×
      ProfiledRawJointPostResolveFreshTargetLeftReceiver A strategy (.inl key)

/-- Left-close mirror. -/
abbrev ProfiledRawJointPostResolveLeftFreshInstalledRoot :=
  Σ key : ProfiledRawJointPostResolveLeftFreshTarget A strategy,
    ProfiledRawJointPostResolveFreshTargetRightOwner A strategy (.inr key) ×
      ProfiledRawJointPostResolveFreshTargetRightReceiver A strategy (.inr key)

/-- Total right-close root lookup.  Failure is reserved for a target for
which no left-rooted package exists. -/
noncomputable def profiledRawJointPostResolveRightFreshInstalledRoot?
    (target : ProfiledRawJointUnitTarget A) (row : PairedEntryRow) :
    Option (ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy) :=
  match profiledRawJointPostResolveRightFreshTarget? A strategy target with
  | none => none
  | some key => some ⟨key,
      profiledRawJointPostResolveRightFreshInitialLeftOwner A strategy key,
      profiledRawJointPostResolveRightFreshInitialLeftReceiver A strategy key
        row⟩

/-- Total left-close root lookup. -/
noncomputable def profiledRawJointPostResolveLeftFreshInstalledRoot?
    (target : ProfiledRawJointUnitTarget A) (row : PairedEntryRow) :
    Option (ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy) :=
  match profiledRawJointPostResolveLeftFreshTarget? A strategy target with
  | none => none
  | some key => some ⟨key,
      profiledRawJointPostResolveLeftFreshInitialRightOwner A strategy key,
      profiledRawJointPostResolveLeftFreshInitialRightReceiver A strategy key
        row⟩

/-- Every root returned by the right-close lookup has source code exactly the
queried public target. -/
theorem profiledRawJointPostResolveRightFreshInstalledRoot?_source_code
    (target : ProfiledRawJointUnitTarget A) (row : PairedEntryRow)
    (root : ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (hroot : profiledRawJointPostResolveRightFreshInstalledRoot? A strategy
      target row = some root) :
    (profiledRawJointPostResolveFreshTargetSource A strategy (.inl root.1)
      ).code A = target := by
  unfold profiledRawJointPostResolveRightFreshInstalledRoot? at hroot
  split at hroot
  · contradiction
  · rename_i key hkey
    simp only [Option.some.injEq] at hroot
    subst root
    have htarget : key.1 = target := by
      unfold profiledRawJointPostResolveRightFreshTarget? at hkey
      split at hkey
      · exact (congrArg Subtype.val (Option.some.inj hkey)).symm
      · contradiction
    rw [profiledRawJointPostResolveFreshTargetSource_code]
    exact htarget

/-- Left-close source-code mirror. -/
theorem profiledRawJointPostResolveLeftFreshInstalledRoot?_source_code
    (target : ProfiledRawJointUnitTarget A) (row : PairedEntryRow)
    (root : ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (hroot : profiledRawJointPostResolveLeftFreshInstalledRoot? A strategy
      target row = some root) :
    (profiledRawJointPostResolveFreshTargetSource A strategy (.inr root.1)
      ).code A = target := by
  unfold profiledRawJointPostResolveLeftFreshInstalledRoot? at hroot
  split at hroot
  · contradiction
  · rename_i key hkey
    simp only [Option.some.injEq] at hroot
    subst root
    have htarget : key.1 = target := by
      unfold profiledRawJointPostResolveLeftFreshTarget? at hkey
      split at hkey
      · exact (congrArg Subtype.val (Option.some.inj hkey)).symm
      · contradiction
    rw [profiledRawJointPostResolveFreshTargetSource_code]
    exact htarget

/-! ## Reachable dispatcher calls always enter the checked bank -/

/-- Every reachable process-one dispatch target passes the total right-close
lookup. -/
theorem profiledRawJointStrictLeftPostResolveFiniteDispatch_rightFreshTarget?
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : LeftSenderState A × LeftReceiverState A)
    (hstate : ProfiledRawJointStrictLeftPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch state)
    (current : In₂ × In₁) (row : PairedEntryRow) :
    ∃ key,
      profiledRawJointPostResolveRightFreshTarget? A strategy
        ((profiledRawJointStrictLeftPostResolveFiniteDispatch A state current.1
          current.2).receiverOutput.target row) = some key ∧
      key.1 =
        (profiledRawJointStrictLeftPostResolveFiniteDispatch A state current.1
          current.2).receiverOutput.target row := by
  apply profiledRawJointPostResolveRightFreshTarget?_eq_some A strategy
  exact
    nonempty_profiledRawJointStrictLeftPostResolveFiniteDispatchRightCloseFreshPolicyPackage_of_reachable
      A strategy hwin initial entry input branch state hstate current row

/-- Mirrored reachable dispatch targets pass the left-close lookup. -/
theorem profiledRawJointStrictRightPostResolveFiniteDispatch_leftFreshTarget?
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : RightSenderState A × RightReceiverState A)
    (hstate : ProfiledRawJointStrictRightPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch state)
    (current : In₁ × In₂) (row : PairedEntryRow) :
    ∃ key,
      profiledRawJointPostResolveLeftFreshTarget? A strategy
        ((profiledRawJointStrictRightPostResolveFiniteDispatch A state current.1
          current.2).receiverOutput.target row) = some key ∧
      key.1 =
        (profiledRawJointStrictRightPostResolveFiniteDispatch A state current.1
          current.2).receiverOutput.target row := by
  apply profiledRawJointPostResolveLeftFreshTarget?_eq_some A strategy
  exact
    nonempty_profiledRawJointStrictRightPostResolveFiniteDispatchLeftCloseFreshPolicyPackage_of_reachable
      A strategy hwin initial entry input branch state hstate current row

/-- The total right-close root lookup cannot fail on a reached dispatcher
target. -/
theorem
    profiledRawJointStrictLeftPostResolveFiniteDispatch_rightFreshInstalledRoot?
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : LeftSenderState A × LeftReceiverState A)
    (hstate : ProfiledRawJointStrictLeftPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch state)
    (current : In₂ × In₁) (row : PairedEntryRow) :
    ∃ root,
      profiledRawJointPostResolveRightFreshInstalledRoot? A strategy
        ((profiledRawJointStrictLeftPostResolveFiniteDispatch A state current.1
          current.2).receiverOutput.target row) row = some root := by
  obtain ⟨key, hkey, _⟩ :=
    profiledRawJointStrictLeftPostResolveFiniteDispatch_rightFreshTarget?
      A strategy hwin initial entry input branch state hstate current row
  refine ⟨⟨key,
    profiledRawJointPostResolveRightFreshInitialLeftOwner A strategy key,
    profiledRawJointPostResolveRightFreshInitialLeftReceiver A strategy key
      row⟩, ?_⟩
  simp [profiledRawJointPostResolveRightFreshInstalledRoot?, hkey]

/-- Mirrored reached dispatch root lookup cannot fail. -/
theorem
    profiledRawJointStrictRightPostResolveFiniteDispatch_leftFreshInstalledRoot?
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : RightSenderState A × RightReceiverState A)
    (hstate : ProfiledRawJointStrictRightPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch state)
    (current : In₁ × In₂) (row : PairedEntryRow) :
    ∃ root,
      profiledRawJointPostResolveLeftFreshInstalledRoot? A strategy
        ((profiledRawJointStrictRightPostResolveFiniteDispatch A state current.1
          current.2).receiverOutput.target row) row = some root := by
  obtain ⟨key, hkey, _⟩ :=
    profiledRawJointStrictRightPostResolveFiniteDispatch_leftFreshTarget?
      A strategy hwin initial entry input branch state hstate current row
  refine ⟨⟨key,
    profiledRawJointPostResolveLeftFreshInitialRightOwner A strategy key,
    profiledRawJointPostResolveLeftFreshInitialRightReceiver A strategy key
      row⟩, ?_⟩
  simp [profiledRawJointPostResolveLeftFreshInstalledRoot?, hkey]

end

end DetParityAutomaton

end DistributedSynthesis
