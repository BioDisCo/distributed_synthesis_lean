/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionPostResolvePhaseLiveFork

/-!
# Finite transition keys and the exact paired-target gap

A recurrent post-resolve lookup must not be indexed only by the emitted
incidence code.  The finite data available at a closing receive are the whole
advanced sender/receiver state and the current input pair.  This file packages
that data as two finite candidate transition-key types.

For every reachable key, the existing dispatcher proves its target theorem at
both rows.  We package those two theorems together.  This is intentionally
weaker than the transition-linked fact needed next: the two `meaning` fields
still provide separate semantic witnesses.  They do not yet say that the
`first` and `both` targets arise from one current semantic occurrence, nor do
they supply a `ProcOnePendingOverlap` or `ProcTwoPendingOverlap` between those
successors.  No such conclusion is assumed below.
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

/-! ## Both row certificates at one reachable call -/

/-- The exact information currently proved about the two targets of one
right-block dispatcher call.  The fields share the finite state and input,
but their semantic target witnesses have not yet been linked. -/
structure ProfiledRawJointStrictLeftPostResolveFiniteDispatchTargetPairMeaning
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : LeftSenderState A × LeftReceiverState A)
    (current : In₂ × In₁) : Prop where
  first :
    ProfiledRawJointStrictLeftPostResolveFiniteDispatchTargetMeaning A strategy
      hwin initial entry input branch state current .first
  both :
    ProfiledRawJointStrictLeftPostResolveFiniteDispatchTargetMeaning A strategy
      hwin initial entry input branch state current .both

/-- Mirrored pair of separately justified row targets. -/
structure ProfiledRawJointStrictRightPostResolveFiniteDispatchTargetPairMeaning
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : RightSenderState A × RightReceiverState A)
    (current : In₁ × In₂) : Prop where
  first :
    ProfiledRawJointStrictRightPostResolveFiniteDispatchTargetMeaning A strategy
      hwin initial entry input branch state current .first
  both :
    ProfiledRawJointStrictRightPostResolveFiniteDispatchTargetMeaning A strategy
      hwin initial entry input branch state current .both

/-- Reachability gives both process-one row certificates at the same finite
call. -/
theorem
    profiledRawJointStrictLeftPostResolveFiniteDispatch_targetPairMeaning_of_reachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : LeftSenderState A × LeftReceiverState A)
    (hstate : ProfiledRawJointStrictLeftPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch state)
    (current : In₂ × In₁) :
    ProfiledRawJointStrictLeftPostResolveFiniteDispatchTargetPairMeaning A
      strategy hwin initial entry input branch state current where
  first :=
    profiledRawJointStrictLeftPostResolveFiniteDispatch_targetMeaning_of_reachable
      A strategy hwin initial entry input branch state hstate current .first
  both :=
    profiledRawJointStrictLeftPostResolveFiniteDispatch_targetMeaning_of_reachable
      A strategy hwin initial entry input branch state hstate current .both

/-- Mirrored reachable pair. -/
theorem
    profiledRawJointStrictRightPostResolveFiniteDispatch_targetPairMeaning_of_reachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : RightSenderState A × RightReceiverState A)
    (hstate : ProfiledRawJointStrictRightPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch state)
    (current : In₁ × In₂) :
    ProfiledRawJointStrictRightPostResolveFiniteDispatchTargetPairMeaning A
      strategy hwin initial entry input branch state current where
  first :=
    profiledRawJointStrictRightPostResolveFiniteDispatch_targetMeaning_of_reachable
      A strategy hwin initial entry input branch state hstate current .first
  both :=
    profiledRawJointStrictRightPostResolveFiniteDispatch_targetMeaning_of_reachable
      A strategy hwin initial entry input branch state hstate current .both

/-! ## The correct finite lookup domain -/

/-- Full finite data of a possible right-block transition. -/
abbrev ProfiledRawJointStrictLeftPostResolveRawTransitionKey :=
  (LeftSenderState A × LeftReceiverState A) × (In₂ × In₁)

/-- Mirrored left-block transition data. -/
abbrev ProfiledRawJointStrictRightPostResolveRawTransitionKey :=
  (RightSenderState A × RightReceiverState A) × (In₁ × In₂)

/-- A raw right-block key is admissible when it has some exact semantic
installation witness.  The witness is propositional and is not runtime data. -/
def ProfiledRawJointStrictLeftPostResolveTransitionAdmissible
    (key : ProfiledRawJointStrictLeftPostResolveRawTransitionKey A) : Prop :=
  ∃ (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
      (branch : Bool),
    ProfiledRawJointStrictLeftPostResolveFiniteInstalledReachable A strategy
      hwin initial entry input branch key.1

/-- Mirrored admissibility predicate. -/
def ProfiledRawJointStrictRightPostResolveTransitionAdmissible
    (key : ProfiledRawJointStrictRightPostResolveRawTransitionKey A) : Prop :=
  ∃ (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
      (branch : Bool),
    ProfiledRawJointStrictRightPostResolveFiniteInstalledReachable A strategy
      hwin initial entry input branch key.1

/-- Finite transition keys on which a transition-linked table may be selected
once and for all. -/
abbrev ProfiledRawJointStrictLeftPostResolveTransitionKey :=
  { key : ProfiledRawJointStrictLeftPostResolveRawTransitionKey A //
    ProfiledRawJointStrictLeftPostResolveTransitionAdmissible A strategy hwin
      key }

/-- Mirrored finite admissible key. -/
abbrev ProfiledRawJointStrictRightPostResolveTransitionKey :=
  { key : ProfiledRawJointStrictRightPostResolveRawTransitionKey A //
    ProfiledRawJointStrictRightPostResolveTransitionAdmissible A strategy hwin
      key }

noncomputable instance :
    Fintype (ProfiledRawJointStrictLeftPostResolveTransitionKey A strategy
      hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointStrictRightPostResolveTransitionKey A strategy
      hwin) := by
  classical
  infer_instance

/-- Every concrete reachable call embeds in the finite transition-key type. -/
def profiledRawJointStrictLeftPostResolveTransitionKeyOfReachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : LeftSenderState A × LeftReceiverState A)
    (hstate : ProfiledRawJointStrictLeftPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch state)
    (current : In₂ × In₁) :
    ProfiledRawJointStrictLeftPostResolveTransitionKey A strategy hwin :=
  ⟨(state, current), initial, entry, input, branch, hstate⟩

/-- Mirrored embedding. -/
def profiledRawJointStrictRightPostResolveTransitionKeyOfReachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : RightSenderState A × RightReceiverState A)
    (hstate : ProfiledRawJointStrictRightPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch state)
    (current : In₁ × In₂) :
    ProfiledRawJointStrictRightPostResolveTransitionKey A strategy hwin :=
  ⟨(state, current), initial, entry, input, branch, hstate⟩

/-- Every admissible right-block key has one semantic witness and both
separate row certificates.  Strengthening the final field to a common-origin
pending-overlap package is the exact next theorem. -/
theorem profiledRawJointStrictLeftPostResolveTransitionKey_targetPairMeaning
    (key : ProfiledRawJointStrictLeftPostResolveTransitionKey A strategy
      hwin) :
    ∃ (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
        (branch : Bool),
      ProfiledRawJointStrictLeftPostResolveFiniteInstalledReachable A strategy
          hwin initial entry input branch key.1.1 ∧
        ProfiledRawJointStrictLeftPostResolveFiniteDispatchTargetPairMeaning A
          strategy hwin initial entry input branch key.1.1 key.1.2 := by
  rcases key.2 with ⟨initial, entry, input, branch, hstate⟩
  exact ⟨initial, entry, input, branch, hstate,
    profiledRawJointStrictLeftPostResolveFiniteDispatch_targetPairMeaning_of_reachable
      A strategy hwin initial entry input branch key.1.1 hstate key.1.2⟩

/-- Mirrored transition-key audit. -/
theorem profiledRawJointStrictRightPostResolveTransitionKey_targetPairMeaning
    (key : ProfiledRawJointStrictRightPostResolveTransitionKey A strategy
      hwin) :
    ∃ (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
        (branch : Bool),
      ProfiledRawJointStrictRightPostResolveFiniteInstalledReachable A strategy
          hwin initial entry input branch key.1.1 ∧
        ProfiledRawJointStrictRightPostResolveFiniteDispatchTargetPairMeaning A
          strategy hwin initial entry input branch key.1.1 key.1.2 := by
  rcases key.2 with ⟨initial, entry, input, branch, hstate⟩
  exact ⟨initial, entry, input, branch, hstate,
    profiledRawJointStrictRightPostResolveFiniteDispatch_targetPairMeaning_of_reachable
      A strategy hwin initial entry input branch key.1.1 hstate key.1.2⟩

end

end DetParityAutomaton

end DistributedSynthesis
