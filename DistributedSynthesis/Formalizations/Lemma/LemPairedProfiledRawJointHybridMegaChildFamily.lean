/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointInitialTaggedChildCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridUnifiedChildFamily
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialImmediateSwitchFamily
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialExactTaggedChildFamily
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingLocalInstallation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingTargetSynchronization
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSiblingTargetIndexedKernel

/-!
# One finite recurrent child family for every hybrid entry seam

The complete hybrid front end can enter a fixed recurrent one-sided policy in
seven ways:

* through a literal child of the old initial strict block;
* through a common-shadow replacement;
* through a literal child of an exact guarded common root; or
* through the shared initial immediate-switch policy; or
* through a literal child of the exact root-pinned initial first block; or
* through a checked target of the pre-rationalized initial sibling move; or
* through a checked target of a recurrent root-pinned common sibling move.

This file puts those seven already finite policy classes into one finite child
code and exposes one uniform source, policy, controller bank, and four local
control families.  The outer sum records proof-side construction provenance.
It is not an observed graph, orientation, or strict-leader signal, and no
transition is defined by inspecting such a signal.
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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

/-! ## Checked targets of the pre-rationalized initial sibling move -/

/-- Every checked recurrent target emitted by either projection of the one
pre-rationalized initial sibling move.  The outer finite installation index
makes the dependent target family one finite global alphabet. -/
abbrev ProfiledRawJointHybridInitialSiblingTargetChildCode :=
  Σ installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂),
    ProfiledRawJointSiblingTargetChildCode A strategy
      (profiledRawJointHybridInitialSiblingParentFamily A strategy
        installation.first)
      (profiledRawJointHybridInitialSiblingDirection installation.current)

noncomputable instance
    profiledRawJointHybridInitialSiblingTargetChildCodeFintype :
    Fintype
      (ProfiledRawJointHybridInitialSiblingTargetChildCode A strategy) := by
  classical
  infer_instance

noncomputable def profiledRawJointHybridInitialSiblingTargetChildSource
    (child : ProfiledRawJointHybridInitialSiblingTargetChildCode A strategy) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  profiledRawJointSiblingTargetChildSource A strategy
    (profiledRawJointHybridInitialSiblingParentFamily A strategy
      child.1.first)
    (profiledRawJointHybridInitialSiblingDirection child.1.current) child.2

noncomputable def profiledRawJointHybridInitialSiblingTargetChildPolicy
    (child : ProfiledRawJointHybridInitialSiblingTargetChildCode A strategy) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointHybridInitialSiblingTargetChildSource A strategy child
        ).code A) :=
  profiledRawJointSiblingTargetChildPolicy A strategy hwin
    (profiledRawJointHybridInitialSiblingParentFamily A strategy
      child.1.first)
    (profiledRawJointHybridInitialSiblingDirection child.1.current) child.2

noncomputable def
    profiledRawJointHybridInitialSiblingTargetChildControllerBank
    (child : ProfiledRawJointHybridInitialSiblingTargetChildCode A strategy) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (profiledRawJointHybridInitialSiblingTargetChildSource A strategy child)
      (profiledRawJointHybridInitialSiblingTargetChildPolicy A strategy hwin
        child) :=
  profiledRawJointSiblingTargetChildControllerBank A strategy hwin
    (profiledRawJointHybridInitialSiblingParentFamily A strategy
      child.1.first)
    (profiledRawJointHybridInitialSiblingDirection child.1.current) child.2

/-! ## The seven-way finite child code -/

/-- The complete recurrent child code.  The seven summands are, in order, the
old initial strict child, common replacement, exact guarded common child,
shared initial immediate switch, exact initial first-block child, and a
checked target of the pre-rationalized initial sibling move, and a checked
target of a recurrent root-pinned common sibling move. -/
abbrev ProfiledRawJointHybridMegaChildCode :=
  ProfiledRawJointInitialTaggedChildCode A strategy initialBank ⊕
    (ProfiledRawJointHybridCommonTaggedReplacement A strategy hwin ⊕
      (ProfiledRawJointHybridExactTaggedChildCode A strategy hwin ⊕
        (ProfiledRawJointHybridInitialImmediateSwitchTag
            (In₁ := In₁) (In₂ := In₂) ⊕
          (ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin ⊕
            (ProfiledRawJointHybridInitialSiblingTargetChildCode A strategy ⊕
              ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin)))))

noncomputable instance profiledRawJointHybridMegaChildCodeFintype :
    Fintype
      (ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) := by
  classical
  infer_instance

/-- Embed an old initial strict-block child. -/
def profiledRawJointHybridMegaChildOfInitial
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :
    ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank :=
  .inl child

/-- Embed a common-shadow replacement. -/
def profiledRawJointHybridMegaChildOfReplacement
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank :=
  .inr (.inl replacement)

/-- Embed an exact guarded-root child. -/
def profiledRawJointHybridMegaChildOfExact
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank :=
  .inr (.inr (.inl child))

/-- Embed a shared initial immediate-switch tag. -/
def profiledRawJointHybridMegaChildOfImmediateSwitch
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank :=
  .inr (.inr (.inr (.inl tag)))

/-- Embed a literal child of the exact root-pinned initial first block. -/
def profiledRawJointHybridMegaChildOfInitialExact
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank :=
  .inr (.inr (.inr (.inr (.inl child))))

/-- Embed a checked target of the pre-rationalized initial sibling move. -/
def profiledRawJointHybridMegaChildOfInitialSiblingTarget
    (child : ProfiledRawJointHybridInitialSiblingTargetChildCode A strategy) :
    ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank :=
  .inr (.inr (.inr (.inr (.inr (.inl child)))))

/-- Embed a checked target of a recurrent root-pinned common sibling move. -/
def profiledRawJointHybridMegaChildOfCommonSiblingTarget
    (child : ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin) :
    ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank :=
  .inr (.inr (.inr (.inr (.inr (.inr child)))))

/-! ## Uniform semantic source and incidence code -/

/-- Recover the exact one-sided semantic source represented by a mega tag. -/
noncomputable def profiledRawJointHybridMegaChildSource
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) := by
  cases child with
  | inl initial =>
      exact profiledRawJointInitialTaggedChildSource A strategy initialBank
        initial
  | inr rest =>
      cases rest with
      | inl replacement =>
          exact profiledRawJointHybridCommonTaggedReplacementSource A strategy
            hwin replacement
      | inr rest =>
          cases rest with
          | inl exactChild =>
              exact profiledRawJointHybridExactTaggedChildSource A strategy
                hwin exactChild
          | inr rest =>
              cases rest with
              | inl immediate =>
                  exact profiledRawJointHybridInitialImmediateSwitchSource A
                    strategy immediate
              | inr rest =>
                  cases rest with
                  | inl initialExact =>
                      exact
                        profiledRawJointHybridInitialExactTaggedChildSource A
                          strategy hwin initialExact
                  | inr siblingTarget =>
                      cases siblingTarget with
                      | inl initialSiblingTarget =>
                          exact
                            profiledRawJointHybridInitialSiblingTargetChildSource
                              A strategy initialSiblingTarget
                      | inr commonSiblingTarget =>
                          exact
                            profiledRawJointHybridCommonSiblingTargetSource A
                              strategy hwin commonSiblingTarget

/-- The finite incidence code advertised by each of the seven summands. -/
noncomputable def profiledRawJointHybridMegaChildIncidenceCode
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    ProfiledRawJointIncidenceCode A (I := Unit) :=
  (profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
    ).code A

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Source recovery preserves the code advertised by every summand. -/
theorem profiledRawJointHybridMegaChildSource_code
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
      ).code A =
      profiledRawJointHybridMegaChildIncidenceCode A strategy hwin initialBank
        child := by
  rfl

@[simp] theorem profiledRawJointHybridMegaChildSource_initial
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :
    profiledRawJointHybridMegaChildSource A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitial A strategy hwin initialBank
          child) =
      profiledRawJointInitialTaggedChildSource A strategy initialBank child :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildSource_replacement
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    profiledRawJointHybridMegaChildSource A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfReplacement A strategy hwin
          initialBank replacement) =
      profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
        replacement :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildSource_exact
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    profiledRawJointHybridMegaChildSource A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfExact A strategy hwin initialBank
          child) =
      profiledRawJointHybridExactTaggedChildSource A strategy hwin child :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildSource_immediateSwitch
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridMegaChildSource A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfImmediateSwitch A strategy hwin
          initialBank tag) =
      profiledRawJointHybridInitialImmediateSwitchSource A strategy tag :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildSource_initialExact
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    profiledRawJointHybridMegaChildSource A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitialExact A strategy hwin
          initialBank child) =
      profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
        child :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildSource_initialSiblingTarget
    (child : ProfiledRawJointHybridInitialSiblingTargetChildCode A strategy) :
    profiledRawJointHybridMegaChildSource A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy hwin
          initialBank child) =
      profiledRawJointHybridInitialSiblingTargetChildSource A strategy child :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildSource_commonSiblingTarget
    (child : ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin) :
    profiledRawJointHybridMegaChildSource A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfCommonSiblingTarget A strategy hwin
          initialBank child) =
      profiledRawJointHybridCommonSiblingTargetSource A strategy hwin child :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildIncidenceCode_initial
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :
    profiledRawJointHybridMegaChildIncidenceCode A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitial A strategy hwin initialBank
          child) =
      match child with
      | .inl tagged => tagged.2.1
      | .inr tagged => tagged.2.1 := by
  exact profiledRawJointInitialTaggedChildSource_code A strategy initialBank
    child

@[simp] theorem profiledRawJointHybridMegaChildIncidenceCode_replacement
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    profiledRawJointHybridMegaChildIncidenceCode A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfReplacement A strategy hwin
          initialBank replacement) =
      profiledRawJointHybridCommonTaggedReplacementChildCode A strategy hwin
        replacement := by
  exact profiledRawJointHybridCommonTaggedReplacementSource_code A strategy
    hwin replacement

@[simp] theorem profiledRawJointHybridMegaChildIncidenceCode_exact
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    profiledRawJointHybridMegaChildIncidenceCode A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfExact A strategy hwin initialBank
          child) =
      match child with
      | .inl tagged => tagged.2.1
      | .inr tagged => tagged.2.1 := by
  exact profiledRawJointHybridExactTaggedChildSource_code A strategy hwin
    child

@[simp] theorem
    profiledRawJointHybridMegaChildIncidenceCode_immediateSwitch
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridMegaChildIncidenceCode A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfImmediateSwitch A strategy hwin
          initialBank tag) =
      (profiledRawJointHybridInitialImmediateSwitchSource A strategy tag).code
        A :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaChildIncidenceCode_initialExact
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    profiledRawJointHybridMegaChildIncidenceCode A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitialExact A strategy hwin
          initialBank child) =
      match child with
      | .inl tagged => tagged.2.1
      | .inr tagged => tagged.2.1 := by
  exact profiledRawJointHybridInitialExactTaggedChildSource_code A strategy hwin
    child

end

/-! ## Uniform fixed policy and controller bank -/

/-- Recover the once-selected fixed recurrent policy from a mega tag. -/
noncomputable def profiledRawJointHybridMegaChildPolicy
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
        ).code A) := by
  cases child with
  | inl initial =>
      exact profiledRawJointInitialTaggedChildPolicy A strategy hwin
        initialBank initial
  | inr rest =>
      cases rest with
      | inl replacement =>
          exact profiledRawJointHybridCommonTaggedReplacementPolicy A strategy
            hwin replacement
      | inr rest =>
          cases rest with
          | inl exactChild =>
              exact profiledRawJointHybridExactTaggedChildPolicy A strategy
                hwin exactChild
          | inr rest =>
              cases rest with
              | inl immediate =>
                  exact profiledRawJointHybridInitialImmediateSwitchPolicy A
                    strategy hwin immediate
              | inr rest =>
                  cases rest with
                  | inl initialExact =>
                      exact
                        profiledRawJointHybridInitialExactTaggedChildPolicy A
                          strategy hwin initialExact
                  | inr siblingTarget =>
                      cases siblingTarget with
                      | inl initialSiblingTarget =>
                          exact
                            profiledRawJointHybridInitialSiblingTargetChildPolicy
                              A strategy hwin initialSiblingTarget
                      | inr commonSiblingTarget =>
                          exact
                            profiledRawJointHybridCommonSiblingTargetPolicy A
                              strategy hwin commonSiblingTarget

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledRawJointHybridMegaChildPolicy_initial
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :
    profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitial A strategy hwin initialBank
          child) =
      profiledRawJointInitialTaggedChildPolicy A strategy hwin initialBank
        child :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildPolicy_replacement
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfReplacement A strategy hwin
          initialBank replacement) =
      profiledRawJointHybridCommonTaggedReplacementPolicy A strategy hwin
        replacement :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildPolicy_exact
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfExact A strategy hwin initialBank
          child) =
      profiledRawJointHybridExactTaggedChildPolicy A strategy hwin child :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildPolicy_immediateSwitch
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfImmediateSwitch A strategy hwin
          initialBank tag) =
      profiledRawJointHybridInitialImmediateSwitchPolicy A strategy hwin
        tag :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildPolicy_initialExact
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitialExact A strategy hwin
          initialBank child) =
      profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        child :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildPolicy_initialSiblingTarget
    (child : ProfiledRawJointHybridInitialSiblingTargetChildCode A strategy) :
    profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy hwin
          initialBank child) =
      profiledRawJointHybridInitialSiblingTargetChildPolicy A strategy hwin
        child :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildPolicy_commonSiblingTarget
    (child : ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin) :
    profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfCommonSiblingTarget A strategy hwin
          initialBank child) =
      profiledRawJointHybridCommonSiblingTargetPolicy A strategy hwin child :=
  rfl

end

/-- Recover the complete recurrent controller bank from a mega tag. -/
noncomputable def profiledRawJointHybridMegaChildControllerBank
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (profiledRawJointHybridMegaChildSource A strategy hwin initialBank child)
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
        child) := by
  cases child with
  | inl initial =>
      exact profiledRawJointInitialTaggedChildControllerBank A strategy hwin
        initialBank initial
  | inr rest =>
      cases rest with
      | inl replacement =>
          exact
            profiledRawJointHybridCommonTaggedReplacementControllerBank A
              strategy hwin replacement
      | inr rest =>
          cases rest with
          | inl exactChild =>
              exact profiledRawJointHybridExactTaggedChildControllerBank A
                strategy hwin exactChild
          | inr rest =>
              cases rest with
              | inl immediate =>
                  exact
                    profiledRawJointHybridInitialImmediateSwitchControllerBank
                      A strategy hwin immediate
              | inr rest =>
                  cases rest with
                  | inl initialExact =>
                      exact
                        profiledRawJointHybridInitialExactTaggedChildControllerBank
                          A strategy hwin initialExact
                  | inr siblingTarget =>
                      cases siblingTarget with
                      | inl initialSiblingTarget =>
                          exact
                            profiledRawJointHybridInitialSiblingTargetChildControllerBank
                              A strategy hwin initialSiblingTarget
                      | inr commonSiblingTarget =>
                          exact
                            profiledRawJointHybridCommonSiblingTargetControllerBank
                              A strategy hwin commonSiblingTarget

@[simp] theorem profiledRawJointHybridMegaChildControllerBank_initial
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :
    profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitial A strategy hwin initialBank
          child) =
      profiledRawJointInitialTaggedChildControllerBank A strategy hwin
        initialBank child :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildControllerBank_replacement
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfReplacement A strategy hwin
          initialBank replacement) =
      profiledRawJointHybridCommonTaggedReplacementControllerBank A strategy
        hwin replacement :=
  rfl

@[simp] theorem profiledRawJointHybridMegaChildControllerBank_exact
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfExact A strategy hwin initialBank
          child) =
      profiledRawJointHybridExactTaggedChildControllerBank A strategy hwin
        child :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaChildControllerBank_immediateSwitch
    (tag : ProfiledRawJointHybridInitialImmediateSwitchTag
      (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfImmediateSwitch A strategy hwin
          initialBank tag) =
      profiledRawJointHybridInitialImmediateSwitchControllerBank A strategy
        hwin tag :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaChildControllerBank_initialExact
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitialExact A strategy hwin
          initialBank child) =
      profiledRawJointHybridInitialExactTaggedChildControllerBank A strategy
        hwin child :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaChildControllerBank_initialSiblingTarget
    (child : ProfiledRawJointHybridInitialSiblingTargetChildCode A strategy) :
    profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy hwin
          initialBank child) =
      profiledRawJointHybridInitialSiblingTargetChildControllerBank A strategy
        hwin child :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaChildControllerBank_commonSiblingTarget
    (child : ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin) :
    profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfCommonSiblingTarget A strategy hwin
          initialBank child) =
      profiledRawJointHybridCommonSiblingTargetControllerBank A strategy hwin
        child :=
  rfl

/-! ## Uniform macro and local-control families -/

abbrev ProfiledRawJointHybridMegaRightMacro
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :=
  ProfiledRawJointUnitRightPolicyMacro A strategy
    ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
      ).code A)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child)

abbrev ProfiledRawJointHybridMegaLeftMacro
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :=
  ProfiledRawJointUnitLeftPolicyMacro A strategy
    ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
      ).code A)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child)

/-- Process-one owner controls while a right macro is live. -/
abbrev ProfiledRawJointHybridMegaRightOwner
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :=
  ProfiledRawJointUnitPolicyRightOwner A strategy
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank child)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child)
    (profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
      child) ()

/-- Process-one receiver controls while a left macro is live. -/
abbrev ProfiledRawJointHybridMegaLeftReceiver
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :=
  ProfiledRawJointUnitPolicyLeftReceiver A strategy
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank child)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child) ()

/-- Process-two receiver controls while a right macro is live. -/
abbrev ProfiledRawJointHybridMegaRightReceiver
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :=
  ProfiledRawJointUnitPolicyRightReceiver A strategy
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank child)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child) ()

/-- Process-two owner controls while a left macro is live. -/
abbrev ProfiledRawJointHybridMegaLeftOwner
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :=
  ProfiledRawJointUnitPolicyLeftOwner A strategy
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank child)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child)
    (profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
      child) ()

/-! ## Definitional reductions for the exact-initial fifth summand -/

@[simp] theorem profiledRawJointHybridMegaRightOwner_initialExact
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    ProfiledRawJointHybridMegaRightOwner A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitialExact A strategy hwin
          initialBank child) =
      ProfiledRawJointHybridInitialExactTaggedRightOwner A strategy hwin child :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridMegaLeftReceiver_initialExact
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    ProfiledRawJointHybridMegaLeftReceiver A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitialExact A strategy hwin
          initialBank child) =
      ProfiledRawJointHybridInitialExactTaggedLeftReceiver A strategy hwin
        child :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridMegaRightReceiver_initialExact
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    ProfiledRawJointHybridMegaRightReceiver A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitialExact A strategy hwin
          initialBank child) =
      ProfiledRawJointHybridInitialExactTaggedRightReceiver A strategy hwin
        child :=
  rfl

@[simp] theorem profiledRawJointHybridMegaLeftOwner_initialExact
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    ProfiledRawJointHybridMegaLeftOwner A strategy hwin initialBank
        (profiledRawJointHybridMegaChildOfInitialExact A strategy hwin
          initialBank child) =
      ProfiledRawJointHybridInitialExactTaggedLeftOwner A strategy hwin child :=
  rfl

noncomputable instance profiledRawJointHybridMegaRightMacroFintype
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    Fintype
      (ProfiledRawJointHybridMegaRightMacro A strategy hwin initialBank
        child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridMegaLeftMacroFintype
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    Fintype
      (ProfiledRawJointHybridMegaLeftMacro A strategy hwin initialBank
        child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridMegaRightOwnerFintype
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    Fintype
      (ProfiledRawJointHybridMegaRightOwner A strategy hwin initialBank
        child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridMegaLeftReceiverFintype
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    Fintype
      (ProfiledRawJointHybridMegaLeftReceiver A strategy hwin initialBank
        child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridMegaRightReceiverFintype
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    Fintype
      (ProfiledRawJointHybridMegaRightReceiver A strategy hwin initialBank
        child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridMegaLeftOwnerFintype
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    Fintype
      (ProfiledRawJointHybridMegaLeftOwner A strategy hwin initialBank
        child) := by
  classical
  infer_instance

end

end DetParityAutomaton

end DistributedSynthesis
