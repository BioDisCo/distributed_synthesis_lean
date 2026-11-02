/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonTaggedReplacementFamily
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridExactTaggedChildFamily

/-!
# One finite recurrent child family for the hybrid carrier

There are two ways to enter the ordinary recurrent raw-joint policy:

* a one-round replacement selected after an ambiguous common shadow, or
* a literal exact child selected when the guarded common root closes.

This file puts both sources in one finite sum.  Each tag recovers its exact
semantic source, one fixed provenance policy, and the corresponding complete
controller bank.  It then exposes the four dependent local control families
consumed by the leader-free recurrent kernel.

The outer sum is construction provenance.  It is not a runtime graph,
orientation, or strict-leader field, and no transition inspects such data.
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

/-! ## The unified finite tag -/

/-- A recurrent child is either a common-shadow replacement or an exact
literal child of a guarded common root. -/
abbrev ProfiledRawJointHybridUnifiedChildCode :=
  ProfiledRawJointHybridCommonTaggedReplacement A strategy hwin ⊕
    ProfiledRawJointHybridExactTaggedChildCode A strategy hwin

noncomputable instance profiledRawJointHybridUnifiedChildCodeFintype :
    Fintype (ProfiledRawJointHybridUnifiedChildCode A strategy hwin) := by
  classical
  infer_instance

/-- Embed a common-shadow replacement into the recurrent family. -/
def profiledRawJointHybridUnifiedChildOfReplacement
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    ProfiledRawJointHybridUnifiedChildCode A strategy hwin :=
  .inl replacement

/-- Embed an exact guarded-root child into the recurrent family. -/
def profiledRawJointHybridUnifiedChildOfExact
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    ProfiledRawJointHybridUnifiedChildCode A strategy hwin :=
  .inr child

/-! ## Recovered source, code, policy, and controller bank -/

/-- The exact semantic source represented by a unified child tag. -/
noncomputable def profiledRawJointHybridUnifiedChildSource
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  match child with
  | .inl replacement =>
      profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
        replacement
  | .inr exact =>
      profiledRawJointHybridExactTaggedChildSource A strategy hwin exact

/-- The finite incidence code explicitly advertised by either summand. -/
noncomputable def profiledRawJointHybridUnifiedChildIncidenceCode
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :
    ProfiledRawJointIncidenceCode A (I := Unit) :=
  match child with
  | .inl replacement =>
      profiledRawJointHybridCommonTaggedReplacementChildCode A strategy hwin
        replacement
  | .inr exact =>
      match exact with
      | .inl right => right.2.1
      | .inr left => left.2.1

section
omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂]

/-- Source recovery preserves the advertised finite code in both summands. -/
theorem profiledRawJointHybridUnifiedChildSource_code
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :
    (profiledRawJointHybridUnifiedChildSource A strategy hwin child).code A =
      profiledRawJointHybridUnifiedChildIncidenceCode A strategy hwin child := by
  cases child with
  | inl replacement =>
      exact profiledRawJointHybridCommonTaggedReplacementSource_code A
        strategy hwin replacement
  | inr exact =>
      exact profiledRawJointHybridExactTaggedChildSource_code A strategy hwin
        exact

@[simp] theorem profiledRawJointHybridUnifiedChildSource_replacement
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    profiledRawJointHybridUnifiedChildSource A strategy hwin
        (profiledRawJointHybridUnifiedChildOfReplacement A strategy hwin
          replacement) =
      profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
        replacement :=
  rfl

@[simp] theorem profiledRawJointHybridUnifiedChildSource_exact
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    profiledRawJointHybridUnifiedChildSource A strategy hwin
        (profiledRawJointHybridUnifiedChildOfExact A strategy hwin child) =
      profiledRawJointHybridExactTaggedChildSource A strategy hwin child :=
  rfl

end

/-- The once-selected fixed recurrent policy of a unified child. -/
noncomputable def profiledRawJointHybridUnifiedChildPolicy
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointHybridUnifiedChildSource A strategy hwin child).code
        A) := by
  cases child with
  | inl replacement =>
      exact profiledRawJointHybridCommonTaggedReplacementPolicy A strategy
        hwin replacement
  | inr exact =>
      exact profiledRawJointHybridExactTaggedChildPolicy A strategy hwin exact

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointHybridUnifiedChildPolicy_replacement
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    profiledRawJointHybridUnifiedChildPolicy A strategy hwin
        (profiledRawJointHybridUnifiedChildOfReplacement A strategy hwin
          replacement) =
      profiledRawJointHybridCommonTaggedReplacementPolicy A strategy hwin
        replacement :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointHybridUnifiedChildPolicy_exact
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    profiledRawJointHybridUnifiedChildPolicy A strategy hwin
        (profiledRawJointHybridUnifiedChildOfExact A strategy hwin child) =
      profiledRawJointHybridExactTaggedChildPolicy A strategy hwin child :=
  rfl

/-- The complete recurrent controller bank recovered from a unified child. -/
noncomputable def profiledRawJointHybridUnifiedChildControllerBank
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (profiledRawJointHybridUnifiedChildSource A strategy hwin child)
      (profiledRawJointHybridUnifiedChildPolicy A strategy hwin child) := by
  cases child with
  | inl replacement =>
      exact
        profiledRawJointHybridCommonTaggedReplacementControllerBank A strategy
          hwin replacement
  | inr exact =>
      exact profiledRawJointHybridExactTaggedChildControllerBank A strategy
        hwin exact

@[simp] theorem
    profiledRawJointHybridUnifiedChildControllerBank_replacement
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    profiledRawJointHybridUnifiedChildControllerBank A strategy hwin
        (profiledRawJointHybridUnifiedChildOfReplacement A strategy hwin
          replacement) =
      profiledRawJointHybridCommonTaggedReplacementControllerBank A strategy
        hwin replacement :=
  rfl

@[simp] theorem profiledRawJointHybridUnifiedChildControllerBank_exact
    (child : ProfiledRawJointHybridExactTaggedChildCode A strategy hwin) :
    profiledRawJointHybridUnifiedChildControllerBank A strategy hwin
        (profiledRawJointHybridUnifiedChildOfExact A strategy hwin child) =
      profiledRawJointHybridExactTaggedChildControllerBank A strategy hwin
        child :=
  rfl

/-! ## Macro and local-control families -/

/-- The right-live recurrent macro type below one unified child. -/
abbrev ProfiledRawJointHybridUnifiedRightMacro
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :=
  ProfiledRawJointUnitRightPolicyMacro A strategy
    ((profiledRawJointHybridUnifiedChildSource A strategy hwin child).code A)
    (profiledRawJointHybridUnifiedChildPolicy A strategy hwin child)

/-- The left-live recurrent macro type below one unified child. -/
abbrev ProfiledRawJointHybridUnifiedLeftMacro
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :=
  ProfiledRawJointUnitLeftPolicyMacro A strategy
    ((profiledRawJointHybridUnifiedChildSource A strategy hwin child).code A)
    (profiledRawJointHybridUnifiedChildPolicy A strategy hwin child)

/-- Process-one owner controls while the right macro is live. -/
abbrev ProfiledRawJointHybridUnifiedRightOwner
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :=
  ProfiledRawJointUnitPolicyRightOwner A strategy
    (profiledRawJointHybridUnifiedChildSource A strategy hwin child)
    (profiledRawJointHybridUnifiedChildPolicy A strategy hwin child)
    (profiledRawJointHybridUnifiedChildControllerBank A strategy hwin child) ()

/-- Process-one receiver controls while the left macro is live. -/
abbrev ProfiledRawJointHybridUnifiedLeftReceiver
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :=
  ProfiledRawJointUnitPolicyLeftReceiver A strategy
    (profiledRawJointHybridUnifiedChildSource A strategy hwin child)
    (profiledRawJointHybridUnifiedChildPolicy A strategy hwin child) ()

/-- Process-two receiver controls while the right macro is live. -/
abbrev ProfiledRawJointHybridUnifiedRightReceiver
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :=
  ProfiledRawJointUnitPolicyRightReceiver A strategy
    (profiledRawJointHybridUnifiedChildSource A strategy hwin child)
    (profiledRawJointHybridUnifiedChildPolicy A strategy hwin child) ()

/-- Process-two owner controls while the left macro is live. -/
abbrev ProfiledRawJointHybridUnifiedLeftOwner
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :=
  ProfiledRawJointUnitPolicyLeftOwner A strategy
    (profiledRawJointHybridUnifiedChildSource A strategy hwin child)
    (profiledRawJointHybridUnifiedChildPolicy A strategy hwin child)
    (profiledRawJointHybridUnifiedChildControllerBank A strategy hwin child) ()

noncomputable instance profiledRawJointHybridUnifiedRightMacroFintype
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :
    Fintype (ProfiledRawJointHybridUnifiedRightMacro A strategy hwin child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridUnifiedLeftMacroFintype
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :
    Fintype (ProfiledRawJointHybridUnifiedLeftMacro A strategy hwin child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridUnifiedRightOwnerFintype
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :
    Fintype (ProfiledRawJointHybridUnifiedRightOwner A strategy hwin child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridUnifiedLeftReceiverFintype
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridUnifiedLeftReceiver A strategy hwin child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridUnifiedRightReceiverFintype
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridUnifiedRightReceiver A strategy hwin child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridUnifiedLeftOwnerFintype
    (child : ProfiledRawJointHybridUnifiedChildCode A strategy hwin) :
    Fintype (ProfiledRawJointHybridUnifiedLeftOwner A strategy hwin child) := by
  classical
  infer_instance

end

end DetParityAutomaton

end DistributedSynthesis
