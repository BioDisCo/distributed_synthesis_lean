/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialPolicyBank
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonReplacementPolicyBank

/-!
# One finite tagged family of common-round replacements

At each reachable common control and current input pair there are two
proof-side replacement sources: the right-live singleton representing the
strict-left alternative, and the left-live singleton representing the
strict-right alternative.  This file collects those choices in one finite
tagged family and recovers from every tag its literal semantic source, fresh
one-sided policy, complete recurrent controller bank, and appropriate live
root macro.

The sum tag is construction provenance.  It is not stored in either local
process state as a graph, orientation, or leader signal.  No carrier
transition is defined here.
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

/-! ## The finite global tag -/

/-- Left summand means a right-live replacement; right summand means its
left-live mirror. -/
abbrev ProfiledRawJointHybridCommonReplacementSideTag := Unit ⊕ Unit

/-- One finite tag records the selected common policy control, current input
pair, and one of the two proof-side singleton replacements. -/
structure ProfiledRawJointHybridCommonTaggedReplacement where
  control : ProfiledRawJointHybridCommonControl A strategy hwin
  input : In₁ × In₂
  side : ProfiledRawJointHybridCommonReplacementSideTag

/-- The complete tagged replacement family is finite. -/
noncomputable instance profiledRawJointHybridCommonTaggedReplacementFintype :
    Fintype (ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) := by
  classical
  let Rep := ProfiledRawJointHybridCommonControl A strategy hwin ×
    (In₁ × In₂) × ProfiledRawJointHybridCommonReplacementSideTag
  let encode :
      ProfiledRawJointHybridCommonTaggedReplacement A strategy hwin → Rep :=
    fun replacement ↦
      (replacement.control, replacement.input, replacement.side)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftControl, leftInput, leftSide⟩
    rcases right with ⟨rightControl, rightInput, rightSide⟩
    simp only [encode] at heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    rfl)

/-! ## Recovering the generic installed common move -/

/-- The once-selected installed common move at this tag's finite control. -/
noncomputable def profiledRawJointHybridCommonTaggedInstalled
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :=
  profiledRawJointHybridCommonControlInstalled A strategy hwin
    replacement.control

/-! ## Recovered source and exact strict-shadow code -/

/-- Literal singleton semantic source selected by the sum tag. -/
noncomputable def profiledRawJointHybridCommonTaggedReplacementSource
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  match replacement.side with
  | .inl _ =>
      ProfiledRawJointHybridCommonRightReplacementSource A
        (profiledRawJointHybridCommonTaggedInstalled A strategy hwin
          replacement) replacement.input
  | .inr _ =>
      ProfiledRawJointHybridCommonLeftReplacementSource A
        (profiledRawJointHybridCommonTaggedInstalled A strategy hwin
          replacement) replacement.input

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridCommonTaggedReplacementSource_inl
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
        ⟨control, input, .inl ()⟩ =
      ProfiledRawJointHybridCommonRightReplacementSource A
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
        input :=
  rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridCommonTaggedReplacementSource_inr
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
        ⟨control, input, .inr ()⟩ =
      ProfiledRawJointHybridCommonLeftReplacementSource A
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
        input :=
  rfl

/-- Exact one-sided child code represented by the tag. -/
noncomputable def profiledRawJointHybridCommonTaggedReplacementChildCode
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) : ProfiledRawJointIncidenceCode A (I := Unit) :=
  let installed := profiledRawJointHybridCommonTaggedInstalled A strategy hwin
    replacement
  match replacement.side with
  | .inl _ =>
      profiledRawJointOneSidedNext A replacement.control.2.incidenceCode
        installed.rawMove
        (profiledRawJointCommonOneRoundStrictLeft replacement.input)
  | .inr _ =>
      profiledRawJointOneSidedNext A replacement.control.2.incidenceCode
        installed.rawMove
        (profiledRawJointCommonOneRoundStrictRight replacement.input)

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The recovered literal source erases to exactly the strict-shadow code
specified by the tag. -/
theorem profiledRawJointHybridCommonTaggedReplacementSource_code
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    (profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
      replacement).code A =
      profiledRawJointHybridCommonTaggedReplacementChildCode A strategy hwin
        replacement := by
  rcases replacement with ⟨control, input, side⟩
  cases side with
  | inl tag =>
      cases tag
      exact profiledRawJointHybridCommonRightReplacementSource_code A
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
        input
  | inr tag =>
      cases tag
      exact profiledRawJointHybridCommonLeftReplacementSource_code A
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
        input

/-! ## Fresh policy and complete recurrent controller bank -/

/-- Fresh one-sided policy selected for the exact replacement source. -/
noncomputable def profiledRawJointHybridCommonTaggedReplacementPolicy
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
        replacement).code A) := by
  rcases replacement with ⟨control, input, side⟩
  cases side with
  | inl tag =>
      cases tag
      exact profiledRawJointHybridCommonRightReplacementPolicy A hwin
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
        input
  | inr tag =>
      cases tag
      exact profiledRawJointHybridCommonLeftReplacementPolicy A hwin
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
        input

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridCommonTaggedReplacementPolicy_inl
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointHybridCommonTaggedReplacementPolicy A strategy hwin
        ⟨control, input, .inl ()⟩ =
      profiledRawJointHybridCommonRightReplacementPolicy A hwin
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
        input :=
  rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridCommonTaggedReplacementPolicy_inr
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointHybridCommonTaggedReplacementPolicy A strategy hwin
        ⟨control, input, .inr ()⟩ =
      profiledRawJointHybridCommonLeftReplacementPolicy A hwin
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
        input :=
  rfl

/-- Complete recurrent controller bank below the tagged fresh policy. -/
noncomputable def profiledRawJointHybridCommonTaggedReplacementControllerBank
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
        replacement)
      (profiledRawJointHybridCommonTaggedReplacementPolicy A strategy hwin
        replacement) := by
  rcases replacement with ⟨control, input, side⟩
  cases side with
  | inl tag =>
      cases tag
      exact profiledRawJointHybridCommonRightReplacementControllerBank A hwin
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
        input
  | inr tag =>
      cases tag
      exact profiledRawJointHybridCommonLeftReplacementControllerBank A hwin
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
        input

/-! ## The appropriate live root -/

/-- Dependent live-root macro type selected by the sum tag. -/
abbrev ProfiledRawJointHybridCommonTaggedReplacementRootMacro
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :=
  match replacement.side with
  | .inl _ =>
      ProfiledRawJointUnitRightPolicyMacro A strategy
        ((profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
          replacement).code A)
        (profiledRawJointHybridCommonTaggedReplacementPolicy A strategy hwin
          replacement)
  | .inr _ =>
      ProfiledRawJointUnitLeftPolicyMacro A strategy
        ((profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
          replacement).code A)
        (profiledRawJointHybridCommonTaggedReplacementPolicy A strategy hwin
          replacement)

/-- Canonical right-live or left-live root of the tagged fresh policy. -/
noncomputable def profiledRawJointHybridCommonTaggedReplacementRoot
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    ProfiledRawJointHybridCommonTaggedReplacementRootMacro A strategy hwin
      replacement := by
  rcases replacement with ⟨control, input, side⟩
  cases side with
  | inl tag =>
      cases tag
      exact profiledRawJointHybridCommonRightReplacementRoot A hwin
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
        input
  | inr tag =>
      cases tag
      exact profiledRawJointHybridCommonLeftReplacementRoot A hwin
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
        input

/-- Every tag's live-root macro type is finite. -/
noncomputable instance profiledRawJointHybridCommonTaggedReplacementRootFintype
    (replacement : ProfiledRawJointHybridCommonTaggedReplacement A strategy
      hwin) :
    Fintype
      (ProfiledRawJointHybridCommonTaggedReplacementRootMacro A strategy hwin
        replacement) := by
  classical
  rcases replacement with ⟨control, input, side⟩
  cases side with
  | inl tag => cases tag; infer_instance
  | inr tag => cases tag; infer_instance

/-! ## Exact root projections for the local carrier -/

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- At a right-live tag, the recovered root is the canonical replacement
root selected by the generic bank. -/
theorem profiledRawJointHybridCommonTaggedReplacementRoot_inl
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointHybridCommonTaggedReplacementRoot A strategy hwin
        ⟨control, input, .inl ()⟩ =
      profiledRawJointHybridCommonRightReplacementRoot A hwin
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
        input :=
  rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-live root mirror. -/
theorem profiledRawJointHybridCommonTaggedReplacementRoot_inr
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointHybridCommonTaggedReplacementRoot A strategy hwin
        ⟨control, input, .inr ()⟩ =
      profiledRawJointHybridCommonLeftReplacementRoot A hwin
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
        input :=
  rfl

end


end DetParityAutomaton

end DistributedSynthesis
