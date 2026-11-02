/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedPolicyLocalAdapter

/-!
# Finite annotated starts for the two guarded common shadows

The decorated local adapter installs one coherent successor pair into both
local shadows.  This file carries the finite annotation selected at that very
same rational-policy occurrence alongside each start result.  Thus a concrete
annotation (notably, cross-table IDs) can be consumed locally without ever
reconstructing it from the public child code.

The executable definitions use only a fixed finite package, a finite policy
state, and the current input pair.  They accept no graph, orientation, leader
bit, or semantic history.
-/

namespace DistributedSynthesis

universe u v x y s b

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

variable {Extra : Type b} [Fintype Extra]

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

private abbrev CommonCode :=
  ProfiledRawJointIncidenceCode A (I := Unit)

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable
  {initial : CommonPoint A strategy}
  {ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop}

/-! ## Executable annotated starts -/

/-- Process one's local start paired with the annotation from the same
successor-policy lookup. -/
noncomputable def startOneShadowAnnotated
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (Out₁ × ProfiledRawJointGuardedCommonOneShadow A strategy hwin) ×
      Extra :=
  (package.startOneShadow A strategy hwin state hreachable input,
    package.nextExtraAt A strategy hwin state input)

/-- Process two's local start paired with that same successor annotation. -/
noncomputable def startTwoShadowAnnotated
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (Out₂ × ProfiledRawJointGuardedCommonTwoShadow A strategy hwin) ×
      Extra :=
  (package.startTwoShadow A strategy hwin state hreachable input,
    package.nextExtraAt A strategy hwin state input)

section
omit [Fintype Extra]

@[simp] theorem startOneShadowAnnotated_start
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.startOneShadowAnnotated A strategy hwin state hreachable
      input).1 =
      package.startOneShadow A strategy hwin state hreachable input :=
  rfl

@[simp] theorem startTwoShadowAnnotated_start
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.startTwoShadowAnnotated A strategy hwin state hreachable
      input).1 =
      package.startTwoShadow A strategy hwin state hreachable input :=
  rfl

@[simp] theorem startOneShadowAnnotated_extra
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.startOneShadowAnnotated A strategy hwin state hreachable
      input).2 = package.nextExtraAt A strategy hwin state input :=
  rfl

@[simp] theorem startTwoShadowAnnotated_extra
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.startTwoShadowAnnotated A strategy hwin state hreachable
      input).2 = package.nextExtraAt A strategy hwin state input :=
  rfl

end

/-! ## Same pair and same annotation -/

section
omit [Fintype Extra]

/-- Process one's annotated start installs the successor pair selected in the
same lookup as its annotation. -/
@[simp] theorem startOneShadowAnnotated_common
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.startOneShadowAnnotated A strategy hwin state hreachable
      input).1.2.common =
      package.nextPairAt A strategy hwin state input :=
  rfl

/-- Process two installs that identical successor pair. -/
@[simp] theorem startTwoShadowAnnotated_common
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.startTwoShadowAnnotated A strategy hwin state hreachable
      input).1.2.common =
      package.nextPairAt A strategy hwin state input :=
  rfl

/-- The two annotated shadows carry literally the same common successor. -/
theorem startAnnotatedShadows_common_eq
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.startOneShadowAnnotated A strategy hwin state hreachable
      input).1.2.common =
      (package.startTwoShadowAnnotated A strategy hwin state hreachable
        input).1.2.common :=
  rfl

/-- The two annotated starts carry literally the same finite annotation. -/
theorem startAnnotatedShadows_extra_eq
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.startOneShadowAnnotated A strategy hwin state hreachable
      input).2 =
      (package.startTwoShadowAnnotated A strategy hwin state hreachable
        input).2 :=
  rfl

end

/-! ## Exact annotation validity -/

omit [Fintype Extra] in
/-- Process one's stored annotation is valid for its installed common pair at
the exact child code emitted by the current pair. -/
theorem startOneShadowAnnotated_extra_valid
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    ExtraValid
      ((package.pairAt A strategy hwin state).bothNextCode A strategy hwin
        input)
      (package.startOneShadowAnnotated A strategy hwin state hreachable
        input).1.2.common
      (package.startOneShadowAnnotated A strategy hwin state hreachable
        input).2 := by
  simpa only [startOneShadowAnnotated_common,
    startOneShadowAnnotated_extra] using
    package.nextExtraAt_valid_at_currentChildCode A strategy hwin hreachable
      input

omit [Fintype Extra] in
/-- Process two receives the same exact annotation-validity fact. -/
theorem startTwoShadowAnnotated_extra_valid
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    ExtraValid
      ((package.pairAt A strategy hwin state).bothNextCode A strategy hwin
        input)
      (package.startTwoShadowAnnotated A strategy hwin state hreachable
        input).1.2.common
      (package.startTwoShadowAnnotated A strategy hwin state hreachable
        input).2 := by
  simpa only [startTwoShadowAnnotated_common,
    startTwoShadowAnnotated_extra] using
    package.nextExtraAt_valid_at_currentChildCode A strategy hwin hreachable
      input

/-! ## Unchanged physical outputs -/

section
omit [Fintype Extra]

/-- Adding the annotation does not alter either physical start output. -/
theorem startAnnotatedShadows_outputs
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    ((package.startOneShadowAnnotated A strategy hwin state hreachable
        input).1.1,
      (package.startTwoShadowAnnotated A strategy hwin state hreachable
        input).1.1) =
      (((package.pairAt A strategy hwin state).rightRootRecord A strategy hwin
        input).2.1.physical.closingBoth,
        ((package.pairAt A strategy hwin state).leftRootRecord A strategy hwin
          input).2.1.physical.closingBoth) := by
  exact package.startShadows_outputs A strategy hwin state hreachable input

/-- Erasing the annotation recovers the old one-shadow result literally. -/
theorem startOneShadowAnnotated_output
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.startOneShadowAnnotated A strategy hwin state hreachable
      input).1.1 =
      (package.startOneShadow A strategy hwin state hreachable input).1 :=
  rfl

/-- Erasing the annotation recovers the old two-shadow result literally. -/
theorem startTwoShadowAnnotated_output
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    (package.startTwoShadowAnnotated A strategy hwin state hreachable
      input).1.1 =
      (package.startTwoShadow A strategy hwin state hreachable input).1 :=
  rfl

end

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
