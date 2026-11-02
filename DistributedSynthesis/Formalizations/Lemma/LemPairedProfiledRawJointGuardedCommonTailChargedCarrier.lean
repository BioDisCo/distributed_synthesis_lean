/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailChargedLocalTable
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointLeaderFreeExceptionalLift

/-!
# One finite carrier for the ordinary tail and both charged shadows

The charged three-graph table has four orientation-specific codomains.  The
final local controller needs one fixed state type.  Here each old exceptional
state and each of the two charged shadow types is embedded into a single
finite exceptional carrier, while all initial and indexed recurrent controls
are kept literally unchanged.

These are structural embeddings only.  They inspect no graph, orientation,
leader bit, input, or semantic history.
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

/-! ## Unified finite exceptional carriers -/

/-- Process one's old front state, right charged shadow, or left charged
shadow.  The sum tags are local phase tags, not physical orientations supplied
at runtime. -/
abbrev ProfiledRawJointGuardedCommonTailChargedExceptionalOne :=
  ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin ⊕
    (ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A strategy hwin ⊕
      ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy hwin)

/-- Process-two mirror. -/
abbrev ProfiledRawJointGuardedCommonTailChargedExceptionalTwo :=
  ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin ⊕
    (ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A strategy hwin ⊕
      ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy hwin)

noncomputable instance
    profiledRawJointGuardedCommonTailChargedExceptionalOneFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTailChargedExceptionalOne A strategy hwin) :=
  inferInstance

noncomputable instance
    profiledRawJointGuardedCommonTailChargedExceptionalTwoFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTailChargedExceptionalTwo A strategy hwin) :=
  inferInstance

abbrev ProfiledRawJointGuardedCommonTailChargedOneControl :=
  ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin initialBank
    (ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin)
    (ProfiledRawJointGuardedCommonTailChargedExceptionalOne A strategy hwin)

abbrev ProfiledRawJointGuardedCommonTailChargedTwoControl :=
  ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin initialBank
    (ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin)
    (ProfiledRawJointGuardedCommonTailChargedExceptionalTwo A strategy hwin)

/-! ## Exceptional injections -/

def profiledRawJointGuardedCommonTailChargedCoreOne
    (state : ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin) :
    ProfiledRawJointGuardedCommonTailChargedExceptionalOne A strategy hwin :=
  .inl state

def profiledRawJointGuardedCommonTailChargedRightOne
    (state : ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A
      strategy hwin) :
    ProfiledRawJointGuardedCommonTailChargedExceptionalOne A strategy hwin :=
  .inr (.inl state)

def profiledRawJointGuardedCommonTailChargedLeftOne
    (state : ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy
      hwin) :
    ProfiledRawJointGuardedCommonTailChargedExceptionalOne A strategy hwin :=
  .inr (.inr state)

def profiledRawJointGuardedCommonTailChargedCoreTwo
    (state : ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin) :
    ProfiledRawJointGuardedCommonTailChargedExceptionalTwo A strategy hwin :=
  .inl state

def profiledRawJointGuardedCommonTailChargedRightTwo
    (state : ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A
      strategy hwin) :
    ProfiledRawJointGuardedCommonTailChargedExceptionalTwo A strategy hwin :=
  .inr (.inl state)

def profiledRawJointGuardedCommonTailChargedLeftTwo
    (state : ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy
      hwin) :
    ProfiledRawJointGuardedCommonTailChargedExceptionalTwo A strategy hwin :=
  .inr (.inr state)

/-! ## Lifting the already verified ordinary controls -/

noncomputable def profiledRawJointGuardedCommonTailLiftOldOne
    (control : ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin
      initialBank
      (ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin)
      (ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin)) :
    ProfiledRawJointGuardedCommonTailChargedOneControl A strategy hwin
      initialBank :=
  ProfiledRawJointLeaderFreeOneControl.mapExceptional
    (profiledRawJointGuardedCommonTailChargedCoreOne A strategy hwin) control

noncomputable def profiledRawJointGuardedCommonTailLiftOldTwo
    (control : ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin
      initialBank
      (ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin)
      (ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin)) :
    ProfiledRawJointGuardedCommonTailChargedTwoControl A strategy hwin
      initialBank :=
  ProfiledRawJointLeaderFreeTwoControl.mapExceptional
    (profiledRawJointGuardedCommonTailChargedCoreTwo A strategy hwin) control

/-! ## Lifting all four charged-table codomains -/

noncomputable def profiledRawJointGuardedCommonTailLiftRightNextOne
    (next : ProfiledRawJointGuardedCommonTailRightChargedNextOne A strategy
      hwin initialBank) :
    ProfiledRawJointGuardedCommonTailChargedOneControl A strategy hwin
      initialBank :=
  match next with
  | .inl control =>
      profiledRawJointGuardedCommonTailLiftOldOne A strategy hwin initialBank
        control
  | .inr shadow =>
      .exceptional
        (profiledRawJointGuardedCommonTailChargedRightOne A strategy hwin
          shadow)

noncomputable def profiledRawJointGuardedCommonTailLiftRightNextTwo
    (next : ProfiledRawJointGuardedCommonTailRightChargedNextTwo A strategy
      hwin initialBank) :
    ProfiledRawJointGuardedCommonTailChargedTwoControl A strategy hwin
      initialBank :=
  match next with
  | .inl control =>
      profiledRawJointGuardedCommonTailLiftOldTwo A strategy hwin initialBank
        control
  | .inr shadow =>
      .exceptional
        (profiledRawJointGuardedCommonTailChargedRightTwo A strategy hwin
          shadow)

noncomputable def profiledRawJointGuardedCommonTailLiftLeftNextOne
    (next : ProfiledRawJointGuardedCommonTailLeftChargedNextOne A strategy hwin
      initialBank) :
    ProfiledRawJointGuardedCommonTailChargedOneControl A strategy hwin
      initialBank :=
  match next with
  | .inl control =>
      profiledRawJointGuardedCommonTailLiftOldOne A strategy hwin initialBank
        control
  | .inr shadow =>
      .exceptional
        (profiledRawJointGuardedCommonTailChargedLeftOne A strategy hwin
          shadow)

noncomputable def profiledRawJointGuardedCommonTailLiftLeftNextTwo
    (next : ProfiledRawJointGuardedCommonTailLeftChargedNextTwo A strategy hwin
      initialBank) :
    ProfiledRawJointGuardedCommonTailChargedTwoControl A strategy hwin
      initialBank :=
  match next with
  | .inl control =>
      profiledRawJointGuardedCommonTailLiftOldTwo A strategy hwin initialBank
        control
  | .inr shadow =>
      .exceptional
        (profiledRawJointGuardedCommonTailChargedLeftTwo A strategy hwin
          shadow)

@[simp] theorem profiledRawJointGuardedCommonTailLiftRightNextOne_inl
    (control : ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin
      initialBank
      (ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin)
      (ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin)) :
    profiledRawJointGuardedCommonTailLiftRightNextOne A strategy hwin
        initialBank (.inl control) =
      profiledRawJointGuardedCommonTailLiftOldOne A strategy hwin initialBank
        control :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonTailLiftRightNextOne_inr
    (shadow : ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A
      strategy hwin) :
    profiledRawJointGuardedCommonTailLiftRightNextOne A strategy hwin
        initialBank (.inr shadow) =
      .exceptional
        (profiledRawJointGuardedCommonTailChargedRightOne A strategy hwin
          shadow) :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonTailLiftRightNextTwo_inl
    (control : ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin
      initialBank
      (ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin)
      (ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin)) :
    profiledRawJointGuardedCommonTailLiftRightNextTwo A strategy hwin
        initialBank (.inl control) =
      profiledRawJointGuardedCommonTailLiftOldTwo A strategy hwin initialBank
        control :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonTailLiftRightNextTwo_inr
    (shadow : ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A
      strategy hwin) :
    profiledRawJointGuardedCommonTailLiftRightNextTwo A strategy hwin
        initialBank (.inr shadow) =
      .exceptional
        (profiledRawJointGuardedCommonTailChargedRightTwo A strategy hwin
          shadow) :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonTailLiftLeftNextOne_inl
    (control : ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin
      initialBank
      (ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin)
      (ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin)) :
    profiledRawJointGuardedCommonTailLiftLeftNextOne A strategy hwin
        initialBank (.inl control) =
      profiledRawJointGuardedCommonTailLiftOldOne A strategy hwin initialBank
        control :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonTailLiftLeftNextOne_inr
    (shadow : ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A
      strategy hwin) :
    profiledRawJointGuardedCommonTailLiftLeftNextOne A strategy hwin
        initialBank (.inr shadow) =
      .exceptional
        (profiledRawJointGuardedCommonTailChargedLeftOne A strategy hwin
          shadow) :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonTailLiftLeftNextTwo_inl
    (control : ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin
      initialBank
      (ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin)
      (ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin)) :
    profiledRawJointGuardedCommonTailLiftLeftNextTwo A strategy hwin
        initialBank (.inl control) =
      profiledRawJointGuardedCommonTailLiftOldTwo A strategy hwin initialBank
        control :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonTailLiftLeftNextTwo_inr
    (shadow : ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A
      strategy hwin) :
    profiledRawJointGuardedCommonTailLiftLeftNextTwo A strategy hwin
        initialBank (.inr shadow) =
      .exceptional
        (profiledRawJointGuardedCommonTailChargedLeftTwo A strategy hwin
          shadow) :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
