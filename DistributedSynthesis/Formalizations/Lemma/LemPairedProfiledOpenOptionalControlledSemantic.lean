/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOptionalLaneFibres
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenHiddenDescriptorFamilyAlphabet
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedHiddenDescriptorContinuity

/-!
# Optional-fresh semantics with literal code-parity control

The correlated finite-tag semantics may reach two-active, right-only,
left-only, or inactive states.  This file attaches the literal code-parity
DPA control to the already total optional-fresh carrier.  Its projection is
exactly the pre-existing controlled correlated semantics, so all fold and
branch-parity results transfer without a lane-liveness assumption.

The full hidden descriptor is

```
((current indexed code, literal DPA control), old correlated finite move).
```

All lane data and fresh-child witnesses remain proof-side.  No graph,
orientation, strict-leader flag, or selected active lane is observable.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

/-! ## Carrier, projection, and initial state -/

/-- The total optional-fresh semantic state paired with the literal control
of the finite code-parity DPA. -/
abbrev ProfiledOpenIndexedOptionalControlledSemanticState
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin basis
      (I := I) ×
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State

/-- Erase only fresh provenance and retain the correlated state/control pair
used by the existing hidden-continuity development. -/
def ProfiledOpenIndexedOptionalControlledSemanticState.toControlled
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
      initialCode :=
  (point.1.state, point.2)

/-- A live-both initial source enters the total optional carrier without
changing its semantic state and starts at the DPA initial control. -/
noncomputable def profiledOpenIndexedOptionalControlledSemanticInitial
    (initial : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
      (initial.state.code A strategy hwin basis) :=
  (ProfiledOpenIndexedOptionalFreshSemanticPoint.ofLiveFresh A strategy hwin
      basis initial,
    (profiledOpenIndexedBiBeliefCodeParityDPA A
      (initial.state.code A strategy hwin basis)).initial)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenIndexedOptionalControlledSemanticInitial_toControlled
    (initial : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) :
    (profiledOpenIndexedOptionalControlledSemanticInitial A strategy hwin basis
      initial).toControlled A strategy hwin basis =
      profiledOpenIndexedControlledSemanticInitial A strategy hwin basis
        initial.state :=
  rfl

/-! ## Full finite hidden descriptor -/

/-- The old correlated move is the proof-side finite semantic identity. -/
noncomputable def profiledOpenIndexedOptionalControlledSemanticDescriptor
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenIndexedOldMoveHiddenDescriptor A initialCode :=
  ((point.1.state.code A strategy hwin basis, point.2),
    point.1.state.move A strategy hwin basis)

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenIndexedOptionalControlledSemanticDescriptor_code
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
      basis initialCode point).code =
      point.1.state.code A strategy hwin basis :=
  rfl

@[simp] theorem profiledOpenIndexedOptionalControlledSemanticDescriptor_control
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
      basis initialCode point).control = point.2 :=
  rfl

@[simp] theorem
    profiledOpenIndexedOptionalControlledSemanticDescriptor_moveIdentity
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
      basis initialCode point).moveIdentity =
      point.1.state.move A strategy hwin basis :=
  rfl

/-- The optional descriptor is definitionally the existing controlled
descriptor with old correlated move as its identity coordinate. -/
theorem profiledOpenIndexedOptionalControlledSemanticDescriptor_eq_controlled
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point =
      profiledOpenIndexedControlledSemanticDescriptor A strategy hwin basis
        initialCode
        (fun state => state.1.move A strategy hwin basis)
        (point.toControlled A strategy hwin basis) :=
  rfl

end

/-! ## Total finite-tag successor -/

/-- Follow the finite tag through its total raw representative, preserve
fresh provenance on whichever child lanes survive, and update the DPA on the
literal child code. -/
noncomputable def profiledOpenIndexedOptionalControlledSemanticNext
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
      initialCode :=
  let raw := profiledOpenIndexedRawDirectionOfFiniteTag A
    (point.1.state.code A strategy hwin basis)
    (point.1.state.move A strategy hwin basis) tag
  let child := profiledOpenIndexedOptionalFreshSemanticNext A strategy hwin
    basis point.1 raw
  (child,
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step point.2
      (child.state.code A strategy hwin basis))

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenIndexedOptionalControlledSemanticNext_state
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    (profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin basis
      initialCode point tag).1 =
      profiledOpenIndexedOptionalFreshSemanticNext A strategy hwin basis
        point.1
        (profiledOpenIndexedRawDirectionOfFiniteTag A
          (point.1.state.code A strategy hwin basis)
          (point.1.state.move A strategy hwin basis) tag) :=
  rfl

/-- Exact control update on the code of the same optional-fresh child. -/
@[simp] theorem profiledOpenIndexedOptionalControlledSemanticNext_control
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    (profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin basis
      initialCode point tag).2 =
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step point.2
        ((profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin
          basis initialCode point tag).1.state.code A strategy hwin basis) :=
  rfl

/-- Erasing fresh witnesses commutes exactly with the established controlled
finite-tag successor. -/
@[simp] theorem profiledOpenIndexedOptionalControlledSemanticNext_toControlled
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    (profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin basis
      initialCode point tag).toControlled A strategy hwin basis =
      profiledOpenIndexedControlledSemanticNext A strategy hwin basis
        initialCode (point.toControlled A strategy hwin basis) tag :=
  rfl

end

/-! ## Fold projection and branch parity -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Projection commutes with every finite-tag history fold. -/
theorem profiledOpenIndexedOptionalControlledSemantic_fold_toControlled
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (initialState : ProfiledOpenIndexedOptionalControlledSemanticState A
      strategy hwin basis initialCode)
    (node : TreeNode (ProfiledOpenIndexedFiniteDirectionTag A (I := I))) :
    ((node.foldl
      (profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin basis
        initialCode)
      initialState).toControlled A strategy hwin basis) =
      node.foldl
        (profiledOpenIndexedControlledSemanticNext A strategy hwin basis
          initialCode)
        (initialState.toControlled A strategy hwin basis) := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node tag ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [profiledOpenIndexedOptionalControlledSemanticNext_toControlled,
        ih]

/-- The optional descriptor-code word is exactly the existing controlled
semantic descriptor-code word. -/
theorem profiledOpenIndexedOptionalControlledSemantic_childCodeWord_eq
    (initial : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I))
    (branch : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    (fun n =>
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis (initial.state.code A strategy hwin basis)
        ((branchNode branch (n + 1)).foldl
          (profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin
            basis (initial.state.code A strategy hwin basis))
          (profiledOpenIndexedOptionalControlledSemanticInitial A strategy
            hwin basis initial))).code) =
      (fun n =>
        (profiledOpenIndexedControlledSemanticDescriptor A strategy hwin basis
          (initial.state.code A strategy hwin basis)
          (fun state => state.1.move A strategy hwin basis)
          ((branchNode branch (n + 1)).foldl
            (profiledOpenIndexedControlledSemanticNext A strategy hwin basis
              (initial.state.code A strategy hwin basis))
            (profiledOpenIndexedControlledSemanticInitial A strategy hwin
              basis initial.state))).code) := by
  funext n
  rw [profiledOpenIndexedOptionalControlledSemanticDescriptor_eq_controlled,
    profiledOpenIndexedOptionalControlledSemantic_fold_toControlled,
    profiledOpenIndexedOptionalControlledSemanticInitial_toControlled]

/-- Every branch of the total optional controlled semantics satisfies the
same code parity already proved for controlled correlated semantics. -/
theorem profiledOpenIndexedOptionalControlledSemanticBranch_accepts
    (initial : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I))
    (branch : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    (profiledOpenIndexedBiBeliefCodeParityDPA A
      (initial.state.code A strategy hwin basis)).Accepts (fun n =>
        (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
          hwin basis (initial.state.code A strategy hwin basis)
          ((branchNode branch (n + 1)).foldl
            (profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin
              basis (initial.state.code A strategy hwin basis))
            (profiledOpenIndexedOptionalControlledSemanticInitial A strategy
              hwin basis initial))).code) := by
  rw [profiledOpenIndexedOptionalControlledSemantic_childCodeWord_eq A
    strategy hwin basis initial branch]
  exact profiledOpenIndexedControlledSemanticBranch_accepts A strategy hwin
    basis initial.state (fun state => state.1.move A strategy hwin basis)
      branch

end

end

end DetParityAutomaton

end DistributedSynthesis
