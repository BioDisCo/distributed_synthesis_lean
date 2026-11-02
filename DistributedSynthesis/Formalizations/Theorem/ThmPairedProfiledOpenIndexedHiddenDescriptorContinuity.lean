/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemHiddenDescriptorSemanticThreadLifting
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedCodeParity
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedFiniteDirectionSemantic

/-!
# Control-aware hidden continuity for the indexed profiled semantics

The hidden coordinate of the staged family construction is

```
((indexed belief code, code-parity DPA control), semantic identity).
```

The last component is deliberately abstract.  It may be the old
`ProfiledOpenIndexedBiBeliefMove` as a proof-side witness identity, but it is
**not** thereby identified with the runtime paired union-controller state.
The paired-bank adapter must prove that its concrete foreign-control readback
contains or realizes the stored semantic witness.

The only model-facing premise below is a current-state one-step lift.  An
edge advertised from the descriptor of the current semantic representative
must be its literal finite-tag successor descriptor.  The generic recursive
lifter then supplies one whole semantic branch, preventing a mosaic of
unrelated representatives at successive levels.
-/

namespace DistributedSynthesis

universe i u v x y s f m z

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

/-! ## Controlled correlated semantics -/

/-- The correlated semantic state paired with its literal path-dependent
code-DPA control. -/
abbrev ProfiledOpenIndexedControlledSemanticState
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis (I := I) ×
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State

/-- Initial control annotation. -/
def profiledOpenIndexedControlledSemanticInitial
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I)) :
    ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
      (initial.code A strategy hwin basis) :=
  (initial,
    (profiledOpenIndexedBiBeliefCodeParityDPA A
      (initial.code A strategy hwin basis)).initial)

/-- Literal finite-tag successor, including the DPA update on the child code. -/
noncomputable def profiledOpenIndexedControlledSemanticNext
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (state : ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
      initialCode)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
      initialCode :=
  let child := profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin
    basis state.1 tag
  (child,
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step state.2
      (child.code A strategy hwin basis))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The semantic projection of the simultaneous semantic/control fold is the
ordinary correlated semantic fold. -/
theorem profiledOpenIndexedControlledSemantic_fold_fst
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (initialState : ProfiledOpenIndexedControlledSemanticState A strategy hwin
      basis initialCode)
    (node : TreeNode (ProfiledOpenIndexedFiniteDirectionTag A (I := I))) :
    (node.foldl
      (profiledOpenIndexedControlledSemanticNext A strategy hwin basis
        initialCode)
      initialState).1 =
    node.foldl
      (profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin basis)
      initialState.1 := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node tag ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change
        profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin basis
            ((node.foldl
              (profiledOpenIndexedControlledSemanticNext A strategy hwin basis
                initialCode)
              initialState).1) tag =
          profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin basis
            (node.foldl
              (profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin basis)
              initialState.1) tag
      rw [ih]

/-! ## Abstract finite semantic identity -/

variable {MoveIdentity : Type z} [Fintype MoveIdentity]

/-- Full finite identity retained by the hidden continuity monitor. -/
abbrev ProfiledOpenIndexedHiddenDescriptor
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  HiddenCodeControlDescriptor
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    (MoveIdentity := MoveIdentity)

/-- Canonical finite public carrier: the two local-fibre images of full
hidden descriptors, with no distinguished actual member. -/
abbrev ProfiledOpenIndexedTwoFibreFamilyCode
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  FiniteTwoFibreCode
    (ProfiledOpenIndexedHiddenDescriptor A
      (MoveIdentity := MoveIdentity) initialCode)

/-- Read a full hidden descriptor from controlled semantics using an abstract
finite proof-side identity. -/
noncomputable def profiledOpenIndexedControlledSemanticDescriptor
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (semanticIdentity :
      ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
        initialCode → MoveIdentity)
    (state : ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
      initialCode) :
    ProfiledOpenIndexedHiddenDescriptor A
      (MoveIdentity := MoveIdentity) initialCode :=
  ((state.1.code A strategy hwin basis, state.2), semanticIdentity state)

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype MoveIdentity]

@[simp] theorem profiledOpenIndexedControlledSemanticDescriptor_code
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (semanticIdentity :
      ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
        initialCode → MoveIdentity)
    (state : ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
      initialCode) :
    (profiledOpenIndexedControlledSemanticDescriptor A strategy hwin basis
      initialCode semanticIdentity state).code =
        state.1.code A strategy hwin basis :=
  rfl

@[simp] theorem profiledOpenIndexedControlledSemanticDescriptor_control
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (semanticIdentity :
      ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
        initialCode → MoveIdentity)
    (state : ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
      initialCode) :
    (profiledOpenIndexedControlledSemanticDescriptor A strategy hwin basis
      initialCode semanticIdentity state).control = state.2 :=
  rfl

@[simp] theorem profiledOpenIndexedControlledSemanticDescriptor_moveIdentity
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (semanticIdentity :
      ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
        initialCode → MoveIdentity)
    (state : ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
      initialCode) :
    (profiledOpenIndexedControlledSemanticDescriptor A strategy hwin basis
      initialCode semanticIdentity state).moveIdentity =
        semanticIdentity state :=
  rfl

@[simp] theorem profiledOpenIndexedControlledSemanticInitial_control
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (semanticIdentity :
      ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
        (initial.code A strategy hwin basis) → MoveIdentity) :
    (profiledOpenIndexedControlledSemanticDescriptor A strategy hwin basis
      (initial.code A strategy hwin basis) semanticIdentity
      (profiledOpenIndexedControlledSemanticInitial A strategy hwin basis
        initial)).control =
      (profiledOpenIndexedBiBeliefCodeParityDPA A
        (initial.code A strategy hwin basis)).initial :=
  rfl

end

/-! ## Exact current-state lifting surface -/

variable {FamilyCode : Type f} {FamilyMove : Type m}

/-- Exact staged edge signature.  The public transition data is the fresh
family bank, Nature's finite tag, and the computed next family code. -/
abbrev ProfiledOpenIndexedExactHiddenDescriptorEdge
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  ProfiledOpenIndexedHiddenDescriptor A
      (MoveIdentity := MoveIdentity) initialCode →
    FamilyMove → ProfiledOpenIndexedFiniteDirectionTag A (I := I) →
      FamilyCode →
        ProfiledOpenIndexedHiddenDescriptor A
          (MoveIdentity := MoveIdentity) initialCode → Prop

/-- The smallest explicit anti-mosaic obligation.

`ExactEdge` owns the safety/readback assertion tying the public paired bank
to the current descriptor.  This field says only that, from the *current*
semantic representative, the advertised target is the literal child under
the advertised finite tag. -/
structure ProfiledOpenIndexedExactHiddenDescriptorLift
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (semanticIdentity :
      ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
        initialCode → MoveIdentity)
    (ExactEdge : ProfiledOpenIndexedExactHiddenDescriptorEdge A
      (I := I) (MoveIdentity := MoveIdentity) (FamilyCode := FamilyCode)
      (FamilyMove := FamilyMove) initialCode) : Prop where
  lifts : ∀
    (state : ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
      initialCode)
    (familyMove : FamilyMove)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (nextFamily : FamilyCode)
    (target : ProfiledOpenIndexedHiddenDescriptor A
      (MoveIdentity := MoveIdentity) initialCode),
    ExactEdge
        (profiledOpenIndexedControlledSemanticDescriptor A strategy hwin basis
          initialCode semanticIdentity state)
        familyMove tag nextFamily target →
      profiledOpenIndexedControlledSemanticDescriptor A strategy hwin basis
          initialCode semanticIdentity
          (profiledOpenIndexedControlledSemanticNext A strategy hwin basis
            initialCode state tag) =
        target

/-- Convert the explicit finite-tag lift to the reusable recursive lifter.
The proof-side selector returns the public tag literally. -/
noncomputable def ProfiledOpenIndexedExactHiddenDescriptorLift.toSemanticEdgeLifter
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (semanticIdentity :
      ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
        initialCode → MoveIdentity)
    (ExactEdge : ProfiledOpenIndexedExactHiddenDescriptorEdge A
      (I := I) (MoveIdentity := MoveIdentity) (FamilyCode := FamilyCode)
      (FamilyMove := FamilyMove) initialCode)
    (lift : ProfiledOpenIndexedExactHiddenDescriptorLift A strategy hwin basis
      initialCode semanticIdentity ExactEdge) :
    HiddenDescriptorSemanticEdgeLifter
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      (profiledOpenIndexedControlledSemanticNext A strategy hwin basis
        initialCode)
      (profiledOpenIndexedControlledSemanticDescriptor A strategy hwin basis
        initialCode semanticIdentity)
      ExactEdge where
  direction := fun _ _ publicData _ => publicData.1
  lifts := by
    intro state familyMove publicData target hedge
    exact lift.lifts state familyMove publicData.1 publicData.2 target hedge

/-! ## Existing semantic parity closes the hidden objective -/

omit [Fintype MoveIdentity] [Inhabited Out₁] [Inhabited Out₂] in
/-- The code projection of a controlled branch is the existing finite-tag
semantic child-code word. -/
theorem profiledOpenIndexedControlledSemantic_childCodeWord_eq
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (semanticIdentity :
      ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
        (initial.code A strategy hwin basis) → MoveIdentity)
    (branch : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    (fun n =>
      (profiledOpenIndexedControlledSemanticDescriptor A strategy hwin basis
        (initial.code A strategy hwin basis) semanticIdentity
        ((branchNode branch (n + 1)).foldl
          (profiledOpenIndexedControlledSemanticNext A strategy hwin basis
            (initial.code A strategy hwin basis))
          (profiledOpenIndexedControlledSemanticInitial A strategy hwin basis
            initial))).code) =
      (profiledOpenIndexedCorrelatedFiniteTagSemanticTree A strategy hwin
        basis initial).childCodeWord branch := by
  funext n
  change
    (((branchNode branch (n + 1)).foldl
      (profiledOpenIndexedControlledSemanticNext A strategy hwin basis
        (initial.code A strategy hwin basis))
      (profiledOpenIndexedControlledSemanticInitial A strategy hwin basis
        initial)).1.code A strategy hwin basis) =
    (((branchNode branch (n + 1)).foldl
      (profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin basis)
      initial).code A strategy hwin basis)
  rw [profiledOpenIndexedControlledSemantic_fold_fst A strategy hwin basis]
  rfl

omit [Fintype MoveIdentity] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every controlled semantic branch inherits the already proved finite-tag
code parity. -/
theorem profiledOpenIndexedControlledSemanticBranch_accepts
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (semanticIdentity :
      ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
        (initial.code A strategy hwin basis) → MoveIdentity)
    (branch : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    (profiledOpenIndexedBiBeliefCodeParityDPA A
      (initial.code A strategy hwin basis)).Accepts (fun n =>
        (profiledOpenIndexedControlledSemanticDescriptor A strategy hwin basis
          (initial.code A strategy hwin basis) semanticIdentity
          ((branchNode branch (n + 1)).foldl
            (profiledOpenIndexedControlledSemanticNext A strategy hwin basis
              (initial.code A strategy hwin basis))
            (profiledOpenIndexedControlledSemanticInitial A strategy hwin basis
              initial))).code) := by
  rw [profiledOpenIndexedControlledSemantic_childCodeWord_eq A strategy hwin
    basis initial semanticIdentity branch]
  simpa [profiledOpenIndexedBiBeliefCodeParityDPA] using
    profiledOpenIndexedCorrelatedFiniteTagSemanticTree_codeDPA_accepts A
      strategy hwin basis initial branch

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- End-to-end word acceptance for the concrete code/control semantics and
an abstract finite semantic-identity coordinate.  The sole model premise is
the exact current-state lift. -/
theorem profiledOpenIndexedHiddenDescriptorContinuity_accepts_of_exactLift
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (semanticIdentity :
      ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
        (initial.code A strategy hwin basis) → MoveIdentity)
    (ExactEdge : ProfiledOpenIndexedExactHiddenDescriptorEdge A
      (I := I) (MoveIdentity := MoveIdentity) (FamilyCode := FamilyCode)
      (FamilyMove := FamilyMove) (initial.code A strategy hwin basis))
    (lift : ProfiledOpenIndexedExactHiddenDescriptorLift A strategy hwin basis
      (initial.code A strategy hwin basis) semanticIdentity ExactEdge)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove)
      (Direction := ProfiledOpenIndexedFiniteDirectionTag A (I := I))
      (FamilyCode := FamilyCode))) :
    (hiddenDescriptorContinuitySystem
      (profiledOpenIndexedBiBeliefCodeParityDPA A
        (initial.code A strategy hwin basis))
      (profiledOpenIndexedControlledSemanticDescriptor A strategy hwin basis
        (initial.code A strategy hwin basis) semanticIdentity
        (profiledOpenIndexedControlledSemanticInitial A strategy hwin basis
          initial))
      ExactEdge).universalRunDPA.Accepts word := by
  apply hiddenDescriptorContinuitySystem_accepts_of_semanticEdgeLifter
    (profiledOpenIndexedBiBeliefCodeParityDPA A
      (initial.code A strategy hwin basis))
    (profiledOpenIndexedControlledSemanticNext A strategy hwin basis
      (initial.code A strategy hwin basis))
    (profiledOpenIndexedControlledSemanticDescriptor A strategy hwin basis
      (initial.code A strategy hwin basis) semanticIdentity)
    (profiledOpenIndexedControlledSemanticInitial A strategy hwin basis
      initial)
    (profiledOpenIndexedControlledSemanticInitial_control A strategy hwin
      basis initial semanticIdentity)
    ExactEdge
    (lift.toSemanticEdgeLifter A strategy hwin basis
      (initial.code A strategy hwin basis) semanticIdentity ExactEdge)
    word
  exact profiledOpenIndexedControlledSemanticBranch_accepts A strategy hwin
    basis initial semanticIdentity

/-! ## Final staged wrapper with a separately installed identity -/

/-- The final staging state keeps the installed finite identity as a literal
coordinate.  It need not be determined by the correlated semantic state. -/
abbrev ProfiledOpenIndexedStagedControlledSemanticState
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
      initialCode ×
    MoveIdentity

/-- Public transition data, in the actual staging order: fresh family bank,
Nature's finite tag, then the computed next family code. -/
abbrev ProfiledOpenIndexedStagedDirection :=
  HiddenDescriptorFamilyLetter
    (FamilyMove := FamilyMove)
    (Direction := ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (FamilyCode := FamilyCode)

/-- Read the full hidden descriptor from the final staged semantic state. -/
noncomputable def profiledOpenIndexedStagedSemanticDescriptor
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (state : ProfiledOpenIndexedStagedControlledSemanticState A strategy hwin
      basis (MoveIdentity := MoveIdentity) initialCode) :
    ProfiledOpenIndexedHiddenDescriptor A
      (MoveIdentity := MoveIdentity) initialCode :=
  ((state.1.1.code A strategy hwin basis, state.1.2), state.2)

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype MoveIdentity]

@[simp] theorem profiledOpenIndexedStagedSemanticDescriptor_code
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (state : ProfiledOpenIndexedStagedControlledSemanticState A strategy hwin
      basis (MoveIdentity := MoveIdentity) initialCode) :
    (profiledOpenIndexedStagedSemanticDescriptor A strategy hwin basis
      initialCode state).code = state.1.1.code A strategy hwin basis :=
  rfl

@[simp] theorem profiledOpenIndexedStagedSemanticDescriptor_control
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (state : ProfiledOpenIndexedStagedControlledSemanticState A strategy hwin
      basis (MoveIdentity := MoveIdentity) initialCode) :
    (profiledOpenIndexedStagedSemanticDescriptor A strategy hwin basis
      initialCode state).control = state.1.2 :=
  rfl

@[simp] theorem profiledOpenIndexedStagedSemanticDescriptor_moveIdentity
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (state : ProfiledOpenIndexedStagedControlledSemanticState A strategy hwin
      basis (MoveIdentity := MoveIdentity) initialCode) :
    (profiledOpenIndexedStagedSemanticDescriptor A strategy hwin basis
      initialCode state).moveIdentity = state.2 :=
  rfl

end

/-- Initial staged state with an explicit installed identity. -/
def profiledOpenIndexedStagedSemanticInitial
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (initialIdentity : MoveIdentity) :
    ProfiledOpenIndexedStagedControlledSemanticState A strategy hwin basis
      (MoveIdentity := MoveIdentity)
      (initial.code A strategy hwin basis) :=
  (profiledOpenIndexedControlledSemanticInitial A strategy hwin basis initial,
    initialIdentity)

/-- Install the next finite identity from the current staged representative
and the complete public transition.  In the final paired-bank adapter this is
the foreign-control readback/install operation. -/
abbrev ProfiledOpenIndexedIdentityInstall
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  ProfiledOpenIndexedStagedControlledSemanticState A strategy hwin basis
      (MoveIdentity := MoveIdentity) initialCode →
    FamilyMove → ProfiledOpenIndexedFiniteDirectionTag A (I := I) →
      FamilyCode → MoveIdentity

/-- Staged successor: parity semantics follows only the finite tag, while
the independent identity coordinate is installed from the public family
transition. -/
noncomputable def profiledOpenIndexedStagedSemanticNext
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (install : ProfiledOpenIndexedIdentityInstall A strategy hwin basis
      (MoveIdentity := MoveIdentity) (FamilyCode := FamilyCode)
      (FamilyMove := FamilyMove) initialCode)
    (state : ProfiledOpenIndexedStagedControlledSemanticState A strategy hwin
      basis (MoveIdentity := MoveIdentity) initialCode)
    (publicData : ProfiledOpenIndexedStagedDirection A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove)) :
    ProfiledOpenIndexedStagedControlledSemanticState A strategy hwin basis
      (MoveIdentity := MoveIdentity) initialCode :=
  (profiledOpenIndexedControlledSemanticNext A strategy hwin basis initialCode
      state.1 publicData.2.1,
    install state publicData.1 publicData.2.1 publicData.2.2)

/-- Forget family-bank and next-family data from a staged direction, retaining
the finite tag that drives the correlated parity semantics. -/
def profiledOpenIndexedStagedDirectionTag
    (publicData : ProfiledOpenIndexedStagedDirection A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove)) :
    ProfiledOpenIndexedFiniteDirectionTag A (I := I) :=
  publicData.2.1

omit [Fintype MoveIdentity] [Inhabited Out₁] [Inhabited Out₂] in
/-- The controlled-semantic projection of the staged fold depends only on
the finite-tag projection of its public transition word. -/
theorem profiledOpenIndexedStagedSemantic_fold_fst
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (install : ProfiledOpenIndexedIdentityInstall A strategy hwin basis
      (MoveIdentity := MoveIdentity) (FamilyCode := FamilyCode)
      (FamilyMove := FamilyMove) initialCode)
    (initialState : ProfiledOpenIndexedStagedControlledSemanticState A strategy
      hwin basis (MoveIdentity := MoveIdentity) initialCode)
    (node : TreeNode (ProfiledOpenIndexedStagedDirection A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove))) :
    (node.foldl
      (profiledOpenIndexedStagedSemanticNext A strategy hwin basis initialCode
        install)
      initialState).1 =
    (node.map (profiledOpenIndexedStagedDirectionTag A)).foldl
      (profiledOpenIndexedControlledSemanticNext A strategy hwin basis
        initialCode)
      initialState.1 := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node publicData ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.map_append, List.map_cons, List.map_nil]
      change
        profiledOpenIndexedControlledSemanticNext A strategy hwin basis
            initialCode
            ((node.foldl
              (profiledOpenIndexedStagedSemanticNext A strategy hwin basis
                initialCode install)
              initialState).1)
            (profiledOpenIndexedStagedDirectionTag A publicData) =
          profiledOpenIndexedControlledSemanticNext A strategy hwin basis
            initialCode
            ((node.map (profiledOpenIndexedStagedDirectionTag A)).foldl
              (profiledOpenIndexedControlledSemanticNext A strategy hwin basis
                initialCode)
              initialState.1)
            (profiledOpenIndexedStagedDirectionTag A publicData)
      rw [ih]

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Mapping the tag projection over a staged branch prefix gives the branch
prefix of the projected tag branch. -/
theorem profiledOpenIndexedStagedDirectionTag_map_branchNode
    (branch : Nat → ProfiledOpenIndexedStagedDirection A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove))
    (n : Nat) :
    (branchNode branch n).map (profiledOpenIndexedStagedDirectionTag A) =
      branchNode
        (fun k => profiledOpenIndexedStagedDirectionTag A (branch k)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        List.map_append, ih]
      rfl

/-- Exact current-state lift for the final staged state.  This is where the
concrete paired-bank install/readback equality belongs. -/
structure ProfiledOpenIndexedStagedExactHiddenDescriptorLift
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (install : ProfiledOpenIndexedIdentityInstall A strategy hwin basis
      (MoveIdentity := MoveIdentity) (FamilyCode := FamilyCode)
      (FamilyMove := FamilyMove) initialCode)
    (ExactEdge : ProfiledOpenIndexedExactHiddenDescriptorEdge A
      (I := I) (MoveIdentity := MoveIdentity) (FamilyCode := FamilyCode)
      (FamilyMove := FamilyMove) initialCode) : Prop where
  lifts : ∀
    (state : ProfiledOpenIndexedStagedControlledSemanticState A strategy hwin
      basis (MoveIdentity := MoveIdentity) initialCode)
    (familyMove : FamilyMove)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (nextFamily : FamilyCode)
    (target : ProfiledOpenIndexedHiddenDescriptor A
      (MoveIdentity := MoveIdentity) initialCode),
    ExactEdge
        (profiledOpenIndexedStagedSemanticDescriptor A strategy hwin basis
          initialCode state)
        familyMove tag nextFamily target →
      profiledOpenIndexedStagedSemanticDescriptor A strategy hwin basis
          initialCode
          (profiledOpenIndexedStagedSemanticNext A strategy hwin basis
            initialCode install state (familyMove, (tag, nextFamily))) =
        target

/-- The staged exact lift is the generic recursive semantic lifter, with the
proof-side direction equal to the complete public transition literally. -/
noncomputable def ProfiledOpenIndexedStagedExactHiddenDescriptorLift.toSemanticEdgeLifter
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (install : ProfiledOpenIndexedIdentityInstall A strategy hwin basis
      (MoveIdentity := MoveIdentity) (FamilyCode := FamilyCode)
      (FamilyMove := FamilyMove) initialCode)
    (ExactEdge : ProfiledOpenIndexedExactHiddenDescriptorEdge A
      (I := I) (MoveIdentity := MoveIdentity) (FamilyCode := FamilyCode)
      (FamilyMove := FamilyMove) initialCode)
    (lift : ProfiledOpenIndexedStagedExactHiddenDescriptorLift A strategy hwin
      basis initialCode install ExactEdge) :
    HiddenDescriptorSemanticEdgeLifter
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      (profiledOpenIndexedStagedSemanticNext A strategy hwin basis initialCode
        install)
      (profiledOpenIndexedStagedSemanticDescriptor A strategy hwin basis
        initialCode)
      ExactEdge where
  direction := fun _ familyMove publicData _ => (familyMove, publicData)
  lifts := by
    intro state familyMove publicData target hedge
    exact lift.lifts state familyMove publicData.1 publicData.2 target hedge

omit [Fintype MoveIdentity] [Inhabited Out₁] [Inhabited Out₂] in
/-- A staged branch projects to the existing finite-tag semantic child-code
word.  Identity installation is irrelevant to parity but remains continuous
in the full hidden descriptor. -/
theorem profiledOpenIndexedStagedSemantic_childCodeWord_eq
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (initialIdentity : MoveIdentity)
    (install : ProfiledOpenIndexedIdentityInstall A strategy hwin basis
      (MoveIdentity := MoveIdentity) (FamilyCode := FamilyCode)
      (FamilyMove := FamilyMove) (initial.code A strategy hwin basis))
    (branch : Nat → ProfiledOpenIndexedStagedDirection A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove)) :
    (fun n =>
      (profiledOpenIndexedStagedSemanticDescriptor A strategy hwin basis
        (initial.code A strategy hwin basis)
        ((branchNode branch (n + 1)).foldl
          (profiledOpenIndexedStagedSemanticNext A strategy hwin basis
            (initial.code A strategy hwin basis) install)
          (profiledOpenIndexedStagedSemanticInitial A strategy hwin basis
            initial initialIdentity))).code) =
      (profiledOpenIndexedCorrelatedFiniteTagSemanticTree A strategy hwin
        basis initial).childCodeWord
          (fun n => profiledOpenIndexedStagedDirectionTag A (branch n)) := by
  funext n
  change
    ((((branchNode branch (n + 1)).foldl
      (profiledOpenIndexedStagedSemanticNext A strategy hwin basis
        (initial.code A strategy hwin basis) install)
      (profiledOpenIndexedStagedSemanticInitial A strategy hwin basis initial
        initialIdentity)).1.1.code A strategy hwin basis)) =
    (((branchNode
      (fun n => profiledOpenIndexedStagedDirectionTag A (branch n))
      (n + 1)).foldl
        (profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin basis)
        initial).code A strategy hwin basis)
  rw [profiledOpenIndexedStagedSemantic_fold_fst A strategy hwin basis]
  rw [profiledOpenIndexedControlledSemantic_fold_fst A strategy hwin basis]
  rw [profiledOpenIndexedStagedDirectionTag_map_branchNode A]
  rfl

omit [Fintype MoveIdentity] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every final staged branch inherits finite-tag parity. -/
theorem profiledOpenIndexedStagedSemanticBranch_accepts
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (initialIdentity : MoveIdentity)
    (install : ProfiledOpenIndexedIdentityInstall A strategy hwin basis
      (MoveIdentity := MoveIdentity) (FamilyCode := FamilyCode)
      (FamilyMove := FamilyMove) (initial.code A strategy hwin basis))
    (branch : Nat → ProfiledOpenIndexedStagedDirection A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove)) :
    (profiledOpenIndexedBiBeliefCodeParityDPA A
      (initial.code A strategy hwin basis)).Accepts (fun n =>
        (profiledOpenIndexedStagedSemanticDescriptor A strategy hwin basis
          (initial.code A strategy hwin basis)
          ((branchNode branch (n + 1)).foldl
            (profiledOpenIndexedStagedSemanticNext A strategy hwin basis
              (initial.code A strategy hwin basis) install)
            (profiledOpenIndexedStagedSemanticInitial A strategy hwin basis
              initial initialIdentity))).code) := by
  rw [profiledOpenIndexedStagedSemantic_childCodeWord_eq A strategy hwin basis
    initial initialIdentity install branch]
  simpa [profiledOpenIndexedBiBeliefCodeParityDPA] using
    profiledOpenIndexedCorrelatedFiniteTagSemanticTree_codeDPA_accepts A
      strategy hwin basis initial
        (fun n => profiledOpenIndexedStagedDirectionTag A (branch n))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Final end-to-end hidden-objective theorem for staged family extraction.
No semantic identity is recomputed from a child history: it is installed by
the supplied finite public readback operation. -/
theorem profiledOpenIndexedStagedHiddenDescriptorContinuity_accepts_of_exactLift
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (initialIdentity : MoveIdentity)
    (install : ProfiledOpenIndexedIdentityInstall A strategy hwin basis
      (MoveIdentity := MoveIdentity) (FamilyCode := FamilyCode)
      (FamilyMove := FamilyMove) (initial.code A strategy hwin basis))
    (ExactEdge : ProfiledOpenIndexedExactHiddenDescriptorEdge A
      (I := I) (MoveIdentity := MoveIdentity) (FamilyCode := FamilyCode)
      (FamilyMove := FamilyMove) (initial.code A strategy hwin basis))
    (lift : ProfiledOpenIndexedStagedExactHiddenDescriptorLift A strategy hwin
      basis (initial.code A strategy hwin basis) install ExactEdge)
    (word : OmegaWord (ProfiledOpenIndexedStagedDirection A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove))) :
    (hiddenDescriptorContinuitySystem
      (profiledOpenIndexedBiBeliefCodeParityDPA A
        (initial.code A strategy hwin basis))
      (profiledOpenIndexedStagedSemanticDescriptor A strategy hwin basis
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedStagedSemanticInitial A strategy hwin basis
          initial initialIdentity))
      ExactEdge).universalRunDPA.Accepts word := by
  apply hiddenDescriptorContinuitySystem_accepts_of_semanticEdgeLifter
    (profiledOpenIndexedBiBeliefCodeParityDPA A
      (initial.code A strategy hwin basis))
    (profiledOpenIndexedStagedSemanticNext A strategy hwin basis
      (initial.code A strategy hwin basis) install)
    (profiledOpenIndexedStagedSemanticDescriptor A strategy hwin basis
      (initial.code A strategy hwin basis))
    (profiledOpenIndexedStagedSemanticInitial A strategy hwin basis initial
      initialIdentity)
    rfl
    ExactEdge
    (lift.toSemanticEdgeLifter A strategy hwin basis
      (initial.code A strategy hwin basis) install ExactEdge)
    word
  exact profiledOpenIndexedStagedSemanticBranch_accepts A strategy hwin basis
    initial initialIdentity install

/-! ## Optional old-move witness specialization -/

/-- The old indexed semantic move is a valid finite *witness identity*.
This definition does not identify it with the paired union controller used at
runtime. -/
noncomputable def profiledOpenIndexedOldMoveWitnessIdentity
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (state : ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
      initialCode) : ProfiledOpenIndexedBiBeliefMove A :=
  state.1.move A strategy hwin basis

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenIndexedOldMoveWitnessIdentity_eq
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (state : ProfiledOpenIndexedControlledSemanticState A strategy hwin basis
      initialCode) :
    profiledOpenIndexedOldMoveWitnessIdentity A strategy hwin basis
      initialCode state = state.1.move A strategy hwin basis :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
