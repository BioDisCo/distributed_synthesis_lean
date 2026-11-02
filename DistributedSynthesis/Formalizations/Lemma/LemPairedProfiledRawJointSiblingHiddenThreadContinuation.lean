/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSiblingTreeTransitionAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedProvenancePolicy

/-!
# Proof-side continuation threads below a coupled sibling transition

The coupled sibling table exposes one finite target relation to both the
simultaneous and strict resolutions.  This file shows that every target in
that relation starts one *literal*, recursively exact one-sided semantic
unfolding.  The semantic root is retained only in the proof: its erasure is
the emitted finite incidence code.

The finite-code version of the unfolding has a finite branch alphabet.  Every
infinite finite-code branch expands recursively to one genuine raw semantic
branch, rather than choosing an unrelated representative at each depth.  Its
code word is therefore accepted by the already proved one-sided parity
theorem.  This is the anti-mosaic continuation needed after the local sibling
pair has been coupled.

Nothing in the construction gives a process the sibling bit, graph,
orientation, actual direction, semantic root, or strict-leader status.  The
only player-facing equality used here is the previously proved equality of
the two projected blind sender tables.

This result concerns the semantic tree and its finite-code rationalization.
It does not assert that independently installed semantic witnesses in a later
provenance policy are definitionally the children of the witnesses chosen at
the preceding policy state.  Such a post-rationalization claim requires the
separate source-aligned edge-lifting law; it must not be inferred merely from
existential representability.
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

/-! ## Exact proof-side roots below a sibling target -/

/-- One exact one-sided semantic root whose finite erasure is the target
emitted by a coupled sibling table.  The field `state` is proof-side data. -/
structure ProfiledRawJointSiblingContinuationRoot
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) where
  state : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)
  code_eq : state.code A = target

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Every target of the common right sibling relation has a recursively exact
literal continuation root.  The construction reads the target through the
strict-left member, whose subsequent right actual child is one-sided. -/
theorem nonempty_profiledRawJointRightSiblingContinuationRoot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : ProfiledRawJointRightSiblingSharedAllowedTarget A family
      direction target) :
    Nonempty (ProfiledRawJointSiblingContinuationRoot A strategy target) := by
  classical
  have hstrict : ProfiledRawJointRightSiblingAllowedTarget A family direction
      true target :=
    (profiledRawJointRightSiblingAllowedTarget_iff_shared A family direction
      true target).mpr htarget
  rcases hstrict with ⟨row, past, input, rfl⟩
  let root := profiledRawJointRightSiblingFamily A family direction true
  let actual := profiledRawJointUnitRightActualDirection
    (In₁ := In₁) (In₂ := In₂) row past input
  have hexact : root.ExactFibreAt A actual.direction := by
    exact family.leftActualChild_exactFibreAt A direction actual.direction
  let common := Classical.choice
    (root.exists_commonSourceAt A actual.direction hexact)
  let state : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
    { family := root.rightActualChild A actual.direction
      exactFibre := root.rightActualChild_exactFibreAt A actual.direction }
  refine ⟨⟨state, ?_⟩⟩
  change (root.rightActualChild A actual.direction).incidenceCode A = _
  rw [root.rightActualChild_incidenceCode_eq A actual.direction common]
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left mirror: every target of the common left sibling relation starts a
literal one-sided continuation. -/
theorem nonempty_profiledRawJointLeftSiblingContinuationRoot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : ProfiledRawJointLeftSiblingSharedAllowedTarget A family
      direction target) :
    Nonempty (ProfiledRawJointSiblingContinuationRoot A strategy target) := by
  classical
  have hstrict : ProfiledRawJointLeftSiblingAllowedTarget A family direction
      true target :=
    (profiledRawJointLeftSiblingAllowedTarget_iff_shared A family direction
      true target).mpr htarget
  rcases hstrict with ⟨row, past, input, rfl⟩
  let root := profiledRawJointLeftSiblingFamily A family direction true
  let actual := profiledRawJointUnitLeftActualDirection
    (In₁ := In₁) (In₂ := In₂) row past input
  have hexact : root.ExactFibreAt A actual.direction := by
    exact family.rightActualChild_exactFibreAt A direction actual.direction
  let common := Classical.choice
    (root.exists_commonSourceAt A actual.direction hexact)
  let state : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
    { family := root.leftActualChild A actual.direction
      exactFibre := root.leftActualChild_exactFibreAt A actual.direction }
  refine ⟨⟨state, ?_⟩⟩
  change (root.leftActualChild A actual.direction).incidenceCode A = _
  rw [root.leftActualChild_incidenceCode_eq A actual.direction common]
  rfl

/-- Canonical proof-side right continuation root. -/
noncomputable def profiledRawJointRightSiblingContinuationRoot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : ProfiledRawJointRightSiblingSharedAllowedTarget A family
      direction target) :
    ProfiledRawJointSiblingContinuationRoot A strategy target :=
  Classical.choice
    (nonempty_profiledRawJointRightSiblingContinuationRoot A family direction
      target htarget)

/-- Canonical proof-side left continuation root. -/
noncomputable def profiledRawJointLeftSiblingContinuationRoot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : ProfiledRawJointLeftSiblingSharedAllowedTarget A family
      direction target) :
    ProfiledRawJointSiblingContinuationRoot A strategy target :=
  Classical.choice
    (nonempty_profiledRawJointLeftSiblingContinuationRoot A family direction
      target htarget)

/-! ## Hidden-root erasure and recursive coherence -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The selected semantic root erases exactly to the public right target. -/
@[simp] theorem profiledRawJointRightSiblingContinuationRoot_code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : ProfiledRawJointRightSiblingSharedAllowedTarget A family
      direction target) :
    (profiledRawJointRightSiblingContinuationRoot A family direction target
      htarget).state.code A = target :=
  (profiledRawJointRightSiblingContinuationRoot A family direction target
    htarget).code_eq

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left erasure mirror. -/
@[simp] theorem profiledRawJointLeftSiblingContinuationRoot_code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : ProfiledRawJointLeftSiblingSharedAllowedTarget A family
      direction target) :
    (profiledRawJointLeftSiblingContinuationRoot A family direction target
      htarget).state.code A = target :=
  (profiledRawJointLeftSiblingContinuationRoot A family direction target
    htarget).code_eq

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Every consecutive node of the continuation tree is the literal semantic
child of the preceding node.  This is the recursive anti-mosaic invariant. -/
theorem profiledRawJointSiblingContinuation_stateAt_append
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {target : ProfiledRawJointIncidenceCode A (I := Unit)}
    (root : ProfiledRawJointSiblingContinuationRoot A strategy target)
    (node : TreeNode (ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)))
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    let raw := profiledRawJointOneSidedSemanticTree A root.state
    raw.stateAt (node ++ [actual]) =
      (raw.stateAt node).step A actual := by
  exact (profiledRawJointOneSidedSemanticTree A root.state).stateAt_append
    node actual

/-! ## Every finite-code branch is one genuine semantic branch -/

/-- The finite-branch semantic tree below a sibling target.  Its directions
are finite incidence codes; the actual raw directions are chosen only in the
proof-side semantic step. -/
noncomputable def profiledRawJointSiblingFiniteCodeSemanticTree
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {target : ProfiledRawJointIncidenceCode A (I := Unit)}
    (root : ProfiledRawJointSiblingContinuationRoot A strategy target) :=
  sourceFreeBeliefFiniteCodeSemanticTree
    (profiledRawJointOneSidedSemanticTree A root.state)
    (profiledRawJointOneSidedNext A)

/-- Actual proof-side direction branch selected recursively by one abstract
finite-code branch. -/
noncomputable def profiledRawJointSiblingRawBranch
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {target : ProfiledRawJointIncidenceCode A (I := Unit)}
    (root : ProfiledRawJointSiblingContinuationRoot A strategy target)
    (branch : Nat → ProfiledRawJointIncidenceCode A (I := Unit)) :=
  sourceFreeBeliefRawBranchOfFiniteCodeBranch
    (profiledRawJointOneSidedSemanticTree A root.state)
    (profiledRawJointOneSidedNext A) branch

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- At every depth, the abstract finite-code branch and its recursively
selected raw branch reach literally the same semantic state.  Thus the hidden
root cannot be reselected between two levels. -/
theorem profiledRawJointSiblingFiniteCodeBranch_stateAt
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {target : ProfiledRawJointIncidenceCode A (I := Unit)}
    (root : ProfiledRawJointSiblingContinuationRoot A strategy target)
    (branch : Nat → ProfiledRawJointIncidenceCode A (I := Unit))
    (n : Nat) :
    (profiledRawJointSiblingFiniteCodeSemanticTree A root).stateAt
        (branchNode branch n) =
      (profiledRawJointOneSidedSemanticTree A root.state).stateAt
        (branchNode (profiledRawJointSiblingRawBranch A root branch) n) := by
  exact sourceFreeBeliefFiniteCodeBranch_stateAt
    (profiledRawJointOneSidedSemanticTree A root.state)
    (profiledRawJointOneSidedNext A) branch n

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Consequently the complete child-code word of an abstract branch is the
child-code word of one literal raw semantic execution. -/
theorem profiledRawJointSiblingFiniteCodeBranch_childCodeWord
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {target : ProfiledRawJointIncidenceCode A (I := Unit)}
    (root : ProfiledRawJointSiblingContinuationRoot A strategy target)
    (branch : Nat → ProfiledRawJointIncidenceCode A (I := Unit)) :
    (profiledRawJointSiblingFiniteCodeSemanticTree A root).childCodeWord
        branch =
      (profiledRawJointOneSidedSemanticTree A root.state).childCodeWord
        (profiledRawJointSiblingRawBranch A root branch) := by
  exact sourceFreeBeliefFiniteCode_childCodeWord_eq_raw
    (profiledRawJointOneSidedSemanticTree A root.state)
    (profiledRawJointOneSidedNext A) branch

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every infinite abstract branch below a sibling target is accepted because
it is the erasure of one genuine semantic branch of the original winning
strategy. -/
theorem profiledRawJointSiblingFiniteCodeBranch_accepts
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {target : ProfiledRawJointIncidenceCode A (I := Unit)}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (root : ProfiledRawJointSiblingContinuationRoot A strategy target)
    (branch : Nat → ProfiledRawJointIncidenceCode A (I := Unit)) :
    (profiledRawJointOneSidedCodeParityDPA A (root.state.code A)).Accepts
      ((profiledRawJointSiblingFiniteCodeSemanticTree A root).childCodeWord
        branch) := by
  rw [profiledRawJointSiblingFiniteCodeBranch_childCodeWord A root branch]
  exact profiledRawJointOneSidedSemanticTree_accepts A strategy hwin
    root.state (profiledRawJointSiblingRawBranch A root branch)

/-! ## Unconditional finite policy below every sibling target -/

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- A right sibling target starts an unconditional finite one-sided policy.
The policy's public initial code is the emitted target; the chosen semantic
root is absent from its type and runtime state. -/
theorem nonempty_profiledRawJointRightSiblingTargetRationalPolicy
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : ProfiledRawJointRightSiblingSharedAllowedTarget A family
      direction target) :
    Nonempty (ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      target) := by
  let root := profiledRawJointRightSiblingContinuationRoot A family direction
    target htarget
  have hpolicy := nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A
    strategy hwin root.state
  rw [root.code_eq] at hpolicy
  exact hpolicy

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left target mirror. -/
theorem nonempty_profiledRawJointLeftSiblingTargetRationalPolicy
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : ProfiledRawJointLeftSiblingSharedAllowedTarget A family
      direction target) :
    Nonempty (ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      target) := by
  let root := profiledRawJointLeftSiblingContinuationRoot A family direction
    target htarget
  have hpolicy := nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A
    strategy hwin root.state
  rw [root.code_eq] at hpolicy
  exact hpolicy

/-! ## Finite child alphabets for the coupled table -/

/-- Finite right child alphabet of one coupled sibling table.  The hidden
member bit is absent: a child is only a finite target code plus the proof that
it belongs to the one shared relation. -/
abbrev ProfiledRawJointRightSiblingChildCode
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :=
  { target : ProfiledRawJointIncidenceCode A (I := Unit) //
    ProfiledRawJointRightSiblingSharedAllowedTarget A family direction target }

noncomputable instance profiledRawJointRightSiblingChildCodeFintype
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    Fintype (ProfiledRawJointRightSiblingChildCode A family direction) := by
  classical
  exact Fintype.ofFinite _

/-- Left child alphabet mirror. -/
abbrev ProfiledRawJointLeftSiblingChildCode
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :=
  { target : ProfiledRawJointIncidenceCode A (I := Unit) //
    ProfiledRawJointLeftSiblingSharedAllowedTarget A family direction target }

noncomputable instance profiledRawJointLeftSiblingChildCodeFintype
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    Fintype (ProfiledRawJointLeftSiblingChildCode A family direction) := by
  classical
  exact Fintype.ofFinite _

/-- Proof-side exact source recovered from a finite right child tag. -/
noncomputable def profiledRawJointRightSiblingChildSource
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (child : ProfiledRawJointRightSiblingChildCode A family direction) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  (profiledRawJointRightSiblingContinuationRoot A family direction child.1
    child.2).state

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointRightSiblingChildSource_code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (child : ProfiledRawJointRightSiblingChildCode A family direction) :
    (profiledRawJointRightSiblingChildSource A family direction child).code A =
      child.1 :=
  profiledRawJointRightSiblingContinuationRoot_code A family direction child.1
    child.2

/-- One fixed unconditional recurrent policy selected once for the right
child tag. -/
noncomputable def profiledRawJointRightSiblingChildPolicy
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (child : ProfiledRawJointRightSiblingChildCode A family direction) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy child.1 :=
  Classical.choice
    (nonempty_profiledRawJointRightSiblingTargetRationalPolicy A hwin family
      direction child.1 child.2)

/-- Left exact source. -/
noncomputable def profiledRawJointLeftSiblingChildSource
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (child : ProfiledRawJointLeftSiblingChildCode A family direction) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  (profiledRawJointLeftSiblingContinuationRoot A family direction child.1
    child.2).state

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointLeftSiblingChildSource_code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (child : ProfiledRawJointLeftSiblingChildCode A family direction) :
    (profiledRawJointLeftSiblingChildSource A family direction child).code A =
      child.1 :=
  profiledRawJointLeftSiblingContinuationRoot_code A family direction child.1
    child.2

/-- One fixed left-child recurrent policy. -/
noncomputable def profiledRawJointLeftSiblingChildPolicy
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (child : ProfiledRawJointLeftSiblingChildCode A family direction) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy child.1 :=
  Classical.choice
    (nonempty_profiledRawJointLeftSiblingTargetRationalPolicy A hwin family
      direction child.1 child.2)

/-! ## Direct handoff from the coupled physical table -/

/-- Every target actually emitted by either right sibling projection both
matches the physical close and starts a coherent semantic continuation plus
an unconditional finite recurrent policy. -/
theorem profiledRawJointRightSiblingMemberController_targetContinuation
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let targetState := profiledRawJointUnitRightTargetProjection A
    let monitor := profiledRawJointRightSiblingBlockMonitor A family direction
      semanticMember member
    let controller := profiledRawJointRightSiblingMemberController A hwin
      family direction semanticMember hmember member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    let target := (play n).2.1.target row
    erasePairedProfiledState A (targetState target) =
        pairedRightCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      Nonempty (ProfiledRawJointSiblingContinuationRoot A strategy target) ∧
      Nonempty (ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
        target) := by
  dsimp only
  obtain ⟨hclose, htarget⟩ :=
    profiledRawJointRightSiblingMemberController_targetSafe_shared A hwin
      family direction semanticMember hmember member env n row
  exact ⟨hclose,
    nonempty_profiledRawJointRightSiblingContinuationRoot A family direction
      _ htarget,
    nonempty_profiledRawJointRightSiblingTargetRationalPolicy A hwin family
      direction _ htarget⟩

/-- Left physical-table mirror. -/
theorem profiledRawJointLeftSiblingMemberController_targetContinuation
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let targetState := profiledRawJointUnitLeftTargetProjection A
    let monitor := profiledRawJointLeftSiblingBlockMonitor A family direction
      semanticMember member
    let controller := profiledRawJointLeftSiblingMemberController A hwin
      family direction semanticMember hmember member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    let target := (play n).2.1.target row
    erasePairedProfiledState A (targetState target) =
        pairedLeftCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      Nonempty (ProfiledRawJointSiblingContinuationRoot A strategy target) ∧
      Nonempty (ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
        target) := by
  dsimp only
  obtain ⟨hclose, htarget⟩ :=
    profiledRawJointLeftSiblingMemberController_targetSafe_shared A hwin
      family direction semanticMember hmember member env n row
  exact ⟨hclose,
    nonempty_profiledRawJointLeftSiblingContinuationRoot A family direction
      _ htarget,
    nonempty_profiledRawJointLeftSiblingTargetRationalPolicy A hwin family
      direction _ htarget⟩

/-! ## Exact post-rationalization alignment boundary -/

/-- A proof-side semantic source installed at one finite policy state.  Its
raw move is the selected policy move and its finite erasure is the policy
code.  This structure contains no runtime component. -/
structure ProfiledRawJointOneSidedPolicySemanticPoint
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (policyState : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode) where
  source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)
  realizes : ProfiledRawJointOneSidedProvenanceMoveRealizesAt A strategy
    initialCode policy policyState (source.move A)
  code_eq : source.code A = policyState.1

/-- The exact law needed to retain one semantic source through a rational
policy transition.  It asks that, when the current installed source takes a
literal actual direction, the policy move selected at the corresponding
successor state is the move of that literal child.

Existential source installation at the two states does not imply this law:
the successor could install another same-code source with a different move.
Thus this is precisely the post-rationalization anti-mosaic boundary. -/
def ProfiledRawJointOneSidedPolicySourceAligned
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode) : Prop :=
  ∀ {policyState}
      (point : ProfiledRawJointOneSidedPolicySemanticPoint A strategy
        initialCode policy policyState)
      (actual : ProfiledRawJointActualDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂)),
    let childCode := profiledRawJointOneSidedNext A policyState.1
      (point.source.move A) actual
    let childState := policy.successor policyState childCode
    ProfiledRawJointOneSidedProvenanceMoveRealizesAt A strategy initialCode
      policy childState ((point.source.step A actual).move A)

/-- Source alignment advances a proof-side point to the literal semantic
child while the finite policy state follows its public child code. -/
noncomputable def ProfiledRawJointOneSidedPolicySemanticPoint.step
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    (haligned : ProfiledRawJointOneSidedPolicySourceAligned A strategy
      initialCode policy)
    {policyState : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    (point : ProfiledRawJointOneSidedPolicySemanticPoint A strategy
      initialCode policy policyState)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    let childCode := profiledRawJointOneSidedNext A policyState.1
      (point.source.move A) actual
    ProfiledRawJointOneSidedPolicySemanticPoint A strategy initialCode policy
      (policy.successor policyState childCode) := by
  let childCode := profiledRawJointOneSidedNext A policyState.1
    (point.source.move A) actual
  let childState := policy.successor policyState childCode
  refine {
    source := point.source.step A actual
    realizes := haligned point actual
    code_eq := ?_ }
  have hsuccessor := point.realizes.successor_eq_raw A strategy initialCode
    policy policyState (point.source.move A) actual
  have hfirst : childState.1 = childCode := congrArg Prod.fst hsuccessor
  rw [ProfiledRawJointOneSidedSemanticState.step_code, point.code_eq]
  exact hfirst.symm

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every provenance policy supplies an initial semantic point.  This is the
proved source-installation fact; source alignment is not used here. -/
theorem nonempty_profiledRawJointOneSidedPolicyInitialSemanticPoint
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode) :
    Nonempty (ProfiledRawJointOneSidedPolicySemanticPoint A strategy
      initialCode policy (policy.run [])) := by
  rcases exists_profiledRawJointOneSidedProvenanceInitialInstalledMove A
      strategy initialCode policy with
    ⟨move, source, hrealizes, hcode, hmove⟩
  refine ⟨{ source := source, realizes := ?_, code_eq := hcode }⟩
  simpa only [hmove] using hrealizes

/-- Canonical initial proof-side point of a provenance policy. -/
noncomputable def profiledRawJointOneSidedPolicyInitialSemanticPoint
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode) :
    ProfiledRawJointOneSidedPolicySemanticPoint A strategy initialCode policy
      (policy.run []) :=
  Classical.choice
    (nonempty_profiledRawJointOneSidedPolicyInitialSemanticPoint A strategy
      initialCode policy)

/-! ## Conditional post-rationalization anti-mosaic thread -/

/-- Recursively follow the finite policy state and one literal semantic source
in lockstep.  The actual directions remain proof-tree data. -/
noncomputable def profiledRawJointOneSidedAlignedPointAt
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (haligned : ProfiledRawJointOneSidedPolicySourceAligned A strategy
      initialCode policy)
    (branch : Nat → ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (n : Nat) → Σ policyState,
      ProfiledRawJointOneSidedPolicySemanticPoint A strategy initialCode policy
        policyState
  | 0 => ⟨policy.run [],
      profiledRawJointOneSidedPolicyInitialSemanticPoint A strategy
        initialCode policy⟩
  | n + 1 =>
      let previous := profiledRawJointOneSidedAlignedPointAt policy haligned
        branch n
      let nextPoint := previous.2.step A haligned (branch n)
      ⟨_, nextPoint⟩

section
omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledRawJointOneSidedAlignedPointAt_zero
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (haligned : ProfiledRawJointOneSidedPolicySourceAligned A strategy
      initialCode policy)
    (branch : Nat → ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointOneSidedAlignedPointAt A policy haligned branch 0).2 =
      profiledRawJointOneSidedPolicyInitialSemanticPoint A strategy
        initialCode policy :=
  rfl

/-- The hidden semantic source at the next abstract depth is definitionally
the literal child of the current source. -/
theorem profiledRawJointOneSidedAlignedPointAt_source_succ
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (haligned : ProfiledRawJointOneSidedPolicySourceAligned A strategy
      initialCode policy)
    (branch : Nat → ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (n : Nat) :
    (profiledRawJointOneSidedAlignedPointAt A policy haligned branch
        (n + 1)).2.source =
      (profiledRawJointOneSidedAlignedPointAt A policy haligned branch
        n).2.source.step A (branch n) :=
  rfl

/-- The aligned hidden source is exactly the ordinary semantic state reached
along the one actual direction branch from the single initial source. -/
theorem profiledRawJointOneSidedAlignedPointAt_source_eq_stateAt
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (haligned : ProfiledRawJointOneSidedPolicySourceAligned A strategy
      initialCode policy)
    (branch : Nat → ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (n : Nat) :
    (profiledRawJointOneSidedAlignedPointAt A policy haligned branch n).2.source =
      (profiledRawJointOneSidedSemanticTree A
        (profiledRawJointOneSidedPolicyInitialSemanticPoint A strategy
          initialCode policy).source).stateAt (branchNode branch n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [profiledRawJointOneSidedAlignedPointAt_source_succ A policy haligned
        branch n, ih]
      symm
      exact (profiledRawJointOneSidedSemanticTree A
        (profiledRawJointOneSidedPolicyInitialSemanticPoint A strategy
          initialCode policy).source).stateAt_append (branchNode branch n)
            (branch n)

/-- Under the single named alignment law, every infinite rational-policy
trajectory has the parity of one genuine semantic execution. -/
theorem profiledRawJointOneSidedAlignedPolicyBranch_accepts
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (haligned : ProfiledRawJointOneSidedPolicySourceAligned A strategy
      initialCode policy)
    (branch : Nat → ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    let initial :=
      (profiledRawJointOneSidedPolicyInitialSemanticPoint A strategy
        initialCode policy).source
    (profiledRawJointOneSidedCodeParityDPA A (initial.code A)).Accepts
      (fun n =>
        (profiledRawJointOneSidedAlignedPointAt A policy haligned branch
          (n + 1)).2.source.code A) := by
  let initial :=
    (profiledRawJointOneSidedPolicyInitialSemanticPoint A strategy
      initialCode policy).source
  have haccepts := profiledRawJointOneSidedSemanticTree_accepts A strategy hwin
    initial branch
  convert haccepts using 1
  funext n
  exact congrArg (ProfiledRawJointOneSidedSemanticState.code A)
    (profiledRawJointOneSidedAlignedPointAt_source_eq_stateAt A policy haligned
      branch (n + 1))

end

end

end DetParityAutomaton

end DistributedSynthesis
