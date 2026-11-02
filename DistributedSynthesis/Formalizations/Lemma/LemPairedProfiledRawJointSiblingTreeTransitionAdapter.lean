/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSemanticSiblingFamilyNarrowing
import DistributedSynthesis.Formalizations.Lemma.LemObservableThreadTreeRationalization

/-!
# Tree-transition adapter for a narrowed semantic sibling family

The simultaneous child and its strict sibling must not choose two block
controllers after the hidden graph choice.  The preceding sibling-family
construction already chooses one controller before that choice and proves
that its blind sender table is shared.

This file records the second fact needed by an input-free or alternating
consumer: the two proof-side members also have the same finite one-sided
target relation.  A right actual successor reads only the right lane, which
is literally shared by the simultaneous/strict-left pair; the left statement
is symmetric.  Hence the member bit may be a hidden resolution of one tree
transition.  It is not an observation, graph, orientation, or leader signal.

The final predicates name the next, genuinely recursive obligation.  A raw
history-tree construction must retain a semantic representative of every
target selected from the shared finite relation.  The local family narrowing
does not assert this global provenance/hidden-thread fact.
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

/-! ## One finite target relation for both right sibling members -/

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- The right one-sided finite successor is independent of the hidden sibling
member.  This is definitional after exposing the Boolean: both roots have the
same complete right semantic lane, and a right actual successor discards the
old left lane. -/
theorem profiledRawJointRightSibling_oneSidedNext_eq_false
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (member : Bool) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    profiledRawJointOneSidedNext A
        ((profiledRawJointRightSiblingFamily A family direction member
          ).incidenceCode A)
        ((profiledRawJointRightSiblingFamily A family direction member).move A)
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input) =
      profiledRawJointOneSidedNext A
        ((profiledRawJointRightSiblingFamily A family direction false
          ).incidenceCode A)
        ((profiledRawJointRightSiblingFamily A family direction false).move A)
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input) := by
  cases member <;> rfl

/-- The target predicate consumed by a tree transition has no hidden member
parameter: use the simultaneous member's relation as the common relation. -/
abbrev ProfiledRawJointRightSiblingSharedAllowedTarget
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :=
  ProfiledRawJointRightSiblingAllowedTarget A family direction false

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Both hidden right sibling resolutions have exactly the common finite
target relation. -/
theorem profiledRawJointRightSiblingAllowedTarget_iff_shared
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (member : Bool) (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    ProfiledRawJointRightSiblingAllowedTarget A family direction member target
      ↔ ProfiledRawJointRightSiblingSharedAllowedTarget A family direction
        target := by
  constructor
  · rintro ⟨row, past, input, rfl⟩
    exact ⟨row, past, input,
      profiledRawJointRightSibling_oneSidedNext_eq_false A family direction
        member row past input⟩
  · rintro ⟨row, past, input, rfl⟩
    exact ⟨row, past, input,
      (profiledRawJointRightSibling_oneSidedNext_eq_false A family direction
        member row past input).symm⟩

/-- Readback of either projected controller lands in the one shared target
relation.  Together with
`profiledRawJointRightSiblingMemberController_sender_eq`, this is the exact
one-transition adapter required by a hidden-resolution tree automaton. -/
theorem profiledRawJointRightSiblingMemberController_targetSafe_shared
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
    erasePairedProfiledState A (targetState ((play n).2.1.target row)) =
        pairedRightCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      ProfiledRawJointRightSiblingSharedAllowedTarget A family direction
        ((play n).2.1.target row) := by
  dsimp only
  obtain ⟨hclose, htarget⟩ :=
    profiledRawJointRightSiblingMemberController_targetSafe A hwin family
      direction semanticMember hmember member env n row
  exact ⟨hclose,
    (profiledRawJointRightSiblingAllowedTarget_iff_shared A family direction
      member _).mp htarget⟩

/-! ## Left mirror -/

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
theorem profiledRawJointLeftSibling_oneSidedNext_eq_false
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (member : Bool) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    profiledRawJointOneSidedNext A
        ((profiledRawJointLeftSiblingFamily A family direction member
          ).incidenceCode A)
        ((profiledRawJointLeftSiblingFamily A family direction member).move A)
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input) =
      profiledRawJointOneSidedNext A
        ((profiledRawJointLeftSiblingFamily A family direction false
          ).incidenceCode A)
        ((profiledRawJointLeftSiblingFamily A family direction false).move A)
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input) := by
  cases member <;> rfl

abbrev ProfiledRawJointLeftSiblingSharedAllowedTarget
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :=
  ProfiledRawJointLeftSiblingAllowedTarget A family direction false

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
theorem profiledRawJointLeftSiblingAllowedTarget_iff_shared
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (member : Bool) (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    ProfiledRawJointLeftSiblingAllowedTarget A family direction member target
      ↔ ProfiledRawJointLeftSiblingSharedAllowedTarget A family direction
        target := by
  constructor
  · rintro ⟨row, past, input, rfl⟩
    exact ⟨row, past, input,
      profiledRawJointLeftSibling_oneSidedNext_eq_false A family direction
        member row past input⟩
  · rintro ⟨row, past, input, rfl⟩
    exact ⟨row, past, input,
      (profiledRawJointLeftSibling_oneSidedNext_eq_false A family direction
        member row past input).symm⟩

theorem profiledRawJointLeftSiblingMemberController_targetSafe_shared
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
    erasePairedProfiledState A (targetState ((play n).2.1.target row)) =
        pairedLeftCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      ProfiledRawJointLeftSiblingSharedAllowedTarget A family direction
        ((play n).2.1.target row) := by
  dsimp only
  obtain ⟨hclose, htarget⟩ :=
    profiledRawJointLeftSiblingMemberController_targetSafe A hwin family
      direction semanticMember hmember member env n row
  exact ⟨hclose,
    (profiledRawJointLeftSiblingAllowedTarget_iff_shared A family direction
      member _).mp htarget⟩

/-! ## Exact recursive boundary -/

/-- Direct input-free recursion additionally needs every shared right target
to be the finite code of a semantic child from which the next coupled move can
be constructed.  This is intentionally separate from the proved local table
law. -/
def ProfiledRawJointRightSiblingTargetsRepresentable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) : Prop :=
  ∀ target, ProfiledRawJointRightSiblingSharedAllowedTarget A family direction
      target →
    ∃ child : ProfiledRawJointSemanticFamily A strategy (I := Unit),
      child.incidenceCode A = target

/-- Left-target representability needed by the alternating step. -/
def ProfiledRawJointLeftSiblingTargetsRepresentable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) : Prop :=
  ∀ target, ProfiledRawJointLeftSiblingSharedAllowedTarget A family direction
      target →
    ∃ child : ProfiledRawJointSemanticFamily A strategy (I := Unit),
      child.incidenceCode A = target

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- The common target relation is recursively representable without an extra
hypothesis.  Read the same target through the strict member (`true`): that
member is already one-sided, hence exact at every following direction. -/
theorem profiledRawJointRightSiblingTargetsRepresentable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointRightSiblingTargetsRepresentable A family direction := by
  intro target htarget
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
  refine ⟨root.rightActualChild A actual.direction, ?_⟩
  rw [root.rightActualChild_incidenceCode_eq A actual.direction common]
  rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Left mirror: use the strict-right one-sided member as the exact semantic
source of every target in the shared relation. -/
theorem profiledRawJointLeftSiblingTargetsRepresentable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointLeftSiblingTargetsRepresentable A family direction := by
  intro target htarget
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
  refine ⟨root.leftActualChild A actual.direction, ?_⟩
  rw [root.leftActualChild_incidenceCode_eq A actual.direction common]
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
