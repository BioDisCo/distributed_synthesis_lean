/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridSiblingCoupledRationalization
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenRepresentablePolicy

/-!
# The representable recursive boundary of the raw-joint sibling family

The pre-policy common/strict sibling construction supplies a fixed-strategy
semantic family before any finite outer move is selected.  This file exposes
that family as a `SemanticallyRepresentable` open class and then applies the
productive representable automaton to all of its recursive successors.

Consequently, once the standard arbitrary-direction input-free rational-run
basis is supplied, the initial family and recursive successor closure are not
open model obligations: every reached family has one valid finite move and
every direction lands in another represented family (or the even sink).

The final theorem deliberately retains exactly one hypothesis,
`ProfiledOpenRepresentableGlobalParity`.  It cannot be removed merely from
the existential `SemanticallyRepresentable` interface: the canonical total
move selector may choose a different semantic realizer when the same finite
view class is reached again.  Proving parity therefore requires a coherent
root/provenance construction, not another local table or a leader signal.

All Boolean indices below are proof-side members of the already coupled
sibling family.  They are absent from the blind sender and from runtime local
states; no graph, orientation, or strict-leader information is introduced.
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
  (basis : ∀ state : PairedProfiledTreeState A,
    (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

/-! ## Initial right sibling source -/

/-- The canonical open class of the common/strict-left process-one sibling
family, constructed before outer rationalization. -/
noncomputable def profiledRawJointHybridInitialRightRepresentableSource
    (first current : In₁ × In₂) : ProfiledOpenRightViewClass A :=
  profiledOpenRightSemanticSourceClass A strategy hwin
    (profiledRawJointHybridInitialRightSiblingEntry A strategy first current)
    (profiledRawJointHybridInitialRightSiblingMinimum A strategy first current)
    false
    (profiledRawJointHybridInitialRightSibling_view_eq A strategy first
      current)
    basis

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The initial right sibling class is represented by the original winning
strategy, with no compatibility premise added after policy selection. -/
theorem profiledRawJointHybridInitialRightRepresentableSource_semantic
    (first current : In₁ × In₂) :
    (profiledRawJointHybridInitialRightRepresentableSource A strategy hwin
      basis first current).SemanticallyRepresentable A := by
  exact profiledOpenRightSemanticSourceClass_representable A strategy hwin
    (profiledRawJointHybridInitialRightSiblingEntry A strategy first current)
    (profiledRawJointHybridInitialRightSiblingMinimum A strategy first current)
    false
    (profiledRawJointHybridInitialRightSibling_view_eq A strategy first
      current)
    basis

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Its finite anchor family is a productive initial family of the
representable outer automaton. -/
theorem profiledRawJointHybridInitialRightRepresentableFamily
    (first current : In₁ × In₂) :
    ProfiledOpenRepresentableFamily A
      (profiledOpenRightClassifiedRoots A
        (profiledRawJointHybridInitialRightRepresentableSource A strategy hwin
          basis first current)) := by
  apply Or.inr
  apply Or.inl
  exact ⟨profiledRawJointHybridInitialRightRepresentableSource A strategy
      hwin basis first current,
    profiledRawJointHybridInitialRightRepresentableSource_semantic A strategy
      hwin basis first current,
    rfl⟩

/-! ## Initial left sibling source -/

/-- Process-two/common-strict-right mirror. -/
noncomputable def profiledRawJointHybridInitialLeftRepresentableSource
    (first current : In₁ × In₂) : ProfiledOpenLeftViewClass A :=
  profiledOpenLeftSemanticSourceClass A strategy hwin
    (profiledRawJointHybridInitialLeftSiblingEntry A strategy first current)
    (profiledRawJointHybridInitialLeftSiblingMinimum A strategy first current)
    false
    (profiledRawJointHybridInitialLeftSibling_view_eq A strategy first current)
    basis

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointHybridInitialLeftRepresentableSource_semantic
    (first current : In₁ × In₂) :
    (profiledRawJointHybridInitialLeftRepresentableSource A strategy hwin
      basis first current).SemanticallyRepresentable A := by
  exact profiledOpenLeftSemanticSourceClass_representable A strategy hwin
    (profiledRawJointHybridInitialLeftSiblingEntry A strategy first current)
    (profiledRawJointHybridInitialLeftSiblingMinimum A strategy first current)
    false
    (profiledRawJointHybridInitialLeftSibling_view_eq A strategy first current)
    basis

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointHybridInitialLeftRepresentableFamily
    (first current : In₁ × In₂) :
    ProfiledOpenRepresentableFamily A
      (profiledOpenLeftClassifiedRoots A
        (profiledRawJointHybridInitialLeftRepresentableSource A strategy hwin
          basis first current)) := by
  apply Or.inr
  apply Or.inr
  exact ⟨profiledRawJointHybridInitialLeftRepresentableSource A strategy
      hwin basis first current,
    profiledRawJointHybridInitialLeftRepresentableSource_semantic A strategy
      hwin basis first current,
    rfl⟩

/-! ## Recursive closure, with no new mathematics -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every node of the canonical right-started unfolding remains productive.
In particular, all successor classes advertised by the narrowed tables retain
a semantic representative. -/
theorem profiledRawJointHybridInitialRightRepresentable_recursive
    (first current : In₁ × In₂) :
    ∀ node,
      match TwoSortedFamilyPolicy.deterministicRun
          (profiledOpenRightClassifiedRoots A
            (profiledRawJointHybridInitialRightRepresentableSource A strategy
              hwin basis first current))
          (profiledOpenRepresentableSuccessorFor A) node with
      | .family roots => ProfiledOpenRepresentableFamily A roots
      | .chosen _ roots => ProfiledOpenRepresentableFamily A roots := by
  exact profiledOpenRepresentableDeterministicRun_productive A
    (profiledOpenRightClassifiedRoots A
      (profiledRawJointHybridInitialRightRepresentableSource A strategy hwin
        basis first current))
    (profiledRawJointHybridInitialRightRepresentableFamily A strategy hwin
      basis first current)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-started recursive closure. -/
theorem profiledRawJointHybridInitialLeftRepresentable_recursive
    (first current : In₁ × In₂) :
    ∀ node,
      match TwoSortedFamilyPolicy.deterministicRun
          (profiledOpenLeftClassifiedRoots A
            (profiledRawJointHybridInitialLeftRepresentableSource A strategy
              hwin basis first current))
          (profiledOpenRepresentableSuccessorFor A) node with
      | .family roots => ProfiledOpenRepresentableFamily A roots
      | .chosen _ roots => ProfiledOpenRepresentableFamily A roots := by
  exact profiledOpenRepresentableDeterministicRun_productive A
    (profiledOpenLeftClassifiedRoots A
      (profiledRawJointHybridInitialLeftRepresentableSource A strategy hwin
        basis first current))
    (profiledRawJointHybridInitialLeftRepresentableFamily A strategy hwin
      basis first current)

/-! ## Exact remaining boundary: global coherent-root parity -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Once coherent-root parity and the standard arbitrary-direction
input-free rational-run basis are supplied, the right sibling source has a
finite rational representable policy. -/
theorem nonempty_profiledRawJointHybridInitialRightRepresentablePolicy_of_globalParity
    (first current : In₁ × In₂)
    (hparity : ProfiledOpenRepresentableGlobalParity A
      (profiledOpenRightClassifiedRoots A
        (profiledRawJointHybridInitialRightRepresentableSource A strategy hwin
          basis first current)))
    (outerBasis : InputFreeRunParityTreeAutomaton.RationalRunBasis
      (profiledOpenRepresentableFamilyRunAutomaton A
        (profiledOpenRightClassifiedRoots A
          (profiledRawJointHybridInitialRightRepresentableSource A strategy
            hwin basis first current)))) :
    Nonempty (InputFreeRunParityTreeAutomaton.RationalTransitionPolicy
      (profiledOpenRepresentableFamilyRunAutomaton A
        (profiledOpenRightClassifiedRoots A
          (profiledRawJointHybridInitialRightRepresentableSource A strategy
            hwin basis first current)))) := by
  exact nonempty_profiledOpenRepresentableRationalPolicy_of_globalParity A
    (profiledOpenRightClassifiedRoots A
      (profiledRawJointHybridInitialRightRepresentableSource A strategy hwin
        basis first current))
    (profiledRawJointHybridInitialRightRepresentableFamily A strategy hwin
      basis first current)
    hparity
    outerBasis

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror. -/
theorem nonempty_profiledRawJointHybridInitialLeftRepresentablePolicy_of_globalParity
    (first current : In₁ × In₂)
    (hparity : ProfiledOpenRepresentableGlobalParity A
      (profiledOpenLeftClassifiedRoots A
        (profiledRawJointHybridInitialLeftRepresentableSource A strategy hwin
          basis first current)))
    (outerBasis : InputFreeRunParityTreeAutomaton.RationalRunBasis
      (profiledOpenRepresentableFamilyRunAutomaton A
        (profiledOpenLeftClassifiedRoots A
          (profiledRawJointHybridInitialLeftRepresentableSource A strategy
            hwin basis first current)))) :
    Nonempty (InputFreeRunParityTreeAutomaton.RationalTransitionPolicy
      (profiledOpenRepresentableFamilyRunAutomaton A
        (profiledOpenLeftClassifiedRoots A
          (profiledRawJointHybridInitialLeftRepresentableSource A strategy
            hwin basis first current)))) := by
  exact nonempty_profiledOpenRepresentableRationalPolicy_of_globalParity A
    (profiledOpenLeftClassifiedRoots A
      (profiledRawJointHybridInitialLeftRepresentableSource A strategy hwin
        basis first current))
    (profiledRawJointHybridInitialLeftRepresentableFamily A strategy hwin
      basis first current)
    hparity
    outerBasis

end

end DetParityAutomaton

end DistributedSynthesis
