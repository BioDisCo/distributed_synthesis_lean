/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Corollary.CorSummarywindowfiniteclosure
import DistributedSynthesis.Formalizations.Lemma.LemRefinementpreservessoundness
import DistributedSynthesis.Formalizations.Proposition.PropHandoffsuccessortests
import DistributedSynthesis.Formalizations.Proposition.PropSummarywindowcompatiblehandoff
import DistributedSynthesis.Formalizations.Proposition.PropSummarywindowreversal

/-!
# Concrete finite summary-window atoms and reversal handoff

This file replaces the deterministic-expansion carrier part of the abstract
`JournalAtomsReversalClosureCertificate` by actual data.  The paper's full
regular transduction can have several output paths; reducing that relation to
this deterministic map still requires simultaneous finite saturation.

For each orientation, the refined atom is the finite value consisting of the
path-semigroup summary and the two endpoint windows.  Equality of these finite
values implies equality of the corresponding raw `SummaryWindowValue`; hence
any synchronized atom determined by the raw window is refined by the finite
atom.

A direct-reversal path transformation gives explicit successor tests.  The
only semantic closure law required below is `SummaryWindowMapCompatible`: the
transformation sends equal old finite atoms to equal new finite atoms.  From
that law the successor tests are proved single-valued, and the existing
successor-test construction yields an actual handoff together with its
semantic invariant.  No unnamed `Prop` field is used in this deterministic
construction.
-/

namespace DistributedSynthesis

universe u v w x y z

/-- The concrete finite atom at endpoint-window radius `radius`. -/
abbrev SummaryWindowAtom
    {EdgeType : Proc -> Type u}
    (S : (d : Proc) -> PathSummarySemigroup.{u, v} (EdgeType d))
    (radius : Nat) (d : Proc) : Type (max u v) :=
  FiniteSummaryWindowValue (S d).Summary (EdgeType d) radius

namespace SummaryWindowAtom

variable {EdgeType : Proc -> Type u}
  (S : (d : Proc) -> PathSummarySemigroup.{u, v} (EdgeType d))
  (radius : Nat)

instance finite (d : Proc) [Fintype (EdgeType d)] :
    Fintype (SummaryWindowAtom S radius d) := by
  infer_instance

/-- Every finite window carrier has the atom of the empty path as a default. -/
instance inhabited (d : Proc) : Inhabited (SummaryWindowAtom S radius d) :=
  ⟨finiteSummaryWindowAbstraction (S d) radius []⟩

/-- The concrete refined atom of a typed path. -/
def ofPath (d : Proc) (path : TypedPath (EdgeType d)) :
    SummaryWindowAtom S radius d :=
  finiteSummaryWindowAbstraction (S d) radius path

/-- Equality of finite-carrier windows implies equality of the raw windows. -/
theorem raw_eq_of_eq {d : Proc} {old new : TypedPath (EdgeType d)}
    (h : ofPath S radius d old = ofPath S radius d new) :
    summaryWindowAbstraction (S d) radius old =
      summaryWindowAbstraction (S d) radius new := by
  have hsummary := congrArg (fun value => value.1) h
  have hpref := congrArg (fun value => value.2.1.toList) h
  have hsuff := congrArg (fun value => value.2.2.toList) h
  apply summaryWindowAbstraction_eq_components (S d) radius
  · simpa [ofPath, finiteSummaryWindowAbstraction] using hsummary
  · simpa [ofPath, finiteSummaryWindowAbstraction] using hpref
  · simpa [ofPath, finiteSummaryWindowAbstraction] using hsuff

/-- On values produced from paths, equality of the raw windows also implies
equality of their finite-carrier representatives. -/
theorem eq_of_raw_eq {d : Proc} {old new : TypedPath (EdgeType d)}
    (h : summaryWindowAbstraction (S d) radius old =
      summaryWindowAbstraction (S d) radius new) :
    ofPath S radius d old = ofPath S radius d new := by
  have hsummary := congrArg SummaryWindowValue.summary h
  have hpref := congrArg SummaryWindowValue.pref h
  have hsuff := congrArg SummaryWindowValue.suff h
  simp [summaryWindowAbstraction] at hsummary hpref hsuff
  have hprefFinite :
      boundedPrefixAtMost radius old = boundedPrefixAtMost radius new := by
    apply BoundedEndpointWindow.toList_injective
    simpa using hpref
  have hsuffFinite :
      boundedSuffixAtMost radius old = boundedSuffixAtMost radius new := by
    apply BoundedEndpointWindow.toList_injective
    simpa using hsuff
  exact Prod.ext hsummary (Prod.ext hprefFinite hsuffFinite)

/-- A raw summary-window-compatible atom is refined by the concrete finite
summary-window atom. -/
theorem refines
    {BaseAtom : Proc -> Type w}
    (baseAtomOf : (d : Proc) -> TypedPath (EdgeType d) -> BaseAtom d)
    (compatible : ∀ d, SummaryWindowCompatible (S d) radius (baseAtomOf d))
    (d : Proc) :
    AtomRefines (baseAtomOf d) (ofPath S radius d) := by
  intro old new heq
  exact compatible d old new (raw_eq_of_eq S radius heq)

/-- One-directional continuation soundness is inherited by the concrete
finite atom. -/
theorem sound
    {BaseAtom : Proc -> Type w} {Continuation : Proc -> Type x}
    (baseAtomOf : (d : Proc) -> TypedPath (EdgeType d) -> BaseAtom d)
    (continuationOf : (d : Proc) -> TypedPath (EdgeType d) -> Continuation d)
    (baseSound : ∀ d, OneDirectionalSound (baseAtomOf d) (continuationOf d))
    (compatible : ∀ d, SummaryWindowCompatible (S d) radius (baseAtomOf d))
    (d : Proc) :
    OneDirectionalSound (ofPath S radius d) (continuationOf d) :=
  refinement_preserves_one_directional_soundness
    (baseAtomOf d) (ofPath S radius d) (continuationOf d)
    (baseSound d) (refines S radius baseAtomOf compatible d)

end SummaryWindowAtom

section Reversal

variable {EdgeType : Proc -> Type u}
  (S : (d : Proc) -> PathSummarySemigroup.{u, v} (EdgeType d))
  (radius : Nat)

variable {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}

/-- A concrete direct-reversal transformation, allowed to depend on the
finite closing tuple. -/
abbrev SummaryWindowReversalMap :=
  (d : Proc) ->
    DirectReversalTuple (SummaryWindowAtom S radius) In₁ In₂ Out₁ Out₂ d ->
      TypedPath (EdgeType d) -> TypedPath (EdgeType d.other)

/-- The exact closure law needed for the finite handoff: equal old refined
atoms have equal transformed refined atoms. -/
def SummaryWindowMapCompatible
    (transform : SummaryWindowReversalMap S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ d tuple old new,
    SummaryWindowAtom.ofPath S radius d old =
        SummaryWindowAtom.ofPath S radius d new ->
      SummaryWindowAtom.ofPath S radius d.other (transform d tuple old) =
        SummaryWindowAtom.ofPath S radius d.other (transform d tuple new)

/-- The paper's bounded-pullback property supplies the concrete compatibility
law at every radius that is stable under one pullback. -/
theorem summaryWindowMapCompatible_of_pullbackBound
    (transform : SummaryWindowReversalMap S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hpullback : ∀ d tuple,
      SummaryWindowMapPullbackBound (S d) (S d.other) (transform d tuple))
    (hradius : endpointPullbackBound radius ≤ radius) :
    SummaryWindowMapCompatible S radius transform := by
  intro d tuple old new hold
  apply SummaryWindowAtom.eq_of_raw_eq S radius
  apply hpullback d tuple radius old new
  exact summaryWindowAbstraction_refines_of_le (S d) hradius
    (SummaryWindowAtom.raw_eq_of_eq S radius hold)

/-- In particular, the fixed closure radius `max c 2` is stable under every
one-step direct-reversal pullback. -/
theorem summaryWindowMapCompatible_atClosureRadius
    (c : Nat)
    (transform : SummaryWindowReversalMap S (max c 2)
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hpullback : ∀ d tuple,
      SummaryWindowMapPullbackBound (S d) (S d.other) (transform d tuple)) :
    SummaryWindowMapCompatible S (max c 2) transform :=
  summaryWindowMapCompatible_of_pullbackBound S (max c 2) transform hpullback
    (endpointPullbackBound_le_self_of_two_le (le_max_right c 2))

/-- A paper-shaped direct-reversal substitution: each old typed edge is
replaced by a three-edge block, with the block allowed to depend on the
finite closing tuple. -/
abbrev SummaryWindowExpansionBlock :=
  (d : Proc) ->
    DirectReversalTuple (SummaryWindowAtom S radius) In₁ In₂ Out₁ Out₂ d ->
      EdgeType d -> List (EdgeType d.other)

/-- The path map induced by a tuple-indexed edge substitution. -/
def summaryWindowExpansionTransform
    (block : SummaryWindowExpansionBlock S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    SummaryWindowReversalMap S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  fun d tuple => expandPath (block d tuple)

/-- The proved three-edge endpoint pullback plus a finite-semigroup update
prove compatibility of the concrete expansion at the closure radius. -/
theorem summaryWindowExpansionMapCompatible_atClosureRadius
    (c : Nat)
    (block : SummaryWindowExpansionBlock S (max c 2)
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hlen : ∀ d tuple edge, (block d tuple edge).length = 3)
    (hsummary : ∀ d tuple k old₁ old₂,
      summaryWindowAbstraction (S d) (endpointPullbackBound k) old₁ =
          summaryWindowAbstraction (S d) (endpointPullbackBound k) old₂ ->
        pathSummaryValue (S d.other)
            (expandPath (block d tuple) old₁) =
          pathSummaryValue (S d.other)
            (expandPath (block d tuple) old₂)) :
    SummaryWindowMapCompatible S (max c 2)
      (summaryWindowExpansionTransform S (max c 2) block) := by
  apply summaryWindowMapCompatible_atClosureRadius S c
  intro d tuple
  exact three_edge_expansion_summary_window_bound
    (S d) (S d.other) (block d tuple) (hlen d tuple) (hsummary d tuple)

/-- Explicit successor tests generated by the concrete reversal map.  A path
belongs to the test precisely when it has the tuple's old atom and its
transformed path has the proposed target atom. -/
def summaryWindowHandoffTests
    (transform : SummaryWindowReversalMap S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    HandoffTests EdgeType (SummaryWindowAtom S radius) In₁ In₂ Out₁ Out₂ where
  successorTest d tuple target :=
    { old |
      SummaryWindowAtom.ofPath S radius d old = tuple.atom ∧
        target = SummaryWindowAtom.ofPath S radius d.other (transform d tuple old) }

/-- Compatibility of the concrete map proves that its successor tests are
single-valued. -/
theorem summaryWindowHandoffTests_unique
    (transform : SummaryWindowReversalMap S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hmap : SummaryWindowMapCompatible S radius transform) :
    AtMostOneHandoffSuccessor (summaryWindowHandoffTests S radius transform) := by
  intro d tuple target₁ target₂ htarget₁ htarget₂
  rcases htarget₁ with ⟨old₁, hold₁, hvalue₁⟩
  rcases htarget₂ with ⟨old₂, hold₂, hvalue₂⟩
  calc
    target₁ = SummaryWindowAtom.ofPath S radius d.other
        (transform d tuple old₁) := hvalue₁
    _ = SummaryWindowAtom.ofPath S radius d.other
        (transform d tuple old₂) :=
      hmap d tuple old₁ old₂ (hold₁.trans hold₂.symm)
    _ = target₂ := hvalue₂.symm

/-- The actual canonical finite direct-reversal handoff. -/
noncomputable def summaryWindowDirectReversalHandoff
    (transform : SummaryWindowReversalMap S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    FiniteDirectReversalHandoff
      (SummaryWindowAtom S radius) In₁ In₂ Out₁ Out₂ :=
  finiteDirectReversalHandoffOf
    (summaryWindowHandoffTests S radius transform)
    (handoffMapFromUniqueSuccessors (summaryWindowHandoffTests S radius transform))

/-- The constructed handoff satisfies the semantic successor invariant. -/
theorem summaryWindowDirectReversalHandoff_invariant
    (transform : SummaryWindowReversalMap S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hmap : SummaryWindowMapCompatible S radius transform) :
    (summaryWindowDirectReversalHandoff S radius transform).invariant := by
  exact handoff_exclusion_check_implies_invariant
    (summaryWindowHandoffTests S radius transform)
    (handoffMapFromUniqueSuccessors (summaryWindowHandoffTests S radius transform))
    (unique_successors_give_exclusion_check
      (summaryWindowHandoffTests S radius transform)
      (summaryWindowHandoffTests_unique S radius transform hmap))

/-- The corresponding functional closing extension, with its functionality
property named by the concrete successor relation. -/
def summaryWindowDirectClosing
    (transform : SummaryWindowReversalMap S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    FunctionalDirectClosingExtension
      EdgeType (SummaryWindowAtom S radius) In₁ In₂ Out₁ Out₂ :=
  functionalDirectClosingFromSuccessors
    (summaryWindowHandoffTests S radius transform)

theorem summaryWindowDirectClosing_functional
    (transform : SummaryWindowReversalMap S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hmap : SummaryWindowMapCompatible S radius transform) :
    (summaryWindowDirectClosing S radius transform).functionalOnReachable :=
  summaryWindowHandoffTests_unique S radius transform hmap

/-- The canonical handoff obtained from a tuple-indexed deterministic
three-edge expansion.  This constructor has no propositional certificate
fields: the finite map is computed from the expansion tests. -/
noncomputable def summaryWindowExpansionHandoff
    (c : Nat)
    (block : SummaryWindowExpansionBlock S (max c 2)
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    FiniteDirectReversalHandoff
      (SummaryWindowAtom S (max c 2)) In₁ In₂ Out₁ Out₂ :=
  summaryWindowDirectReversalHandoff S (max c 2)
    (summaryWindowExpansionTransform S (max c 2) block)

/-- The three-edge expansion hypotheses prove the semantic invariant of the
canonical expansion handoff. -/
theorem summaryWindowExpansionHandoff_invariant
    (c : Nat)
    (block : SummaryWindowExpansionBlock S (max c 2)
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hlen : ∀ d tuple edge, (block d tuple edge).length = 3)
    (hsummary : ∀ d tuple k old₁ old₂,
      summaryWindowAbstraction (S d) (endpointPullbackBound k) old₁ =
          summaryWindowAbstraction (S d) (endpointPullbackBound k) old₂ ->
        pathSummaryValue (S d.other)
            (expandPath (block d tuple) old₁) =
          pathSummaryValue (S d.other)
            (expandPath (block d tuple) old₂)) :
    (summaryWindowExpansionHandoff S c block).invariant := by
  apply summaryWindowDirectReversalHandoff_invariant
  exact summaryWindowExpansionMapCompatible_atClosureRadius
    S c block hlen hsummary

/-- The matching functional closing relation for the expansion handoff. -/
def summaryWindowExpansionClosing
    (c : Nat)
    (block : SummaryWindowExpansionBlock S (max c 2)
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    FunctionalDirectClosingExtension
      EdgeType (SummaryWindowAtom S (max c 2)) In₁ In₂ Out₁ Out₂ :=
  summaryWindowDirectClosing S (max c 2)
    (summaryWindowExpansionTransform S (max c 2) block)

theorem summaryWindowExpansionClosing_functional
    (c : Nat)
    (block : SummaryWindowExpansionBlock S (max c 2)
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hlen : ∀ d tuple edge, (block d tuple edge).length = 3)
    (hsummary : ∀ d tuple k old₁ old₂,
      summaryWindowAbstraction (S d) (endpointPullbackBound k) old₁ =
          summaryWindowAbstraction (S d) (endpointPullbackBound k) old₂ ->
        pathSummaryValue (S d.other)
            (expandPath (block d tuple) old₁) =
          pathSummaryValue (S d.other)
            (expandPath (block d tuple) old₂)) :
    (summaryWindowExpansionClosing S c block).functionalOnReachable := by
  apply summaryWindowDirectClosing_functional
  exact summaryWindowExpansionMapCompatible_atClosureRadius
    S c block hlen hsummary

end Reversal

end DistributedSynthesis
