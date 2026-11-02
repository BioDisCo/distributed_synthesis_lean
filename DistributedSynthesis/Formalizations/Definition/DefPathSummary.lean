/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import DistributedSynthesis.Basic

/-!
# Typed-path summaries and summary windows

This file formalizes the requested typed-path and summary-window definitions
from `real_model/paper.tex`.
-/

namespace DistributedSynthesis

universe u v w x

/-- Endpoint labels for path summaries use the disjoint union of the two output alphabets. -/
abbrev BoundaryLabel (Out₁ : Type u) (Out₂ : Type v) := PSum Out₁ Out₂

/-- A deterministic parity automaton over an arbitrary alphabet. -/
structure DetParityAutomaton (Alphabet : Type u) where
  State : Type v
  stateFinite : Fintype State
  initial : State
  step : State -> Alphabet -> State
  priority : State -> Nat

attribute [instance] DetParityAutomaton.stateFinite

/-- An oriented automaton edge type records endpoint owners together with the automaton state. -/
structure AutomatonEdgeType (State : Type u) where
  srcOwner : Proc
  tgtOwner : Proc
  ownersDistinct : srcOwner ≠ tgtOwner
  state : State

/-- A path constraint is represented by its semantic relation on endpoint labels. -/
structure PathConstraint (Out₁ : Type u) (Out₂ : Type v) where
  summary : Set (BoundaryLabel Out₁ Out₂ × BoundaryLabel Out₁ Out₂)

/-- The two-boundary summary of a path constraint. -/
def twoBoundarySummary
    {Out₁ : Type u} {Out₂ : Type v}
    (P : PathConstraint Out₁ Out₂) :
    Set (BoundaryLabel Out₁ Out₂ × BoundaryLabel Out₁ Out₂) :=
  P.summary

/-- The output-label type associated with a process-owned vertex. -/
abbrev OwnedLabel (Out₁ : Type u) (Out₂ : Type v) (p : Proc) :=
  { label : BoundaryLabel Out₁ Out₂ //
    match p, label with
    | Proc.one, PSum.inl _ => True
    | Proc.two, PSum.inr _ => True
    | _, _ => False }

noncomputable instance ownedLabelFintype
    {Out₁ : Type u} {Out₂ : Type v}
    [Fintype Out₁] [Fintype Out₂]
    (p : Proc) :
    Fintype (OwnedLabel Out₁ Out₂ p) := by
  classical
  cases p
  · exact
      Fintype.ofEquiv Out₁
        { toFun := fun a => ⟨PSum.inl a, trivial⟩
          invFun := fun label =>
            by
              cases label with
              | mk value ok =>
                  cases value with
                  | inl a => exact a
                  | inr b => cases ok
          left_inv := by
            intro a
            rfl
          right_inv := by
            intro label
            cases label with
            | mk value ok =>
                cases value with
                | inl a => rfl
                | inr b => cases ok }
  · exact
      Fintype.ofEquiv Out₂
        { toFun := fun b => ⟨PSum.inr b, trivial⟩
          invFun := fun label =>
            by
              cases label with
              | mk value ok =>
                  cases value with
                  | inl a => cases ok
                  | inr b => exact b
          left_inv := by
            intro b
            rfl
          right_inv := by
            intro label
            cases label with
            | mk value ok =>
                cases value with
                | inl a => cases ok
                | inr b => rfl }

/-- A finite rooted constraint tree, represented by its finite vertices and edge constraints. -/
structure RootedConstraintTree (Out₁ : Type u) (Out₂ : Type v) where
  Vertex : Type w
  vertexFinite : Fintype Vertex
  root : Vertex
  owner : Vertex -> Proc
  edge : Vertex -> Vertex -> Prop
  edgeRel :
    (a b : Vertex) ->
      edge a b ->
        OwnedLabel Out₁ Out₂ (owner a) ->
          OwnedLabel Out₁ Out₂ (owner b) ->
            Prop

attribute [instance] RootedConstraintTree.vertexFinite

/-- A labeling assigns to each vertex an output of the owning process. -/
abbrev RootedConstraintTree.Labeling
    {Out₁ : Type u} {Out₂ : Type v}
    (T : RootedConstraintTree Out₁ Out₂) :=
  (a : T.Vertex) -> OwnedLabel Out₁ Out₂ (T.owner a)

/-- A labeling satisfies all edge constraints of the rooted constraint tree. -/
def RootedConstraintTree.Satisfying
    {Out₁ : Type u} {Out₂ : Type v}
    (T : RootedConstraintTree Out₁ Out₂)
    (label : T.Labeling) :
    Prop :=
  ∀ a b h, T.edgeRel a b h (label a) (label b)

/-- Definition `def:boundarysummary`: labels at the root extendable to a satisfying labeling. -/
def boundarySummary
    {Out₁ : Type u} {Out₂ : Type v}
    (T : RootedConstraintTree Out₁ Out₂) :
    Set (OwnedLabel Out₁ Out₂ (T.owner T.root)) :=
  { o | ∃ label : T.Labeling, T.Satisfying label ∧ label T.root = o }

/-- A typed path is a finite list of edge types. -/
abbrev TypedPath (EdgeType : Type u) := List EdgeType

/-- A finite semigroup-style summary algebra for typed paths. -/
structure PathSummarySemigroup (EdgeType : Type u) where
  Summary : Type v
  summaryFinite : Fintype Summary
  empty : Summary
  ofEdge : EdgeType -> Summary
  multiply : Summary -> Summary -> Summary

attribute [instance] PathSummarySemigroup.summaryFinite

/-- The path-summary semigroup value of a typed path. -/
def pathSummaryValue
    {EdgeType : Type u}
    (S : PathSummarySemigroup EdgeType)
    (path : TypedPath EdgeType) :
    S.Summary :=
  path.foldl (fun acc edge => S.multiply acc (S.ofEdge edge)) S.empty

/-- Prefix of length at most `c`. -/
def prefixAtMost {α : Type u} (c : Nat) (path : List α) : List α :=
  path.take c

/-- Suffix of length at most `c`. -/
def suffixAtMost {α : Type u} (c : Nat) (path : List α) : List α :=
  path.drop (path.length - c)

/--
A finite representation of endpoint windows of length at most `c`.
The value stores its actual length `n ≤ c` and the labels at positions
`0, ..., n-1`.
-/
abbrev BoundedEndpointWindow (EdgeType : Type u) (c : Nat) :=
  Σ n : Fin (c + 1), Fin n.val -> EdgeType

/-- Convert a bounded endpoint-window value back to its list of entries. -/
def BoundedEndpointWindow.toList
    {EdgeType : Type u} {c : Nat}
    (window : BoundedEndpointWindow EdgeType c) :
    List EdgeType :=
  List.ofFn window.2

@[simp]
theorem BoundedEndpointWindow.length_toList
    {EdgeType : Type u} {c : Nat}
    (window : BoundedEndpointWindow EdgeType c) :
    window.toList.length = window.1.val := by
  simp [BoundedEndpointWindow.toList]

/-- The list representation remembers the complete bounded window. -/
theorem BoundedEndpointWindow.toList_injective
    {EdgeType : Type u} {c : Nat} :
    Function.Injective (@BoundedEndpointWindow.toList EdgeType c) := by
  intro left right h
  rcases left with ⟨⟨m, hm⟩, left⟩
  rcases right with ⟨⟨n, hn⟩, right⟩
  have hsigma : (⟨m, left⟩ : Σ k, Fin k → EdgeType) = ⟨n, right⟩ :=
    List.ofFn_inj'.mp h
  cases hsigma
  rfl

/-- Package a concrete list of length at most `c` as a finite endpoint-window value. -/
def boundedEndpointWindowOfList
    {EdgeType : Type u}
    (c : Nat)
    (window : List EdgeType)
    (h : window.length ≤ c) :
    BoundedEndpointWindow EdgeType c :=
  ⟨⟨window.length, Nat.lt_succ_of_le h⟩, fun i => window.get ⟨i.val, i.isLt⟩⟩

@[simp]
theorem boundedEndpointWindowOfList_toList
    {EdgeType : Type u}
    (c : Nat)
    (window : List EdgeType)
    (h : window.length ≤ c) :
    (boundedEndpointWindowOfList c window h).toList = window := by
  simp [BoundedEndpointWindow.toList, boundedEndpointWindowOfList]

/-- Bounded finite representation of the prefix window. -/
def boundedPrefixAtMost
    {EdgeType : Type u}
    (c : Nat)
    (path : List EdgeType) :
    BoundedEndpointWindow EdgeType c :=
  boundedEndpointWindowOfList c (prefixAtMost c path) (by
    simp [prefixAtMost])

/-- Bounded finite representation of the suffix window. -/
def boundedSuffixAtMost
    {EdgeType : Type u}
    (c : Nat)
    (path : List EdgeType) :
    BoundedEndpointWindow EdgeType c :=
  boundedEndpointWindowOfList c (suffixAtMost c path) (by
    unfold suffixAtMost
    rw [List.length_drop]
    omega)

@[simp]
theorem boundedPrefixAtMost_toList
    {EdgeType : Type u}
    (c : Nat)
    (path : List EdgeType) :
    (boundedPrefixAtMost c path).toList = prefixAtMost c path := by
  simp [boundedPrefixAtMost]

@[simp]
theorem boundedSuffixAtMost_toList
    {EdgeType : Type u}
    (c : Nat)
    (path : List EdgeType) :
    (boundedSuffixAtMost c path).toList = suffixAtMost c path := by
  simp [boundedSuffixAtMost]

/-- A summary-window value stores the semigroup value together with bounded endpoint windows. -/
structure SummaryWindowValue (Summary : Type u) (EdgeType : Type v) where
  summary : Summary
  pref : TypedPath EdgeType
  suff : TypedPath EdgeType

/--
Finite summary-window values use the same mathematical components as
`SummaryWindowValue`, but store endpoint windows in a finite bounded carrier.
-/
abbrev FiniteSummaryWindowValue (Summary : Type u) (EdgeType : Type v) (c : Nat) :=
  Summary × BoundedEndpointWindow EdgeType c × BoundedEndpointWindow EdgeType c

/-- The summary-window abstraction of a typed path. -/
def summaryWindowAbstraction
    {EdgeType : Type u}
    (S : PathSummarySemigroup EdgeType)
    (c : Nat)
    (path : TypedPath EdgeType) :
    SummaryWindowValue S.Summary EdgeType :=
  {
    summary := pathSummaryValue S path
    pref := prefixAtMost c path
    suff := suffixAtMost c path
  }

/-- The finite-carrier version of the summary-window abstraction. -/
def finiteSummaryWindowAbstraction
    {EdgeType : Type u}
    (S : PathSummarySemigroup EdgeType)
    (c : Nat)
    (path : TypedPath EdgeType) :
    FiniteSummaryWindowValue S.Summary EdgeType c :=
  (pathSummaryValue S path, boundedPrefixAtMost c path, boundedSuffixAtMost c path)

theorem finite_summary_window_values_finite
    (EdgeType : Type u)
    (Summary : Type v)
    [Fintype EdgeType] [Fintype Summary]
    (c : Nat) :
    Nonempty (Fintype (FiniteSummaryWindowValue Summary EdgeType c)) := by
  exact ⟨inferInstance⟩

/-- Summary-window compatibility means the summary-window value determines the synchronized atom. -/
def SummaryWindowCompatible
    {EdgeType : Type u} {Atom : Type v}
    (S : PathSummarySemigroup EdgeType)
    (c : Nat)
    (atomOf : TypedPath EdgeType -> Atom) : Prop :=
  ∀ u v,
    summaryWindowAbstraction S c u = summaryWindowAbstraction S c v ->
      atomOf u = atomOf v

/-- A finite family of deterministic monitors over typed paths. -/
structure DeterministicMonitorFamily (EdgeType : Type u) where
  index : Type v
  indexFinite : Fintype index
  state : index -> Type w
  stateFinite : (i : index) -> Fintype (state i)
  init : (i : index) -> state i
  step : (i : index) -> state i -> EdgeType -> state i

attribute [instance] DeterministicMonitorFamily.indexFinite

/-- Run one monitor from the family along a typed path. -/
def runMonitor
    {EdgeType : Type u}
    (family : DeterministicMonitorFamily EdgeType)
    (i : family.index)
    (path : TypedPath EdgeType) :
    family.state i :=
  path.foldl (family.step i) (family.init i)

/-- The atom-enriched summary-window value augments the raw window with terminal monitor states. -/
structure AtomEnrichedSummaryWindowValue
    (Summary : Type u)
    (EdgeType : Type v)
    (family : DeterministicMonitorFamily EdgeType) where
  raw : SummaryWindowValue Summary EdgeType
  terminal : (i : family.index) -> family.state i

/-- Finite-carrier atom-enriched summary-window values. -/
abbrev FiniteAtomEnrichedSummaryWindowValue
    (Summary : Type u)
    (EdgeType : Type v)
    (family : DeterministicMonitorFamily EdgeType)
    (c : Nat) :=
  FiniteSummaryWindowValue Summary EdgeType c ×
    ((i : family.index) -> family.state i)

/-- Definition `def:atomenrichedsummarywindow`. -/
def atomEnrichedSummaryWindowAbstraction
    {EdgeType : Type u}
    (S : PathSummarySemigroup EdgeType)
    (family : DeterministicMonitorFamily EdgeType)
    (c : Nat)
    (path : TypedPath EdgeType) :
    AtomEnrichedSummaryWindowValue S.Summary EdgeType family :=
  {
    raw := summaryWindowAbstraction S c path
    terminal := fun i => runMonitor family i path
  }

/-- The finite-carrier version of the atom-enriched summary-window abstraction. -/
def finiteAtomEnrichedSummaryWindowAbstraction
    {EdgeType : Type u}
    (S : PathSummarySemigroup EdgeType)
    (family : DeterministicMonitorFamily EdgeType)
    (c : Nat)
    (path : TypedPath EdgeType) :
    FiniteAtomEnrichedSummaryWindowValue S.Summary EdgeType family c :=
  (finiteSummaryWindowAbstraction S c path, fun i => runMonitor family i path)

theorem finite_atom_enriched_summary_window_values_finite
    (EdgeType : Type u)
    (Summary : Type v)
    [Fintype EdgeType] [Fintype Summary]
    (family : DeterministicMonitorFamily.{u, w, x} EdgeType)
    (c : Nat) :
    Nonempty (Fintype (FiniteAtomEnrichedSummaryWindowValue Summary EdgeType family c)) := by
  classical
  letI : Fintype family.index := family.indexFinite
  letI : (i : family.index) -> Fintype (family.state i) := family.stateFinite
  exact ⟨inferInstance⟩

@[simp]
theorem atomEnrichedSummaryWindowAbstraction_raw
    {EdgeType : Type u}
    (S : PathSummarySemigroup EdgeType)
    (family : DeterministicMonitorFamily EdgeType)
    (c : Nat)
    (path : TypedPath EdgeType) :
    (atomEnrichedSummaryWindowAbstraction S family c path).raw =
      summaryWindowAbstraction S c path := rfl

end DistributedSynthesis
