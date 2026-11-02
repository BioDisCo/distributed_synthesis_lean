/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemConcreteSummaryWindowClosure

/-!
# Relational direct-reversal substitution and simultaneous saturation

The paper's concrete direct-reversal substitution is a finite regular
relation: one old typed path may produce several output paths.  This file
proves the relation-to-function theorem that the deterministic layer of
`LemConcreteSummaryWindowClosure` was waiting for.

The single semantic law is **simultaneous saturation**
(`SummaryWindowRelSaturated`): all outputs of all inputs of one refined
old atom land in one refined successor atom.  From it:

* the canonical selection (one output per input, by choice) is a
  deterministic reversal map satisfying `SummaryWindowMapCompatible`
  (`summaryWindowRelSelection_compatible`), so the entire deterministic
  layer applies to it;
* every relational output is covered by the selection's successor atom
  (`summaryWindowRelSelection_covers`) -- the outputs land in one atom,
  not merely the selected one;
* the relational successor tests are single-valued
  (`summaryWindowRelHandoffTests_unique`), yield the canonical handoff
  with its semantic invariant and the functional closing extension, and
  agree exactly with the deterministic tests of the selection
  (`summaryWindowRelHandoffTests_eq_selection`).

Saturation itself follows from the relational bounded-pullback property
at every radius stable under one pullback
(`summaryWindowRelSaturated_of_pullbackBound`), in particular at the
fixed closure radius `max c 2`.  Discharging that pullback bound for the
paper's concrete transduction is the remaining model-specific input.
-/

namespace DistributedSynthesis

universe u v w x y z

/-- The relational bounded-pullback property: any two outputs of any two
inputs with equal summary windows at the pulled-back radius have equal
summary windows at the requested radius.  The relational analogue of
`SummaryWindowMapPullbackBound`. -/
def SummaryWindowRelPullbackBound
    {OldEdge : Type u} {NewEdge : Type v}
    (Sold : PathSummarySemigroup.{u, w} OldEdge)
    (Snew : PathSummarySemigroup.{v, w} NewEdge)
    (rel : TypedPath OldEdge -> Set (TypedPath NewEdge)) : Prop :=
  ∀ (k : Nat) (old₁ old₂ : TypedPath OldEdge)
    (out₁ out₂ : TypedPath NewEdge),
    out₁ ∈ rel old₁ -> out₂ ∈ rel old₂ ->
      summaryWindowAbstraction Sold (endpointPullbackBound k) old₁ =
        summaryWindowAbstraction Sold (endpointPullbackBound k) old₂ ->
      summaryWindowAbstraction Snew k out₁ =
        summaryWindowAbstraction Snew k out₂

section RelationalReversal

variable {EdgeType : Proc -> Type u}
  (S : (d : Proc) -> PathSummarySemigroup.{u, v} (EdgeType d))
  (radius : Nat)

variable {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}

/-- A concrete direct-reversal substitution as a relation, allowed to
depend on the finite closing tuple. -/
abbrev SummaryWindowReversalRel :=
  (d : Proc) ->
    DirectReversalTuple (SummaryWindowAtom S radius) In₁ In₂ Out₁ Out₂ d ->
      TypedPath (EdgeType d) -> Set (TypedPath (EdgeType d.other))

/-- **Simultaneous saturation**: all outputs of all inputs of one refined
old atom have one refined successor atom. -/
def SummaryWindowRelSaturated
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ d tuple old new outOld outNew,
    SummaryWindowAtom.ofPath S radius d old =
        SummaryWindowAtom.ofPath S radius d new ->
      outOld ∈ rel d tuple old -> outNew ∈ rel d tuple new ->
        SummaryWindowAtom.ofPath S radius d.other outOld =
          SummaryWindowAtom.ofPath S radius d.other outNew

/-- Totality: the substitution offers at least one output path. -/
def SummaryWindowRelTotal
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ d tuple old, (rel d tuple old).Nonempty

/-- The relational pullback bound yields simultaneous saturation at every
radius stable under one pullback. -/
theorem summaryWindowRelSaturated_of_pullbackBound
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hpullback : ∀ d tuple,
      SummaryWindowRelPullbackBound (S d) (S d.other) (rel d tuple))
    (hradius : endpointPullbackBound radius ≤ radius) :
    SummaryWindowRelSaturated S radius rel := by
  intro d tuple old new outOld outNew hatom hmemOld hmemNew
  apply SummaryWindowAtom.eq_of_raw_eq S radius
  apply hpullback d tuple radius old new outOld outNew hmemOld hmemNew
  exact summaryWindowAbstraction_refines_of_le (S d) hradius
    (SummaryWindowAtom.raw_eq_of_eq S radius hatom)

/-- In particular at the fixed closure radius `max c 2`. -/
theorem summaryWindowRelSaturated_atClosureRadius
    (c : Nat)
    (rel : SummaryWindowReversalRel S (max c 2)
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hpullback : ∀ d tuple,
      SummaryWindowRelPullbackBound (S d) (S d.other) (rel d tuple)) :
    SummaryWindowRelSaturated S (max c 2) rel :=
  summaryWindowRelSaturated_of_pullbackBound S (max c 2) rel hpullback
    (endpointPullbackBound_le_self_of_two_le (le_max_right c 2))

/-- The canonical selection of a total relation: one output per input. -/
noncomputable def summaryWindowRelSelection
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (htotal : SummaryWindowRelTotal S radius rel) :
    SummaryWindowReversalMap S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  fun d tuple old => (htotal d tuple old).choose

theorem summaryWindowRelSelection_mem
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (htotal : SummaryWindowRelTotal S radius rel)
    (d : Proc)
    (tuple : DirectReversalTuple (SummaryWindowAtom S radius)
      In₁ In₂ Out₁ Out₂ d)
    (old : TypedPath (EdgeType d)) :
    summaryWindowRelSelection S radius rel htotal d tuple old ∈
      rel d tuple old :=
  (htotal d tuple old).choose_spec

/-- **The relation-to-function theorem**: the canonical selection of a
simultaneously saturated total relation is a summary-window-compatible
deterministic reversal map, so the entire deterministic handoff layer
applies to it. -/
theorem summaryWindowRelSelection_compatible
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hsat : SummaryWindowRelSaturated S radius rel)
    (htotal : SummaryWindowRelTotal S radius rel) :
    SummaryWindowMapCompatible S radius
      (summaryWindowRelSelection S radius rel htotal) := by
  intro d tuple old new hatom
  exact hsat d tuple old new _ _ hatom
    (summaryWindowRelSelection_mem S radius rel htotal d tuple old)
    (summaryWindowRelSelection_mem S radius rel htotal d tuple new)

/-- **Coverage**: every relational output lands in the selection's refined
successor atom -- the outputs occupy one atom, not merely the selected
representative. -/
theorem summaryWindowRelSelection_covers
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hsat : SummaryWindowRelSaturated S radius rel)
    (htotal : SummaryWindowRelTotal S radius rel)
    {d : Proc}
    {tuple : DirectReversalTuple (SummaryWindowAtom S radius)
      In₁ In₂ Out₁ Out₂ d}
    {old : TypedPath (EdgeType d)} {out : TypedPath (EdgeType d.other)}
    (hmem : out ∈ rel d tuple old) :
    SummaryWindowAtom.ofPath S radius d.other out =
      SummaryWindowAtom.ofPath S radius d.other
        (summaryWindowRelSelection S radius rel htotal d tuple old) :=
  hsat d tuple old old _ _ rfl hmem
    (summaryWindowRelSelection_mem S radius rel htotal d tuple old)

/-- The relational successor tests: a path passes precisely when it has
the tuple's old atom and some relational output has the proposed target
atom. -/
def summaryWindowRelHandoffTests
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    HandoffTests EdgeType (SummaryWindowAtom S radius) In₁ In₂ Out₁ Out₂ where
  successorTest d tuple target :=
    { old |
      SummaryWindowAtom.ofPath S radius d old = tuple.atom ∧
        ∃ out ∈ rel d tuple old,
          target = SummaryWindowAtom.ofPath S radius d.other out }

/-- Simultaneous saturation makes the relational successor tests
single-valued. -/
theorem summaryWindowRelHandoffTests_unique
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hsat : SummaryWindowRelSaturated S radius rel) :
    AtMostOneHandoffSuccessor (summaryWindowRelHandoffTests S radius rel) := by
  intro d tuple target₁ target₂ htarget₁ htarget₂
  rcases htarget₁ with ⟨old₁, hatom₁, out₁, hmem₁, hvalue₁⟩
  rcases htarget₂ with ⟨old₂, hatom₂, out₂, hmem₂, hvalue₂⟩
  calc
    target₁ = SummaryWindowAtom.ofPath S radius d.other out₁ := hvalue₁
    _ = SummaryWindowAtom.ofPath S radius d.other out₂ :=
      hsat d tuple old₁ old₂ out₁ out₂ (hatom₁.trans hatom₂.symm) hmem₁ hmem₂
    _ = target₂ := hvalue₂.symm

/-- Under saturation and totality the relational successor tests agree
exactly with the deterministic tests of the canonical selection. -/
theorem summaryWindowRelHandoffTests_eq_selection
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hsat : SummaryWindowRelSaturated S radius rel)
    (htotal : SummaryWindowRelTotal S radius rel) :
    summaryWindowRelHandoffTests S radius rel =
      summaryWindowHandoffTests S radius
        (summaryWindowRelSelection S radius rel htotal) := by
  unfold summaryWindowRelHandoffTests summaryWindowHandoffTests
  congr 1
  funext d tuple target
  ext old
  constructor
  · rintro ⟨hatom, out, hmem, hvalue⟩
    exact ⟨hatom,
      hvalue.trans
        (summaryWindowRelSelection_covers S radius rel hsat htotal hmem)⟩
  · rintro ⟨hatom, hvalue⟩
    exact ⟨hatom,
      summaryWindowRelSelection S radius rel htotal d tuple old,
      summaryWindowRelSelection_mem S radius rel htotal d tuple old, hvalue⟩

/-- The canonical finite direct-reversal handoff of a relational
substitution. -/
noncomputable def summaryWindowRelHandoff
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    FiniteDirectReversalHandoff
      (SummaryWindowAtom S radius) In₁ In₂ Out₁ Out₂ :=
  finiteDirectReversalHandoffOf
    (summaryWindowRelHandoffTests S radius rel)
    (handoffMapFromUniqueSuccessors (summaryWindowRelHandoffTests S radius rel))

/-- The relational handoff satisfies the semantic successor invariant. -/
theorem summaryWindowRelHandoff_invariant
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hsat : SummaryWindowRelSaturated S radius rel) :
    (summaryWindowRelHandoff S radius rel).invariant :=
  handoff_exclusion_check_implies_invariant
    (summaryWindowRelHandoffTests S radius rel)
    (handoffMapFromUniqueSuccessors (summaryWindowRelHandoffTests S radius rel))
    (unique_successors_give_exclusion_check
      (summaryWindowRelHandoffTests S radius rel)
      (summaryWindowRelHandoffTests_unique S radius rel hsat))

/-- The functional closing extension of a relational substitution. -/
def summaryWindowRelClosing
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    FunctionalDirectClosingExtension
      EdgeType (SummaryWindowAtom S radius) In₁ In₂ Out₁ Out₂ :=
  functionalDirectClosingFromSuccessors
    (summaryWindowRelHandoffTests S radius rel)

theorem summaryWindowRelClosing_functional
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hsat : SummaryWindowRelSaturated S radius rel) :
    (summaryWindowRelClosing S radius rel).functionalOnReachable :=
  summaryWindowRelHandoffTests_unique S radius rel hsat

/-! ### Set-level simultaneous saturation

For the paper's concrete scheme (`automatonSubstitutionTriple`) the
pointwise cross-choice law is **false**: the free internal output labels
enter the letters stepping the objective automaton, so different choices
produce different output windows.  The correct simultaneous-saturation
law is set-level: the *set* of output windows is determined by the input
window.  Window-region choices can be mirrored between window-equal
inputs, and the interior coupling through the threaded boundary label is
absorbed by the path summary.  The set law subsumes the pointwise one:
when the image is a subsingleton it collapses to
`SummaryWindowRelSaturated`. -/

/-- The relational set-level bounded-pullback property: inputs with equal
summary windows at the pulled-back radius have equal *images* of output
summary windows at the requested radius. -/
def SummaryWindowRelSetPullbackBound
    {OldEdge : Type u} {NewEdge : Type v}
    (Sold : PathSummarySemigroup.{u, w} OldEdge)
    (Snew : PathSummarySemigroup.{v, w} NewEdge)
    (rel : TypedPath OldEdge -> Set (TypedPath NewEdge)) : Prop :=
  ∀ (k : Nat) (old₁ old₂ : TypedPath OldEdge),
    summaryWindowAbstraction Sold (endpointPullbackBound k) old₁ =
        summaryWindowAbstraction Sold (endpointPullbackBound k) old₂ ->
      (summaryWindowAbstraction Snew k) '' rel old₁ =
        (summaryWindowAbstraction Snew k) '' rel old₂

/-- The single-radius form of the relational set pullback bound: only the
closure radius is ever consumed downstream. -/
def SummaryWindowRelSetPullbackBoundAt (k : Nat)
    {OldEdge : Type u} {NewEdge : Type v}
    (Sold : PathSummarySemigroup.{u, w} OldEdge)
    (Snew : PathSummarySemigroup.{v, w} NewEdge)
    (rel : TypedPath OldEdge -> Set (TypedPath NewEdge)) : Prop :=
  ∀ (old₁ old₂ : TypedPath OldEdge),
    summaryWindowAbstraction Sold (endpointPullbackBound k) old₁ =
        summaryWindowAbstraction Sold (endpointPullbackBound k) old₂ ->
      (summaryWindowAbstraction Snew k) '' rel old₁ =
        (summaryWindowAbstraction Snew k) '' rel old₂

theorem SummaryWindowRelSetPullbackBound.at {k : Nat}
    {OldEdge : Type u} {NewEdge : Type v}
    {Sold : PathSummarySemigroup.{u, w} OldEdge}
    {Snew : PathSummarySemigroup.{v, w} NewEdge}
    {rel : TypedPath OldEdge -> Set (TypedPath NewEdge)}
    (h : SummaryWindowRelSetPullbackBound Sold Snew rel) :
    SummaryWindowRelSetPullbackBoundAt k Sold Snew rel :=
  h k

section SetSaturation

variable {EdgeType : Proc -> Type u}
  (S : (d : Proc) -> PathSummarySemigroup.{u, v} (EdgeType d))
  (radius : Nat)

variable {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}

/-- The saturated successor-atom image of one input path: the set of
refined atoms of its relational outputs. -/
def summaryWindowRelAtomImage
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (d : Proc)
    (tuple : DirectReversalTuple (SummaryWindowAtom S radius)
      In₁ In₂ Out₁ Out₂ d)
    (old : TypedPath (EdgeType d)) :
    Set (SummaryWindowAtom S radius d.other) :=
  SummaryWindowAtom.ofPath S radius d.other '' rel d tuple old

/-- Coverage is definitional: every relational output's refined atom lies
in the saturated image. -/
theorem mem_summaryWindowRelAtomImage
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    {d : Proc}
    {tuple : DirectReversalTuple (SummaryWindowAtom S radius)
      In₁ In₂ Out₁ Out₂ d}
    {old : TypedPath (EdgeType d)} {out : TypedPath (EdgeType d.other)}
    (hmem : out ∈ rel d tuple old) :
    SummaryWindowAtom.ofPath S radius d.other out ∈
      summaryWindowRelAtomImage S radius rel d tuple old :=
  Set.mem_image_of_mem _ hmem

/-- Raw-window images determine finite-atom images: the finite refined
atom and the raw summary window are interconvertible on paths. -/
theorem summaryWindowRelAtomImage_eq_of_raw_image_eq
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    {d : Proc}
    {tuple : DirectReversalTuple (SummaryWindowAtom S radius)
      In₁ In₂ Out₁ Out₂ d}
    {old new : TypedPath (EdgeType d)}
    (himage :
      (summaryWindowAbstraction (S d.other) radius) '' rel d tuple old =
        (summaryWindowAbstraction (S d.other) radius) '' rel d tuple new) :
    summaryWindowRelAtomImage S radius rel d tuple old =
      summaryWindowRelAtomImage S radius rel d tuple new := by
  ext atom
  constructor
  · rintro ⟨out, hmem, rfl⟩
    have hraw :
        summaryWindowAbstraction (S d.other) radius out ∈
          (summaryWindowAbstraction (S d.other) radius) '' rel d tuple new := by
      rw [<- himage]
      exact Set.mem_image_of_mem _ hmem
    rcases hraw with ⟨out', hmem', hraw'⟩
    exact ⟨out', hmem',
      SummaryWindowAtom.eq_of_raw_eq S radius hraw'⟩
  · rintro ⟨out, hmem, rfl⟩
    have hraw :
        summaryWindowAbstraction (S d.other) radius out ∈
          (summaryWindowAbstraction (S d.other) radius) '' rel d tuple old := by
      rw [himage]
      exact Set.mem_image_of_mem _ hmem
    rcases hraw with ⟨out', hmem', hraw'⟩
    exact ⟨out', hmem',
      SummaryWindowAtom.eq_of_raw_eq S radius hraw'⟩

/-- **Set-level simultaneous saturation from the set pullback bound**: at
any radius stable under one pullback, inputs with equal refined atoms have
equal saturated successor-atom images. -/
theorem summaryWindowRelAtomImage_eq_of_atom_eq
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hpullback : ∀ d tuple,
      SummaryWindowRelSetPullbackBoundAt radius (S d) (S d.other)
        (rel d tuple))
    (hradius : endpointPullbackBound radius ≤ radius)
    {d : Proc}
    {tuple : DirectReversalTuple (SummaryWindowAtom S radius)
      In₁ In₂ Out₁ Out₂ d}
    {old new : TypedPath (EdgeType d)}
    (hatom :
      SummaryWindowAtom.ofPath S radius d old =
        SummaryWindowAtom.ofPath S radius d new) :
    summaryWindowRelAtomImage S radius rel d tuple old =
      summaryWindowRelAtomImage S radius rel d tuple new := by
  apply summaryWindowRelAtomImage_eq_of_raw_image_eq S radius rel
  apply hpullback d tuple old new
  exact summaryWindowAbstraction_refines_of_le (S d) hradius
    (SummaryWindowAtom.raw_eq_of_eq S radius hatom)

/-- At the fixed closure radius `max c 2`. -/
theorem summaryWindowRelAtomImage_eq_atClosureRadius
    (c : Nat)
    (rel : SummaryWindowReversalRel S (max c 2)
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hpullback : ∀ d tuple,
      SummaryWindowRelSetPullbackBoundAt (max c 2) (S d) (S d.other)
        (rel d tuple))
    {d : Proc}
    {tuple : DirectReversalTuple (SummaryWindowAtom S (max c 2))
      In₁ In₂ Out₁ Out₂ d}
    {old new : TypedPath (EdgeType d)}
    (hatom :
      SummaryWindowAtom.ofPath S (max c 2) d old =
        SummaryWindowAtom.ofPath S (max c 2) d new) :
    summaryWindowRelAtomImage S (max c 2) rel d tuple old =
      summaryWindowRelAtomImage S (max c 2) rel d tuple new :=
  summaryWindowRelAtomImage_eq_of_atom_eq S (max c 2) rel hpullback
    (endpointPullbackBound_le_self_of_two_le (le_max_right c 2)) hatom

/-- The set law collapses to the pointwise saturation exactly on the
tuples where the saturated image is a subsingleton (the tuple pins the
window-relevant choices). -/
theorem summaryWindowRelSaturated_of_setPullbackBound_of_subsingleton
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hpullback : ∀ d tuple,
      SummaryWindowRelSetPullbackBoundAt radius (S d) (S d.other)
        (rel d tuple))
    (hradius : endpointPullbackBound radius ≤ radius)
    (hsub : ∀ d tuple old,
      (summaryWindowRelAtomImage S radius rel d tuple old).Subsingleton) :
    SummaryWindowRelSaturated S radius rel := by
  intro d tuple old new outOld outNew hatom hmemOld hmemNew
  have himage :=
    summaryWindowRelAtomImage_eq_of_atom_eq S radius rel hpullback hradius
      (tuple := tuple) hatom
  refine hsub d tuple old
    (mem_summaryWindowRelAtomImage S radius rel hmemOld) ?_
  rw [himage]
  exact mem_summaryWindowRelAtomImage S radius rel hmemNew

section Materialization

variable [∀ d, Fintype (EdgeType d)]

/-- The saturated successor image materialized as a finite candidate set. -/
noncomputable def summaryWindowRelAtomImageFinset
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (d : Proc)
    (tuple : DirectReversalTuple (SummaryWindowAtom S radius)
      In₁ In₂ Out₁ Out₂ d)
    (old : TypedPath (EdgeType d)) :
    Finset (SummaryWindowAtom S radius d.other) :=
  (Set.toFinite (summaryWindowRelAtomImage S radius rel d tuple old)).toFinset

@[simp]
theorem mem_summaryWindowRelAtomImageFinset
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    {d : Proc}
    {tuple : DirectReversalTuple (SummaryWindowAtom S radius)
      In₁ In₂ Out₁ Out₂ d}
    {old : TypedPath (EdgeType d)}
    {atom : SummaryWindowAtom S radius d.other} :
    atom ∈ summaryWindowRelAtomImageFinset S radius rel d tuple old ↔
      atom ∈ summaryWindowRelAtomImage S radius rel d tuple old :=
  Set.Finite.mem_toFinset _

/-- The finite candidate set is determined by the refined old atom, at any
radius stable under one pullback. -/
theorem summaryWindowRelAtomImageFinset_eq_of_atom_eq
    (rel : SummaryWindowReversalRel S radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hpullback : ∀ d tuple,
      SummaryWindowRelSetPullbackBoundAt radius (S d) (S d.other)
        (rel d tuple))
    (hradius : endpointPullbackBound radius ≤ radius)
    {d : Proc}
    {tuple : DirectReversalTuple (SummaryWindowAtom S radius)
      In₁ In₂ Out₁ Out₂ d}
    {old new : TypedPath (EdgeType d)}
    (hatom :
      SummaryWindowAtom.ofPath S radius d old =
        SummaryWindowAtom.ofPath S radius d new) :
    summaryWindowRelAtomImageFinset S radius rel d tuple old =
      summaryWindowRelAtomImageFinset S radius rel d tuple new := by
  ext atom
  rw [mem_summaryWindowRelAtomImageFinset, mem_summaryWindowRelAtomImageFinset,
    summaryWindowRelAtomImage_eq_of_atom_eq S radius rel hpullback hradius
      (tuple := tuple) hatom]

end Materialization

end SetSaturation

end RelationalReversal

end DistributedSynthesis
