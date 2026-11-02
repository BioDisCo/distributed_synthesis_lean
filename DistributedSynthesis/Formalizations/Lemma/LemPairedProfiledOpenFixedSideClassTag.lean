/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedSuccessorAPI
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenHiddenDescriptorFamilyAlphabet
import DistributedSynthesis.Formalizations.Lemma.LemSidewiseRelationalCandidateCommonMove

/-!
# Fixed local-class tags for generated indexed successors

The indexed reversal construction already computes the finite local class of
one selected pivot.  After forgetting successor roots, its child code is just

`I → Option PairedEntryRow`.

This file exposes that map as the fixed codomain used by the sidewise
candidate interface.  For process one the tag is read from the left pattern
and pivot; for process two it is read from the right pattern and pivot.  The
choice is by process identity, never by a current graph, orientation, lane, or
strict-leader test.

The semantic equality theorems deliberately quantify over one common parent
entry, past, and input.  Equal finite row-slot tags then mean equal child
views.  No theorem compares tags produced by unrelated semantic parents:
equal Boolean patterns need not identify the literal perfect-recall views
behind them.  An iterated candidate construction must therefore retain a
sticky finite parent/controller identity in addition to the row-slot tag.
`StickyIndexedLineageLocalClassTag` names exactly that fixed product.
-/

namespace DistributedSynthesis

universe i p u v x y s f

namespace DetParityAutomaton

/-! ## Root-free finite class code -/

/-- The fixed finite code of one selected local equality class.  Each
persistent lineage contributes at most one of its two physical rows. -/
abbrev IndexedLineageLocalClassTag (I : Type i) :=
  I → Option PairedEntryRow

noncomputable instance [Fintype I] :
    Fintype (IndexedLineageLocalClassTag I) := by
  classical
  infer_instance

/-- Forget the objective roots of the ordinary indexed child code.  The
dummy root is proof-irrelevant; the result depends only on `pattern` and
`pivot`. -/
def indexedLineageLocalClassTag
    (pattern : IndexedLineageEqualityPattern I)
    (pivot : IndexedLineageCandidate I) :
    IndexedLineageLocalClassTag I :=
  fun member ↦
    if pattern (member, .first) pivot = true then some .first
    else if pattern (member, .both) pivot = true then some .both
    else none

/-- The root-free definition is literally the row projection of every
ordinary indexed child code, independently of the objective roots stored in
that code. -/
theorem indexedLineageLocalClassTag_eq_childCode_rowSlots
    {Root : Type u}
    (pattern : IndexedLineageEqualityPattern I)
    (root : IndexedLineageCandidate I → Root)
    (pivot : IndexedLineageCandidate I) :
    indexedLineageLocalClassTag pattern pivot =
      (indexedLineageChildCodeOfPattern pattern root pivot).rowSlots := by
  funext member
  by_cases hfirst : pattern (member, .first) pivot = true
  · simp [indexedLineageLocalClassTag, indexedLineageChildCodeOfPattern,
      IndexedLineageChildCode.rowSlots, hfirst]
  · by_cases hboth : pattern (member, .both) pivot = true
    · simp [indexedLineageLocalClassTag, indexedLineageChildCodeOfPattern,
        IndexedLineageChildCode.rowSlots, hfirst, hboth]
    · simp [indexedLineageLocalClassTag, indexedLineageChildCodeOfPattern,
        IndexedLineageChildCode.rowSlots, hfirst, hboth]

/-- Exact membership law for the root-free tag. -/
theorem indexedLineageLocalClassTag_eq_some_iff
    (pattern : IndexedLineageEqualityPattern I)
    (pivot : IndexedLineageCandidate I)
    (hfunctional : pattern.RowFunctionalAt pivot)
    (member : I) (row : PairedEntryRow) :
    indexedLineageLocalClassTag pattern pivot member = some row ↔
      pattern (member, row) pivot = true := by
  cases row with
  | first =>
      by_cases hfirst : pattern (member, .first) pivot = true
      · simp [indexedLineageLocalClassTag, hfirst]
      · simp [indexedLineageLocalClassTag, hfirst]
  | both =>
      by_cases hfirst : pattern (member, .first) pivot = true
      · have hboth : pattern (member, .both) pivot ≠ true := by
          intro hboth
          exact hfunctional member ⟨hfirst, hboth⟩
        simp [indexedLineageLocalClassTag, hfirst, hboth]
      · simp [indexedLineageLocalClassTag, hfirst]

/-- A reflexive pivot occurs in its own finite class tag. -/
theorem indexedLineageLocalClassTag_self
    (pattern : IndexedLineageEqualityPattern I)
    (pivot : IndexedLineageCandidate I)
    (hfunctional : pattern.RowFunctionalAt pivot)
    (hreflexive : pattern pivot pivot = true) :
    indexedLineageLocalClassTag pattern pivot pivot.1 = some pivot.2 := by
  exact (indexedLineageLocalClassTag_eq_some_iff pattern pivot hfunctional
    pivot.1 pivot.2).2 hreflexive

/-- Inside one fixed equality pattern, equal complete class tags force the
left pivot to be related to the right pivot.  The premise that the left pivot
is related to itself is stated explicitly; arbitrary Boolean matrices are not
silently treated as equivalence relations. -/
theorem indexedLineageLocalClassTag_eq_implies_related
    (pattern : IndexedLineageEqualityPattern I)
    (left right : IndexedLineageCandidate I)
    (hleftFunctional : pattern.RowFunctionalAt left)
    (hrightFunctional : pattern.RowFunctionalAt right)
    (hleftReflexive : pattern left left = true)
    (htags : indexedLineageLocalClassTag pattern left =
      indexedLineageLocalClassTag pattern right) :
    pattern left right = true := by
  have hleft : indexedLineageLocalClassTag pattern left left.1 =
      some left.2 :=
    indexedLineageLocalClassTag_self pattern left hleftFunctional
      hleftReflexive
  have hright : indexedLineageLocalClassTag pattern right left.1 =
      some left.2 := by
    rw [← congrFun htags left.1]
    exact hleft
  exact (indexedLineageLocalClassTag_eq_some_iff pattern right
    hrightFunctional left.1 left.2).1 hright

/-! ## Semantic exactness, restricted to one generated parent -/

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- Two process-two children generated from the same process-one parent
family have equal views whenever their fixed row-slot class tags agree. -/
theorem procTwoChildView_eq_of_localClassTag_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (left right : IndexedLineageCandidate I)
    (htags :
      indexedLineageLocalClassTag
          (procTwoChildViewPattern strategy entry past input) left =
        indexedLineageLocalClassTag
          (procTwoChildViewPattern strategy entry past input) right) :
    currentView Proc.two
        (procTwoViewClassChild strategy entry past input left).rightHistory =
      currentView Proc.two
        (procTwoViewClassChild strategy entry past input right).rightHistory := by
  let pattern := procTwoChildViewPattern strategy entry past input
  apply (procTwoChildViewPattern_eq_true_iff strategy entry past input left
    right).1
  apply indexedLineageLocalClassTag_eq_implies_related pattern left right
    (procTwoChildViewPattern_rowFunctionalAt strategy entry past input left)
    (procTwoChildViewPattern_rowFunctionalAt strategy entry past input right)
  · exact (procTwoChildViewPattern_eq_true_iff strategy entry past input
      left left).2 rfl
  · exact htags

/-- Process-one mirror of `procTwoChildView_eq_of_localClassTag_eq`.  Again,
both children are generated from the same literal parent family. -/
theorem procOneChildView_eq_of_localClassTag_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (left right : IndexedLineageCandidate I)
    (htags :
      indexedLineageLocalClassTag
          (procOneChildViewPattern strategy entry past input) left =
        indexedLineageLocalClassTag
          (procOneChildViewPattern strategy entry past input) right) :
    currentView Proc.one
        (procOneViewClassChild strategy entry past input left).leftHistory =
      currentView Proc.one
        (procOneViewClassChild strategy entry past input right).leftHistory := by
  let pattern := procOneChildViewPattern strategy entry past input
  apply (procOneChildViewPattern_eq_true_iff strategy entry past input left
    right).1
  apply indexedLineageLocalClassTag_eq_implies_related pattern left right
    (procOneChildViewPattern_rowFunctionalAt strategy entry past input left)
    (procOneChildViewPattern_rowFunctionalAt strategy entry past input right)
  · exact (procOneChildViewPattern_eq_true_iff strategy entry past input
      left left).2 rfl
  · exact htags

/-! ## Concrete sidewise tags of an indexed transition -/

variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Process one's fixed local-class tag is computed from the left family,
which contains process-one children. -/
def profiledOpenIndexedProcessOneSideClassTag
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    IndexedLineageLocalClassTag I :=
  indexedLineageLocalClassTag code.leftPattern direction.leftPivot

/-- Process two reads the independent right-family class tag. -/
def profiledOpenIndexedProcessTwoSideClassTag
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    IndexedLineageLocalClassTag I :=
  indexedLineageLocalClassTag code.rightPattern direction.rightPivot

/-- Enrich any old full family tag by the two independent fixed class codes
computed at one indexed transition. -/
def profiledOpenIndexedSidewiseTaggedFamily
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (family : Type f) (value : family) :
    SidewiseTaggedFamily (IndexedLineageLocalClassTag I)
      (IndexedLineageLocalClassTag I) family :=
  ((profiledOpenIndexedProcessOneSideClassTag A code direction,
      profiledOpenIndexedProcessTwoSideClassTag A code direction), value)

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledOpenIndexedSidewiseTaggedFamily_oneClass
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (family : Type f) (value : family) :
    (profiledOpenIndexedSidewiseTaggedFamily A code direction family
      value).1.1 =
      profiledOpenIndexedProcessOneSideClassTag A code direction :=
  rfl

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledOpenIndexedSidewiseTaggedFamily_twoClass
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (family : Type f) (value : family) :
    (profiledOpenIndexedSidewiseTaggedFamily A code direction family
      value).1.2 =
      profiledOpenIndexedProcessTwoSideClassTag A code direction :=
  rfl

/-! ## Sticky parent identity -/

variable {ParentTag : Type p}

/-- The iteratable fixed class type.  `ParentTag` is a finite identity of the
literal parent controller/provenance bank; the second coordinate is the
generated equality class inside that parent.  Keeping only the second
coordinate would unsoundly compare unrelated perfect-recall histories that
happen to have the same finite Boolean pattern. -/
abbrev StickyIndexedLineageLocalClassTag
    (ParentTag : Type p) (I : Type i) :=
  ParentTag × IndexedLineageLocalClassTag I

noncomputable instance [Fintype ParentTag] [Fintype I] :
    Fintype (StickyIndexedLineageLocalClassTag ParentTag I) := by
  classical
  infer_instance

/-- Install the sticky parent coordinate without inspecting any graph or
leader status. -/
def stickyIndexedLineageLocalClassTag
    (parent : ParentTag)
    (pattern : IndexedLineageEqualityPattern I)
    (pivot : IndexedLineageCandidate I) :
    StickyIndexedLineageLocalClassTag ParentTag I :=
  (parent, indexedLineageLocalClassTag pattern pivot)

/-- Exact model premise required before sticky tags from possibly different
semantic parents may be used as genuine local-view classes.  Equality of the
finite parent identity plus equality of the row-slot code must imply the
desired semantic relation.  The generic finite construction does not prove
this premise from cardinality or from equality of Boolean patterns. -/
def StickyParentDeterminesLocalClass
    {Global : Type u}
    (parentOf : Global → ParentTag)
    (patternOf : Global → IndexedLineageEqualityPattern I)
    (pivotOf : Global → IndexedLineageCandidate I)
    (Rel : Global → Global → Prop) : Prop :=
  ∀ left right,
    parentOf left = parentOf right →
      indexedLineageLocalClassTag (patternOf left) (pivotOf left) =
        indexedLineageLocalClassTag (patternOf right) (pivotOf right) →
      Rel left right

section
omit [Fintype I]

/-- The named premise is exactly sufficient for equality of complete sticky
tags to imply the semantic local relation. -/
theorem rel_of_stickyIndexedLineageLocalClassTag_eq
    {Global : Type u}
    (parentOf : Global → ParentTag)
    (patternOf : Global → IndexedLineageEqualityPattern I)
    (pivotOf : Global → IndexedLineageCandidate I)
    (Rel : Global → Global → Prop)
    (hsound : StickyParentDeterminesLocalClass parentOf patternOf pivotOf Rel)
    {left right : Global}
    (htags :
      stickyIndexedLineageLocalClassTag (parentOf left) (patternOf left)
          (pivotOf left) =
        stickyIndexedLineageLocalClassTag (parentOf right) (patternOf right)
          (pivotOf right)) :
    Rel left right := by
  exact hsound left right (congrArg Prod.fst htags)
    (congrArg Prod.snd htags)

@[simp] theorem stickyIndexedLineageLocalClassTag_parent
    (parent : ParentTag)
    (pattern : IndexedLineageEqualityPattern I)
    (pivot : IndexedLineageCandidate I) :
    (stickyIndexedLineageLocalClassTag parent pattern pivot).1 = parent :=
  rfl

@[simp] theorem stickyIndexedLineageLocalClassTag_class
    (parent : ParentTag)
    (pattern : IndexedLineageEqualityPattern I)
    (pivot : IndexedLineageCandidate I) :
    (stickyIndexedLineageLocalClassTag parent pattern pivot).2 =
      indexedLineageLocalClassTag pattern pivot :=
  rfl

end

/-! ## Same-parent semantic use -/

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Same-parent sticky version of the process-two child theorem.  The sticky
coordinate is identical on both sides because the children are generated by
one literal parent controller. -/
theorem procTwoChildView_eq_of_stickyLocalClassTag_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (parent : ParentTag)
    (left right : IndexedLineageCandidate I)
    (htags :
      stickyIndexedLineageLocalClassTag parent
          (procTwoChildViewPattern strategy entry past input) left =
        stickyIndexedLineageLocalClassTag parent
          (procTwoChildViewPattern strategy entry past input) right) :
    currentView Proc.two
        (procTwoViewClassChild strategy entry past input left).rightHistory =
      currentView Proc.two
        (procTwoViewClassChild strategy entry past input right).rightHistory := by
  apply procTwoChildView_eq_of_localClassTag_eq strategy entry past input
    left right
  exact congrArg Prod.snd htags

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Same-parent sticky process-one mirror. -/
theorem procOneChildView_eq_of_stickyLocalClassTag_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (parent : ParentTag)
    (left right : IndexedLineageCandidate I)
    (htags :
      stickyIndexedLineageLocalClassTag parent
          (procOneChildViewPattern strategy entry past input) left =
        stickyIndexedLineageLocalClassTag parent
          (procOneChildViewPattern strategy entry past input) right) :
    currentView Proc.one
        (procOneViewClassChild strategy entry past input left).leftHistory =
      currentView Proc.one
        (procOneViewClassChild strategy entry past input right).leftHistory := by
  apply procOneChildView_eq_of_localClassTag_eq strategy entry past input
    left right
  exact congrArg Prod.snd htags

end DetParityAutomaton

end DistributedSynthesis
