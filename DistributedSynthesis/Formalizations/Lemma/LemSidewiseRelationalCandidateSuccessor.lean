/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSidewiseRelationalCandidateCommonMove

/-!
# Exact successors retain both sidewise local-class tags

The sidewise common-move interface enriches a public family with one finite
class coordinate for each process.  This file proves that the enrichment is
stable under the relational successor construction: tag the target by the
two class maps of its retained descriptor, and every base exact successor
lifts to a tagged exact successor.

This is deliberately a transport theorem.  It neither constructs the class
maps nor claims that a finite class determines a winning local controller.
Those are the model-specific and uniformity obligations.  No process is told
which class belongs to the other process, and no graph, orientation, lane, or
strict-leader flag appears.
-/

namespace DistributedSynthesis

universe oc tc f d m q

/-- The canonical family enrichment of a retained descriptor. -/
def sidewiseTaggedFamilyOf
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    (oneClassOf : Descriptor → OneClass)
    (twoClassOf : Descriptor → TwoClass)
    (descriptor : Descriptor) (family : Family) :
    SidewiseTaggedFamily OneClass TwoClass Family :=
  ((oneClassOf descriptor, twoClassOf descriptor), family)

@[simp] theorem sidewiseTaggedFamilyOf_oneClass
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    (oneClassOf : Descriptor → OneClass)
    (twoClassOf : Descriptor → TwoClass)
    (descriptor : Descriptor) (family : Family) :
    (sidewiseTaggedFamilyOf oneClassOf twoClassOf descriptor family).1.1 =
      oneClassOf descriptor :=
  rfl

@[simp] theorem sidewiseTaggedFamilyOf_twoClass
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    (oneClassOf : Descriptor → OneClass)
    (twoClassOf : Descriptor → TwoClass)
    (descriptor : Descriptor) (family : Family) :
    (sidewiseTaggedFamilyOf oneClassOf twoClassOf descriptor family).1.2 =
      twoClassOf descriptor :=
  rfl

@[simp] theorem sidewiseTaggedFamilyOf_family
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    (oneClassOf : Descriptor → OneClass)
    (twoClassOf : Descriptor → TwoClass)
    (descriptor : Descriptor) (family : Family) :
    (sidewiseTaggedFamilyOf oneClassOf twoClassOf descriptor family).2 =
      family :=
  rfl

/-- A tagged family is correct when its two class coordinates are exactly
the class maps of the retained descriptor. -/
def SidewiseTaggedFamilyCorrect
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    (oneClassOf : Descriptor → OneClass)
    (twoClassOf : Descriptor → TwoClass)
    (descriptor : Descriptor)
    (family : SidewiseTaggedFamily OneClass TwoClass Family) : Prop :=
  family.1.1 = oneClassOf descriptor ∧
    family.1.2 = twoClassOf descriptor

theorem sidewiseTaggedFamilyOf_correct
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    (oneClassOf : Descriptor → OneClass)
    (twoClassOf : Descriptor → TwoClass)
    (descriptor : Descriptor) (family : Family) :
    SidewiseTaggedFamilyCorrect oneClassOf twoClassOf descriptor
      (sidewiseTaggedFamilyOf oneClassOf twoClassOf descriptor family) :=
  ⟨rfl, rfl⟩

/-- Lift a base liveness predicate while retaining exact side-class tags. -/
def SidewiseTaggedLive
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    (oneClassOf : Descriptor → OneClass)
    (twoClassOf : Descriptor → TwoClass)
    (BaseLive : Descriptor → Family → Prop)
    (descriptor : Descriptor)
    (family : SidewiseTaggedFamily OneClass TwoClass Family) : Prop :=
  BaseLive descriptor family.2 ∧
    SidewiseTaggedFamilyCorrect oneClassOf twoClassOf descriptor family

/-- Lift move validity without weakening its semantic component. -/
def SidewiseTaggedCandidateValid
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {Move : Type m}
    (oneClassOf : Descriptor → OneClass)
    (twoClassOf : Descriptor → TwoClass)
    (BaseValid : Descriptor → Family → Move → Prop)
    (descriptor : Descriptor)
    (family : SidewiseTaggedFamily OneClass TwoClass Family)
    (move : Move) : Prop :=
  BaseValid descriptor family.2 move ∧
    SidewiseTaggedFamilyCorrect oneClassOf twoClassOf descriptor family

/-- The tagged exact edge forgets the target tags for the base semantic edge
and separately checks that they are the canonical tags of the target
descriptor. -/
def SidewiseTaggedExactEdge
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (oneClassOf : Descriptor → OneClass)
    (twoClassOf : Descriptor → TwoClass)
    (BaseExactEdge : Descriptor → Move → Query → Family →
      Descriptor → Prop)
    (source : Descriptor) (move : Move) (query : Query)
    (targetFamily : SidewiseTaggedFamily OneClass TwoClass Family)
    (target : Descriptor) : Prop :=
  BaseExactEdge source move query targetFamily.2 target ∧
    SidewiseTaggedFamilyCorrect oneClassOf twoClassOf target targetFamily

/-- One base live-successor theorem lifts canonically to the two-tagged
relation.  The target descriptor is unchanged; only its family tag is
enriched. -/
theorem relationalCandidateLiveSuccessorCoverage_sidewiseTagged
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (oneClassOf : Descriptor → OneClass)
    (twoClassOf : Descriptor → TwoClass)
    (BaseLive : Descriptor → Family → Prop)
    (BaseValid : Descriptor → Family → Move → Prop)
    (BaseExactEdge : Descriptor → Move → Query → Family →
      Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (coverage : RelationalCandidateLiveSuccessorCoverage BaseLive BaseValid
      BaseExactEdge ControlStep) :
    RelationalCandidateLiveSuccessorCoverage
      (SidewiseTaggedLive oneClassOf twoClassOf BaseLive)
      (SidewiseTaggedCandidateValid oneClassOf twoClassOf BaseValid)
      (SidewiseTaggedExactEdge oneClassOf twoClassOf BaseExactEdge)
      ControlStep := by
  intro source move query hlive hvalid
  obtain ⟨target, hgood, htargetLive⟩ :=
    coverage (source.1.2, source.2) move query hlive.1 hvalid.1
  let taggedTarget : RelationalFamilyCandidate
      (SidewiseTaggedFamily OneClass TwoClass Family) Descriptor :=
    (sidewiseTaggedFamilyOf oneClassOf twoClassOf target.2 target.1,
      target.2)
  refine ⟨taggedTarget, ?_, ?_⟩
  · constructor
    · exact ⟨hgood.1, sidewiseTaggedFamilyOf_correct
          oneClassOf twoClassOf target.2 target.1⟩
    · exact hgood.2
  · exact ⟨htargetLive, sidewiseTaggedFamilyOf_correct
        oneClassOf twoClassOf target.2 target.1⟩

/-- Correct tagging is preserved by every good tagged edge, independently of
how the base semantic edge was obtained. -/
theorem sidewiseTaggedFamilyCorrect_of_candidateGood
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (oneClassOf : Descriptor → OneClass)
    (twoClassOf : Descriptor → TwoClass)
    (BaseExactEdge : Descriptor → Move → Query → Family →
      Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (source target : RelationalFamilyCandidate
      (SidewiseTaggedFamily OneClass TwoClass Family) Descriptor)
    (move : Move) (query : Query)
    (hgood : RelationalFamilyCandidateGood
      (SidewiseTaggedExactEdge oneClassOf twoClassOf BaseExactEdge)
      ControlStep source move query target) :
    SidewiseTaggedFamilyCorrect oneClassOf twoClassOf target.2 target.1 :=
  hgood.1.2

/-! ## Context-dependent tags for generated candidate sets

The class carried by a generated child need not be a function of the bare
target descriptor.  In the concrete reversal construction it also retains a
finite identity of the parent controller and the row-class computed by the
current query.  The following variant is the honest interface for that case.
-/

/-- Liveness with an arbitrary, model-supplied invariant on the two retained
class tags. -/
def ContextualSidewiseTaggedLive
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    (BaseLive : Descriptor → Family → Prop)
    (TagInvariant : Descriptor →
      SidewiseTaggedFamily OneClass TwoClass Family → Prop)
    (descriptor : Descriptor)
    (family : SidewiseTaggedFamily OneClass TwoClass Family) : Prop :=
  BaseLive descriptor family.2 ∧ TagInvariant descriptor family

/-- Move validity with the same generated-tag invariant retained. -/
def ContextualSidewiseTaggedCandidateValid
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {Move : Type m}
    (BaseValid : Descriptor → Family → Move → Prop)
    (TagInvariant : Descriptor →
      SidewiseTaggedFamily OneClass TwoClass Family → Prop)
    (descriptor : Descriptor)
    (family : SidewiseTaggedFamily OneClass TwoClass Family)
    (move : Move) : Prop :=
  BaseValid descriptor family.2 move ∧ TagInvariant descriptor family

/-- A generated target tag may depend on the complete current edge data.
This is where a concrete construction may retain the parent controller
identity and its finite row-equivalence summary. -/
def ContextualSidewiseTaggedExactEdge
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (targetTag : Descriptor → Move → Query → Family → Descriptor →
      OneClass × TwoClass)
    (BaseExactEdge : Descriptor → Move → Query → Family →
      Descriptor → Prop)
    (source : Descriptor) (move : Move) (query : Query)
    (targetFamily : SidewiseTaggedFamily OneClass TwoClass Family)
    (target : Descriptor) : Prop :=
  BaseExactEdge source move query targetFamily.2 target ∧
    targetFamily.1 = targetTag source move query targetFamily.2 target

/-- Base successor coverage lifts through a contextual tag generator exactly
when every generated tag satisfies the model invariant.  This isolates the
sticky-provenance proof from all relational-table plumbing. -/
theorem relationalCandidateLiveSuccessorCoverage_contextualSidewiseTagged
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (BaseLive : Descriptor → Family → Prop)
    (BaseValid : Descriptor → Family → Move → Prop)
    (BaseExactEdge : Descriptor → Move → Query → Family →
      Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (TagInvariant : Descriptor →
      SidewiseTaggedFamily OneClass TwoClass Family → Prop)
    (targetTag : Descriptor → Move → Query → Family → Descriptor →
      OneClass × TwoClass)
    (coverage : RelationalCandidateLiveSuccessorCoverage BaseLive BaseValid
      BaseExactEdge ControlStep)
    (htag : ∀ source move query family target,
      BaseExactEdge source move query family target →
        TagInvariant target (targetTag source move query family target,
          family)) :
    RelationalCandidateLiveSuccessorCoverage
      (ContextualSidewiseTaggedLive BaseLive TagInvariant)
      (ContextualSidewiseTaggedCandidateValid BaseValid TagInvariant)
      (ContextualSidewiseTaggedExactEdge targetTag BaseExactEdge)
      ControlStep := by
  intro source move query hlive hvalid
  obtain ⟨target, hgood, htargetLive⟩ :=
    coverage (source.1.2, source.2) move query hlive.1 hvalid.1
  let taggedTarget : RelationalFamilyCandidate
      (SidewiseTaggedFamily OneClass TwoClass Family) Descriptor :=
    ((targetTag source.2 move query target.1 target.2, target.1), target.2)
  refine ⟨taggedTarget, ?_, ?_⟩
  · constructor
    · exact ⟨hgood.1, rfl⟩
    · exact hgood.2
  · exact ⟨htargetLive,
        htag source.2 move query target.1 target.2 hgood.1⟩

/-- Every contextual good edge exposes the literal generated tag equation. -/
theorem contextualSidewiseTagged_tag_eq_of_candidateGood
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (targetTag : Descriptor → Move → Query → Family → Descriptor →
      OneClass × TwoClass)
    (BaseExactEdge : Descriptor → Move → Query → Family →
      Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (source target : RelationalFamilyCandidate
      (SidewiseTaggedFamily OneClass TwoClass Family) Descriptor)
    (move : Move) (query : Query)
    (hgood : RelationalFamilyCandidateGood
      (ContextualSidewiseTaggedExactEdge targetTag BaseExactEdge)
      ControlStep source move query target) :
    target.1.1 = targetTag source.2 move query target.1.2 target.2 :=
  hgood.1.2

end DistributedSynthesis
