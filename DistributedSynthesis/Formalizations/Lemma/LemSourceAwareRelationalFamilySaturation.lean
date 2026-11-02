/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemRelationalFamilySaturation

/-!
# Source-aware relational family saturation

`RelationalFamilyCandidateGood` passes only the source descriptor to its
`ExactEdge`; the source family tag is discarded.  That interface is adequate
only when the edge is independent of the advertised source family.  It is too
weak for a receipt invariant whose meaning is precisely that the descriptor
is represented by that tagged family.

This file gives the minimal source-aware variant.  The edge receives the full
source and target candidates.  No representative is selected and no hidden
coordinate is exposed: the public state remains a finite set of tagged
candidates.
-/

namespace DistributedSynthesis

universe f d m q

/-- One exact successor which can inspect the retained source family tag. -/
def SourceAwareRelationalFamilyCandidateGood
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (ExactEdge : RelationalFamilyCandidate Family Descriptor → Move →
      Query → RelationalFamilyCandidate Family Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (current : RelationalFamilyCandidate Family Descriptor)
    (move : Move) (query : Query)
    (target : RelationalFamilyCandidate Family Descriptor) : Prop :=
  ExactEdge current move query target ∧
    ControlStep current.2 target.2

/-- Saturate by all exact successors while retaining the source family in
the edge call. -/
noncomputable def sourceAwareRelationalFamilySaturation
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : RelationalFamilyCandidate Family Descriptor → Move →
      Query → RelationalFamilyCandidate Family Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (current : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Move) (query : Query) :
    Finset (RelationalFamilyCandidate Family Descriptor) := by
  classical
  exact Finset.univ.filter fun target ↦
    ∃ source ∈ current,
      SourceAwareRelationalFamilyCandidateGood ExactEdge ControlStep source
        move query target

/-- Exact membership characterization. -/
theorem mem_sourceAwareRelationalFamilySaturation_iff
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : RelationalFamilyCandidate Family Descriptor → Move →
      Query → RelationalFamilyCandidate Family Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (current : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Move) (query : Query)
    (target : RelationalFamilyCandidate Family Descriptor) :
    target ∈ sourceAwareRelationalFamilySaturation ExactEdge ControlStep
        current move query ↔
      ∃ source ∈ current,
        SourceAwareRelationalFamilyCandidateGood ExactEdge ControlStep source
          move query target := by
  classical
  simp [sourceAwareRelationalFamilySaturation]

/-- Per-live-candidate successor coverage for the source-aware interface. -/
def SourceAwareRelationalCandidateLiveSuccessorCoverage
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (Live : Descriptor → Family → Prop)
    (CandidateValid : Descriptor → Family → Move → Prop)
    (ExactEdge : RelationalFamilyCandidate Family Descriptor → Move →
      Query → RelationalFamilyCandidate Family Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop) : Prop :=
  ∀ source move query,
    Live source.2 source.1 →
    CandidateValid source.2 source.1 move →
      ∃ target,
        SourceAwareRelationalFamilyCandidateGood ExactEdge ControlStep source
            move query target ∧
          Live target.2 target.1

/-- Source-aware coverage puts a live target in the finite saturation. -/
theorem exists_live_mem_sourceAwareRelationalFamilySaturation
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (Live : Descriptor → Family → Prop)
    (CandidateValid : Descriptor → Family → Move → Prop)
    (ExactEdge : RelationalFamilyCandidate Family Descriptor → Move →
      Query → RelationalFamilyCandidate Family Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (coverage : SourceAwareRelationalCandidateLiveSuccessorCoverage Live
      CandidateValid ExactEdge ControlStep)
    (candidates : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Move) (query : Query)
    (actual : RelationalFamilyCandidate Family Descriptor)
    (hactual : actual ∈ candidates)
    (hlive : Live actual.2 actual.1)
    (hvalid : CandidateValid actual.2 actual.1 move) :
    ∃ target ∈ sourceAwareRelationalFamilySaturation ExactEdge
        ControlStep candidates move query,
      SourceAwareRelationalFamilyCandidateGood ExactEdge ControlStep actual
          move query target ∧
        Live target.2 target.1 := by
  obtain ⟨target, hgood, htargetLive⟩ :=
    coverage actual move query hlive hvalid
  exact ⟨target,
    (mem_sourceAwareRelationalFamilySaturation_iff ExactEdge ControlStep
      candidates move query target).2 ⟨actual, hactual, hgood⟩,
    hgood, htargetLive⟩

/-! ## A proof-side distinguished successor -/

/-- Choose one live exact successor of one literal source candidate, falling
back to the source only when no such successor exists.  This is a transition
of an omniscient finite proof machine, not a process-local choice.  The full
saturation above remains the public belief object and retains every possible
successor. -/
noncomputable def sourceAwareRelationalDistinguishedSuccessor
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (Live : Descriptor → Family → Prop)
    (ExactEdge : RelationalFamilyCandidate Family Descriptor → Move →
      Query → RelationalFamilyCandidate Family Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (source : RelationalFamilyCandidate Family Descriptor)
    (move : Move) (query : Query) :
    RelationalFamilyCandidate Family Descriptor := by
  classical
  exact if h : ∃ target,
      SourceAwareRelationalFamilyCandidateGood ExactEdge ControlStep source
          move query target ∧
        Live target.2 target.1 then
    Classical.choose h
  else source

/-- Under live-successor coverage, the distinguished successor is an exact
good edge from the literal source. -/
theorem sourceAwareRelationalDistinguishedSuccessor_good
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (Live : Descriptor → Family → Prop)
    (CandidateValid : Descriptor → Family → Move → Prop)
    (ExactEdge : RelationalFamilyCandidate Family Descriptor → Move →
      Query → RelationalFamilyCandidate Family Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (coverage : SourceAwareRelationalCandidateLiveSuccessorCoverage Live
      CandidateValid ExactEdge ControlStep)
    (source : RelationalFamilyCandidate Family Descriptor)
    (move : Move) (query : Query)
    (hlive : Live source.2 source.1)
    (hvalid : CandidateValid source.2 source.1 move) :
    SourceAwareRelationalFamilyCandidateGood ExactEdge ControlStep source move
  query
      (sourceAwareRelationalDistinguishedSuccessor Live ExactEdge ControlStep
        source move query) := by
  classical
  have hex := coverage source move query hlive hvalid
  unfold sourceAwareRelationalDistinguishedSuccessor
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).1

/-- The selected proof-side successor remains live. -/
theorem sourceAwareRelationalDistinguishedSuccessor_live
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (Live : Descriptor → Family → Prop)
    (CandidateValid : Descriptor → Family → Move → Prop)
    (ExactEdge : RelationalFamilyCandidate Family Descriptor → Move →
      Query → RelationalFamilyCandidate Family Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (coverage : SourceAwareRelationalCandidateLiveSuccessorCoverage Live
      CandidateValid ExactEdge ControlStep)
    (source : RelationalFamilyCandidate Family Descriptor)
    (move : Move) (query : Query)
    (hlive : Live source.2 source.1)
    (hvalid : CandidateValid source.2 source.1 move) :
    Live
      (sourceAwareRelationalDistinguishedSuccessor Live ExactEdge ControlStep
        source move query).2
      (sourceAwareRelationalDistinguishedSuccessor Live ExactEdge ControlStep
        source move query).1 := by
  classical
  have hex := coverage source move query hlive hvalid
  unfold sourceAwareRelationalDistinguishedSuccessor
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).2

/-- The distinguished successor is one member of the full source-aware
saturation whenever its literal source belongs to the current candidate set.
Thus the proof thread never removes any locally possible alternative. -/
theorem sourceAwareRelationalDistinguishedSuccessor_mem_saturation
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (Live : Descriptor → Family → Prop)
    (CandidateValid : Descriptor → Family → Move → Prop)
    (ExactEdge : RelationalFamilyCandidate Family Descriptor → Move →
      Query → RelationalFamilyCandidate Family Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (coverage : SourceAwareRelationalCandidateLiveSuccessorCoverage Live
      CandidateValid ExactEdge ControlStep)
    (candidates : Finset (RelationalFamilyCandidate Family Descriptor))
    (source : RelationalFamilyCandidate Family Descriptor)
    (hsource : source ∈ candidates)
    (move : Move) (query : Query)
    (hlive : Live source.2 source.1)
    (hvalid : CandidateValid source.2 source.1 move) :
    sourceAwareRelationalDistinguishedSuccessor Live ExactEdge ControlStep
        source move query ∈
      sourceAwareRelationalFamilySaturation ExactEdge ControlStep candidates
        move query := by
  apply (mem_sourceAwareRelationalFamilySaturation_iff ExactEdge ControlStep
    candidates move query _).2
  exact ⟨source, hsource,
    sourceAwareRelationalDistinguishedSuccessor_good Live CandidateValid
      ExactEdge ControlStep coverage source move query hlive hvalid⟩

/-- Forgetting the source family turns a source-aware good edge into the old
descriptor-only good edge whenever the concrete edge admits that erasure. -/
theorem SourceAwareRelationalFamilyCandidateGood.to_descriptorOnly
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (SourceAwareEdge : RelationalFamilyCandidate Family Descriptor → Move →
      Query → RelationalFamilyCandidate Family Descriptor → Prop)
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (herase : ∀ source move query target,
      SourceAwareEdge source move query target →
        ExactEdge source.2 move query target.1 target.2)
    {source target : RelationalFamilyCandidate Family Descriptor}
    {move : Move} {query : Query}
    (hgood : SourceAwareRelationalFamilyCandidateGood SourceAwareEdge
      ControlStep source move query target) :
    RelationalFamilyCandidateGood ExactEdge ControlStep source move query
      target :=
  ⟨herase source move query target hgood.1, hgood.2⟩

end DistributedSynthesis
