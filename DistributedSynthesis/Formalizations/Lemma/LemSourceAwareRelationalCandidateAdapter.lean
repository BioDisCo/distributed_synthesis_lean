/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFixedPolicyRelationalCandidateTable

/-!
# Retaining the source family in relational candidate edges

`RelationalFamilyCandidateGood` deliberately has the small edge interface

```lean
Descriptor -> Move -> Query -> Family -> Descriptor -> Prop
```

and therefore does not pass the current candidate's family to the edge.  That
interface is sufficient only when the edge is genuinely independent of the
source family.  It is not sufficient for the profiled reversal construction:
there the source family is semantic provenance, and forgetting it permits an
edge witness to be silently reselected from a different same-descriptor
family.

This file gives a reusable, non-invasive repair.  The source family is copied
into the descriptor.  Liveness requires the copy to agree with the public
family, and every edge installs the target family as the next copy.  Hence the
existing saturation and fixed-policy table may be reused without changing
their APIs, while a concrete edge receives both the literal source and target
families.

The duplicate is public finite data.  It is not a selected semantic member,
orientation, lane, strict-leader flag, or hidden bit.
-/

namespace DistributedSynthesis

universe f d m q

/-! ## Source-aware encoding -/

/-- The descriptor remembers the literal public family from which its edge
must be witnessed. -/
abbrev SourceAwareRelationalDescriptor (Family : Type f)
    (Descriptor : Type d) :=
  Family × Descriptor

/-- Forget the redundant source-family copy. -/
def sourceAwareRelationalCandidateDecode
    {Family : Type f} {Descriptor : Type d}
    (candidate : RelationalFamilyCandidate Family
      (SourceAwareRelationalDescriptor Family Descriptor)) :
    RelationalFamilyCandidate Family Descriptor :=
  (candidate.1, candidate.2.2)

/-- Materialize all decoded candidates of a finite source-aware set. -/
noncomputable def sourceAwareRelationalCandidatesDecode
    {Family : Type f} {Descriptor : Type d}
    (candidates : Finset (RelationalFamilyCandidate Family
      (SourceAwareRelationalDescriptor Family Descriptor))) :
    Finset (RelationalFamilyCandidate Family Descriptor) := by
  classical
  exact candidates.image sourceAwareRelationalCandidateDecode

theorem mem_sourceAwareRelationalCandidatesDecode
    {Family : Type f} {Descriptor : Type d}
    (candidates : Finset (RelationalFamilyCandidate Family
      (SourceAwareRelationalDescriptor Family Descriptor)))
    (candidate : RelationalFamilyCandidate Family
      (SourceAwareRelationalDescriptor Family Descriptor))
    (hcandidate : candidate ∈ candidates) :
    sourceAwareRelationalCandidateDecode candidate ∈
      sourceAwareRelationalCandidatesDecode candidates := by
  classical
  exact Finset.mem_image.2 ⟨candidate, hcandidate, rfl⟩

/-- A source-aware candidate is live only when its stored source family is
literally its public candidate family. -/
def SourceAwareRelationalLive
    {Family : Type f} {Descriptor : Type d}
    (Live : Descriptor -> Family -> Prop)
    (descriptor : SourceAwareRelationalDescriptor Family Descriptor)
    (family : Family) : Prop :=
  descriptor.1 = family ∧ Live descriptor.2 family

/-- Candidate validity retains the same literal-family agreement. -/
def SourceAwareRelationalCandidateValid
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    (CandidateValid : Descriptor -> Family -> Move -> Prop)
    (descriptor : SourceAwareRelationalDescriptor Family Descriptor)
    (family : Family) (move : Move) : Prop :=
  descriptor.1 = family ∧ CandidateValid descriptor.2 family move

/-- A concrete source-aware edge receives both public families.  The target
descriptor is required to store the target family for the next round. -/
def sourceAwareRelationalExactEdge
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (ExactEdge : Family -> Descriptor -> Move -> Query -> Family ->
      Descriptor -> Prop)
    (source : SourceAwareRelationalDescriptor Family Descriptor)
    (move : Move) (query : Query) (targetFamily : Family)
    (target : SourceAwareRelationalDescriptor Family Descriptor) : Prop :=
  ExactEdge source.1 source.2 move query targetFamily target.2 ∧
    target.1 = targetFamily

/-- Control evolution ignores only the redundant public-family copy. -/
def sourceAwareRelationalControlStep
    {Family : Type f} {Descriptor : Type d}
    (ControlStep : Descriptor -> Descriptor -> Prop)
    (source target : SourceAwareRelationalDescriptor Family Descriptor) : Prop :=
  ControlStep source.2 target.2

/-! ## The model-facing source-aware coverage law -/

/-- Pointwise coverage in which the exact edge receives the current
candidate's literal public family. -/
def EncodedSourceAwareRelationalCandidateLiveSuccessorCoverage
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (Live : Descriptor -> Family -> Prop)
    (CandidateValid : Descriptor -> Family -> Move -> Prop)
    (ExactEdge : Family -> Descriptor -> Move -> Query -> Family ->
      Descriptor -> Prop)
    (ControlStep : Descriptor -> Descriptor -> Prop) : Prop :=
  ∀ (source : RelationalFamilyCandidate Family Descriptor) move query,
    Live source.2 source.1 ->
    CandidateValid source.2 source.1 move ->
      ∃ target : RelationalFamilyCandidate Family Descriptor,
        ExactEdge source.1 source.2 move query target.1 target.2 ∧
          ControlStep source.2 target.2 ∧
          Live target.2 target.1

/-- Source-aware model coverage becomes ordinary candidate-table coverage
after storing the source family in the descriptor. -/
theorem relationalCandidateLiveSuccessorCoverage_sourceAware
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (Live : Descriptor -> Family -> Prop)
    (CandidateValid : Descriptor -> Family -> Move -> Prop)
    (ExactEdge : Family -> Descriptor -> Move -> Query -> Family ->
      Descriptor -> Prop)
    (ControlStep : Descriptor -> Descriptor -> Prop)
    (coverage : EncodedSourceAwareRelationalCandidateLiveSuccessorCoverage Live
      CandidateValid ExactEdge ControlStep) :
    RelationalCandidateLiveSuccessorCoverage
      (SourceAwareRelationalLive Live)
      (SourceAwareRelationalCandidateValid CandidateValid)
      (sourceAwareRelationalExactEdge ExactEdge)
      (sourceAwareRelationalControlStep ControlStep) := by
  intro source move query hlive hvalid
  obtain ⟨target, hedge, hcontrol, htargetLive⟩ :=
    coverage (source.1, source.2.2) move query hlive.2 hvalid.2
  let encodedTarget : RelationalFamilyCandidate Family
      (SourceAwareRelationalDescriptor Family Descriptor) :=
    (target.1, (target.1, target.2))
  refine ⟨encodedTarget, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact ⟨by simpa only [hlive.1] using hedge, rfl⟩
    · exact hcontrol
  · exact ⟨rfl, htargetLive⟩

/-! ## Candidate-wide common moves lift without new mathematics -/

/-- A common-move theorem on ordinary candidates supplies a common move on
the source-aware encoding.  Only live (hence family-consistent) candidates
are constrained. -/
theorem relationalCandidateCommonMoveExists_sourceAware
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    (Live : Descriptor -> Family -> Prop)
    (CandidateValid : Descriptor -> Family -> Move -> Prop)
    (common : RelationalCandidateCommonMoveExists Live CandidateValid) :
    RelationalCandidateCommonMoveExists
      (SourceAwareRelationalLive Live)
      (SourceAwareRelationalCandidateValid CandidateValid) := by
  intro candidates hactive
  let decoded := sourceAwareRelationalCandidatesDecode candidates
  have hdecodedActive : RelationalCandidateSetActive Live decoded := by
    obtain ⟨candidate, hcandidate, hlive⟩ := hactive
    exact ⟨sourceAwareRelationalCandidateDecode candidate,
      mem_sourceAwareRelationalCandidatesDecode candidates candidate hcandidate,
      hlive.2⟩
  obtain ⟨move, hmove⟩ := common decoded hdecodedActive
  refine ⟨move, ?_⟩
  intro candidate hcandidate hlive
  refine ⟨hlive.1, ?_⟩
  exact hmove (sourceAwareRelationalCandidateDecode candidate)
    (mem_sourceAwareRelationalCandidatesDecode candidates candidate hcandidate)
    hlive.2

/-! ## Initial sets and exact-thread decoding -/

/-- Store the current public family alongside every initial descriptor. -/
def sourceAwareRelationalCandidateEncode
    {Family : Type f} {Descriptor : Type d}
    (candidate : RelationalFamilyCandidate Family Descriptor) :
    RelationalFamilyCandidate Family
      (SourceAwareRelationalDescriptor Family Descriptor) :=
  (candidate.1, (candidate.1, candidate.2))

@[simp] theorem sourceAwareRelationalCandidateDecode_encode
    {Family : Type f} {Descriptor : Type d}
    (candidate : RelationalFamilyCandidate Family Descriptor) :
    sourceAwareRelationalCandidateDecode
        (sourceAwareRelationalCandidateEncode candidate) = candidate :=
  rfl

noncomputable def sourceAwareRelationalCandidatesEncode
    {Family : Type f} {Descriptor : Type d}
    (candidates : Finset (RelationalFamilyCandidate Family Descriptor)) :
    Finset (RelationalFamilyCandidate Family
      (SourceAwareRelationalDescriptor Family Descriptor)) := by
  classical
  exact candidates.image sourceAwareRelationalCandidateEncode

theorem mem_sourceAwareRelationalCandidatesEncode
    {Family : Type f} {Descriptor : Type d}
    (candidates : Finset (RelationalFamilyCandidate Family Descriptor))
    (candidate : RelationalFamilyCandidate Family Descriptor)
    (hcandidate : candidate ∈ candidates) :
    sourceAwareRelationalCandidateEncode candidate ∈
      sourceAwareRelationalCandidatesEncode candidates := by
  classical
  exact Finset.mem_image.2 ⟨candidate, hcandidate, rfl⟩

/-- Every encoded exact thread decodes to a genuine source-family-aware
thread.  In particular, the source family used by every edge is definitionally
the family carried by the preceding decoded candidate. -/
structure SourceAwareRelationalFamilyExactThread
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (ExactEdge : Family -> Descriptor -> Move -> Query -> Family ->
      Descriptor -> Prop)
    (ControlStep : Descriptor -> Descriptor -> Prop)
    (initial : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Nat -> Move) (query : Nat -> Query) where
  candidate : Nat -> RelationalFamilyCandidate Family Descriptor
  initial_mem : candidate 0 ∈ initial
  exact : ∀ n,
    ExactEdge (candidate n).1 (candidate n).2 (move n) (query n)
      (candidate (n + 1)).1 (candidate (n + 1)).2
  control : ∀ n, ControlStep (candidate n).2 (candidate (n + 1)).2

/-- Decode a generic exact thread over the source-aware encoding. -/
def sourceAwareRelationalFamilyExactThreadDecode
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (ExactEdge : Family -> Descriptor -> Move -> Query -> Family ->
      Descriptor -> Prop)
    (ControlStep : Descriptor -> Descriptor -> Prop)
    (initial : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Nat -> Move) (query : Nat -> Query)
    (thread : RelationalFamilyExactThread
      (sourceAwareRelationalExactEdge ExactEdge)
      (sourceAwareRelationalControlStep ControlStep)
      (sourceAwareRelationalCandidatesEncode initial) move query) :
    SourceAwareRelationalFamilyExactThread ExactEdge ControlStep initial move
      query := by
  have hconsistent : ∀ n,
      (thread.candidate n).2.1 = (thread.candidate n).1 := by
    intro n
    cases n with
    | zero =>
        have hinitial := thread.initial_mem
        classical
        change thread.candidate 0 ∈
          initial.image sourceAwareRelationalCandidateEncode at hinitial
        rw [Finset.mem_image] at hinitial
        obtain ⟨candidate, _hcandidate, hencode⟩ := hinitial
        rw [← hencode]
        rfl
    | succ n =>
        exact (thread.exact n).1.2
  refine
    { candidate := fun n => sourceAwareRelationalCandidateDecode
        (thread.candidate n)
      initial_mem := ?_
      exact := ?_
      control := ?_ }
  · have hinitial := thread.initial_mem
    classical
    change thread.candidate 0 ∈
      initial.image sourceAwareRelationalCandidateEncode at hinitial
    rw [Finset.mem_image] at hinitial
    obtain ⟨candidate, hcandidate, hencode⟩ := hinitial
    rw [← hencode]
    exact hcandidate
  · intro n
    simpa only [sourceAwareRelationalCandidateDecode, hconsistent n] using
      (thread.exact n).1.1
  · intro n
    exact (thread.exact n).2

end DistributedSynthesis
