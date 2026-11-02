/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemHiddenDescriptorFamilyTotality

/-!
# Finite saturation of family-tagged exact successors

A receiver need not identify one current hidden descriptor in order to carry
all possible one-step continuations.  From a finite set of
`(public family, hidden descriptor)` candidates and a fixed move/query, this
file forms the finite union of every exact, control-correct successor pair.
Every actual candidate is covered by that union, provided it has one exact
successor.

The family tag is retained on each candidate.  This is essential: replacing
the candidate set by the coordinatewise union of its two-fibre families loses
which target descriptor came from which family, and can create a spurious
intersection.  Thus `HiddenDescriptorTwoFibreFamily` is a suitable finite
*component*, but not by itself a provenance-preserving saturated carrier.

Iteration is non-vacuous under pointwise coverage.  It admits an infinite
coherent exact thread, and membership in every iterated saturation is
automatic for every exact thread.  Consequently universal parity over exact
threads is unchanged by the candidate-set presentation; no child-family
functionality or equality is assumed.

This is a proof-side symmetric powerset construction.  It carries no lane,
orientation, strict-leader, or selected-candidate signal.  A concrete model
still has to supply one family-wide valid move and pathwise acceptance of all
exact threads; saturation does not manufacture either property.
-/

namespace DistributedSynthesis

universe f d m q u v x

/-- A candidate retains both the advertised public family and the hidden
descriptor which has provenance in that family. -/
abbrev RelationalFamilyCandidate (Family : Type f) (Descriptor : Type d) :=
  Family × Descriptor

/-- One exact and control-correct successor of a family-tagged candidate. -/
def RelationalFamilyCandidateGood
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (current : RelationalFamilyCandidate Family Descriptor)
    (move : Move) (query : Query)
    (target : RelationalFamilyCandidate Family Descriptor) : Prop :=
  ExactEdge current.2 move query target.1 target.2 ∧
    ControlStep current.2 target.2

/-- The finite saturation by all exact successors of all current candidates.
No representative is chosen. -/
noncomputable def relationalFamilySaturation
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (current : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Move) (query : Query) :
    Finset (RelationalFamilyCandidate Family Descriptor) := by
  classical
  exact Finset.univ.filter fun target ↦
    ∃ source ∈ current,
      RelationalFamilyCandidateGood ExactEdge ControlStep source move query
        target

/-- Membership in the saturation is exactly witnessed by one current source
and one exact edge. -/
theorem mem_relationalFamilySaturation_iff
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (current : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Move) (query : Query)
    (target : RelationalFamilyCandidate Family Descriptor) :
    target ∈ relationalFamilySaturation ExactEdge ControlStep current move query ↔
      ∃ source ∈ current,
        RelationalFamilyCandidateGood ExactEdge ControlStep source move query
          target := by
  classical
  simp [relationalFamilySaturation]

/-- Pointwise one-step coverage of a finite candidate set. -/
def RelationalFamilySaturationCoverage
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (current : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Move) (query : Query) : Prop :=
  ∀ source ∈ current,
    ∃ target,
      RelationalFamilyCandidateGood ExactEdge ControlStep source move query
        target

/-- Every possible actual current candidate has an exact target in the common
saturated successor set. -/
theorem exists_mem_relationalFamilySaturation_of_coverage
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (current : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Move) (query : Query)
    (coverage : RelationalFamilySaturationCoverage ExactEdge ControlStep
      current move query)
    (source : RelationalFamilyCandidate Family Descriptor)
    (hsource : source ∈ current) :
    ∃ target ∈ relationalFamilySaturation ExactEdge ControlStep current move
        query,
      RelationalFamilyCandidateGood ExactEdge ControlStep source move query
        target := by
  obtain ⟨target, htarget⟩ := coverage source hsource
  exact ⟨target,
    (mem_relationalFamilySaturation_iff ExactEdge ControlStep current move query
      target).2 ⟨source, hsource, htarget⟩,
    htarget⟩

/-- A nonempty covered family has a nonempty saturated successor. -/
theorem relationalFamilySaturation_nonempty
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (current : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Move) (query : Query)
    (coverage : RelationalFamilySaturationCoverage ExactEdge ControlStep
      current move query)
    (hcurrent : current.Nonempty) :
    (relationalFamilySaturation ExactEdge ControlStep current move query).Nonempty := by
  obtain ⟨source, hsource⟩ := hcurrent
  obtain ⟨target, htarget, _⟩ :=
    exists_mem_relationalFamilySaturation_of_coverage ExactEdge ControlStep
      current move query coverage source hsource
  exact ⟨target, htarget⟩

/-- Iterated candidate saturation along a fixed sequence of moves and finite
queries. -/
noncomputable def relationalFamilySaturationAt
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (initial : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Nat → Move) (query : Nat → Query) :
    Nat → Finset (RelationalFamilyCandidate Family Descriptor)
  | 0 => initial
  | n + 1 => relationalFamilySaturation ExactEdge ControlStep
      (relationalFamilySaturationAt ExactEdge ControlStep initial move query n)
      (move n) (query n)

@[simp] theorem relationalFamilySaturationAt_zero
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (initial : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Nat → Move) (query : Nat → Query) :
    relationalFamilySaturationAt ExactEdge ControlStep initial move query 0 =
      initial :=
  rfl

@[simp] theorem relationalFamilySaturationAt_succ
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (initial : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Nat → Move) (query : Nat → Query) (n : Nat) :
    relationalFamilySaturationAt ExactEdge ControlStep initial move query
        (n + 1) =
      relationalFamilySaturation ExactEdge ControlStep
        (relationalFamilySaturationAt ExactEdge ControlStep initial move query n)
        (move n) (query n) :=
  rfl

/-- An exact thread does not choose a child-family function.  At every step it
may take any family-tagged answer in the exact relation. -/
structure RelationalFamilyExactThread
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (initial : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Nat → Move) (query : Nat → Query) where
  candidate : Nat → RelationalFamilyCandidate Family Descriptor
  initial_mem : candidate 0 ∈ initial
  exact : ∀ n,
    RelationalFamilyCandidateGood ExactEdge ControlStep (candidate n)
      (move n) (query n) (candidate (n + 1))

namespace RelationalFamilyExactThread

/-- Every exact thread is automatically contained in the iterated saturation.
This is the key universal, rather than representative-based, property. -/
theorem candidate_mem_saturationAt
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (initial : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Nat → Move) (query : Nat → Query)
    (thread : RelationalFamilyExactThread ExactEdge ControlStep initial move
      query) :
    ∀ n, thread.candidate n ∈
      relationalFamilySaturationAt ExactEdge ControlStep initial move query n
  | 0 => thread.initial_mem
  | n + 1 => by
      rw [relationalFamilySaturationAt_succ]
      exact (mem_relationalFamilySaturation_iff ExactEdge ControlStep
        (relationalFamilySaturationAt ExactEdge ControlStep initial move query n)
        (move n) (query n) (thread.candidate (n + 1))).2
          ⟨thread.candidate n,
            thread.candidate_mem_saturationAt ExactEdge ControlStep initial move
              query n,
            thread.exact n⟩

end RelationalFamilyExactThread

/-- Pointwise coverage at every level of the saturation iteration. -/
def RelationalFamilySaturationRunCovered
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (initial : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Nat → Move) (query : Nat → Query) : Prop :=
  ∀ n, RelationalFamilySaturationCoverage ExactEdge ControlStep
    (relationalFamilySaturationAt ExactEdge ControlStep initial move query n)
    (move n) (query n)

/-- A covered nonempty iteration has a coherent exact thread.  This rules out
acceptance caused solely by the hidden monitor's dead fallback. -/
noncomputable def relationalFamilySaturationMemberOfCoverage
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (initial : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Nat → Move) (query : Nat → Query)
    (covered : RelationalFamilySaturationRunCovered ExactEdge ControlStep
      initial move query)
    (initialCandidate : RelationalFamilyCandidate Family Descriptor)
    (hinitial : initialCandidate ∈ initial) : (n : Nat) →
    { candidate // candidate ∈ relationalFamilySaturationAt ExactEdge
        ControlStep initial move query n }
  | 0 => ⟨initialCandidate, hinitial⟩
  | n + 1 => by
      classical
      let current := relationalFamilySaturationMemberOfCoverage ExactEdge
        ControlStep initial move query covered initialCandidate hinitial n
      let hexists := covered n current.1 current.2
      let target := Classical.choose hexists
      have htarget : RelationalFamilyCandidateGood ExactEdge ControlStep
          current.1 (move n) (query n) target :=
        Classical.choose_spec hexists
      exact ⟨target,
        (mem_relationalFamilySaturation_iff ExactEdge ControlStep
          (relationalFamilySaturationAt ExactEdge ControlStep initial move query n)
          (move n) (query n) target).2 ⟨current.1, current.2, htarget⟩⟩

@[simp] theorem relationalFamilySaturationMemberOfCoverage_zero
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (initial : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Nat → Move) (query : Nat → Query)
    (covered : RelationalFamilySaturationRunCovered ExactEdge ControlStep
      initial move query)
    (initialCandidate : RelationalFamilyCandidate Family Descriptor)
    (hinitial : initialCandidate ∈ initial) :
    (relationalFamilySaturationMemberOfCoverage ExactEdge ControlStep initial
      move query covered initialCandidate hinitial 0).1 = initialCandidate :=
  rfl

theorem relationalFamilySaturationMemberOfCoverage_succ_good
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (initial : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Nat → Move) (query : Nat → Query)
    (covered : RelationalFamilySaturationRunCovered ExactEdge ControlStep
      initial move query)
    (initialCandidate : RelationalFamilyCandidate Family Descriptor)
    (hinitial : initialCandidate ∈ initial) (n : Nat) :
    RelationalFamilyCandidateGood ExactEdge ControlStep
      (relationalFamilySaturationMemberOfCoverage ExactEdge ControlStep initial
        move query covered initialCandidate hinitial n).1
      (move n) (query n)
      (relationalFamilySaturationMemberOfCoverage ExactEdge ControlStep initial
        move query covered initialCandidate hinitial (n + 1)).1 := by
  classical
  rw [relationalFamilySaturationMemberOfCoverage]
  exact Classical.choose_spec
    (covered n
      (relationalFamilySaturationMemberOfCoverage ExactEdge ControlStep initial
        move query covered initialCandidate hinitial n).1
      (relationalFamilySaturationMemberOfCoverage ExactEdge ControlStep initial
        move query covered initialCandidate hinitial n).2)

/-- A covered nonempty iteration has a coherent exact thread.  This rules out
acceptance caused solely by the hidden monitor's dead fallback. -/
noncomputable def relationalFamilyExactThreadOfCoverage
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (initial : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Nat → Move) (query : Nat → Query)
    (covered : RelationalFamilySaturationRunCovered ExactEdge ControlStep
      initial move query)
    (initialCandidate : RelationalFamilyCandidate Family Descriptor)
    (hinitial : initialCandidate ∈ initial) :
    RelationalFamilyExactThread ExactEdge ControlStep initial move query := by
  refine {
    candidate := fun n ↦
      (relationalFamilySaturationMemberOfCoverage ExactEdge ControlStep initial
        move query covered initialCandidate hinitial n).1
    initial_mem := ?_
    exact := ?_
  }
  · exact hinitial
  · exact relationalFamilySaturationMemberOfCoverage_succ_good ExactEdge
      ControlStep initial move query covered initialCandidate hinitial

/-- The candidate-set presentation preserves universal properties of exact
threads.  The extra membership premise on the right is redundant: exactness
and initial membership force it by saturation.  Taking `Accepts` to be a DPA
parity predicate is the promised universal-parity specialization. -/
theorem relationalFamilySaturation_universal_iff
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (initial : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Nat → Move) (query : Nat → Query)
    (Accepts : (Nat → RelationalFamilyCandidate Family Descriptor) → Prop) :
    (∀ thread : RelationalFamilyExactThread ExactEdge ControlStep initial move
        query,
      Accepts thread.candidate) ↔
      ∀ candidate : Nat → RelationalFamilyCandidate Family Descriptor,
        candidate 0 ∈ initial →
        (∀ n, candidate n ∈ relationalFamilySaturationAt ExactEdge ControlStep
          initial move query n) →
        (∀ n, RelationalFamilyCandidateGood ExactEdge ControlStep
          (candidate n) (move n) (query n) (candidate (n + 1))) →
        Accepts candidate := by
  constructor
  · intro hall candidate hinitial _hmembers hedge
    exact hall {
      candidate := candidate
      initial_mem := hinitial
      exact := hedge
    }
  · intro hall thread
    exact hall thread.candidate thread.initial_mem
      (thread.candidate_mem_saturationAt ExactEdge ControlStep initial move
        query) thread.exact

/-! ## Two-fibre projection: useful but not provenance-reflecting -/

section TwoFibre

variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable [Fintype Code] [Fintype MoveIdentity]

/-- Coordinatewise union of the public two-fibre tags carried by a finite
candidate set.  The tagged set, not this projection, is the iterated state. -/
noncomputable def hiddenDescriptorCandidateFamilyUnion
    (candidates : Finset
      (RelationalFamilyCandidate
        (HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity))
        (HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)))) :
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) := by
  classical
  exact
    (candidates.biUnion fun candidate ↦ candidate.1.1,
      candidates.biUnion fun candidate ↦ candidate.1.2)

/-- A descriptor represented in one tagged candidate remains represented in
the coordinatewise public union. -/
theorem hiddenDescriptorRepresented_candidateFamilyUnion
    (candidates : Finset
      (RelationalFamilyCandidate
        (HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity))
        (HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity))))
    (candidate : RelationalFamilyCandidate
      (HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity))
      (HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)))
    (hcandidate : candidate ∈ candidates)
    (hrepresented : HiddenDescriptorRepresented D candidate.2 candidate.1) :
    HiddenDescriptorRepresented D candidate.2
      (hiddenDescriptorCandidateFamilyUnion D candidates) := by
  classical
  exact ⟨Finset.mem_biUnion.2 ⟨candidate, hcandidate, hrepresented.1⟩,
    Finset.mem_biUnion.2 ⟨candidate, hcandidate, hrepresented.2⟩⟩

/-- The converse to the preceding theorem is false already for one
descriptor: the two coordinates can be supplied by two different candidates.
This is the finite form of the forbidden rectangle/provenance inference. -/
theorem hiddenDescriptorCandidateFamilyUnion_does_not_reflect_provenance
    (descriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity)) :
    ∃ candidates : Finset
        (RelationalFamilyCandidate
          (HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity))
          (HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity))),
      HiddenDescriptorRepresented D descriptor
          (hiddenDescriptorCandidateFamilyUnion D candidates) ∧
        ¬ ∃ candidate ∈ candidates,
          candidate.2 = descriptor ∧
            HiddenDescriptorRepresented D descriptor candidate.1 := by
  classical
  let left : RelationalFamilyCandidate
      (HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity))
      (HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)) :=
    (({descriptor}, ∅), descriptor)
  let right : RelationalFamilyCandidate
      (HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity))
      (HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)) :=
    ((∅, {descriptor}), descriptor)
  refine ⟨{left, right}, ?_, ?_⟩
  · constructor <;>
      simp [hiddenDescriptorCandidateFamilyUnion, left, right]
  · rintro ⟨candidate, hcandidate, _hdescriptor, hrepresented⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcandidate
    rcases hcandidate with hleft | hright
    · rw [hleft] at hrepresented
      simpa [left] using hrepresented.2
    · rw [hright] at hrepresented
      simpa [right] using hrepresented.1

end TwoFibre

end DistributedSynthesis
