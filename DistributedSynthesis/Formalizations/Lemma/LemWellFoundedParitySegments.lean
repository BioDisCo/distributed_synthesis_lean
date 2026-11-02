/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSharedParityProgress
import Mathlib.SetTheory.Ordinal.Rank

/-!
# Constructing shared parity ranks from well-founded odd segments

For an odd cutoff `p`, an odd segment follows zero or more edges whose source
priorities are at least `p`, then takes an edge with source priority exactly
`p`. The relation is written backwards: the segment's endpoint is below its
start. An infinite descending chain would concatenate to a run seeing `p`
infinitely often and never seeing a smaller priority.

Well-foundedness of these relations constructs an ordinal progress family.
Conversely, any shared progress family in a well-founded linear order makes
all these segment relations well-founded. Thus the progress condition has an
exact relational characterization; it is not an assumed finite countdown.
-/

namespace DistributedSynthesis
namespace DetParityAutomaton

universe u v c

variable {Alphabet : Type u} (A : DetParityAutomaton.{u, v} Alphabet)
variable {Context : Type c} (objective : Context → A.State)
variable (edge : Context → Context → Prop)

/-- A finite segment with no smaller source priority and a final source
priority equal to the cutoff. The endpoint is the first relation argument. -/
def OddPrioritySegment (p : Nat) (target source : Context) : Prop :=
  ∃ last,
    Relation.ReflTransGen
      (fun a b ↦ edge a b ∧ p ≤ A.priority (objective a)) source last ∧
    A.priority (objective last) = p ∧ edge last target

theorem OddPrioritySegment.prepend
    {p : Nat} {source middle target : Context}
    (hfirst : edge source middle)
    (hlower : p ≤ A.priority (objective source))
    (hsegment : OddPrioritySegment A objective edge p target middle) :
    OddPrioritySegment A objective edge p target source := by
  obtain ⟨last, hpath, hpriority, hlast⟩ := hsegment
  exact ⟨last, hpath.head ⟨hfirst, hlower⟩, hpriority, hlast⟩

theorem OddPrioritySegment.single
    {p : Nat} {source target : Context}
    (hfirst : edge source target)
    (hpriority : A.priority (objective source) = p) :
    OddPrioritySegment A objective edge p target source :=
  ⟨source, .refl, hpriority, hfirst⟩

noncomputable def oddPrioritySegmentRank (p : Nat)
    (hwf : WellFounded (OddPrioritySegment A objective edge p))
    (source : Context) : Ordinal.{c} :=
  letI : IsWellFounded Context (OddPrioritySegment A objective edge p) := ⟨hwf⟩
  IsWellFounded.rank (OddPrioritySegment A objective edge p) source

/-- Prepending an allowed edge includes every odd-segment successor cone
of the target in that of the source, so the ordinal rank cannot increase. -/
theorem oddPrioritySegmentRank_nonincrease
    (p : Nat) (hwf : WellFounded (OddPrioritySegment A objective edge p))
    {source target : Context} (hedge : edge source target)
    (hlower : p ≤ A.priority (objective source)) :
    oddPrioritySegmentRank A objective edge p hwf target ≤
      oddPrioritySegmentRank A objective edge p hwf source := by
  letI : IsWellFounded Context (OddPrioritySegment A objective edge p) := ⟨hwf⟩
  change IsWellFounded.rank (OddPrioritySegment A objective edge p) target ≤
    IsWellFounded.rank (OddPrioritySegment A objective edge p) source
  rw [IsWellFounded.rank_eq (OddPrioritySegment A objective edge p) target]
  apply Ordinal.iSup_le
  intro endpoint
  apply Order.succ_le_of_lt
  exact IsWellFounded.rank_lt_of_rel
    (endpoint.2.prepend A objective edge hedge hlower)

/-- At the cutoff itself, a single operational edge is already an odd
segment, hence causes a strict rank decrease. -/
theorem oddPrioritySegmentRank_decrease
    (p : Nat) (hwf : WellFounded (OddPrioritySegment A objective edge p))
    {source target : Context} (hedge : edge source target)
    (hpriority : A.priority (objective source) = p) :
    oddPrioritySegmentRank A objective edge p hwf target <
      oddPrioritySegmentRank A objective edge p hwf source := by
  letI : IsWellFounded Context (OddPrioritySegment A objective edge p) := ⟨hwf⟩
  exact IsWellFounded.rank_lt_of_rel
    (OddPrioritySegment.single A objective edge hedge hpriority)

/-- Canonical construction of one ordinal certificate for the entire
transition relation, including all replacement edges. -/
noncomputable def sharedParityProgressOfWellFoundedSegments
    (hwf : ∀ p, ¬ NatEven p → WellFounded (OddPrioritySegment A objective edge p)) :
    SharedParityProgress A objective edge Ordinal.{c} := by
  classical
  refine {
    rank := fun p source ↦ if hp : NatEven p then 0
      else oddPrioritySegmentRank A objective edge p (hwf p hp) source
    nonincrease := ?_
    decrease := ?_ }
  · intro p hodd source target hedge hlower
    simp only [dif_neg hodd]
    exact oddPrioritySegmentRank_nonincrease A objective edge p (hwf p hodd)
      hedge hlower
  · intro p hodd source target hedge heq
    simp only [dif_neg hodd]
    exact oddPrioritySegmentRank_decrease A objective edge p (hwf p hodd)
      hedge heq

/-- Every odd segment strictly decreases any shared progress certificate. -/
theorem SharedParityProgress.decrease_segment
    {Rank : Type*} [LinearOrder Rank]
    (certificate : SharedParityProgress A objective edge Rank)
    {p : Nat} (hodd : ¬ NatEven p) {source target : Context}
    (hsegment : OddPrioritySegment A objective edge p target source) :
    certificate.rank p target < certificate.rank p source := by
  obtain ⟨last, hpath, hpriority, hlast⟩ := hsegment
  have hle : certificate.rank p last ≤ certificate.rank p source := by
    clear hpriority hlast
    induction hpath with
    | refl => exact le_rfl
    | tail hpath hstep ih =>
      exact le_trans (certificate.nonincrease p hodd _ _ hstep.1 hstep.2) ih
  exact lt_of_lt_of_le (certificate.decrease p hodd _ _ hlast hpriority) hle

/-- In particular, existence of a shared certificate never conceals an
infinite chain of postponed odd-priority obligations. -/
theorem SharedParityProgress.wellFounded_segments
    {Rank : Type*} [LinearOrder Rank] [WellFoundedLT Rank]
    (certificate : SharedParityProgress A objective edge Rank)
    (p : Nat) (hodd : ¬ NatEven p) :
    WellFounded (OddPrioritySegment A objective edge p) := by
  apply (InvImage.wf (fun source ↦ certificate.rank p source)
    (wellFounded_lt : WellFounded ((· < ·) : Rank → Rank → Prop))).mono
  intro target source hsegment
  exact certificate.decrease_segment A objective edge hodd hsegment

/-- Exact characterization of the shared ordinal certificate. No finite
memory or finite-rank bound is assumed or concluded. -/
theorem sharedParityProgress_ordinal_iff_wellFounded_segments :
    Nonempty (SharedParityProgress A objective edge Ordinal.{c}) ↔
      ∀ p, ¬ NatEven p → WellFounded (OddPrioritySegment A objective edge p) := by
  constructor
  · rintro ⟨certificate⟩ p hodd
    exact certificate.wellFounded_segments A objective edge p hodd
  · intro hwf
    exact ⟨sharedParityProgressOfWellFoundedSegments A objective edge hwf⟩

end DetParityAutomaton
end DistributedSynthesis
