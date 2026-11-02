/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderProgressRealization
import Mathlib.SetTheory.Ordinal.Rank

/-! Ordinal progress obtained from acceptance of every branch of a strategy
tree. In particular, progress is proved here rather than assumed as an extra
condition on a realizing strategy. Priorities are measured at source nodes. -/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis

/-- A nonempty tree segment stays above `p` and visits `p`. The arguments
are reversed so that extension along a branch is descent in this relation. -/
def PrioritySegment {E : Type} (priority : List E → Nat) (p : Nat)
    (target source : List E) : Prop :=
  source.IsPrefix target ∧ source.length < target.length ∧
    (∀ n, source.length ≤ n → n < target.length → p ≤ priority (target.take n)) ∧
    ∃ n, source.length ≤ n ∧ n < target.length ∧ priority (target.take n) = p

/-- Every round beyond the first cut belongs to a unique finite interval
between consecutive cuts. Only existence is needed below. -/
theorem exists_cut_interval (cuts : Nat → Nat) (strict : StrictMono cuts)
    (n : Nat) (after : cuts 0 ≤ n) :
    ∃ k, cuts k ≤ n ∧ n < cuts (k + 1) := by
  have ex : ∃ k, n < cuts k := ⟨n+1, lt_of_lt_of_le (Nat.lt_succ_self n) (strict.id_le _)⟩
  let j := Nat.find ex
  have hj : n < cuts j := Nat.find_spec ex
  have positive : 0 < j := by
    by_contra bad
    have zero : j = 0 := by omega
    rw [zero] at hj
    omega
  refine ⟨j-1, ?_, ?_⟩
  · have := Nat.find_min ex (show j-1 < j by omega)
    omega
  · simpa only [Nat.sub_add_cancel positive] using hj

/-- If every infinite branch is accepting, an odd-priority segment relation
has no infinite descending chain. This supplies the ranks used for folding. -/
theorem prioritySegment_wellFounded {E : Type} (priority : List E → Nat)
    (winning : ∀ word : Nat → E, NatSeqMinEvenParity (fun n => priority (branchNode word n)))
    (p : Nat) (odd : ¬ DetParityAutomaton.NatEven p) :
    WellFounded (PrioritySegment priority p) := by
  apply wellFounded_iff_isEmpty_descending_chain.mpr
  refine ⟨?_⟩
  rintro ⟨hist, steps⟩
  have strict : StrictMono (fun n => (hist n).length) :=
    strictMono_nat_of_lt_succ (fun n => (steps n).2.1)
  obtain ⟨word, exactHistory⟩ := exists_word_of_prefix_chain hist strict (fun n => (steps n).1)
  have exactPrefix : ∀ k n, n ≤ (hist k).length →
      (hist k).take n = branchNode word n := by
    intro k n within
    rw [← exactHistory k, ← branchNode_eq_ofFn]
    exact take_branchNode word n _ within
  have seen : NatSeqSeenInfinitelyOften (fun n => priority (branchNode word n)) p := by
    intro n
    obtain ⟨j, lower, upper, eq⟩ := (steps n).2.2.2
    exact ⟨j, le_trans (strict.id_le n) lower, by
      rwa [exactPrefix (n+1) j (Nat.le_of_lt upper)] at eq⟩
  have lower : ∀ n, (hist 0).length ≤ n → p ≤ priority (branchNode word n) := by
    intro n after
    obtain ⟨k, lo, hi⟩ := exists_cut_interval (fun k => (hist k).length) strict n after
    have bound := (steps k).2.2.1 n lo hi
    rwa [exactPrefix (k+1) n (Nat.le_of_lt hi)] at bound
  obtain ⟨q, even, recurring, minimal⟩ := winning word
  have qp := minimal p seen
  obtain ⟨n, after, atq⟩ := recurring (hist 0).length
  have pq := lower n after
  dsimp only at atq
  rw [atq] at pq
  exact odd ((Nat.le_antisymm pq qp) ▸ even)

/-- Prepending a segment whose priorities are all at least `p` preserves
the property of later reaching `p`. -/
theorem PrioritySegment.prepend {E : Type} {priority : List E → Nat} {p : Nat}
    {source middle target : List E} (pref : source.IsPrefix middle)
    (lower : ∀ n, source.length ≤ n → n < middle.length → p ≤ priority (middle.take n))
    (segment : PrioritySegment priority p target middle) :
    PrioritySegment priority p target source := by
  have takes : ∀ n, n ≤ middle.length → middle.take n = target.take n := by
    intro n le
    obtain ⟨suffix, eq⟩ := segment.1
    rw [← eq, List.take_append_of_le_length le]
  refine ⟨pref.trans segment.1, lt_of_le_of_lt pref.length_le segment.2.1, ?_, ?_⟩
  · intro n lo hi
    by_cases before : n < middle.length
    · rw [← takes n (Nat.le_of_lt before)]
      exact lower n lo before
    · exact segment.2.2.1 n (by omega) hi
  · obtain ⟨n, lo, hi, eq⟩ := segment.2.2.2
    exact ⟨n, le_trans pref.length_le lo, hi, eq⟩

noncomputable def segmentRank {E : Type} (priority : List E → Nat)
    (p : Nat) (wf : WellFounded (PrioritySegment priority p)) (h : List E) : Ordinal :=
  letI : IsWellFounded (List E) (PrioritySegment priority p) := ⟨wf⟩
  IsWellFounded.rank (PrioritySegment priority p) h

theorem segmentRank_le {E : Type} (priority : List E → Nat) (p : Nat)
    (wf : WellFounded (PrioritySegment priority p)) {source target : List E}
    (pref : source.IsPrefix target)
    (lower : ∀ n, source.length ≤ n → n < target.length → p ≤ priority (target.take n)) :
    segmentRank priority p wf target ≤ segmentRank priority p wf source := by
  letI : IsWellFounded (List E) (PrioritySegment priority p) := ⟨wf⟩
  change IsWellFounded.rank (PrioritySegment priority p) target ≤
    IsWellFounded.rank (PrioritySegment priority p) source
  rw [IsWellFounded.rank_eq (PrioritySegment priority p) target]
  apply Ordinal.iSup_le
  intro endpoint
  apply Order.succ_le_of_lt
  exact IsWellFounded.rank_lt_of_rel (endpoint.2.prepend pref lower)

theorem segmentRank_lt {E : Type} (priority : List E → Nat) (p : Nat)
    (wf : WellFounded (PrioritySegment priority p)) {source target : List E}
    (segment : PrioritySegment priority p target source) :
    segmentRank priority p wf target < segmentRank priority p wf source := by
  letI : IsWellFounded (List E) (PrioritySegment priority p) := ⟨wf⟩
  exact IsWellFounded.rank_lt_of_rel segment

end Characterisation.PeriodicBlocks
