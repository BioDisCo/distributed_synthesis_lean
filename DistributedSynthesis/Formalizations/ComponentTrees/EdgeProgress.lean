/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.LexicographicProgress

/-! The ordinal proof in the forward bounded-representation argument.

An alphabet letter here is a COMPLETE block. A node's priority labels the
incoming edge, exactly as in the draft (unlike `PrioritySegment`, which
counts source priorities). Only live branches are required to accept.
The prefix-closed domain need not be regular or finitely branching.
-/

namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation.PeriodicBlocks
noncomputable section
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

variable {E : Type}

/-- A nonempty segment of the live history tree, with incoming-edge
priorities at least `p`, and at least one occurrence of `p`. -/
def EdgeSegment (live : List E → Prop) (priority : List E → Nat) (p : Nat)
    (target source : List E) : Prop :=
  live target ∧ source.IsPrefix target ∧ source.length < target.length ∧
    (∀ n, source.length < n → n ≤ target.length → p ≤ priority (target.take n)) ∧
    ∃ n, source.length < n ∧ n ≤ target.length ∧ priority (target.take n) = p

variable (live : List E → Prop) (priority : List E → Nat)
variable (closed : ∀ h k, h.IsPrefix k → live k → live h)
variable (winning : ∀ word : Nat → E, (∀ n, live (branchNode word n)) →
  NatSeqMinEvenParity (fun n => priority (branchNode word n)))

include closed winning in
/-- An infinite descending chain concatenates to a live rejecting branch,
as in the English proof. Acceptance of nonlive branches is NOT a premise. -/
theorem edgeSegment_wellFounded (p : Nat) (odd : ¬ DetParityAutomaton.NatEven p) :
    WellFounded (EdgeSegment live priority p) := by
  apply wellFounded_iff_isEmpty_descending_chain.mpr
  refine ⟨?_⟩
  rintro ⟨hist, steps⟩
  have strict : StrictMono (fun n => (hist n).length) :=
    strictMono_nat_of_lt_succ (fun n => (steps n).2.2.1)
  obtain ⟨word, exactHistory⟩ := exists_word_of_prefix_chain hist strict (fun n => (steps n).2.1)
  have exactPrefix : ∀ k n, n ≤ (hist k).length →
      (hist k).take n = branchNode word n := by
    intro k n within
    rw [← exactHistory k, ← branchNode_eq_ofFn]
    exact take_branchNode word n _ within
  have liveWord (n : Nat) : live (branchNode word n) := by
    rw [← exactPrefix (n+1) n (by have le : n+1 ≤ (hist (n+1)).length := strict.id_le (n+1); omega)]
    exact closed _ _ (List.take_prefix _ _) (steps n).1
  have seen : NatSeqSeenInfinitelyOften (fun n => priority (branchNode word n)) p := by
    intro n
    obtain ⟨j, lower, upper, eq⟩ := (steps n).2.2.2.2
    exact ⟨j, by have le : n ≤ (hist n).length := strict.id_le n; omega,
      by rwa [exactPrefix (n+1) j upper] at eq⟩
  have lower : ∀ n, (hist 0).length + 1 ≤ n → p ≤ priority (branchNode word n) := by
    intro n after
    obtain ⟨k, lo, hi⟩ := exists_cut_interval (fun k => (hist k).length) strict (n-1)
      (by change (hist 0).length ≤ n-1; omega)
    have bound := (steps k).2.2.2.1 n (by omega) (by omega)
    rwa [exactPrefix (k+1) n (by omega)] at bound
  obtain ⟨q, even, recurring, minimal⟩ := winning word liveWord
  have qp := minimal p seen
  obtain ⟨n, after, atq⟩ := recurring ((hist 0).length+1)
  have pq := lower n after
  dsimp only at atq
  rw [atq] at pq
  exact odd ((Nat.le_antisymm pq qp) ▸ even)

omit closed winning in
theorem EdgeSegment.prepend {p : Nat} {source middle target : List E}
    (pref : source.IsPrefix middle)
    (lower : ∀ n, source.length < n → n ≤ middle.length → p ≤ priority (middle.take n))
    (segment : EdgeSegment live priority p target middle) :
    EdgeSegment live priority p target source := by
  have takes : ∀ n, n ≤ middle.length → middle.take n = target.take n := by
    intro n le
    obtain ⟨suffix, eq⟩ := segment.2.1
    rw [← eq, List.take_append_of_le_length le]
  refine ⟨segment.1, pref.trans segment.2.1,
    lt_of_le_of_lt pref.length_le segment.2.2.1, ?_, ?_⟩
  · intro n lo hi
    by_cases before : n ≤ middle.length
    · rw [← takes n before]
      exact lower n lo before
    · exact segment.2.2.2.1 n (by omega) hi
  · obtain ⟨n, lo, hi, eq⟩ := segment.2.2.2.2
    exact ⟨n, lt_of_le_of_lt pref.length_le lo, hi, eq⟩

/-- Supremum of successor ranks plus one. This is Mathlib's ordinal rank,
not an additional progress assumption. Even coordinates are fixed zeros. -/
def edgeCoordinate (p : Nat) (h : List E) : Ordinal := by
  classical
  exact if odd : ¬ DetParityAutomaton.NatEven p then
    letI : IsWellFounded (List E) (EdgeSegment live priority p) :=
      ⟨edgeSegment_wellFounded live priority closed winning p odd⟩
    IsWellFounded.rank (EdgeSegment live priority p) h
  else 0

def edgeRank (K : Nat) (h : List E) : Lex (Fin (K+1) → Ordinal) :=
  toLex (fun p => edgeCoordinate live priority closed winning p.val h)

theorem edgeRank_restrict {p K : Nat} (bound : p ≤ K) {h k : List E}
    (le : edgeRank live priority closed winning K h ≤ edgeRank live priority closed winning K k) :
    edgeRank live priority closed winning p h ≤ edgeRank live priority closed winning p k :=
  lex_restrict_le (Nat.succ_le_succ bound) _ _ le

theorem edgeCoordinate_le (p : Nat) {source target : List E}
    (pref : source.IsPrefix target)
    (lower : ∀ n, source.length < n → n ≤ target.length → p ≤ priority (target.take n)) :
    edgeCoordinate live priority closed winning p target ≤
      edgeCoordinate live priority closed winning p source := by
  unfold edgeCoordinate
  split
  · rename_i odd
    letI : IsWellFounded (List E) (EdgeSegment live priority p) :=
      ⟨edgeSegment_wellFounded live priority closed winning p odd⟩
    rw [IsWellFounded.rank_eq (EdgeSegment live priority p) target]
    apply Ordinal.iSup_le
    intro endpoint
    apply Order.succ_le_of_lt
    exact IsWellFounded.rank_lt_of_rel (endpoint.2.prepend live priority pref lower)
  · exact le_refl _

theorem edgeRank_le (p : Nat) {source target : List E}
    (pref : source.IsPrefix target)
    (lower : ∀ n, source.length < n → n ≤ target.length → p ≤ priority (target.take n)) :
    edgeRank live priority closed winning p target ≤ edgeRank live priority closed winning p source := by
  apply Pi.toLex_monotone
  intro j
  exact edgeCoordinate_le live priority closed winning j.val pref
    (fun n lo hi => le_trans (Nat.le_of_lt_succ j.isLt) (lower n lo hi))

theorem edgeRank_lt (p : Nat) (odd : ¬ DetParityAutomaton.NatEven p) {source target : List E}
    (segment : EdgeSegment live priority p target source) :
    edgeRank live priority closed winning p target < edgeRank live priority closed winning p source := by
  apply Pi.toLex_strictMono
  apply lt_of_le_of_ne
  · intro j
    exact edgeCoordinate_le live priority closed winning j.val segment.2.1
      (fun n lo hi => le_trans (Nat.le_of_lt_succ j.isLt) (segment.2.2.2.1 n lo hi))
  · intro eq
    have last := congrFun eq (Fin.last p)
    simp only [edgeCoordinate, Fin.val_last, dif_pos odd] at last
    letI : IsWellFounded (List E) (EdgeSegment live priority p) :=
      ⟨edgeSegment_wellFounded live priority closed winning p odd⟩
    exact (ne_of_lt (IsWellFounded.rank_lt_of_rel segment)) last

/-- The final contradiction in the English proof: rank-minimizing changes
of old prefixes, followed by genuine live edges, preserve parity along
EVERY compatible run, even if its prefixes change infinitely often. -/
theorem folded_edges_parity (K : Nat) (root chosen : Nat → List E) (letter : Nat → E)
    (color : Nat → Fin (K+1))
    (replace : ∀ n, edgeRank live priority closed winning K (chosen n) ≤
      edgeRank live priority closed winning K (root n))
    (next : ∀ n, root (n+1) = chosen n ++ [letter n])
    (retainedLive : ∀ n, live (root (n+1)))
    (labels : ∀ n, priority (root (n+1)) = (color n).val) :
    NatSeqMinEvenParity (fun n => (color n).val) := by
  have pref (n : Nat) : (chosen n).IsPrefix (root (n+1)) := ⟨[letter n], (next n).symm⟩
  have grows (n : Nat) : (chosen n).length < (root (n+1)).length := by simp [next]
  have only (n t : Nat) (lo : (chosen n).length < t) (hi : t ≤ (root (n+1)).length) :
      (root (n+1)).take t = root (n+1) := by
    have len : (root (n+1)).length = (chosen n).length+1 := by simp [next]
    have eq : t = (root (n+1)).length := by omega
    rw [eq, List.take_length]
  apply parity_of_progress color (fun p => Lex (Fin (p.val+1) → Ordinal))
    (fun p n => edgeRank live priority closed winning p.val (root n))
  · intro p _ n cutoff
    apply le_trans (edgeRank_le live priority closed winning p.val (pref n) ?_)
      (edgeRank_restrict live priority closed winning (Nat.le_of_lt_succ p.isLt) (replace n))
    intro t lo hi
    rw [only n t lo hi, labels]
    exact cutoff
  · intro p odd n eq
    apply lt_of_lt_of_le (edgeRank_lt live priority closed winning p.val odd ?_)
      (edgeRank_restrict live priority closed winning (Nat.le_of_lt_succ p.isLt) (replace n))
    refine ⟨retainedLive n, pref n, grows n, ?_, ?_⟩
    · intro t lo hi
      rw [only n t lo hi, labels, eq]
    · exact ⟨(root (n+1)).length, grows n, le_refl _, by rw [List.take_length, labels, eq]⟩

end
end Characterisation.ComponentTrees
