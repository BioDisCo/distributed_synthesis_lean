/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.TreeProgress
import DistributedSynthesis.Formalizations.PeriodicBlocks.Representatives
import Mathlib.Data.DFinsupp.WellFounded

/-! Lexicographic progress under repeated root replacements. A replacement
minimizes the full source rank. Each odd priority uses only the prefix of that
rank up to its own coordinate. No endpoint-rank minimization is assumed. -/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section

/-- Taking an initial segment preserves lexicographic nonincrease. -/
theorem lex_restrict_le {Rank : Type*} [LinearOrder Rank] {n m : Nat} (bound : n ≤ m)
    (a b : Fin m → Rank) (le : toLex a ≤ toLex b) :
    toLex (fun i : Fin n => a ⟨i.val, lt_of_lt_of_le i.isLt bound⟩) ≤
      toLex (fun i : Fin n => b ⟨i.val, lt_of_lt_of_le i.isLt bound⟩) := by
  rcases lt_or_eq_of_le le with lt | eq
  · obtain ⟨i, before, less⟩ := lt
    by_cases inside : i.val < n
    · apply le_of_lt
      refine ⟨⟨i.val, inside⟩, ?_, less⟩
      intro j earlier
      exact before ⟨j.val, lt_of_lt_of_le j.isLt bound⟩ earlier
    · apply le_of_eq
      apply congrArg toLex
      funext j
      exact before ⟨j.val, lt_of_lt_of_le j.isLt bound⟩ (by change j.val < i.val; omega)
  · have same : a = b := congrArg ofLex eq
    subst b
    exact le_refl _

def treeCoordinate {E : Type} (priority : List E → Nat)
    (winning : ∀ word : Nat → E, NatSeqMinEvenParity (fun n => priority (branchNode word n)))
    (p : Nat) (h : List E) : Ordinal := by
  classical
  exact if odd : ¬ DetParityAutomaton.NatEven p then
    segmentRank priority p (prioritySegment_wellFounded priority winning p odd) h
  else 0

def treeRank {E : Type} (priority : List E → Nat)
    (winning : ∀ word : Nat → E, NatSeqMinEvenParity (fun n => priority (branchNode word n)))
    (K : Nat) (h : List E) : Lex (Fin (K+1) → Ordinal) :=
  toLex (fun p => treeCoordinate priority winning p.val h)

theorem treeRank_restrict {E : Type} (priority : List E → Nat)
    (winning : ∀ word : Nat → E, NatSeqMinEvenParity (fun n => priority (branchNode word n)))
    {p K : Nat} (bound : p ≤ K) {h k : List E}
    (le : treeRank priority winning K h ≤ treeRank priority winning K k) :
    treeRank priority winning p h ≤ treeRank priority winning p k :=
  lex_restrict_le (Nat.succ_le_succ bound) _ _ le

/-- A tree segment above a cutoff cannot increase its rank prefix. -/
theorem treeRank_le {E : Type} (priority : List E → Nat)
    (winning : ∀ word : Nat → E, NatSeqMinEvenParity (fun n => priority (branchNode word n)))
    (p : Nat) {source target : List E} (pref : source.IsPrefix target)
    (lower : ∀ n, source.length ≤ n → n < target.length → p ≤ priority (target.take n)) :
    treeRank priority winning p target ≤ treeRank priority winning p source := by
  apply Pi.toLex_monotone
  intro j
  unfold treeCoordinate
  dsimp only
  split
  · apply segmentRank_le _ _ _ pref
    intro n lo hi
    exact le_trans (Nat.le_of_lt_succ j.isLt) (lower n lo hi)
  · exact le_refl _

/-- Visiting an odd cutoff makes its rank prefix strictly decrease. -/
theorem treeRank_lt {E : Type} (priority : List E → Nat)
    (winning : ∀ word : Nat → E, NatSeqMinEvenParity (fun n => priority (branchNode word n)))
    (p : Nat) (odd : ¬ DetParityAutomaton.NatEven p) {source target : List E}
    (segment : PrioritySegment priority p target source) :
    treeRank priority winning p target < treeRank priority winning p source := by
  apply Pi.toLex_strictMono
  apply lt_of_le_of_ne
  · intro j
    unfold treeCoordinate
    dsimp only
    split
    · apply segmentRank_le _ _ _ segment.1
      intro n lo hi
      exact le_trans (Nat.le_of_lt_succ j.isLt) (segment.2.2.1 n lo hi)
    · exact le_refl _
  · intro eq
    have last := congrFun eq (Fin.last p)
    simp only [treeCoordinate, Fin.val_last, dif_pos odd] at last
    exact (ne_of_lt (segmentRank_lt priority p _ segment)) last

/-- Well-founded ranks for the odd cutoffs imply parity for a finite-range
priority sequence. The rank type is allowed to depend on the cutoff. -/
theorem parity_of_progress {K : Nat} (color : Nat → Fin (K+1))
    (Rank : Fin (K+1) → Type*) [∀ p, LinearOrder (Rank p)] [∀ p, WellFoundedLT (Rank p)]
    (rank : (p : Fin (K+1)) → Nat → Rank p)
    (weak : ∀ p, ¬ DetParityAutomaton.NatEven p.val → ∀ n,
      p.val ≤ (color n).val → rank p (n+1) ≤ rank p n)
    (strict : ∀ p, ¬ DetParityAutomaton.NatEven p.val → ∀ n,
      (color n).val = p.val → rank p (n+1) < rank p n) :
    NatSeqMinEvenParity (fun n => (color n).val) := by
  let A : DetParityAutomaton (Fin (K+1)) :=
    { State := Fin (K+1), stateFinite := inferInstance, initial := color 0,
      step := fun _ c => c, priority := Fin.val }
  let word n := color (n+1)
  have run : ∀ n, A.run word n = color n := by
    intro n
    cases n <;> rfl
  have acceptance : A.Accepts word ↔ NatSeqMinEvenParity (fun n => (color n).val) := by
    rw [A.accepts_iff_natSeqMinEvenParity]
    simp only [run]
    rfl
  apply acceptance.mp
  by_contra reject
  obtain ⟨p, q, N, atq, seen, lower, odd⟩ :=
    A.exists_recurrent_runState_min_priority_not_even_and_eventually_ge_of_not_accepts word reject
  have bounded : p < K+1 := by rw [← atq]; exact q.isLt
  let j : Fin (K+1) := ⟨p, bounded⟩
  have monotone : Antitone (fun k => rank j (N+k)) := by
    apply antitone_nat_of_succ_le
    intro k
    apply weak j odd (N+k)
    simpa only [run] using lower (N+k) (by omega)
  obtain ⟨least, ⟨k, hk⟩, minimal⟩ :=
    (wellFounded_lt : WellFounded ((· < ·) : Rank j → Rank j → Prop)).has_min
      (Set.range (fun k => rank j (N+k))) ⟨rank j N, 0, by simp⟩
  obtain ⟨m, later, state⟩ := seen (N+k)
  have below : rank j m ≤ rank j (N+k) := by
    have h := monotone (show k ≤ m-N by omega)
    simpa only [Nat.add_sub_of_le (show N ≤ m by omega)] using h
  have decrease : rank j (m+1) < rank j m := strict j odd m (by
    change (color m).val = p
    rw [← run m, state]
    exact atq)
  have mem : rank j (m+1) ∈ Set.range (fun k => rank j (N+k)) :=
    ⟨m+1-N, by simp only [Nat.add_sub_of_le (by omega : N ≤ m+1)]⟩
  apply minimal _ mem
  rw [← hk]
  exact lt_of_lt_of_le decrease below

/-- Repeated root replacements preserve parity. Each block starts at a
rank-smaller substitute for the current root and follows a genuine tree
segment. Its recorded priority is the minimum on that segment. -/
theorem folded_blocks_parity {E : Type} (priority : List E → Nat)
    (winning : ∀ word : Nat → E, NatSeqMinEvenParity (fun n => priority (branchNode word n)))
    (K : Nat) (root chosen : Nat → List E) (color : Nat → Fin (K+1))
    (replace : ∀ n, treeRank priority winning K (chosen n) ≤ treeRank priority winning K (root n))
    (pref : ∀ n, (chosen n).IsPrefix (root (n+1)))
    (grows : ∀ n, (chosen n).length < (root (n+1)).length)
    (lower : ∀ n t, (chosen n).length ≤ t → t < (root (n+1)).length →
      (color n).val ≤ priority ((root (n+1)).take t))
    (attained : ∀ n, ∃ t, (chosen n).length ≤ t ∧ t < (root (n+1)).length ∧
      priority ((root (n+1)).take t) = (color n).val) :
    NatSeqMinEvenParity (fun n => (color n).val) := by
  apply parity_of_progress color (fun p => Lex (Fin (p.val+1) → Ordinal))
    (fun p n => treeRank priority winning p.val (root n))
  · intro p _ n cutoff
    apply le_trans (treeRank_le priority winning p.val (pref n) ?_)
      (treeRank_restrict priority winning (Nat.le_of_lt_succ p.isLt) (replace n))
    intro t lo hi
    exact le_trans cutoff (lower n t lo hi)
  · intro p odd n eq
    apply lt_of_lt_of_le (treeRank_lt priority winning p.val odd ?_)
      (treeRank_restrict priority winning (Nat.le_of_lt_succ p.isLt) (replace n))
    rw [← eq]
    exact ⟨pref n, grows n, lower n, attained n⟩

end
end Characterisation.PeriodicBlocks
