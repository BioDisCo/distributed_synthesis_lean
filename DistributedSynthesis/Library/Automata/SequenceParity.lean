/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmParityTreeEmptinessGame

/-! # Recurrence and parity of finite-range priority sequences

Extracted from the universal thread proof without changing theorem names. -/
namespace DistributedSynthesis

/-- Any sequence with finite range has a minimal infinitely-recurring value. -/
theorem natSeq_exists_min_recurring
    (s : Nat -> Nat) (hfin : (Set.range s).Finite) :
    ∃ p : Nat,
      NatSeqSeenInfinitelyOften s p ∧
        ∀ q : Nat, NatSeqSeenInfinitelyOften s q -> p ≤ q := by
  classical
  set recurring : Finset Nat :=
    hfin.toFinset.filter (fun p => NatSeqSeenInfinitelyOften s p)
    with hrecurring
  have hnonempty : recurring.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hbound : ∀ p : Nat,
        ∃ n : Nat, p ∈ hfin.toFinset -> ∀ k : Nat, n ≤ k -> s k ≠ p := by
      intro p
      by_cases hp : p ∈ hfin.toFinset
      · have hnotrec : ¬ NatSeqSeenInfinitelyOften s p := by
          intro hrec
          have hmem : p ∈ recurring := Finset.mem_filter.mpr ⟨hp, hrec⟩
          rw [hempty] at hmem
          exact absurd hmem (Finset.notMem_empty p)
        rw [NatSeqSeenInfinitelyOften] at hnotrec
        push Not at hnotrec
        rcases hnotrec with ⟨n, hn⟩
        exact ⟨n, fun _ k hk => hn k hk⟩
      · exact ⟨0, fun hp' => absurd hp' hp⟩
    choose cutoff hcutoff using hbound
    have hmem : s (hfin.toFinset.sup cutoff) ∈ hfin.toFinset :=
      hfin.mem_toFinset.mpr ⟨hfin.toFinset.sup cutoff, rfl⟩
    exact hcutoff (s (hfin.toFinset.sup cutoff)) hmem
      (hfin.toFinset.sup cutoff) (Finset.le_sup hmem) rfl
  refine ⟨recurring.min' hnonempty, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (recurring.min'_mem hnonempty)).2
  · intro q hq
    have hqmem : q ∈ recurring := by
      rcases hq 0 with ⟨k, _, hk⟩
      exact Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr ⟨k, hk⟩, hq⟩
    exact recurring.min'_le q hqmem

/-- Parity dichotomy for sequences with finite range. -/
theorem natSeqMinEvenParity_or_minOddParity
    (s : Nat -> Nat) (hfin : (Set.range s).Finite) :
    NatSeqMinEvenParity s ∨ NatSeqMinOddParity s := by
  rcases natSeq_exists_min_recurring s hfin with ⟨p, hseen, hmin⟩
  by_cases hpEven : DetParityAutomaton.NatEven p
  · exact Or.inl ⟨p, hpEven, hseen, hmin⟩
  · exact Or.inr ⟨p, hpEven, hseen, hmin⟩

/-- The minimal recurring value eventually bounds the sequence from below. -/
theorem natSeq_eventually_ge_of_min_recurring
    (s : Nat -> Nat) (hfin : (Set.range s).Finite)
    {p : Nat}
    (hmin : ∀ q : Nat, NatSeqSeenInfinitelyOften s q -> p ≤ q) :
    ∃ N : Nat, ∀ k : Nat, N ≤ k -> p ≤ s k := by
  classical
  have hsmall : ∀ v : Nat,
      ∃ n : Nat, v < p -> ∀ k : Nat, n ≤ k -> s k ≠ v := by
    intro v
    by_cases hvp : v < p
    · have hnotrec : ¬ NatSeqSeenInfinitelyOften s v := by
        intro hrec
        exact absurd (hmin v hrec) (by omega)
      rw [NatSeqSeenInfinitelyOften] at hnotrec
      push Not at hnotrec
      rcases hnotrec with ⟨n, hn⟩
      exact ⟨n, fun _ k hk => hn k hk⟩
    · exact ⟨0, fun hvp' => absurd hvp' hvp⟩
  choose cutoff hcutoff using hsmall
  refine ⟨hfin.toFinset.sup cutoff, ?_⟩
  intro k hk
  by_contra hlt
  push Not at hlt
  have hmem : s k ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨k, rfl⟩
  exact hcutoff (s k) hlt k (le_trans (Finset.le_sup hmem) hk) rfl

end DistributedSynthesis
