/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmParityTreeEmptinessGame

/-!
# Parity pasting along block decompositions

This file proves the omega-combinatorial core of the block pasting step
of the journal construction (`paper.tex`, the epoch decomposition
feeding `thm:dynhiersynth`): the min-even parity condition of a
priority sequence is equivalent to the min-even parity condition of its
per-block minima, along any decomposition of the round indices into
consecutive finite blocks.

Blocks are given by a strictly monotone cut sequence starting at zero:
block `k` covers the interval from `cuts k` inclusive to `cuts (k + 1)`
exclusive.  The boundary game of the readback-upgrade plan emits one
priority per block, namely the block minimum, and
`natSeqMinEvenParity_cutBlockMin` transfers its parity value to the
real play.  The shift lemma `natSeqMinEvenParity_shift` handles plays
with finitely many boundaries, whose parity is decided on the infinite
tail block.

The key transfers are: a value recurring among block minima recurs in
the sequence (block minima are attained, and distinct blocks contain
distinct indices), and a value recurring in the sequence pushes some
value below it to recur among block minima (a pigeonhole descent,
`exists_le_seenInfinitelyOften_of_frequently_le`).
-/

namespace DistributedSynthesis

/-- A value below the bound recurs whenever values below the bound occur
at unboundedly large indices. -/
theorem exists_le_seenInfinitelyOften_of_frequently_le
    (f : Nat -> Nat) (bound : Nat)
    (hfrequent : ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ f k ≤ bound) :
    ∃ w : Nat, w ≤ bound ∧ NatSeqSeenInfinitelyOften f w := by
  induction bound with
  | zero =>
      refine ⟨0, Nat.le_refl 0, ?_⟩
      intro n
      rcases hfrequent n with ⟨k, hk, hfk⟩
      exact ⟨k, hk, Nat.le_zero.mp hfk⟩
  | succ bound ih =>
      by_cases hrec : NatSeqSeenInfinitelyOften f (bound + 1)
      · exact ⟨bound + 1, Nat.le_refl _, hrec⟩
      · rw [NatSeqSeenInfinitelyOften] at hrec
        push Not at hrec
        rcases hrec with ⟨N, hN⟩
        have hfrequent' : ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ f k ≤ bound := by
          intro n
          rcases hfrequent (max n N) with ⟨k, hk, hfk⟩
          refine ⟨k, Nat.le_trans (Nat.le_max_left n N) hk, ?_⟩
          have hne := hN k (Nat.le_trans (Nat.le_max_right n N) hk)
          omega
        rcases ih hfrequent' with ⟨w, hw, hwSeen⟩
        exact ⟨w, Nat.le_succ_of_le hw, hwSeen⟩

/--
Abstract parity transfer between two priority sequences: if every value
recurring in the first recurs in the second, and every value recurring
in the second dominates values of the first at unboundedly large
indices, then the two min-even parity conditions agree.  The minimal
recurring values are squeezed to be equal.
-/
theorem natSeqMinEvenParity_iff_of_recurring_transfer
    (t s : Nat -> Nat)
    (hup : ∀ w : Nat, NatSeqSeenInfinitelyOften t w ->
      NatSeqSeenInfinitelyOften s w)
    (hdown : ∀ v : Nat, NatSeqSeenInfinitelyOften s v ->
      ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ t k ≤ v) :
    NatSeqMinEvenParity t ↔ NatSeqMinEvenParity s := by
  constructor
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    refine ⟨p, hpEven, hup p hpSeen, ?_⟩
    intro q hq
    rcases
        exists_le_seenInfinitelyOften_of_frequently_le t q (hdown q hq)
      with ⟨w, hwq, hwSeen⟩
    exact Nat.le_trans (hpMin w hwSeen) hwq
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    rcases
        exists_le_seenInfinitelyOften_of_frequently_le t p (hdown p hpSeen)
      with ⟨w, hwp, hwSeen⟩
    have hwInS := hup w hwSeen
    have hweq : w = p := Nat.le_antisymm hwp (hpMin w hwInS)
    subst hweq
    refine ⟨w, hpEven, hwSeen, ?_⟩
    intro q hq
    exact hpMin q (hup q hq)

/-- The minimum of a priority sequence over the inclusive index range
from `a` to `a + n`. -/
def rangeMin (s : Nat -> Nat) (a : Nat) : Nat -> Nat
  | 0 => s a
  | n + 1 => min (rangeMin s a n) (s (a + (n + 1)))

theorem rangeMin_le (s : Nat -> Nat) (a : Nat) :
    ∀ n : Nat, ∀ i : Nat, i ≤ n -> rangeMin s a n ≤ s (a + i) := by
  intro n
  induction n with
  | zero =>
      intro i hi
      rw [Nat.le_zero.mp hi]
      exact Nat.le_refl _
  | succ n ihn =>
      intro i hi
      by_cases hcase : i ≤ n
      · exact Nat.le_trans (Nat.min_le_left _ _) (ihn i hcase)
      · have : i = n + 1 := by omega
        rw [this]
        exact Nat.min_le_right _ _

theorem rangeMin_attained (s : Nat -> Nat) (a : Nat) :
    ∀ n : Nat, ∃ i : Nat, i ≤ n ∧ rangeMin s a n = s (a + i) := by
  intro n
  induction n with
  | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ n ihn =>
      rcases ihn with ⟨i, hi, hival⟩
      rcases Nat.le_total (rangeMin s a n) (s (a + (n + 1))) with hle | hge
      · refine ⟨i, Nat.le_succ_of_le hi, ?_⟩
        rw [← hival]
        exact Nat.min_eq_left hle
      · refine ⟨n + 1, Nat.le_refl _, ?_⟩
        exact Nat.min_eq_right hge

section CutBlocks

variable {cuts : Nat -> Nat}

/-- Every index is at least its own cut value. -/
theorem le_cuts (hmono : StrictMono cuts) : ∀ k : Nat, k ≤ cuts k := by
  intro k
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hlt : cuts k < cuts (k + 1) := hmono (Nat.lt_succ_self k)
      omega

/-- The block containing a given index. -/
def cutBlock (cuts : Nat -> Nat) (n : Nat) : Nat :=
  Nat.findGreatest (fun k => cuts k ≤ n) n

theorem cuts_cutBlock_le (h0 : cuts 0 = 0) (n : Nat) :
    cuts (cutBlock cuts n) ≤ n := by
  have hzero : (fun k => cuts k ≤ n) 0 := by simp [h0]
  exact
    Nat.findGreatest_spec (P := fun k => cuts k ≤ n) (Nat.zero_le n) hzero

theorem lt_cuts_succ_cutBlock (hmono : StrictMono cuts) (n : Nat) :
    n < cuts (cutBlock cuts n + 1) := by
  by_contra hle
  push Not at hle
  have hb_le : cutBlock cuts n ≤ n := Nat.findGreatest_le n
  by_cases hcase : cutBlock cuts n + 1 ≤ n
  · exact
      Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hcase hle
  · have hlast := le_cuts hmono (cutBlock cuts n + 1)
    omega

theorem le_cutBlock (n : Nat) {m : Nat} (hm : m ≤ n) (hcut : cuts m ≤ n) :
    m ≤ cutBlock cuts n :=
  Nat.le_findGreatest hm hcut

/-- The minimum priority of block `k`. -/
def cutBlockMin (s cuts : Nat -> Nat) (k : Nat) : Nat :=
  rangeMin s (cuts k) (cuts (k + 1) - cuts k - 1)

theorem cutBlockMin_le (s : Nat -> Nat) (hmono : StrictMono cuts)
    {k j : Nat} (hlower : cuts k ≤ j) (hupper : j < cuts (k + 1)) :
    cutBlockMin s cuts k ≤ s j := by
  have hlt : cuts k < cuts (k + 1) := hmono (Nat.lt_succ_self k)
  have hbound : j - cuts k ≤ cuts (k + 1) - cuts k - 1 := by omega
  have hj : cuts k + (j - cuts k) = j := by omega
  have := rangeMin_le s (cuts k) (cuts (k + 1) - cuts k - 1)
    (j - cuts k) hbound
  rwa [hj] at this

theorem cutBlockMin_attained (s : Nat -> Nat) (hmono : StrictMono cuts)
    (k : Nat) :
    ∃ j : Nat,
      cuts k ≤ j ∧ j < cuts (k + 1) ∧ cutBlockMin s cuts k = s j := by
  have hlt : cuts k < cuts (k + 1) := hmono (Nat.lt_succ_self k)
  rcases rangeMin_attained s (cuts k) (cuts (k + 1) - cuts k - 1) with
    ⟨i, hi, hival⟩
  exact ⟨cuts k + i, by omega, by omega, hival⟩

/-- A value recurring among block minima recurs in the sequence. -/
theorem natSeqSeenInfinitelyOften_of_cutBlockMin
    (s : Nat -> Nat) (hmono : StrictMono cuts) {w : Nat}
    (hw : NatSeqSeenInfinitelyOften (cutBlockMin s cuts) w) :
    NatSeqSeenInfinitelyOften s w := by
  intro n
  rcases hw n with ⟨k, hk, hbk⟩
  rcases cutBlockMin_attained s hmono k with ⟨j, hj1, _, hjval⟩
  have hkc := le_cuts hmono k
  exact ⟨j, by omega, by rw [← hjval, hbk]⟩

/-- A value recurring in the sequence bounds block minima at unboundedly
large block indices. -/
theorem frequently_cutBlockMin_le_of_seenInfinitelyOften
    (s : Nat -> Nat) (hmono : StrictMono cuts) (h0 : cuts 0 = 0)
    {q : Nat} (hq : NatSeqSeenInfinitelyOften s q) :
    ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ cutBlockMin s cuts k ≤ q := by
  intro n
  rcases hq (cuts n) with ⟨j, hj, hsj⟩
  have hnj : n ≤ j := Nat.le_trans (le_cuts hmono n) hj
  refine ⟨cutBlock cuts j, le_cutBlock j hnj hj, ?_⟩
  rw [← hsj]
  exact
    cutBlockMin_le s hmono (cuts_cutBlock_le h0 j)
      (lt_cuts_succ_cutBlock hmono j)

/--
Parity pasting: min-even parity of a priority sequence is equivalent to
min-even parity of its per-block minima, along any strictly monotone
block decomposition starting at zero.
-/
theorem natSeqMinEvenParity_cutBlockMin
    (s : Nat -> Nat) (hmono : StrictMono cuts) (h0 : cuts 0 = 0) :
    NatSeqMinEvenParity (cutBlockMin s cuts) ↔ NatSeqMinEvenParity s := by
  constructor
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    refine
      ⟨p, hpEven, natSeqSeenInfinitelyOften_of_cutBlockMin s hmono hpSeen,
        ?_⟩
    intro q hq
    rcases
        exists_le_seenInfinitelyOften_of_frequently_le
          (cutBlockMin s cuts) q
          (frequently_cutBlockMin_le_of_seenInfinitelyOften s hmono h0 hq)
      with ⟨w, hwq, hwSeen⟩
    exact Nat.le_trans (hpMin w hwSeen) hwq
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    rcases
        exists_le_seenInfinitelyOften_of_frequently_le
          (cutBlockMin s cuts) p
          (frequently_cutBlockMin_le_of_seenInfinitelyOften s hmono h0
            hpSeen)
      with ⟨w, hwp, hwSeen⟩
    have hwInS := natSeqSeenInfinitelyOften_of_cutBlockMin s hmono hwSeen
    have hweq : w = p := Nat.le_antisymm hwp (hpMin w hwInS)
    subst hweq
    refine ⟨w, hpEven, hwSeen, ?_⟩
    intro q hq
    exact hpMin q (natSeqSeenInfinitelyOften_of_cutBlockMin s hmono hq)

end CutBlocks

section CutEnumeration

variable {B : Nat -> Prop} [DecidablePred B]

/-- The least marked index strictly after `n`. -/
def nextMarked (hinf : ∀ n : Nat, ∃ m : Nat, n < m ∧ B m) (n : Nat) : Nat :=
  Nat.find (hinf n)

theorem lt_nextMarked (hinf : ∀ n : Nat, ∃ m : Nat, n < m ∧ B m)
    (n : Nat) : n < nextMarked hinf n :=
  (Nat.find_spec (hinf n)).1

theorem marked_nextMarked (hinf : ∀ n : Nat, ∃ m : Nat, n < m ∧ B m)
    (n : Nat) : B (nextMarked hinf n) :=
  (Nat.find_spec (hinf n)).2

theorem not_marked_of_lt_nextMarked
    (hinf : ∀ n : Nat, ∃ m : Nat, n < m ∧ B m)
    {n m : Nat} (h1 : n < m) (h2 : m < nextMarked hinf n) : ¬ B m :=
  fun hB => absurd ⟨h1, hB⟩ (Nat.find_min (hinf n) h2)

/-- The enumeration of the marked indices, started at zero. -/
def cutSeq (hinf : ∀ n : Nat, ∃ m : Nat, n < m ∧ B m) : Nat -> Nat
  | 0 => 0
  | k + 1 => nextMarked hinf (cutSeq hinf k)

@[simp]
theorem cutSeq_zero (hinf : ∀ n : Nat, ∃ m : Nat, n < m ∧ B m) :
    cutSeq hinf 0 = 0 :=
  rfl

theorem cutSeq_strictMono (hinf : ∀ n : Nat, ∃ m : Nat, n < m ∧ B m) :
    StrictMono (cutSeq hinf) :=
  strictMono_nat_of_lt_succ (fun k => lt_nextMarked hinf (cutSeq hinf k))

theorem marked_cutSeq_succ (hinf : ∀ n : Nat, ∃ m : Nat, n < m ∧ B m)
    (k : Nat) : B (cutSeq hinf (k + 1)) :=
  marked_nextMarked hinf (cutSeq hinf k)

/-- No marked index lies strictly inside a block. -/
theorem not_marked_between (hinf : ∀ n : Nat, ∃ m : Nat, n < m ∧ B m)
    {k m : Nat} (h1 : cutSeq hinf k < m) (h2 : m < cutSeq hinf (k + 1)) :
    ¬ B m :=
  not_marked_of_lt_nextMarked hinf h1 h2

/-- Every positive marked index is a cut. -/
theorem cutSeq_exhaustive (hinf : ∀ n : Nat, ∃ m : Nat, n < m ∧ B m)
    {n : Nat} (hn : B n) (hpos : 0 < n) :
    ∃ k : Nat, cutSeq hinf (k + 1) = n := by
  set k := cutBlock (cutSeq hinf) n with hk
  have hlower : cutSeq hinf k ≤ n :=
    cuts_cutBlock_le (cutSeq_zero hinf) n
  have hupper : n < cutSeq hinf (k + 1) :=
    lt_cuts_succ_cutBlock (cutSeq_strictMono hinf) n
  have heq : cutSeq hinf k = n := by
    rcases Nat.lt_or_ge (cutSeq hinf k) n with hlt | hge
    · exact absurd hn (not_marked_between hinf hlt hupper)
    · omega
  cases hcase : k with
  | zero =>
      rw [hcase] at heq
      simp at heq
      omega
  | succ j =>
      rw [hcase] at heq
      exact ⟨j, heq⟩

/--
Parity pasting along the enumeration of unboundedly many marked
indices: the min-even parity of a priority sequence is decided by the
minima of the blocks between consecutive marked indices.
-/
theorem natSeqMinEvenParity_cutSeq
    (s : Nat -> Nat) (hinf : ∀ n : Nat, ∃ m : Nat, n < m ∧ B m) :
    NatSeqMinEvenParity (cutBlockMin s (cutSeq hinf)) ↔
      NatSeqMinEvenParity s :=
  natSeqMinEvenParity_cutBlockMin s (cutSeq_strictMono hinf)
    (cutSeq_zero hinf)

end CutEnumeration

/-- Recurring values are invariant under dropping a finite prefix. -/
theorem natSeqSeenInfinitelyOften_shift
    (s : Nat -> Nat) (m p : Nat) :
    NatSeqSeenInfinitelyOften (fun n => s (m + n)) p ↔
      NatSeqSeenInfinitelyOften s p := by
  constructor
  · intro hseen n
    rcases hseen n with ⟨k, hk, hsk⟩
    exact ⟨m + k, by omega, hsk⟩
  · intro hseen n
    rcases hseen (m + n) with ⟨j, hj, hsj⟩
    refine ⟨j - m, by omega, ?_⟩
    have hjm : m + (j - m) = j := by omega
    show s (m + (j - m)) = p
    rw [hjm]
    exact hsj

/-- Min-even parity is invariant under dropping a finite prefix. -/
theorem natSeqMinEvenParity_shift
    (s : Nat -> Nat) (m : Nat) :
    NatSeqMinEvenParity (fun n => s (m + n)) ↔ NatSeqMinEvenParity s := by
  constructor
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    exact
      ⟨p, hpEven, (natSeqSeenInfinitelyOften_shift s m p).mp hpSeen,
        fun q hq =>
          hpMin q ((natSeqSeenInfinitelyOften_shift s m q).mpr hq)⟩
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    exact
      ⟨p, hpEven, (natSeqSeenInfinitelyOften_shift s m p).mpr hpSeen,
        fun q hq =>
          hpMin q ((natSeqSeenInfinitelyOften_shift s m q).mp hq)⟩

/--
Reindexing a priority sequence through a round map preserves
infinitely-often occurrence: if `f t = g (roundAt t)`, the round map
tends to infinity, and hits every round, then `f` and `g` see exactly
the same priorities infinitely often.  This is the robust replacement
for a rigid `t / N` division when rounds have variable length.
-/
theorem natSeqSeenInfinitelyOften_reindex
    {f g roundAt : Nat -> Nat}
    (hval : ∀ t, f t = g (roundAt t))
    (htend : ∀ N, ∃ T, ∀ t, T ≤ t -> N ≤ roundAt t)
    (hsurj : ∀ k, ∃ t, roundAt t = k) (p : Nat) :
    NatSeqSeenInfinitelyOften f p ↔ NatSeqSeenInfinitelyOften g p := by
  constructor
  · intro hf m
    obtain ⟨T, hT⟩ := htend m
    obtain ⟨k, hk, hfk⟩ := hf T
    exact ⟨roundAt k, hT k hk, by rw [← hval k]; exact hfk⟩
  · intro hg n
    set B : Nat := (Finset.range n).sup roundAt with hB
    obtain ⟨j, hj, hgj⟩ := hg (B + 1)
    obtain ⟨k, hk⟩ := hsurj j
    have hkn : n ≤ k := by
      by_contra hlt
      push Not at hlt
      have hle : roundAt k ≤ B := by
        rw [hB]
        exact Finset.le_sup (Finset.mem_range.mpr hlt)
      omega
    exact ⟨k, hkn, by rw [hval k, hk]; exact hgj⟩

/-- The min-even parity is invariant under such a round reindexing. -/
theorem natSeqMinEvenParity_reindex
    {f g roundAt : Nat -> Nat}
    (hval : ∀ t, f t = g (roundAt t))
    (htend : ∀ N, ∃ T, ∀ t, T ≤ t -> N ≤ roundAt t)
    (hsurj : ∀ k, ∃ t, roundAt t = k) :
    NatSeqMinEvenParity f ↔ NatSeqMinEvenParity g := by
  constructor
  · rintro ⟨q, hqEven, hqSeen, hqMin⟩
    exact
      ⟨q, hqEven,
        (natSeqSeenInfinitelyOften_reindex hval htend hsurj q).mp hqSeen,
        fun r hr =>
          hqMin r
            ((natSeqSeenInfinitelyOften_reindex hval htend hsurj r).mpr
              hr)⟩
  · rintro ⟨q, hqEven, hqSeen, hqMin⟩
    exact
      ⟨q, hqEven,
        (natSeqSeenInfinitelyOften_reindex hval htend hsurj q).mpr hqSeen,
        fun r hr =>
          hqMin r
            ((natSeqSeenInfinitelyOften_reindex hval htend hsurj r).mp
              hr)⟩

end DistributedSynthesis
