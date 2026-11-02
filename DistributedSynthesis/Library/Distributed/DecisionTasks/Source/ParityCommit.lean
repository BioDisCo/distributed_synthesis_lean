/- Extracted from consensusLTL/lean/ConsensusLTL/ParityCommit.lean.
Only decision-task dependencies are retained; see ../SOURCE.md. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Model
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Parity

-- Preserve the source section contexts on Lean 4.30.
set_option linter.unusedSectionVars false

namespace DistributedSynthesis.DecisionTasks.Source

open DistributedSynthesis.DecisionTasks.Source.FiniteParity

theorem exists_infOften_of_bounded {c : ℕ → ℕ} {M : ℕ} (h : ∀ n, c n ≤ M) :
    ∃ d, InfOften fun n => c n = d := by
  classical
  by_contra hcon
  push Not at hcon
  have hN : ∀ d, ∃ N, ∀ n, N ≤ n → c n ≠ d := fun d => (not_infOften _).mp (hcon d)
  choose N hNspec using hN
  set B := (Finset.range (M + 1)).sup N with hB
  have hle : N (c B) ≤ B := by
    refine Finset.le_sup (f := N) ?_
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (h B))
  exact hNspec (c B) B hle rfl

theorem exists_least_infOften {c : ℕ → ℕ} {M : ℕ} (h : ∀ n, c n ≤ M) :
    ∃ d, InfOften (fun n => c n = d) ∧ ∀ e, InfOften (fun n => c n = e) → d ≤ e := by
  classical
  obtain ⟨d, hd⟩ := exists_infOften_of_bounded h
  have hex : ∃ d, InfOften fun n => c n = d := ⟨d, hd⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun e he => ?_⟩
  by_contra hlt
  exact Nat.find_min hex (Nat.lt_of_not_le hlt) he

/-- Exactly one player wins a bounded priority sequence. -/
theorem colourWins_exists {c : ℕ → ℕ} {M : ℕ} (h : ∀ n, c n ≤ M) : ∃ p, ColourWins c p := by
  classical
  obtain ⟨d, hd, hmin⟩ := exists_least_infOften h
  exact ⟨decide (d % 2 = 1), d, ⟨hd, hmin⟩, rfl⟩

theorem colourWins_unique {c : ℕ → ℕ} {p q : Bool} (hp : ColourWins c p)
    (hq : ColourWins c q) : p = q := by
  obtain ⟨d, ⟨hd, hdm⟩, rfl⟩ := hp
  obtain ⟨e, ⟨he, hem⟩, rfl⟩ := hq
  rw [le_antisymm (hdm e he) (hem d hd)]

theorem colourWins_not {c : ℕ → ℕ} {M : ℕ} (h : ∀ n, c n ≤ M) :
    ¬ ColourWins c false ↔ ColourWins c true := by
  constructor
  · intro hn
    obtain ⟨p, hp⟩ := colourWins_exists h
    cases p
    · exact absurd hp hn
    · exact hp
  · intro ht hf
    exact Bool.false_ne_true (colourWins_unique hf ht)

/-- Shifting all priorities by one swaps the winner. -/
theorem colourWins_succ {c : ℕ → ℕ} {M : ℕ} (hbd : ∀ n, c n ≤ M) :
    ColourWins (fun n => c n + 1) false ↔ ¬ ColourWins c false := by
  classical
  obtain ⟨d, hd, hdm⟩ := exists_least_infOften hbd
  have hd1 : InfOften fun n => c n + 1 = d + 1 := by
    intro K
    obtain ⟨n, hn, hp⟩ := hd K
    exact ⟨n, hn, by omega⟩
  have hmin1 : ∀ e, InfOften (fun n => c n + 1 = e) → d + 1 ≤ e := by
    intro e he
    have hpos : 1 ≤ e := by
      obtain ⟨n, -, hp⟩ := he 0
      omega
    have he' : InfOften fun n => c n = e - 1 := by
      intro K
      obtain ⟨n, hn, hp⟩ := he K
      exact ⟨n, hn, by omega⟩
    have := hdm _ he'
    omega
  rw [colourWins_not hbd]
  constructor
  · rintro ⟨e, ⟨he, hem⟩, hpar⟩
    have hde : e = d + 1 := le_antisymm (hem _ hd1) (hmin1 e he)
    subst hde
    refine ⟨d, ⟨hd, hdm⟩, ?_⟩
    have h0 : ¬ ((d + 1) % 2 = 1) := by simpa using hpar
    have h1 : d % 2 = 1 := by omega
    simp [h1]
  · rintro ⟨e, ⟨he, hem⟩, hpar⟩
    have hed : e = d := le_antisymm (hem _ hd) (hdm _ he)
    subst hed
    refine ⟨e + 1, ⟨hd1, hmin1⟩, ?_⟩
    have h1 : e % 2 = 1 := by simpa using hpar
    have h2 : ¬ ((e + 1) % 2 = 1) := by omega
    simp [h2]

/-- Being the least recurring value is a tail bound plus recurrence. -/
theorem least_infOften_iff {c : ℕ → ℕ} {M d : ℕ} (hbd : ∀ n, c n ≤ M) :
    (InfOften (fun n => c n = d) ∧ ∀ e, InfOften (fun n => c n = e) → d ≤ e) ↔
      (InfOften (fun n => c n = d) ∧ ∃ N, ∀ n, N ≤ n → d ≤ c n) := by
  classical
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h e he => ?_⟩
  · have hfin : ∀ e, e < d → ∃ N, ∀ n, N ≤ n → c n ≠ e := by
      intro e hed
      refine (not_infOften _).mp fun hI => ?_
      exact absurd (h e hI) (by omega)
    choose N hN using hfin
    refine ⟨(Finset.range d).attach.sup fun e => N e.1 (Finset.mem_range.mp e.2), fun n hn => ?_⟩
    by_contra hlt
    push Not at hlt
    have hmem : c n ∈ Finset.range d := Finset.mem_range.mpr hlt
    have hle : N (c n) hlt ≤ n := by
      refine le_trans ?_ hn
      exact Finset.le_sup (f := fun e : {x // x ∈ Finset.range d} =>
        N e.1 (Finset.mem_range.mp e.2)) (Finset.mem_attach _ ⟨c n, hmem⟩)
    exact hN (c n) hlt n hle rfl
  · obtain ⟨N, hN⟩ := h
    obtain ⟨n, hn, hp⟩ := he N
    rw [← hp]
    exact hN n hn

theorem colourWins_zeroOne {f : ℕ → Bool} :
    ColourWins (fun n => if f n then 0 else 1) false ↔ ∀ K, ∃ n, K ≤ n ∧ f n = true := by
  classical
  have hzero : InfOften (fun n => (if f n then 0 else 1) = 0) ↔ ∀ K, ∃ n, K ≤ n ∧ f n = true := by
    constructor
    · intro h K
      obtain ⟨n, hn, hp⟩ := h K
      refine ⟨n, hn, ?_⟩
      by_cases hz : f n = true
      · exact hz
      · have hp' : (if f n = true then 0 else 1) = 0 := hp
        rw [if_neg hz] at hp'
        exact absurd hp' (by omega)
    · intro h K
      obtain ⟨n, hn, hz⟩ := h K
      refine ⟨n, hn, ?_⟩
      show (if f n = true then 0 else 1) = 0
      rw [if_pos hz]
  constructor
  · rintro ⟨d, ⟨hd, hdm⟩, hpar⟩
    refine hzero.mp ?_
    have h01 : InfOften (fun n => (if f n then 0 else 1) = 0) ∨
        InfOften (fun n => (if f n then 0 else 1) = 1) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨K0, h0⟩ := (not_infOften _).mp hcon.1
      obtain ⟨K1, h1⟩ := (not_infOften _).mp hcon.2
      set n := max K0 K1 with hn
      by_cases hz : f n = true
      · exact h0 n (le_max_left _ _) (show (if f n = true then 0 else 1) = 0 by rw [if_pos hz])
      · exact h1 n (le_max_right _ _) (show (if f n = true then 0 else 1) = 1 by rw [if_neg hz])
    have hdle : d ≤ 1 := by
      rcases h01 with h | h
      · exact le_trans (hdm 0 h) (Nat.zero_le 1)
      · exact hdm 1 h
    have hd0 : d = 0 := by
      have : d % 2 ≠ 1 := by
        intro hc
        rw [decide_eq_false_iff_not] at hpar
        exact hpar hc
      omega
    rw [hd0] at hd
    exact hd
  · intro hz
    exact ⟨0, ⟨hzero.mpr hz, fun e _ => Nat.zero_le e⟩, rfl⟩

theorem colourWins_oneTwo {f : ℕ → Bool} :
    ColourWins (fun n => if f n then 2 else 1) false ↔ ∃ N, ∀ n, N ≤ n → f n = true := by
  classical
  have hone : InfOften (fun n => (if f n then 2 else 1) = 1) ↔ ¬ ∃ N, ∀ n, N ≤ n → f n = true := by
    rw [not_exists]
    constructor
    · intro h N hN
      obtain ⟨n, hn, hp⟩ := h N
      have hp' : (if f n = true then 2 else 1) = 1 := hp
      by_cases hz : f n = true
      · rw [if_pos hz] at hp'; exact absurd hp' (by omega)
      · exact hz (hN n hn)
    · intro h K
      have hk := h K
      push Not at hk
      obtain ⟨n, hn, hz⟩ := hk
      refine ⟨n, hn, ?_⟩
      show (if f n = true then 2 else 1) = 1
      rw [if_neg (by simpa using hz)]
  constructor
  · rintro ⟨d, ⟨hd, hdm⟩, hpar⟩
    by_contra hcon
    have h1 : InfOften (fun n => (if f n then 2 else 1) = 1) := hone.mpr hcon
    have hd1 : d ≤ 1 := hdm 1 h1
    have hodd : d % 2 ≠ 1 := by
      intro hc
      rw [decide_eq_false_iff_not] at hpar
      exact hpar hc
    have hd0 : d = 0 := by omega
    rw [hd0] at hd
    obtain ⟨n, -, hp⟩ := hd 0
    have hp' : (if f n = true then 2 else 1) = 0 := hp
    by_cases hz : f n = true
    · rw [if_pos hz] at hp'; exact absurd hp' (by omega)
    · rw [if_neg hz] at hp'; exact absurd hp' (by omega)
  · intro hev
    refine ⟨2, ⟨?_, ?_⟩, rfl⟩
    · obtain ⟨N, hN⟩ := hev
      intro K
      refine ⟨max N K, le_max_right _ _, ?_⟩
      show (if f (max N K) = true then 2 else 1) = 2
      rw [if_pos (hN _ (le_max_left _ _))]
    · intro e he
      by_contra hlt
      push Not at hlt
      interval_cases e
      · obtain ⟨n, -, hp⟩ := he 0
        have hp' : (if f n = true then 2 else 1) = 0 := hp
        by_cases hz : f n = true
        · rw [if_pos hz] at hp'; exact absurd hp' (by omega)
        · rw [if_neg hz] at hp'; exact absurd hp' (by omega)
      · exact (hone.mp he) hev

/-- The counter waits for `c false`, then for `c true`, and wraps. -/
structure RoundRobin (c : Bool → ℕ → Bool) (rr : ℕ → Bool) (fired : ℕ → Bool) : Prop where
  step : ∀ n, rr (n + 1) = (if c (rr n) n then !rr n else rr n)
  fire : ∀ n, fired n = (c (rr n) n && rr n)

/-- A flag that is false at `K` and true at `n` flips somewhere in between. -/
theorem exists_flip {rr : ℕ → Bool} {K : ℕ} (hK : rr K = false) :
    ∀ n, K ≤ n → rr n = true → ∃ j, K ≤ j ∧ j < n ∧ rr j = false ∧ rr (j + 1) = true := by
  intro n
  induction n with
  | zero =>
      intro hKn hn
      have hK0 : K = 0 := by omega
      rw [hK0] at hK
      rw [hK] at hn
      exact absurd hn (by simp)
  | succ m ih =>
      intro hKn hn
      have hKm : K ≤ m := by
        rcases Nat.lt_or_ge m K with h' | h'
        · exfalso
          have hKe : K = m + 1 := by omega
          rw [hKe] at hK
          rw [hK] at hn
          exact absurd hn (by simp)
        · exact h'
      by_cases hm : rr m = true
      · obtain ⟨j, hj1, hj2, hj3, hj4⟩ := ih hKm hm
        exact ⟨j, hj1, by omega, hj3, hj4⟩
      · rw [Bool.not_eq_true] at hm
        exact ⟨m, hKm, Nat.lt_succ_self m, hm, hn⟩

/-- If the wrap recurs then both obligations recur. -/
theorem RoundRobin.of_fired {c : Bool → ℕ → Bool} {rr : ℕ → Bool} {fired : ℕ → Bool}
    (h : RoundRobin c rr fired) (hf : ∀ K, ∃ n, K ≤ n ∧ fired n = true) :
    ∀ i, ∀ K, ∃ n, K ≤ n ∧ c i n = true := by
  have hwrap : ∀ m, fired m = true → rr m = true ∧ c true m = true := by
    intro m hm
    have hfm : (c (rr m) m && rr m) = true := (h.fire m).symm.trans hm
    rw [Bool.and_eq_true] at hfm
    have hrm : rr m = true := hfm.2
    refine ⟨hrm, ?_⟩
    have := hfm.1
    rwa [hrm] at this
  intro i K
  cases i
  · -- after a wrap the counter is `false`, and it must flip back before the next wrap
    obtain ⟨m, hm, hfm⟩ := hf K
    obtain ⟨hrm, hcm⟩ := hwrap m hfm
    have hnext : rr (m + 1) = false := by
      have hc : c (rr m) m = true := by rw [hrm]; exact hcm
      rw [h.step m, if_pos hc, hrm]
      rfl
    obtain ⟨n, hn, hfn⟩ := hf (m + 1)
    obtain ⟨hrn, -⟩ := hwrap n hfn
    obtain ⟨j, hj1, -, hj3, hj4⟩ := exists_flip hnext n hn hrn
    refine ⟨j, by omega, ?_⟩
    have hstep := h.step j
    rw [hj4, hj3] at hstep
    by_cases hcj : c false j = true
    · exact hcj
    · rw [Bool.not_eq_true] at hcj
      rw [hcj] at hstep
      exact absurd hstep (by simp)
  · obtain ⟨n, hn, hfn⟩ := hf K
    exact ⟨n, hn, (hwrap n hfn).2⟩

/-- A flag that is true at `K` and false at `n` flips down somewhere in between. -/
theorem exists_flip_down {rr : ℕ → Bool} {K : ℕ} (hK : rr K = true) :
    ∀ n, K ≤ n → rr n = false → ∃ j, K ≤ j ∧ j < n ∧ rr j = true ∧ rr (j + 1) = false := by
  intro n hn hrn
  obtain ⟨j, h1, h2, h3, h4⟩ :=
    exists_flip (rr := fun m => !rr m) (by simp [hK]) n hn (by simp [hrn])
  exact ⟨j, h1, h2, by simpa using h3, by simpa using h4⟩

/-- **The converse of `RoundRobin.of_fired`.**  If both components recur then so does the wrap.
The counter cannot be stuck: it points at one component and flips as soon as that one fires, so a
stretch on which the wrap never fires would have to be a stretch on which the component the counter
points at never fires. -/
theorem RoundRobin.fired_of {c : Bool → ℕ → Bool} {rr : ℕ → Bool} {fired : ℕ → Bool}
    (h : RoundRobin c rr fired) (hc : ∀ i K, ∃ n, K ≤ n ∧ c i n = true) :
    ∀ K, ∃ n, K ≤ n ∧ fired n = true := by
  classical
  have hup : ∀ K, ∃ m, K ≤ m ∧ rr m = true := by
    intro K
    by_cases hK : rr K = true
    · exact ⟨K, le_rfl, hK⟩
    rw [Bool.not_eq_true] at hK
    obtain ⟨n, hn, hcn⟩ := hc false K
    by_cases hall : ∀ j, K ≤ j → j ≤ n → rr j = false
    · refine ⟨n + 1, by omega, ?_⟩
      have hstep := h.step n
      rw [hall n hn le_rfl] at hstep
      rw [hstep, hcn]
      rfl
    · simp only [not_forall, Bool.not_eq_false] at hall
      obtain ⟨j, hj1, hj2, hj3⟩ := hall
      exact ⟨j, hj1, by simpa using hj3⟩
  intro K
  obtain ⟨m, hm, hrm⟩ := hup K
  obtain ⟨n, hn, hcn⟩ := hc true m
  by_cases hall : ∀ j, m ≤ j → j ≤ n → rr j = true
  · refine ⟨n, le_trans hm hn, ?_⟩
    have hrn := hall n hn le_rfl
    rw [h.fire n, hrn, hcn]
    rfl
  · simp only [not_forall, Bool.not_eq_true] at hall
    obtain ⟨j, hj1, hj2, hj3⟩ := hall
    have hj3' : rr j = false := by simpa using hj3
    obtain ⟨i, hi1, hi2, hi3, hi4⟩ := exists_flip_down hrm j hj1 hj3'
    refine ⟨i, le_trans hm hi1, ?_⟩
    have hstep := h.step i
    rw [hi3, hi4] at hstep
    have hci : c true i = true := by
      by_cases hc' : c true i = true
      · exact hc'
      · rw [Bool.not_eq_true] at hc'
        rw [hc'] at hstep
        exact absurd hstep.symm (by simp)
    rw [h.fire i, hi3, hci]
    rfl

end DistributedSynthesis.DecisionTasks.Source
