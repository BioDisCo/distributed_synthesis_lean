/- Extracted from consensusLTL/lean/ConsensusLTL/Colouring.lean.
Only decision-task dependencies are retained; see ../SOURCE.md. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Views
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Model

-- Preserve the source section contexts on Lean 4.30.
set_option linter.unusedSectionVars false

namespace DistributedSynthesis.DecisionTasks.Source

universe v

/-- A round as its two reception bits: `(a, b)`, `a` = `u` hears `v`, `b` = `v` hears `u`. -/
abbrev Letter := Bool × Bool

/-- Whether `p` hears in the round `g`. -/
def Letter.hears (g : Letter) (p : Bool) : Bool := if p then g.2 else g.1

/-- The round in which both hear. -/
def hearL : Letter := (true, true)

@[simp] theorem hearL_hears (p : Bool) : hearL.hears p = true := by cases p <;> rfl

open Classical in
/-- The letter of round `i` of `σ`. -/
noncomputable def letter (σ : ℕ → Event Bool) (i : ℕ) : Letter :=
  (decide (Hears U σ i), decide (Hears W σ i))

theorem letter_hears_iff {σ : ℕ → Event Bool} {i : ℕ} {p : Bool} :
    (letter σ i).hears p = true ↔ Hears p σ i := by
  cases p <;> simp [letter, Letter.hears]

theorem letter_hears_eq_false_iff {σ : ℕ → Event Bool} {i : ℕ} {p : Bool} :
    (letter σ i).hears p = false ↔ ¬ Hears p σ i := by
  rw [← letter_hears_iff]; simp

theorem letter_eq_of_hears_iff {σ τ : ℕ → Event Bool} {i : ℕ}
    (hU : Hears U σ i ↔ Hears U τ i) (hW : Hears W σ i ↔ Hears W τ i) :
    letter σ i = letter τ i := by
  classical
  simp only [letter]
  rw [decide_eq_decide.mpr hU, decide_eq_decide.mpr hW]

/-- The history of the first `n` rounds. -/
noncomputable def pre (σ : ℕ → Event Bool) (n : ℕ) : List Letter :=
  (List.range n).map (letter σ)

section Pre

variable {σ : ℕ → Event Bool}

theorem pre_succ (n : ℕ) : pre σ (n + 1) = pre σ n ++ [letter σ n] := by
  simp [pre, List.range_succ]

@[simp] theorem pre_length (n : ℕ) : (pre σ n).length = n := by simp [pre]

theorem pre_add (s k : ℕ) :
    pre σ (s + k) = pre σ s ++ (List.range k).map (fun i => letter σ (s + i)) := by
  simp [pre, List.range_add, List.map_map, Function.comp_def]

theorem mem_pre {g : Letter} {n : ℕ} : g ∈ pre σ n ↔ ∃ i, i < n ∧ letter σ i = g := by
  simp [pre]

theorem pre_eq_of_letters {τ : ℕ → Event Bool} {n : ℕ}
    (h : ∀ i, i < n → letter σ i = letter τ i) : pre σ n = pre τ n := by
  simp only [pre]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- After the last reception `s`, the history is `pre σ s`, the letter of round `s`, and the
letters since. -/
theorem pre_split {s n : ℕ} (hsn : s < n) :
    pre σ n = pre σ s ++ letter σ s :: (List.range (n - s - 1)).map (fun i => letter σ (s + 1 + i)) := by
  have hn : n = (s + 1) + (n - s - 1) := by omega
  conv_lhs => rw [hn, pre_add, pre_succ]
  simp

end Pre

/-- A base view: `none` is the initial view, `some h` the view right after hearing following
the history `h`. -/
abbrev Base := Option (List Letter)

open Classical in
/-- The base of `p` at time `n`: the history before its last reception, if any. -/
noncomputable def base (p : Bool) (σ : ℕ → Event Bool) : ℕ → Base
  | 0 => none
  | n + 1 => if Hears p σ n then some (pre σ n) else base p σ n

section Base

variable {p : Bool} {σ : ℕ → Event Bool}

@[simp] theorem base_zero : base p σ 0 = none := rfl

theorem base_succ_of_hears {n : ℕ} (h : Hears p σ n) : base p σ (n + 1) = some (pre σ n) := by
  simp [base, h]

theorem base_succ_of_not_hears {n : ℕ} (h : ¬ Hears p σ n) : base p σ (n + 1) = base p σ n := by
  simp [base, h]

theorem base_eq_of_silent_between {r : ℕ} :
    ∀ n, r ≤ n → (∀ i, r ≤ i → i < n → ¬ Hears p σ i) → base p σ n = base p σ r := by
  intro n
  induction n with
  | zero => intro hr _; rw [Nat.le_zero.mp hr]
  | succ n ih =>
      intro hr hsil
      rcases Nat.lt_or_ge r (n + 1) with hlt | hge
      · rw [base_succ_of_not_hears (hsil n (by omega) (by omega))]
        exact ih (by omega) fun i hri hin => hsil i hri (by omega)
      · rw [show r = n + 1 by omega]

theorem base_eq_none_of_silent {n : ℕ} (h : ∀ i, i < n → ¬ Hears p σ i) : base p σ n = none := by
  rw [base_eq_of_silent_between n (Nat.zero_le n) fun i _ hi => h i hi]
  rfl

/-- A base is the initial one with silence so far, or the history before the last reception. -/
theorem base_cases (n : ℕ) :
    (base p σ n = none ∧ ∀ i, i < n → ¬ Hears p σ i) ∨
    ∃ s, s < n ∧ Hears p σ s ∧ (∀ i, s < i → i < n → ¬ Hears p σ i) ∧
      base p σ n = some (pre σ s) := by
  induction n with
  | zero => exact Or.inl ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
      by_cases hn : Hears p σ n
      · exact Or.inr ⟨n, Nat.lt_succ_self n, hn, fun i h1 h2 => by omega,
          base_succ_of_hears hn⟩
      · rcases ih with ⟨hb, hsil⟩ | ⟨s, hsn, hs, hsil, hb⟩
        · refine Or.inl ⟨?_, ?_⟩
          · rw [base_succ_of_not_hears hn, hb]
          · intro i hi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
            · exact hsil i hi
            · rw [hi]; exact hn
        · refine Or.inr ⟨s, by omega, hs, ?_, ?_⟩
          · intro i h1 h2
            rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | h2
            · exact hsil i h1 h2
            · rw [h2]; exact hn
          · rw [base_succ_of_not_hears hn, hb]

end Base

/-- `j` is a possible history right before the next reception of `p` from the base `b`:
the base's history, a round in which `p` hears, then silence for `p`. -/
def FirstReturn (p : Bool) : Base → List Letter → Prop
  | none, j => ∀ g ∈ j, g.hears p = false
  | some h, j => ∃ g t, g.hears p = true ∧ (∀ g' ∈ t, g'.hears p = false) ∧ j = h ++ g :: t

/-- The base after `h` is *good* for `c` if it and every base reachable from it by a further
reception have colour `c`.  The colour type `K` is `Bool` for consensus and the output type
for a general task. -/
def Good {K : Type*} (p : Bool) (C : Bool → Base → K) (h : List Letter) (c : K) : Prop :=
  C p (some h) = c ∧ ∀ g t, g.hears p = true → C p (some (h ++ g :: t)) = c

/-- The first-return histories of `b` that are not good for `c`. -/
def Bad {K : Type*} (p : Bool) (C : Bool → Base → K) (b : Base) (c : K) : Set (List Letter) :=
  {j | FirstReturn p b j ∧ ¬ Good p C j c}

/-- The base `b` *ends* with `c`: it has colour `c` and only finitely many bad first returns,
so that after a finite silence every further reception lands on a good base. -/
def End {K : Type*} (p : Bool) (C : Bool → Base → K) (b : Base) (c : K) : Prop :=
  C p b = c ∧ (Bad p C b c).Finite

theorem good_descendant {K : Type*} {p : Bool} {C : Bool → Base → K} {h : List Letter} {c : K}
    (hg : Good p C h c) {g : Letter} (hgp : g.hears p = true) (t : List Letter) :
    Good p C (h ++ g :: t) c := by
  refine ⟨hg.2 g t hgp, fun g' t' _ => ?_⟩
  rw [List.append_assoc, List.cons_append]
  exact hg.2 g _ hgp

theorem ViewEq.hears_iff {p : Bool} {r : ℕ} {σ τ : ℕ → Event Bool} (h : ViewEq p r σ τ)
    {i : ℕ} (hi : i < r) : Hears p σ i ↔ Hears p τ i := by
  unfold Hears; rw [h.1 i hi]

theorem ViewEq.refl (p : Bool) (r : ℕ) (σ : ℕ → Event Bool) : ViewEq p r σ σ :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩

theorem ViewEq.symm {p : Bool} {r : ℕ} {σ τ : ℕ → Event Bool} (h : ViewEq p r σ τ) :
    ViewEq p r τ σ :=
  ⟨fun i hi => (h.1 i hi).symm,
   fun i hi hh j hj => (h.2 i hi ((h.hears_iff hi).mpr hh) j hj).symm⟩

theorem ViewEq.trans {p : Bool} {r : ℕ} {σ τ ρ : ℕ → Event Bool} (h₁ : ViewEq p r σ τ)
    (h₂ : ViewEq p r τ ρ) : ViewEq p r σ ρ :=
  ⟨fun i hi => (h₁.1 i hi).trans (h₂.1 i hi),
   fun i hi hh j hj => (h₁.2 i hi hh j hj).trans (h₂.2 i hi ((h₁.hears_iff hi).mp hh) j hj)⟩

/-- View equality from the reception bits alone. -/
theorem viewEq_of_bits {p : Bool} {r : ℕ} {σ τ : ℕ → Event Bool}
    (hown : ∀ i, i < r → (Hears p σ i ↔ Hears p τ i))
    (hother : ∀ i, i < r → Hears p σ i → ∀ j, j < i → (Hears (!p) σ j ↔ Hears (!p) τ j)) :
    ViewEq p r σ τ :=
  ⟨fun i hi => inN_eq_of_hears_iff (hown i hi),
   fun i hi hh j hj => inN_eq_of_hears_iff (hother i hi hh j hj)⟩

theorem viewEq_of_inN_eq {p : Bool} {r : ℕ} {σ τ : ℕ → Event Bool}
    (h : ∀ i, i < r → ∀ q, (σ i).inN q = (τ i).inN q) : ViewEq p r σ τ :=
  ⟨fun i hi => h i hi p, fun _ hi _ j hj => h j (lt_trans hj hi) (!p)⟩

/-- The same view gives the same base. -/
theorem base_eq_of_viewEq {p : Bool} {σ τ : ℕ → Event Bool} :
    ∀ {r : ℕ}, ViewEq p r σ τ → base p τ r = base p σ r := by
  intro r
  induction r with
  | zero => intro _; rfl
  | succ r ih =>
      intro h
      by_cases hr : Hears p σ r
      · have hr' : Hears p τ r := (h.hears_iff (Nat.lt_succ_self r)).mp hr
        rw [base_succ_of_hears hr, base_succ_of_hears hr']
        congr 1
        refine pre_eq_of_letters fun i hi => ?_
        have hp : Hears p σ i ↔ Hears p τ i := h.hears_iff (by omega)
        have hq : Hears (!p) σ i ↔ Hears (!p) τ i := by
          unfold Hears; rw [h.2 r (Nat.lt_succ_self r) hr i hi]
        cases p with
        | false => exact letter_eq_of_hears_iff hp.symm hq.symm
        | true => exact letter_eq_of_hears_iff hq.symm hp.symm
      · have hr' : ¬ Hears p τ r := fun h' => hr ((h.hears_iff (Nat.lt_succ_self r)).mpr h')
        rw [base_succ_of_not_hears hr, base_succ_of_not_hears hr']
        exact ih (h.mono (Nat.le_succ r))

section Stable

variable {K : Type*} {p : Bool} {C : Bool → Base → K} {τ : ℕ → Event Bool}

/-- Silence since `r` makes the current history a first return of the base at `r`. -/
theorem firstReturn_pre {r n : ℕ} (hrn : r ≤ n) (hsil : ∀ i, r ≤ i → i < n → ¬ Hears p τ i) :
    FirstReturn p (base p τ r) (pre τ n) := by
  rcases base_cases (p := p) (σ := τ) r with ⟨hb, hs⟩ | ⟨s, hsr, hs, hs', hb⟩
  · rw [hb]
    intro g hg
    obtain ⟨i, hi, rfl⟩ := mem_pre.mp hg
    rw [letter_hears_eq_false_iff]
    rcases Nat.lt_or_ge i r with h | h
    · exact hs i h
    · exact hsil i h hi
  · rw [hb, pre_split (lt_of_lt_of_le hsr hrn)]
    refine ⟨letter τ s, _, letter_hears_iff.mpr hs, ?_, rfl⟩
    intro g' hg'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg'
    rw [List.mem_range] at hk
    rw [letter_hears_eq_false_iff]
    rcases Nat.lt_or_ge (s + 1 + k) r with h | h
    · exact hs' _ (by omega) h
    · exact hsil _ h (by omega)

/-- **Colours are stable after commitment.**  If the base at time `r` has colour `c` and every
first return of it of length at least `r` is good for `c`, the current colour is `c` from `r`
on, whatever happens. -/
theorem colour_stable {r : ℕ} {c : K} (hb : C p (base p τ r) = c)
    (hgood : ∀ j, FirstReturn p (base p τ r) j → r ≤ j.length → Good p C j c) :
    ∀ n, r ≤ n → C p (base p τ n) = c := by
  have key : ∀ n, r ≤ n →
      (∀ i, r ≤ i → i < n → ¬ Hears p τ i) ∨
      ∃ j, r ≤ j ∧ j < n ∧ Hears p τ j ∧ base p τ n = some (pre τ j) ∧ Good p C (pre τ j) c := by
    intro n
    induction n with
    | zero => intro _; exact Or.inl fun i _ hi => absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
        intro hrn
        rcases Nat.lt_or_ge n r with hnr | hnr
        · exact Or.inl fun i hri hin => by omega
        rcases ih hnr with hsil | ⟨j, hrj, hjn, hj, hbj, hgj⟩
        · by_cases hn : Hears p τ n
          · refine Or.inr ⟨n, hnr, Nat.lt_succ_self n, hn, base_succ_of_hears hn, ?_⟩
            exact hgood _ (firstReturn_pre hnr hsil) (by rw [pre_length]; exact hnr)
          · refine Or.inl fun i hri hin => ?_
            rcases Nat.lt_succ_iff_lt_or_eq.mp hin with hin | hin
            · exact hsil i hri hin
            · rw [hin]; exact hn
        · by_cases hn : Hears p τ n
          · refine Or.inr ⟨n, hnr, Nat.lt_succ_self n, hn, base_succ_of_hears hn, ?_⟩
            rw [pre_split hjn]
            exact good_descendant hgj (letter_hears_iff.mpr hj) _
          · exact Or.inr ⟨j, hrj, by omega, hj, by rw [base_succ_of_not_hears hn, hbj], hgj⟩
  intro n hrn
  rcases key n hrn with hsil | ⟨j, _, _, _, hbj, hgj⟩
  · rw [base_eq_of_silent_between n hrn hsil, hb]
  · rw [hbj]; exact hgj.1

end Stable

/-- **The termination clause is a commitment time.**  A good reception, or an end at the
eventual base, yields a time `r` and a colour `c` such that the colour at `r` is `c` and every
first return of length at least `r` is good for `c`: from `r` on the colour can no longer
change, whatever the run does.  This is where the *finiteness* of the bad set is used, and it
is what an eventually-stabilising rule does not provide. -/
theorem stable_of_term_disj {K : Type*} {p : Bool} {C : Bool → Base → K} {σ : ℕ → Event Bool}
    (h : (∃ i c, Hears p σ i ∧ Good p C (pre σ i) c) ∨
      (∃ b c, (∃ n₀, ∀ n, n₀ ≤ n → base p σ n = b) ∧ End p C b c)) :
    ∃ r c, C p (base p σ r) = c ∧
      ∀ j, FirstReturn p (base p σ r) j → r ≤ j.length → Good p C j c := by
  rcases h with ⟨i, c, hi, hg⟩ | ⟨b, c, ⟨n₀, hn₀⟩, hCb, hfin⟩
  · refine ⟨i + 1, c, ?_, ?_⟩
    · rw [base_succ_of_hears hi]; exact hg.1
    · intro j hj _
      rw [base_succ_of_hears hi] at hj
      obtain ⟨g, t, hgp, -, rfl⟩ := hj
      exact good_descendant hg hgp t
  · obtain ⟨L, hL⟩ : ∃ L, ∀ j ∈ Bad p C b c, j.length ≤ L := by
      obtain ⟨L, hL⟩ := (hfin.image List.length).bddAbove
      exact ⟨L, fun j hj => hL ⟨j, hj, rfl⟩⟩
    refine ⟨max n₀ (L + 1), c, ?_, ?_⟩
    · rw [hn₀ _ (le_max_left _ _)]; exact hCb
    · intro j hj hlen
      rw [hn₀ _ (le_max_left _ _)] at hj
      by_contra hng
      have := hL j ⟨hj, hng⟩
      have := le_max_right n₀ (L + 1)
      omega

section ToScheme

variable {adv : Set (ℕ → Event Bool)} {C : Bool → Base → Bool}

/-- The colour of `p` is eventually `c` along `σ`. -/
def EvCol {K : Type*} (C : Bool → Base → K) (p : Bool) (σ : ℕ → Event Bool) (c : K) : Prop :=
  ∃ n₀, ∀ n, n₀ ≤ n → C p (base p σ n) = c

theorem evCol_unique {K : Type*} {C : Bool → Base → K} {p : Bool} {σ : ℕ → Event Bool} {c c' : K}
    (h : EvCol C p σ c) (h' : EvCol C p σ c') : c = c' := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨n', hn'⟩ := h'
  rw [← hn (max n n') (le_max_left _ _), hn' (max n n') (le_max_right _ _)]

end ToScheme

/-- The event with the given reception bits. -/
def Event.ofLetter (g : Letter) : Event Bool where
  inN p := if g.hears p = true then {p, !p} else {p}
  self_mem p := by by_cases h : g.hears p = true <;> simp [h]

theorem mem_inN_ofLetter_iff {g : Letter} {p : Bool} :
    (!p) ∈ (Event.ofLetter g).inN p ↔ g.hears p = true := by
  by_cases h : g.hears p = true
  · simp [Event.ofLetter, h]
  · cases p <;> simp [Event.ofLetter, h]

theorem inN_ofLetter_letter (σ : ℕ → Event Bool) (i : ℕ) (q : Bool) :
    (Event.ofLetter (letter σ i)).inN q = (σ i).inN q := by
  by_cases h : Hears q σ i
  · rw [inN_eq_of_hears h]; simp [Event.ofLetter, letter_hears_iff.mpr h]
  · rw [inN_eq_self_of_not_hears h]; simp [Event.ofLetter, letter_hears_eq_false_iff.mpr h]

theorem letter_eq_of_ofLetter {σ : ℕ → Event Bool} {i : ℕ} {g : Letter}
    (h : σ i = Event.ofLetter g) : letter σ i = g := by
  classical
  have h1 : Hears U σ i ↔ g.1 = true := by unfold Hears; rw [h]; exact mem_inN_ofLetter_iff
  have h2 : Hears W σ i ↔ g.2 = true := by unfold Hears; rw [h]; exact mem_inN_ofLetter_iff
  obtain ⟨a, b⟩ := g
  refine Prod.ext ?_ ?_
  · show decide (Hears U σ i) = a
    cases a
    · exact decide_eq_false fun hh => Bool.false_ne_true (h1.mp hh)
    · exact decide_eq_true (h1.mpr rfl)
  · show decide (Hears W σ i) = b
    cases b
    · exact decide_eq_false fun hh => Bool.false_ne_true (h2.mp hh)
    · exact decide_eq_true (h2.mpr rfl)

/-- The canonical run of a base: its history, a round in which both hear, then silence. -/
noncomputable def extRun : Base → ℕ → Event Bool
  | none, _ => silentEvent
  | some w, i =>
      match w[i]? with
      | some g => Event.ofLetter g
      | none => if i = w.length then Event.ofLetter hearL else silentEvent

section ExtRun

variable {p : Bool} {w : List Letter} {i : ℕ}

theorem extRun_some_lt (hi : i < w.length) : extRun (some w) i = Event.ofLetter w[i] := by
  simp [extRun, List.getElem?_eq_getElem hi]

theorem extRun_some_len : extRun (some w) w.length = Event.ofLetter hearL := by
  simp [extRun]

theorem extRun_some_gt (hi : w.length < i) : extRun (some w) i = silentEvent := by
  simp [extRun, List.getElem?_eq_none_iff.mpr (Nat.le_of_lt hi), Nat.ne_of_gt hi]

theorem not_hears_silent {σ : ℕ → Event Bool} (h : σ i = silentEvent) : ¬ Hears p σ i := by
  intro hh
  rw [Hears, h, silentEvent_inN] at hh
  cases p <;> simp at hh

theorem not_hears_extRun_none : ¬ Hears p (extRun none) i := not_hears_silent rfl

theorem hears_extRun_some_lt (hi : i < w.length) :
    Hears p (extRun (some w)) i ↔ w[i].hears p = true := by
  unfold Hears; rw [extRun_some_lt hi]; exact mem_inN_ofLetter_iff

theorem hears_extRun_some_len : Hears p (extRun (some w)) w.length := by
  unfold Hears; rw [extRun_some_len]; exact mem_inN_ofLetter_iff.mpr (hearL_hears p)

theorem not_hears_extRun_some_gt (hi : w.length < i) : ¬ Hears p (extRun (some w)) i :=
  not_hears_silent (extRun_some_gt hi)

theorem letter_extRun_some_lt (hi : i < w.length) : letter (extRun (some w)) i = w[i] :=
  letter_eq_of_ofLetter (extRun_some_lt hi)

theorem pre_extRun (w : List Letter) : pre (extRun (some w)) w.length = w := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [pre, List.getElem_map, List.getElem_range]
  exact letter_extRun_some_lt h2

theorem base_extRun_succ (w : List Letter) :
    base p (extRun (some w)) (w.length + 1) = some w := by
  rw [base_succ_of_hears hears_extRun_some_len, pre_extRun]

/-- Two canonical runs agree below the length of a common prefix. -/
theorem extRun_eq_of_prefix {w' : List Letter} (hw : w <+: w') (hi : i < w.length) :
    extRun (some w) i = extRun (some w') i := by
  obtain ⟨s, rfl⟩ := hw
  rw [extRun_some_lt hi, extRun_some_lt (by simp; omega), List.getElem_append_left hi]

/-- The canonical run of any extension of the current history has the current view. -/
theorem viewEq_extRun_of_prefix {σ : ℕ → Event Bool} {r n : ℕ} (hw : pre σ n <+: w)
    (hrn : r ≤ n) : ViewEq p r σ (extRun (some w)) := by
  refine viewEq_of_inN_eq fun k hk q => ?_
  have hkn : k < n := lt_of_lt_of_le hk hrn
  obtain ⟨s, rfl⟩ := hw
  rw [extRun_some_lt (by simp; omega), List.getElem_append_left (by simpa using hkn)]
  simp only [pre, List.getElem_map, List.getElem_range]
  exact (inN_ofLetter_letter σ k q).symm

end ExtRun

/-- Two events on two processes with the same in-neighbourhoods are equal. -/
theorem event_eq_of_inN {G H : Event Bool} (h : G.inN = H.inN) : G = H := by
  cases G; cases H; cases h; rfl

/-- A letter word as a run. -/
def runOfWord (w : ℕ → Letter) : ℕ → Event Bool := fun i => Event.ofLetter (w i)

theorem letter_runOfWord (w : ℕ → Letter) (i : ℕ) : letter (runOfWord w) i = w i :=
  letter_eq_of_ofLetter rfl

/-- The canonical run of the current base has the current view. -/
theorem viewEq_extRun_base (p : Bool) (σ : ℕ → Event Bool) (n : ℕ) :
    ViewEq p n σ (extRun (base p σ n)) := by
  rcases base_cases (p := p) (σ := σ) n with ⟨hb, hs⟩ | ⟨s, hsn, hs, hs', hb⟩
  · rw [hb]
    refine viewEq_of_bits (fun i hi => ?_) (fun i hi hh => absurd hh (hs i hi))
    exact iff_of_false (hs i hi) not_hears_extRun_none
  · rw [hb]
    have hlen : (pre σ s).length = s := pre_length s
    refine viewEq_of_bits (fun i hi => ?_) (fun i hi hh j hj => ?_)
    · rcases lt_trichotomy i s with his | his | hsi
      · rw [hears_extRun_some_lt (by omega)]
        simp only [pre, List.getElem_map, List.getElem_range]
        exact letter_hears_iff.symm
      · have := hears_extRun_some_len (p := p) (w := pre σ s)
        rw [hlen] at this
        rw [his]
        exact iff_of_true hs this
      · exact iff_of_false (hs' i hsi hi) (not_hears_extRun_some_gt (by omega))
    · have his : i ≤ s := by
        by_contra hcon
        exact hs' i (by omega) hi hh
      rw [hears_extRun_some_lt (by omega)]
      simp only [pre, List.getElem_map, List.getElem_range]
      exact letter_hears_iff.symm

/-- Silence from `r` on, and a first return `j` of the base at `r` of length at least `r`:
the canonical run of `j` has `p`'s view at time `r`. -/
theorem viewEq_extRun_firstReturn {p : Bool} {σ : ℕ → Event Bool} {r : ℕ} {j : List Letter}
    (hj : FirstReturn p (base p σ r) j) (hlen : r ≤ j.length) :
    ViewEq p r σ (extRun (some j)) := by
  rcases base_cases (p := p) (σ := σ) r with ⟨hb, hs⟩ | ⟨s, hsr, hs, hs', hb⟩
  · rw [hb] at hj
    refine viewEq_of_bits (fun i hi => ?_) (fun i hi hh => absurd hh (hs i hi))
    rw [hears_extRun_some_lt (by omega)]
    exact iff_of_false (hs i hi) (by rw [hj _ (List.getElem_mem _)]; simp)
  · rw [hb] at hj
    obtain ⟨g, t, hg, ht, rfl⟩ := hj
    have hlen' : (pre σ s).length = s := pre_length s
    refine viewEq_of_bits (fun i hi => ?_) (fun i hi hh k hk => ?_)
    · rcases lt_trichotomy i s with his | his | hsi
      · rw [hears_extRun_some_lt (by omega), List.getElem_append_left (by omega)]
        simp only [pre, List.getElem_map, List.getElem_range]
        exact letter_hears_iff.symm
      · rw [hears_extRun_some_lt (by omega), List.getElem_append_right (by omega),
          List.getElem_cons, dif_pos (by omega), his]
        exact iff_of_true hs hg
      · rw [hears_extRun_some_lt (by omega), List.getElem_append_right (by omega),
          List.getElem_cons, dif_neg (by omega)]
        exact iff_of_false (hs' i hsi hi) (by rw [ht _ (List.getElem_mem _)]; simp)
    · have his : i ≤ s := by
        by_contra hcon
        exact hs' i (by omega) hi hh
      rw [hears_extRun_some_lt (by omega), List.getElem_append_left (by omega)]
      simp only [pre, List.getElem_map, List.getElem_range]
      exact letter_hears_iff.symm

end DistributedSynthesis.DecisionTasks.Source
