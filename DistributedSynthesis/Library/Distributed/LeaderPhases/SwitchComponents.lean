/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.InputHandoff

/-! Finite input-dependent components at changes of the selected process.
Outputs are Unit here because the objects being counted are environment histories. -/
namespace Characterisation
open DistributedSynthesis

abbrev EnvHistory (I₁ I₂ : Type*) := History I₁ I₂ Graph Unit Unit

def InputHistoryComponent {I₁ I₂ : Type*} (P : List Graph → Prop) (h : EnvHistory I₁ I₂) :=
  {k : EnvHistory I₁ I₂ // InputConnected P h k}

private theorem history_ext {I₁ I₂ : Type*} {h k : EnvHistory I₁ I₂}
    (graphs : History.graphSequence h = History.graphSequence k)
    (one : inputWord .one h = inputWord .one k)
    (two : inputWord .two h = inputWord .two k) : h = k := by
  have len : h.length = k.length := by
    have := congrArg List.length graphs
    simpa [History.graphSequence] using this
  apply List.ext_getElem len
  intro i hi hk
  have eg := congrArg (fun w => w[i]?) graphs
  have eo := congrArg (fun w => w[i]?) one
  have et := congrArg (fun w => w[i]?) two
  simp [History.graphSequence, inputWord, hi, hk] at eg eo et
  have out : ∀ a b : RoundRecord I₁ I₂ Graph Unit Unit,
      a.graph = b.graph → a.inputOne = b.inputOne → a.inputTwo = b.inputTwo → a = b := by
    intro a b g x y
    cases a; cases b
    simp_all
  exact out _ _ eg eo et

private theorem word_eq_of_prefix_suffix {α : Type*} {a b : List α} (n : Nat)
    (pref : a.take n = b.take n) (suffix : a.drop n = b.drop n) : a = b := by
  calc
    a = a.take n ++ a.drop n := (List.take_append_drop n a).symm
    _ = b.take n ++ b.drop n := by rw [pref, suffix]
    _ = b := List.take_append_drop n b

/-- Equal sufficiently long old prefixes leave a finite family of possible
input words. A bounded array records all remaining positions. -/
private theorem bounded_word_family {α : Type*} [Finite α] (m : Nat) (pref : List α) :
    Finite {w : List α // w.take pref.length = pref ∧ w.length ≤ pref.length + m} ∧
    Nat.card {w : List α // w.take pref.length = pref ∧ w.length ≤ pref.length + m} ≤
      Nat.card (Fin m → Option α) := by
  let key : {w : List α // w.take pref.length = pref ∧ w.length ≤ pref.length + m} →
      (Fin m → Option α) := fun w i => w.val[pref.length + i.val]?
  have inj : Function.Injective key := by
    intro a b eq
    apply Subtype.ext
    apply word_eq_of_prefix_suffix pref.length (a.property.1.trans b.property.1.symm)
    apply List.ext_getElem?
    intro i
    by_cases inside : i < m
    · have e := congrFun eq ⟨i,inside⟩
      simpa [key, List.getElem?_drop, Nat.add_comm] using e
    · have ha : a.val.length ≤ pref.length + i := by have := a.property.2; omega
      have hb : b.val.length ≤ pref.length + i := by have := b.property.2; omega
      simp [List.getElem?_drop, List.getElem?_eq_none ha, List.getElem?_eq_none hb]
  exact ⟨Finite.of_injective key inj, Nat.card_le_card_of_injective key inj⟩

/-- Bounded graph components and fixed old input prefixes imply a finite
component of environment histories. The bound on recent input length is m. -/
theorem finite_family_of_common_prefixes {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (P : List Graph → Prop) (bounded : BoundedViewComponents P)
    (m : Nat) (h : EnvHistory I₁ I₂) (hh : P (History.graphSequence h))
    (R : EnvHistory I₁ I₂ → Prop)
    (projects : ∀ k, R k → InputConnected P h k)
    (common : ∀ k, R k →
      olderInputPrefix .one m h = olderInputPrefix .one m k ∧
      olderInputPrefix .two m h = olderInputPrefix .two m k) :
    Finite ({k : EnvHistory I₁ I₂ // R k}) ∧
      Nat.card ({k : EnvHistory I₁ I₂ // R k}) ≤
        Nat.card (HistoryComponent P (History.graphSequence h)) *
          (Nat.card (Fin m → Option (PSum I₁ I₂)))^2 := by
  let w₁ := olderInputPrefix .one m h
  let w₂ := olderInputPrefix .two m h
  let T (w : List (PSum I₁ I₂)) :=
    {u : List (PSum I₁ I₂) // u.take w.length = w ∧ u.length ≤ w.length+m}
  letI : Finite (T w₁) := (bounded_word_family m w₁).1
  letI : Finite (T w₂) := (bounded_word_family m w₂).1
  obtain ⟨K,bound⟩ := bounded
  letI : Finite (HistoryComponent P (History.graphSequence h)) := (bound _ hh).1
  have lengths : w₁.length = h.length-m ∧ w₂.length = h.length-m := by
    simp [w₁, w₂, olderInputPrefix, inputWord, History.length]
  let build (k : {k : EnvHistory I₁ I₂ // R k}) : T w₁ × T w₂ := by
    have len : h.length = k.val.length := by
      have e := connected_same_depth P (inputConnected_projects P (projects k.val k.property))
      simpa [History.graphSequence] using e
    refine ⟨⟨inputWord .one k.val, ?_, ?_⟩, ⟨inputWord .two k.val, ?_, ?_⟩⟩
    · rw [lengths.1, len]
      exact (common k.val k.property).1.symm
    · simp only [inputWord, List.length_map, lengths.1, History.length] at *
      omega
    · rw [lengths.2, len]
      exact (common k.val k.property).2.symm
    · simp only [inputWord, List.length_map, lengths.2, History.length] at *
      omega
  let key : {k : EnvHistory I₁ I₂ // R k} →
      HistoryComponent P (History.graphSequence h) × T w₁ × T w₂ := fun k =>
    (⟨History.graphSequence k.val, inputConnected_projects P (projects k.val k.property)⟩, build k)
  have inj : Function.Injective key := by
    intro a b eq
    apply Subtype.ext
    apply history_ext
    · exact congrArg (fun z => z.1.val) eq
    · exact congrArg (fun z => z.2.1.val) eq
    · exact congrArg (fun z => z.2.2.val) eq
  refine ⟨Finite.of_injective key inj, ?_⟩
  have count := Nat.card_le_card_of_injective key inj
  simp only [Nat.card_prod] at count
  have first := (bounded_word_family m w₁).2
  have second := (bounded_word_family m w₂).2
  have product := Nat.mul_le_mul first second
  have total := Nat.mul_le_mul_left (Nat.card (HistoryComponent P (History.graphSequence h))) product
  exact count.trans (by simpa only [pow_two] using total)

/-- The full-component specialization of the family bound. -/
theorem finite_component_of_common_prefixes {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (P : List Graph → Prop) (bounded : BoundedViewComponents P)
    (m : Nat) (h : EnvHistory I₁ I₂) (hh : P (History.graphSequence h))
    (common : ∀ k, InputConnected P h k →
      olderInputPrefix .one m h = olderInputPrefix .one m k ∧
      olderInputPrefix .two m h = olderInputPrefix .two m k) :
    Finite (InputHistoryComponent P h) ∧
      Nat.card (InputHistoryComponent P h) ≤
        Nat.card (HistoryComponent P (History.graphSequence h)) *
          (Nat.card (Fin m → Option (PSum I₁ I₂)))^2 :=
  finite_family_of_common_prefixes P bounded m h hh (InputConnected P h)
    (fun _ conn => conn) common

/-- At a change of selected process, the input-dependent environment
component is finite despite allowing arbitrary private input streams. -/
theorem finite_component_at_switch {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (P : List Graph → Prop) (closed : PrefixClosed P) (bounded : BoundedViewComponents P)
    (d : Nat) (old new : Proc) (h : EnvHistory I₁ I₂) (hh : P (History.graphSequence h))
    (changed : old ≠ new)
    (oldRecent : RecentOther P d (History.graphSequence h.dropLast) old)
    (newRecent : RecentOther P d (History.graphSequence h) new) :
    Finite (InputHistoryComponent P h) :=
  (finite_component_of_common_prefixes P bounded (d+1) h hh
    (fun _ conn => both_input_prefixes_at_switch P closed d old new changed oldRecent newRecent conn)).1

/-- Uniform, depth-independent cardinality bound at every owner switch.
The bound depends on P, the window, and the input alphabets only. -/
theorem uniformly_bounded_switch_components {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (P : List Graph → Prop) (closed : PrefixClosed P) (bounded : BoundedViewComponents P)
    (d : Nat) : ∃ B, ∀ old new (h : EnvHistory I₁ I₂), P (History.graphSequence h) →
      old ≠ new → RecentOther P d (History.graphSequence h.dropLast) old →
      RecentOther P d (History.graphSequence h) new →
      Finite (InputHistoryComponent P h) ∧ Nat.card (InputHistoryComponent P h) ≤ B := by
  obtain ⟨K,hK⟩ := bounded
  refine ⟨K * (Nat.card (Fin (d+1) → Option (PSum I₁ I₂)))^2, ?_⟩
  intro old new h hh changed oldRecent newRecent
  have result := finite_component_of_common_prefixes P ⟨K,hK⟩ (d+1) h hh
    (fun _ conn => both_input_prefixes_at_switch P closed d old new changed oldRecent newRecent conn)
  exact ⟨result.1, result.2.trans (Nat.mul_le_mul_right _ (hK _ hh).2)⟩

theorem holes_uniformly_bounded_switch_components {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d B, ∀ h : EnvHistory I₁ I₂, LivePrefix A (History.graphSequence h) →
      componentLeader (LivePrefix A) d (History.graphSequence h.dropLast) ≠
        componentLeader (LivePrefix A) d (History.graphSequence h) →
      Finite (InputHistoryComponent (LivePrefix A) h) ∧
        Nat.card (InputHistoryComponent (LivePrefix A) h) ≤ B := by
  obtain ⟨d,recent⟩ := holes_component_recent_receiver A regular holes
  obtain ⟨B,bound⟩ := uniformly_bounded_switch_components (I₁ := I₁) (I₂ := I₂)
    (LivePrefix A) (livePrefix_closed A)
    ((omegaRegular_holes_iff_bounded_components A regular).mp holes) d
  refine ⟨d,B,?_⟩
  intro h hh changed
  have parentLive : LivePrefix A (History.graphSequence h.dropLast) := by
    rw [graphSequence_dropLast]
    exact live_parent _ (livePrefix_closed A) hh
  exact bound _ _ h hh changed
    (componentLeader_correct _ _ _ (recent _ parentLive))
    (componentLeader_correct _ _ _ (recent _ hh))

end Characterisation
