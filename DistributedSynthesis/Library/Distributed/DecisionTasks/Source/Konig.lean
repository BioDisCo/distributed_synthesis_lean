/- Extracted from consensusLTL/lean/ConsensusLTL/Konig.lean.
Only decision-task dependencies are retained; see ../SOURCE.md. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Colouring
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Model
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Views

-- Preserve the source section contexts on Lean 4.30.
set_option linter.unusedSectionVars false

namespace DistributedSynthesis.DecisionTasks.Source

universe u

section Konig

variable {L : Type u} [Finite L]

/-- A branch of the tree of words: an increasing sequence of prefixes, one letter at a time. -/
def IsBranch (β : ℕ → List L) : Prop := ∀ n, ∃ a : L, β (n + 1) = β n ++ [a]

theorem IsBranch.length {β : ℕ → List L} (h : IsBranch β) (h0 : β 0 = []) (n : ℕ) :
    (β n).length = n := by
  induction n with
  | zero => rw [h0]; rfl
  | succ n ih => obtain ⟨a, ha⟩ := h n; rw [ha]; simp [ih]

/-- The nodes above which the set has infinitely many members. -/
private def fat (S : Set (List L)) : Set (List L) := {w | {j ∈ S | w <+: j}.Infinite}

/-- A word extending `w` is `w` itself or extends one of its children. -/
private theorem sub_children (S : Set (List L)) (w : List L) :
    {j ∈ S | w <+: j} ⊆ insert w (⋃ a : L, {j ∈ S | w ++ [a] <+: j}) := by
  rintro j ⟨hj, t, rfl⟩
  match t with
  | [] => simp
  | a :: t =>
      refine Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨a, hj, ?_⟩)
      exact ⟨t, by simp⟩

/-- A node with infinitely many members above it has a child with infinitely many. -/
private theorem fat_succ {S : Set (List L)} {w : List L} (hw : w ∈ fat S) :
    ∃ a : L, w ++ [a] ∈ fat S := by
  by_contra hcon
  push Not at hcon
  have hfin : ∀ a : L, {j ∈ S | w ++ [a] <+: j}.Finite := by
    intro a
    exact Set.not_infinite.mp (hcon a)
  exact hw (((Set.finite_iUnion hfin).insert w).subset (sub_children S w))

/-- **König's lemma.**  Over a finite alphabet, a set of words is infinite exactly when some
branch has a member of the set above each of its nodes. -/
theorem infinite_iff_exists_branch (S : Set (List L)) :
    S.Infinite ↔ ∃ β : ℕ → List L, β 0 = [] ∧ IsBranch β ∧ ∀ n, ∃ j ∈ S, β n <+: j := by
  classical
  constructor
  · intro hS
    have h0 : ([] : List L) ∈ fat S := by
      refine hS.mono ?_
      rintro j hj
      exact ⟨hj, List.nil_prefix⟩
    choose f hf using fun w : {w : List L // w ∈ fat S} => fat_succ w.2
    let step : {w : List L // w ∈ fat S} → {w : List L // w ∈ fat S} :=
      fun w => ⟨w.1 ++ [f w], hf w⟩
    let g : ℕ → {w : List L // w ∈ fat S} := fun n => step^[n] ⟨[], h0⟩
    refine ⟨fun n => (g n).1, rfl, fun n => ⟨f (g n), ?_⟩, fun n => ?_⟩
    · show ((step^[n + 1]) ⟨[], h0⟩).1 = _
      rw [Function.iterate_succ_apply']
    · obtain ⟨j, hj⟩ := ((g n).2).nonempty
      exact ⟨j, hj.1, hj.2⟩
  · rintro ⟨β, h0, hb, hmem⟩ hfin
    obtain ⟨N, hN⟩ := (hfin.image List.length).bddAbove
    obtain ⟨j, hjS, hpre⟩ := hmem (N + 1)
    have h1 : j.length ≤ N := hN ⟨j, hjS, rfl⟩
    have h2 : (β (N + 1)).length ≤ j.length := hpre.length_le
    rw [hb.length h0 (N + 1)] at h2
    omega

end Konig

/-- The depth of a base: the number of rounds it takes to create it. -/
def bdepth : Base → ℕ
  | none => 0
  | some h => h.length + 1

theorem bdepth_base_le {p : Bool} {σ : ℕ → Event Bool} (n : ℕ) : bdepth (base p σ n) ≤ n := by
  rcases base_cases (p := p) (σ := σ) n with ⟨hb, -⟩ | ⟨s, hsn, -, -, hb⟩
  · rw [hb]; exact Nat.zero_le n
  · rw [hb]
    show (pre σ s).length + 1 ≤ n
    rw [pre_length]
    omega

/-- **The eventual base is eventual silence.**  A run has an eventually constant base for `p`
exactly when `p` receives finitely often, which is a branch condition. -/
theorem exists_eventual_base_iff {p : Bool} {σ : ℕ → Event Bool} :
    (∃ b, ∃ N, ∀ n, N ≤ n → base p σ n = b) ↔ ∃ N, ∀ i, N ≤ i → ¬ Hears p σ i := by
  constructor
  · rintro ⟨b, N, hN⟩
    refine ⟨N, fun i hi hh => ?_⟩
    have h₁ : base p σ (i + 1) = some (pre σ i) := base_succ_of_hears hh
    have h₂ : bdepth (base p σ i) ≤ i := bdepth_base_le i
    rw [hN i hi, ← hN (i + 1) (by omega), h₁] at h₂
    have h₃ : (pre σ i).length + 1 ≤ i := h₂
    rw [pre_length] at h₃
    omega
  · rintro ⟨N, hN⟩
    exact ⟨base p σ N, N, fun n hn =>
      base_eq_of_silent_between n hn fun i hi _ => hN i hi⟩

section Annotation

variable {K : Type*}

/-- Every node of the cone above `x` carries the colour `c`. -/
def AllCol (p : Bool) (C : Bool → Base → K) (x : List Letter) (c : K) : Prop :=
  ∀ j, x <+: j → C p (some j) = c

/-- **Goodness is a safety condition.**  A node is good exactly when it carries `c` and every
cone above a reception child is constantly `c`. -/
theorem good_iff_allCol {p : Bool} {C : Bool → Base → K} {h : List Letter} {c : K} :
    Good p C h c ↔ C p (some h) = c ∧ ∀ a : Letter, a.hears p = true → AllCol p C (h ++ [a]) c := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a ha j hj => ?_⟩
    obtain ⟨t, rfl⟩ := hj
    rw [List.append_assoc]
    exact h2 a t ha
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun g t hg => ?_⟩
    have := h2 g hg (h ++ g :: t) ⟨t, by rw [List.append_assoc]; rfl⟩
    exact this

/-- No node of the cone above `x` belongs to `S`. -/
def NoBelow (S : Set (List Letter)) (x : List Letter) : Prop := ∀ j, x <+: j → j ∉ S

/-- **Finiteness is an eventuality.**  A set of nodes is finite exactly when every branch
eventually reaches a node with no member of the set above it. -/
theorem finite_iff_eventually_noBelow (S : Set (List Letter)) :
    S.Finite ↔ ∀ β : ℕ → List Letter, β 0 = [] → IsBranch β → ∃ n, NoBelow S (β n) := by
  constructor
  · intro hfin β h0 hb
    obtain ⟨N, hN⟩ := (hfin.image List.length).bddAbove
    refine ⟨N + 1, fun j hj hjS => ?_⟩
    have h1 : j.length ≤ N := hN ⟨j, hjS, rfl⟩
    have h2 : (β (N + 1)).length ≤ j.length := hj.length_le
    rw [hb.length h0 (N + 1)] at h2
    omega
  · intro h
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨β, h0, hb, hmem⟩ := (infinite_iff_exists_branch S).mp hinf
    obtain ⟨n, hn⟩ := h β h0 hb
    obtain ⟨j, hjS, hj⟩ := hmem n
    exact hn j hj hjS

end Annotation

end DistributedSynthesis.DecisionTasks.Source
