/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemScalingSourceLabels

/-! # The explicit perfect-recall scaling winner in the actual execution model -/

namespace DistributedSynthesis.ScalingSafety.Source

def turn (oneLeft : Bool) (g : Graph) : Bool := if g = .both then !oneLeft else oneLeft
def childIndex (j : Nat) (oneLeft : Bool) (g : Graph) : Nat := 3*j + (digit oneLeft g).val

def geometricRound (n j : Nat) (oneLeft : Bool) (g : Graph) :
    RoundRecord Unit Unit Graph Label Label :=
  let k := childIndex j oneLeft g
  let t := turn oneLeft g
  ⟨(),(),g, if t then label (n+1) k else label (n+1) (k+1),
    if t then label (n+1) (k+1) else label (n+1) k⟩

structure Aligned (n j : Nat) (oneLeft : Bool) (s : State) : Prop where
  good : s.good = true
  orientation : s.oneLeft = oneLeft
  left : s.leftBoundary = true → j = 0
  right : s.rightBoundary = true → j+1 = width n
  previous : ∀ p, s.previous = some p → p = edgePlan n j

theorem initial_aligned : Aligned 0 0 true objective.initial := by
  refine ⟨rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩
  intro p h
  cases h

theorem geometric_step (n j : Nat) (t : Bool) (s : State) (g : Graph)
    (h : Aligned n j t s) :
    Aligned (n+1) (childIndex j t g) (turn t g) (step s (geometricRound n j t g)) := by
  let k := childIndex j t g
  let lb := s.leftBoundary && decide (digit t g = 0)
  let rb := s.rightBoundary && decide (digit t g = 2)
  have hl : lb = true → k = 0 := by
    intro hl
    have ha := Bool.and_eq_true_iff.mp hl
    have hj := h.left ha.1
    have hd : digit t g = 0 := of_decide_eq_true ha.2
    simp [k, childIndex, hj, hd]
  have hr : rb = true → k+1 = width (n+1) := by
    intro hr
    have ha := Bool.and_eq_true_iff.mp hr
    have hj := h.right ha.1
    have hd : digit t g = 2 := of_decide_eq_true ha.2
    simp only [k, childIndex, hd]
    change 3*j+2+1 = width (n+1)
    rw [show width (n+1) = 3 * width n by simp [width, pow_succ, Nat.mul_comm], ← hj]
    omega
  have hp : ∀ old, s.previous = some old → weight (n+1) k = old.childValue (digit t g) := by
    intro old ho
    rw [h.previous old ho, edgePlan_child]
    rfl
  have hsafe : (label (n+1) k).up = (label (n+1) (k+1)).up ∧
      (label (n+1) k).right = (label (n+1) (k+1)).left ∧
      (label (n+1) k).right.childValue 0 + (label (n+1) k).right.childValue 1 +
        (label (n+1) k).right.childValue 2 + (label (n+1) k).carry.val =
          (label (n+1) k).multiplier * (label (n+1) k).right.value + (label (n+1) (k+1)).carry.val ∧
      (lb = true → (label (n+1) k).carry.val = 0) ∧
      (rb = true → (label (n+1) (k+1)).carry.val = 0) ∧
      (∀ old, s.previous = some old → (label (n+1) k).right.value = old.childValue (digit t g)) := by
    refine ⟨rfl, label_matching _ _, label_conservation _ _, ?_, ?_, ?_⟩
    · intro hb
      change carry (n+1) k = 0
      rw [hl hb, carry_left]
    · intro hb
      change carry (n+1) (k+1) = 0
      rw [hr hb, carry_right]
    · exact fun old ho ↦ (edgePlan_value _ _).trans (hp old ho)
  have hresult : step s (geometricRound n j t g) =
      ⟨turn t g, lb, rb, some (edgePlan (n+1) k), true⟩ := by
    unfold step geometricRound
    rw [h.orientation, h.good]
    cases ht : turn t g <;>
      simp only [turn] at ht <;>
      simp only [ht, Bool.false_eq_true, ↓reduceIte, Bool.true_and]
    all_goals
      rw [decide_eq_true hsafe]
      rfl
  rw [hresult]
  refine ⟨rfl, rfl, hl, hr, ?_⟩
  intro p hp
  exact (Option.some.inj hp).symm

def depth : {p : Proc} → View Unit Unit p → Nat
  | _, .empty _ => 0
  | _, .noRecv v _ => depth v + 1
  | _, .recv v _ _ _ => depth v + 1

def strategy : StrategyPair Unit Unit Label Label where
  one := fun v ↦ label (depth v) (coordinate v)
  two := fun v ↦ label (depth v) (coordinate v)

def ViewGeometry (n j : Nat) (t : Bool) (v : View Unit Unit .one) (u : View Unit Unit .two) : Prop :=
  depth v = n ∧ depth u = n ∧
    coordinate v = (if t then j else j+1) ∧ coordinate u = (if t then j+1 else j)

theorem advance_geometry (n j : Nat) (t : Bool)
    (v : View Unit Unit .one) (u : View Unit Unit .two)
    (e : EnvironmentRound Unit Unit) (h : ViewGeometry n j t v u) :
    ViewGeometry (n+1) (childIndex j t e.graph) (turn t e.graph)
      (advanceViewsWithEnvironment (v,u) e).1 (advanceViewsWithEnvironment (v,u) e).2 := by
  rcases h with ⟨hdv,hdu,hv,hu⟩
  cases t <;> cases hg : e.graph <;>
    simp only [ViewGeometry, advanceViewsWithEnvironment, hg, depth, coordinate,
      childIndex, digit, turn, Bool.false_eq_true, Bool.not_false, Bool.not_true,
      ↓reduceIte] at hv hu ⊢ <;>
    simp only [hdv,hdu,hv,hu,Proc.other] <;>
    ring_nf <;> simp [Nat.add_comm, Nat.add_left_comm] <;> omega

theorem nextRound_geometric (n j : Nat) (t : Bool)
    (history : History Unit Unit Graph Label Label) (e : EnvironmentRound Unit Unit)
    (h : ViewGeometry n j t (currentView .one history) (currentView .two history)) :
    nextRound strategy history e = geometricRound n j t e.graph := by
  have hg := advance_geometry n j t (currentView .one history) (currentView .two history) e h
  change ViewGeometry (n+1) (childIndex j t e.graph) (turn t e.graph)
    (nextView .one history e) (nextView .two history e) at hg
  rcases hg with ⟨hdv,hdu,hv,hu⟩
  unfold nextRound geometricRound
  simp only [strategy, hdv, hdu, hv, hu]
  cases turn t e.graph <;> simp

/-- Literal execution invariant: the coordinates come from the actual local
views, and the aligned state is the actual objective-DPA run. -/
theorem execution_invariant (env : EnvironmentSequence Unit Unit) : ∀ n,
    ∃ j t, ViewGeometry n j t
      (currentView .one (executionPrefix strategy env n))
      (currentView .two (executionPrefix strategy env n)) ∧
      Aligned n j t (objective.run (execution strategy env) n) := by
  intro n
  induction n with
  | zero => exact ⟨0,true,⟨rfl,rfl,rfl,rfl⟩,initial_aligned⟩
  | succ n ih =>
    obtain ⟨j,t,hgeom,halign⟩ := ih
    refine ⟨childIndex j t (env n).graph, turn t (env n).graph, ?_, ?_⟩
    · rw [currentView_executionPrefix_succ, currentView_executionPrefix_succ]
      exact advance_geometry n j t _ _ (env n) hgeom
    · rw [objective.run_succ, execution_apply, nextRound_geometric n j t _ _ hgeom]
      exact geometric_step n j t _ (env n).graph halign

/-- The specified finite safety objective really is realizable by a local
perfect-recall strategy, on every infinite environment, without acknowledgements. -/
theorem wins (env : EnvironmentSequence Unit Unit) :
    objective.Accepts (execution strategy env) := by
  apply (accepts_iff_good _).mpr
  intro n
  obtain ⟨j,t,hgeom,halign⟩ := execution_invariant env n
  exact halign.good

theorem realizable : ∃ σ : StrategyPair Unit Unit Label Label,
    ∀ env, objective.Accepts (execution σ env) := ⟨strategy,wins⟩

end DistributedSynthesis.ScalingSafety.Source
