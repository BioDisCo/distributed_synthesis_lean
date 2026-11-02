/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Formalizations.Lemma.LemCounterMachineRowSoundness

/-! # A local perfect-recall winner for every nonhalting machine -/
namespace DistributedSynthesis.CounterMachine.Source
open TernaryCounter
variable {Q : Type*}
variable (M : Machine Q)

def counter (n : Nat) (k : Fin 2) := (M.run n).2 k
def op (n : Nat) (k : Fin 2) := M.op (M.run n).1 (flags (M.run n).2) k
theorem counter_succ (n : Nat) (k : Fin 2) :
    counter M (n+1) k = (op M n k).applyCount (counter M n k) := rfl
theorem counter_bound (n : Nat) (k : Fin 2) : counter M n k ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [counter_succ]; cases op M n k <;> simp [Operation.applyCount] <;> omega
theorem decrement_positive (n : Nat) (k : Fin 2) (h : op M n k = .decrement) :
    0 < counter M n k := by
  have hz := M.op_decrement _ _ k h
  simp only [flags,decide_eq_false_iff_not] at hz
  exact Nat.pos_of_ne_zero hz
def binary (c j : Nat) : Fin 2 := ⟨weight c j,by have := weight_bound c j; omega⟩
def edgePlan (n j : Nat) (k : Fin 2) : Plan :=
  ⟨binary (counter M (n-1) k) j,fun d ↦ binary (counter M n k) (3*j+d.val)⟩
def finiteCarry (n j : Nat) (k : Fin 2) : Fin 9 :=
  ⟨carry (counter M (n-1) k) (op M (n-1) k).factor j,
    carry_bound _ _ _ (by cases op M (n-1) k <;> decide)
      (by cases op M (n-1) k <;> decide)⟩
def label (n j : Nat) : Label Q :=
  ⟨(M.run (n-1)).1,flags (M.run (n-1)).2,finiteCarry M n j,
    edgePlan M n j⟩
theorem label_conservation (n j : Nat) (k : Fin 2) :
    ((label M (n+1) j).right k).promised + ((label M (n+1) j).carry k).val =
      (M.op (label M (n+1) j).control (label M (n+1) j).zero k).factor *
        ((label M (n+1) j).right k).weight.val + ((label M (n+1) (j+1)).carry k).val := by
  simpa only [label,edgePlan,Plan.promised,binary,finiteCarry,Nat.add_sub_cancel,
    Fin.val_zero,Fin.val_one,Fin.val_ofNat,Nat.add_zero,counter_succ,op,counter]
    using conservation (op M n k) (counter M n k) j (decrement_positive M n k)
theorem carry_left (n : Nat) (k : Fin 2) : ((label M n 0).carry k).val = 0 := by
  simp [label,finiteCarry,carry]
theorem carry_right (n : Nat) (k : Fin 2) : ((label M (n+1) (3^(n+1))).carry k).val = 0 := by
  have hc : counter M n k ≤ n+1 := (counter_bound M n k).trans (by omega)
  have he : 3^(n+1) = 3^(counter M n k) * 3^(n+1-counter M n k) := by
    rw [← pow_add,Nat.add_sub_of_le hc]
  change carry (counter M n k) (op M n k).factor (3^(n+1)) = 0
  rw [he]
  exact carry_at_multiple _ _ _

def geometricRound (n j : Nat) (t : Bool) (g : Graph) :
    RoundRecord Unit Unit Graph (Label Q) (Label Q) :=
  let k := ScalingSafety.Source.childIndex j t g
  let u := ScalingSafety.Source.turn t g
  ⟨(),(),g,if u then label M (n+1) k else label M (n+1) (k+1),
    if u then label M (n+1) (k+1) else label M (n+1) k⟩

structure Aligned (n j : Nat) (t : Bool) (s : State Q) : Prop where
  good : s.good = true
  orientation : s.oneLeft = t
  left : s.leftBoundary = true → j = 0
  right : s.rightBoundary = true → j+1 = 3^n
  fresh : s.previous = none → n = 0
  previous : ∀ p, s.previous = some p → 0 < n ∧ p = (label M n j).snapshot
variable [DecidableEq Q] [Fintype Q]
theorem initial_aligned : Aligned M 0 0 true (objective M).initial := by
  refine ⟨rfl,rfl,fun _ ↦ rfl,fun _ ↦ rfl,fun _ ↦ rfl,?_⟩
  intro p h; cases h

theorem geometric_step (hnh : M.Nonhalting) (n j : Nat) (t : Bool) (s : State Q) (g : Graph)
    (h : Aligned M n j t s) :
    Aligned M (n+1) (ScalingSafety.Source.childIndex j t g) (ScalingSafety.Source.turn t g)
      (step M s (geometricRound M n j t g)) := by
  let k := ScalingSafety.Source.childIndex j t g
  let lb := s.leftBoundary && decide (ScalingSafety.digit t g = 0)
  let rb := s.rightBoundary && decide (ScalingSafety.digit t g = 2)
  have hl : lb = true → k = 0 := by
    intro hh
    have ha := Bool.and_eq_true_iff.mp hh
    have hj := h.left ha.1
    have hd : ScalingSafety.digit t g = 0 := of_decide_eq_true ha.2
    simp [k,ScalingSafety.Source.childIndex,hj,hd]
  have hr : rb = true → k+1 = 3^(n+1) := by
    intro hh
    have ha := Bool.and_eq_true_iff.mp hh
    have hj := h.right ha.1
    have hd : ScalingSafety.digit t g = 2 := of_decide_eq_true ha.2
    simp only [k,ScalingSafety.Source.childIndex,hd]
    change 3*j+2+1 = 3^(n+1)
    rw [pow_succ,← hj]
    omega
  have hv : Valid M lb rb s.previous (ScalingSafety.digit t g)
      (label M (n+1) k) (label M (n+1) (k+1)) := by
    refine ⟨rfl,rfl,?_,label_conservation M n k,?_,?_,?_,?_,?_,?_⟩
    · exact hnh n
    · intro r hz
      have hc : counter M n r = 0 := of_decide_eq_true hz
      change weight (counter M n r) k = 1
      rw [hc,weight_zero_counter]
    · intro hh r
      rw [hl hh]; exact carry_left M _ r
    · intro hh r hz
      have hc : counter M n r ≠ 0 := of_decide_eq_false hz
      change weight (counter M n r) k = 0
      rw [hl hh]; exact weight_left_positive _ (Nat.pos_of_ne_zero hc)
    · intro hh r
      rw [hr hh]; exact carry_right M n r
    · intro hp
      have hn := h.fresh hp
      subst n
      exact ⟨rfl,fun _ ↦ rfl⟩
    · intro old hp
      obtain ⟨hn,rfl⟩ := h.previous old hp
      have hn' : n-1+1 = n := by omega
      constructor
      · change (M.run n).1 = M.next (M.run (n-1)).1 (flags (M.run (n-1)).2)
        conv_lhs => rw [← hn',Machine.run]
        rfl
      · intro r
        rfl
  have he : step M s (geometricRound M n j t g) =
      ⟨ScalingSafety.Source.turn t g,lb,rb,some (label M (n+1) k).snapshot,true⟩ := by
    unfold step geometricRound
    rw [h.orientation,h.good]
    cases ScalingSafety.Source.turn t g <;>
      simp only [Bool.false_eq_true,↓reduceIte,Bool.true_and]
    all_goals rw [decide_eq_true hv]
  rw [he]
  refine ⟨rfl,rfl,hl,hr,?_,?_⟩
  · intro hh; cases hh
  · intro p hp; exact ⟨by omega,(Option.some.inj hp).symm⟩

def strategy : StrategyPair Unit Unit (Label Q) (Label Q) where
  one := fun v ↦ label M (ScalingSafety.Source.depth v) (ScalingSafety.coordinate v)
  two := fun v ↦ label M (ScalingSafety.Source.depth v) (ScalingSafety.coordinate v)
omit [DecidableEq Q] [Fintype Q] in
theorem nextRound_geometric (n j : Nat) (t : Bool)
    (history : History Unit Unit Graph (Label Q) (Label Q)) (e : EnvironmentRound Unit Unit)
    (h : ScalingSafety.Source.ViewGeometry n j t (currentView .one history) (currentView .two history)) :
    nextRound (strategy M) history e = geometricRound M n j t e.graph := by
  have hg := ScalingSafety.Source.advance_geometry n j t _ _ e h
  change ScalingSafety.Source.ViewGeometry (n+1) (ScalingSafety.Source.childIndex j t e.graph)
    (ScalingSafety.Source.turn t e.graph) (nextView .one history e) (nextView .two history e) at hg
  rcases hg with ⟨hdv,hdu,hv,hu⟩
  unfold nextRound geometricRound
  simp only [strategy,hdv,hdu,hv,hu]
  cases ScalingSafety.Source.turn t e.graph <;> simp
theorem execution_invariant (hnh : M.Nonhalting) (env : EnvironmentSequence Unit Unit) : ∀ n,
    ∃ j t, ScalingSafety.Source.ViewGeometry n j t
      (currentView .one (executionPrefix (strategy M) env n))
      (currentView .two (executionPrefix (strategy M) env n)) ∧
      Aligned M n j t ((objective M).run (execution (strategy M) env) n) := by
  intro n
  induction n with
  | zero => exact ⟨0,true,⟨rfl,rfl,rfl,rfl⟩,initial_aligned M⟩
  | succ n ih =>
    obtain ⟨j,t,hg,ha⟩ := ih
    refine ⟨ScalingSafety.Source.childIndex j t (env n).graph,
      ScalingSafety.Source.turn t (env n).graph,?_,?_⟩
    · rw [currentView_executionPrefix_succ,currentView_executionPrefix_succ]
      exact ScalingSafety.Source.advance_geometry n j t _ _ (env n) hg
    · rw [(objective M).run_succ,execution_apply,nextRound_geometric M n j t _ _ hg]
      exact geometric_step M hnh n j t _ (env n).graph ha
theorem wins (hnh : M.Nonhalting) : Rows.Winning M (strategy M) := by
  intro env
  apply (accepts_iff_good M _).mpr
  intro n
  obtain ⟨j,t,hg,ha⟩ := execution_invariant M hnh env n
  exact ha.good

/-- Exact realizability equivalence, in the actual full-view execution model. -/
theorem realizable_iff_nonhalting :
    (∃ σ : StrategyPair Unit Unit (Label Q) (Label Q), Rows.Winning M σ) ↔ M.Nonhalting :=
  ⟨fun ⟨σ,h⟩ ↦ Rows.winning_implies_nonhalting M σ h,fun h ↦ ⟨strategy M,wins M h⟩⟩

end DistributedSynthesis.CounterMachine.Source
