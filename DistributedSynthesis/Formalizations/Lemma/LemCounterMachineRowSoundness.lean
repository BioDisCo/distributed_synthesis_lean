/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Formalizations.Lemma.LemCounterMachineViewRows

/-! # Winning perfect-recall strategies force the actual counter-machine run -/
namespace DistributedSynthesis.CounterMachine.Rows
open ScalingRow
variable {Q : Type*} [DecidableEq Q] [Fintype Q]
variable (M : Machine Q) (σ : StrategyPair Unit Unit (Label Q) (Label Q))

def ray (g : Graph) (n : Nat) : Cell Q := (fun s ↦ advance M σ s g)^[n] root
theorem ray_succ (g : Graph) (n : Nat) : ray M σ g (n+1) = advance M σ (ray M σ g n) g :=
  Function.iterate_succ_apply' _ _ _
theorem ray_reachable (g : Graph) (n : Nat) : Reachable M σ (ray M σ g n) := by
  induction n with
  | zero => exact ⟨[],rfl⟩
  | succ n ih => rw [ray_succ]; exact reachable_advance M σ ih g
theorem right_ray_flags (n : Nat) :
    (ray M σ .right n).2.oneLeft = true ∧ (ray M σ .right n).2.leftBoundary = true := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => rw [ray_succ]; simp [advance,step,ScalingSafety.digit,ScalingSafety.Source.turn,ih.1,ih.2]
theorem left_ray_flags (n : Nat) :
    (ray M σ .left n).2.oneLeft = true ∧ (ray M σ .left n).2.rightBoundary = true := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => rw [ray_succ]; simp [advance,step,ScalingSafety.digit,ScalingSafety.Source.turn,ih.1,ih.2]
theorem right_ray_end (n : Nat) :
    left (ray M σ .right n) = blind^[n] (left (root : Cell Q)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ray_succ,Function.iterate_succ_apply',← ih]
    simp [left,blind,advance,step,ScalingSafety.Source.turn,
      advanceViewsWithEnvironment,(right_ray_flags M σ n).1]
theorem left_ray_end (n : Nat) :
    right (ray M σ .left n) = blind^[n] (right (root : Cell Q)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ray_succ,Function.iterate_succ_apply',← ih]
    simp [right,blind,advance,step,ScalingSafety.Source.turn,
      advanceViewsWithEnvironment,(left_ray_flags M σ n).1]
theorem ray_checked (hwin : Winning M σ) (g : Graph) (n : Nat) :
    Checked M σ (ray M σ g (n+1)) (ray M σ g n).2.previous
      (ScalingSafety.digit (ray M σ g n).2.oneLeft g) := by
  rw [ray_succ]
  exact advance_checked M σ _ _
    (reachable_good M σ hwin (reachable_advance M σ (ray_reachable M σ g n) g))
theorem row_head (n : Nat) : ∃ tail, row M σ n = ray M σ .right n :: tail := by
  induction n with
  | zero => exact ⟨[],rfl⟩
  | succ n ih =>
    obtain ⟨tail,ht⟩ := ih
    simp [row,ht,children,(right_ray_flags M σ n).1,ray_succ]
theorem boundary_carries (hwin : Winning M σ) (n : Nat) (k : Fin 2) :
    carry σ k (blind^[n+1] (left (root : Cell Q))) = 0 ∧
      carry σ k (blind^[n+1] (right (root : Cell Q))) = 0 := by
  rw [← right_ray_end M σ,← left_ray_end M σ]
  exact ⟨(ray_checked M σ hwin .right n).leftCarry (right_ray_flags M σ (n+1)).2 k,
    (ray_checked M σ hwin .left n).rightCarry (left_ray_flags M σ (n+1)).2 k⟩

private theorem uniform_value {E V A : Type*} {l r : E → V} {a b : V} {xs : List E}
    (h : Path l r a xs b) (value : V → A)
    (heq : ∀ e ∈ xs, value (l e) = value (r e)) :
    value b = value a ∧ ∀ e ∈ xs, value (l e) = value a := by
  induction h with
  | nil => simp
  | cons e h ih =>
    have hf := heq e (by simp)
    obtain ⟨hl,hr⟩ := ih (fun f hh ↦ heq f (by simp [hh]))
    refine ⟨hl.trans hf.symm,?_⟩
    intro f hh
    rcases List.mem_cons.mp hh with rfl | hh
    · rfl
    · exact (hr f hh).trans hf.symm

def rowHeader (n : Nat) := header σ (blind^[n+1] (left (root : Cell Q)))
def rowControl (n : Nat) := (rowHeader σ n).1
def rowZero (n : Nat) := (rowHeader σ n).2
def rowMass (n : Nat) (k : Fin 2) := ((row M σ (n+1)).map (weight σ k)).sum
theorem ray_header (n : Nat) :
    header σ (left (ray M σ .right (n+1))) = rowHeader σ n := by
  rw [right_ray_end]; rfl
theorem row_uniform (hwin : Winning M σ) (n : Nat) {s : Cell Q}
    (hs : s ∈ row M σ (n+1)) :
    (label σ s).control = rowControl σ n ∧ (label σ s).zero = rowZero σ n := by
  have hu := uniform_value (row_path M σ (n+1)) (header σ) ?_
  · have hh := hu.2 s hs
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  · intro e he
    obtain ⟨p,d,h⟩ := row_checked M σ hwin n he
    exact Prod.ext h.control h.zero
theorem children_weight_sum (hwin : Winning M σ) {s : Cell Q} (hs : Reachable M σ s)
    (hp : s.2.previous = some (label σ s).snapshot) (k : Fin 2) :
    ((children M σ s).map (weight σ k)).sum = promised σ k s := by
  have heq (g : Graph) : weight σ k (advance M σ s g) =
      ((plan σ s k).child (ScalingSafety.digit s.2.oneLeft g)).val :=
    congrArg Fin.val (((advance_checked M σ s g
      (reachable_good M σ hwin (reachable_advance M σ hs g))).next _ hp).2 k)
  cases ht : s.2.oneLeft <;>
    simp [children,ht,heq,ScalingSafety.digit,promised,Plan.promised,Nat.add_assoc]

theorem row_recurrence (hwin : Winning M σ) (n : Nat) (k : Fin 2) :
    rowMass M σ (n+1) k = (M.op (rowControl σ n) (rowZero σ n) k).factor * rowMass M σ n k := by
  have hb := (row_path M σ (n+1)).balance (carry σ k) (weight σ k) (promised σ k)
    (M.op (rowControl σ n) (rowZero σ n) k).factor ?_
  · have hboundary := boundary_carries M σ hwin n k
    rw [hboundary.1,hboundary.2,Nat.add_zero,Nat.add_zero] at hb
    change (((row M σ (n+1)).flatMap (children M σ)).map (weight σ k)).sum = _
    rw [List.map_flatMap]
    simp only [List.flatMap_def,List.sum_flatten,List.map_map,Function.comp_def]
    have heq : (row M σ (n+1)).map (fun s ↦ ((children M σ s).map (weight σ k)).sum) =
        (row M σ (n+1)).map (promised σ k) := by
      apply List.map_congr_left
      intro s hs
      exact children_weight_sum M σ hwin (row_reachable M σ (n+1) s hs) (row_previous M σ n hs) k
    rw [heq]
    exact hb
  · intro s hs
    obtain ⟨p,d,h⟩ := row_checked M σ hwin n hs
    have hc := h.balance k
    rw [(row_uniform M σ hwin n hs).1,(row_uniform M σ hwin n hs).2] at hc
    exact hc

theorem row_guard (hwin : Winning M σ) (n : Nat) (k : Fin 2) :
    TernaryCounter.Guard (rowZero σ n k) ((row M σ (n+1)).map (bit σ k)) := by
  constructor
  · intro hz x hx
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
    obtain ⟨p,d,h⟩ := row_checked M σ hwin n hs
    exact h.zeroWeight k (by rw [(row_uniform M σ hwin n hs).2]; exact hz)
  · intro hz
    obtain ⟨tail,ht⟩ := row_head M σ (n+1)
    refine ⟨tail.map (bit σ k),?_⟩
    rw [ht,List.map_cons]
    have hh := congrArg Prod.snd (ray_header M σ n)
    have hw := (ray_checked M σ hwin .right n).leftWeight
      (right_ray_flags M σ (n+1)).2 k (by change (label σ _).zero = _ at hh; rw [hh]; exact hz)
    have hb : bit σ k (ray M σ .right (n+1)) = 0 := Fin.ext hw
    rw [hb]

theorem row_zero_exact (hwin : Winning M σ) (n : Nat) (k : Fin 2) :
    rowZero σ n k = true ↔ rowMass M σ n k = 3^(n+1) := by
  have h := TernaryCounter.guard_exact (row_guard M σ hwin n k)
  simpa only [TernaryCounter.rowMass,List.map_map,List.length_map,row_length,
    Function.comp_def,weight,rowMass] using h

theorem row_initial_weight (hwin : Winning M σ) {s : Cell Q} (hs : s ∈ row M σ 1) (k : Fin 2) :
    (bit σ k s).val = 1 := by
  obtain ⟨z,hz,hs⟩ := List.mem_flatMap.mp hs
  have he : z = root := List.mem_singleton.mp hz
  subst z
  obtain ⟨g,rfl⟩ := mem_children M σ hs
  have checked := advance_checked M σ root g (reachable_good M σ hwin
    (reachable_advance M σ ⟨[],rfl⟩ g))
  exact checked.zeroWeight k ((checked.initial rfl).2 k)
theorem row_initial_mass (hwin : Winning M σ) (k : Fin 2) : rowMass M σ 0 k = 3 := by
  have h := TernaryCounter.rowMass_all_one ((row M σ 1).map (bit σ k)) ?_
  · simpa only [TernaryCounter.rowMass,List.map_map,List.length_map,row_length,
      Function.comp_def,weight,rowMass] using h
  · intro x hx
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
    exact row_initial_weight M σ hwin hs k
theorem row_initial_control (hwin : Winning M σ) : rowControl σ 0 = M.initial := by
  have hh := congrArg Prod.fst (ray_header M σ 0)
  exact hh.symm.trans ((ray_checked M σ hwin .right 0).initial rfl).1
theorem row_control_next (hwin : Winning M σ) (n : Nat) :
    rowControl σ (n+1) = M.next (rowControl σ n) (rowZero σ n) := by
  have hp : (ray M σ .right (n+1)).2.previous =
      some (label σ (ray M σ .right (n+1))).snapshot := by
    rw [ray_succ]; exact advance_previous M σ _ _
  have hn := ((ray_checked M σ hwin .right (n+1)).next _ hp).1
  have hq := congrArg Prod.fst (ray_header M σ n)
  have hz := congrArg Prod.snd (ray_header M σ n)
  have hq' := congrArg Prod.fst (ray_header M σ (n+1))
  change (label σ _).control = rowControl σ n at hq
  change (label σ _).zero = rowZero σ n at hz
  change (label σ _).control = rowControl σ (n+1) at hq'
  simpa only [Label.snapshot,hq,hz,hq'] using hn
theorem row_live (hwin : Winning M σ) (n : Nat) : M.code (rowControl σ n) ≠ none := by
  have h := (ray_checked M σ hwin .right n).live
  have hh := congrArg Prod.fst (ray_header M σ n)
  change (label σ _).control = rowControl σ n at hh
  rw [← hh]
  exact h

def rowOps (k : Fin 2) (n : Nat) := M.op (rowControl σ n) (rowZero σ n) k
def extractedCounters (n : Nat) : Fin 2 → Nat := fun k ↦ TernaryCounter.count (rowOps M σ k) n
theorem forced_counters (hwin : Winning M σ) (n : Nat) (k : Fin 2) :
    rowMass M σ n k * 3^(extractedCounters M σ n k) = 3^(n+1) ∧
      (rowZero σ n k = true ↔ extractedCounters M σ n k = 0) := by
  exact TernaryCounter.forced_counts (fun n ↦ rowMass M σ n k) (fun n ↦ rowZero σ n k)
    (rowOps M σ k) (row_initial_mass M σ hwin k) (fun n ↦ row_zero_exact M σ hwin n k)
    (fun n h ↦ M.op_decrement _ _ k h) (fun n ↦ row_recurrence M σ hwin n k) n
theorem extracted_flags (hwin : Winning M σ) (n : Nat) :
    flags (extractedCounters M σ n) = rowZero σ n := by
  funext k
  have hz := (forced_counters M σ hwin n k).2
  cases h : rowZero σ n k <;> simp_all [flags]

/-- There is no guessed computation in this statement: the control and
counter sequence extracted from the strategy equals the machine's own run. -/
theorem extracted_eq_run (hwin : Winning M σ) (n : Nat) :
    (rowControl σ n,extractedCounters M σ n) = M.run n := by
  induction n with
  | zero => exact Prod.ext (row_initial_control M σ hwin) rfl
  | succ n ih =>
    rw [Machine.run,← ih]
    apply Prod.ext
    · simpa only [Machine.advance,extracted_flags M σ hwin n] using row_control_next M σ hwin n
    · funext k
      change (rowOps M σ k n).applyCount (extractedCounters M σ n k) = _
      simp only [Machine.advance,extracted_flags M σ hwin n,rowOps]

/-- End-to-end soundness for the literal finite monitor and arbitrary local
perfect-recall strategies. No row certificate or finite-memory premise remains. -/
theorem winning_implies_nonhalting (hwin : Winning M σ) : M.Nonhalting := by
  intro n
  rw [← extracted_eq_run M σ hwin n]
  exact row_live M σ hwin n

end DistributedSynthesis.CounterMachine.Rows
