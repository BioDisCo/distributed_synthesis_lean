/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemScalingSafetyObjective
import DistributedSynthesis.Formalizations.Lemma.LemScalingRowPath

/-! # Actual finite-controller rows in reflected graph order -/

namespace DistributedSynthesis.ScalingSafety.Physical
open ScalingRow

universe u v
variable (C : FinitePairedPhysicalController.{0,0,0,0,u,v} Unit Unit Label Label)

abbrev Cell := (C.OneControl × C.TwoControl) × State
abbrev Vertex := C.OneControl ⊕ C.TwoControl

def root : Cell C := ((C.initialOne,C.initialTwo),objective.initial)
def emit : Vertex C → Label := Sum.elim C.outputOne C.outputTwo
def blind : Vertex C → Vertex C
  | .inl c => .inl (C.noRecvOne c ())
  | .inr c => .inr (C.noRecvTwo c ())
def left (s : Cell C) : Vertex C := if s.2.oneLeft then .inl s.1.1 else .inr s.1.2
def right (s : Cell C) : Vertex C := if s.2.oneLeft then .inr s.1.2 else .inl s.1.1
def plan (s : Cell C) : Plan := (emit C (left C s)).right
def weight (s : Cell C) : Nat := (plan C s).value
def promised (s : Cell C) : Nat :=
  (plan C s).childValue 0 + (plan C s).childValue 1 + (plan C s).childValue 2
def mode (c : Vertex C) : Nat := (emit C c).multiplier
def carry (c : Vertex C) : Nat := (emit C c).carry.val

def advance (s : Cell C) (g : Graph) : Cell C :=
  let controls := C.advanceControls s.1 ⟨(),(),g⟩
  (controls, step s.2 ⟨(),(),g,C.outputOne controls.1,C.outputTwo controls.2⟩)

def nodeState (path : List Graph) : Cell C := path.foldl (advance C) (root C)

theorem at_append (path : List Graph) (g : Graph) :
    nodeState C (path ++ [g]) = advance C (nodeState C path) g := by simp [nodeState, List.foldl_append]

def Reachable (s : Cell C) : Prop := ∃ path, nodeState C path = s

theorem reachable_advance {s : Cell C} (h : Reachable C s) (g : Graph) :
    Reachable C (advance C s g) := by
  obtain ⟨path,rfl⟩ := h
  exact ⟨path ++ [g],at_append C path g⟩

def trace (env : EnvironmentSequence Unit Unit) : Nat → Cell C
  | 0 => root C
  | n+1 => advance C (trace env n) (env n).graph

theorem trace_controls (env : EnvironmentSequence Unit Unit) (n : Nat) :
    (trace C env n).1 = C.globalMachine.globalStateTrace env n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change C.advanceControls (trace C env n).1 ⟨(),(),(env n).graph⟩ =
      C.advanceControls (C.globalMachine.globalStateTrace env n) (env n)
    rw [ih]

theorem trace_monitor (env : EnvironmentSequence Unit Unit) (n : Nat) :
    (trace C env n).2 = objective.run
      (C.globalMachine.globalMachineTraceWord C.globalOutputOne C.globalOutputTwo env) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [objective.run_succ]
    change step (trace C env n).2
      ⟨(),(),(env n).graph,C.outputOne (trace C env (n+1)).1.1,
        C.outputTwo (trace C env (n+1)).1.2⟩ = _
    rw [ih, trace_controls]
    rfl

theorem trace_at (env : EnvironmentSequence Unit Unit) (n : Nat) :
    trace C env n = nodeState C (branchNode (fun k ↦ (env k).graph) n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [branchNode, at_append, trace, ih]

private def extend (path : List Graph) : EnvironmentSequence Unit Unit :=
  fun n ↦ ⟨(),(),path.getD n .both⟩

private theorem extend_prefix (path : List Graph) : ∀ n, n ≤ path.length →
    branchNode (fun k ↦ (extend path k).graph) n = path.take n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [show branchNode (fun k ↦ (extend path k).graph) (n+1) =
      branchNode (fun k ↦ (extend path k).graph) n ++ [path.getD n .both] from rfl,
      ih (by omega), List.getD_eq_getElem path .both (by omega),
      List.take_add_one, List.getElem?_eq_getElem (by omega)]
    rfl

def Winning : Prop := ∀ env, objective.Accepts
  (C.globalMachine.globalMachineTraceWord C.globalOutputOne C.globalOutputTwo env)

theorem reachable_good (hwin : Winning C) {s : Cell C} (hs : Reachable C s) : s.2.good = true := by
  obtain ⟨path,rfl⟩ := hs
  have h := (accepts_iff_good _).mp (hwin (extend path)) path.length
  rw [← trace_monitor, trace_at, extend_prefix path _ (Nat.le_refl _), List.take_length] at h
  exact h

def Checked (s : Cell C) (previous : Option Plan) (d : Fin 3) : Prop :=
  let l := emit C (left C s)
  let r := emit C (right C s)
  l.up = r.up ∧ l.right = r.left ∧
    promised C s + l.carry.val = l.multiplier * weight C s + r.carry.val ∧
    (s.2.leftBoundary = true → l.carry.val = 0) ∧
    (s.2.rightBoundary = true → r.carry.val = 0) ∧
    (∀ old, previous = some old → weight C s = old.childValue d)

theorem advance_checked (s : Cell C) (g : Graph) (h : (advance C s g).2.good = true) :
    Checked C (advance C s g) s.2.previous (digit s.2.oneLeft g) := by
  have hv := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  cases ht : s.2.oneLeft <;> cases g <;>
    simpa [Checked, advance, step, left, right, emit, plan, promised, weight, ht] using hv

theorem advance_previous (s : Cell C) (g : Graph) :
    (advance C s g).2.previous = some (plan C (advance C s g)) := by
  cases ht : s.2.oneLeft <;> cases g <;>
    simp [advance, step, left, emit, plan, ht]

def children (s : Cell C) : List (Cell C) := if s.2.oneLeft then
  [advance C s .right,advance C s .both,advance C s .left] else
  [advance C s .left,advance C s .both,advance C s .right]

theorem mem_children {s z : Cell C} (hz : z ∈ children C s) :
    ∃ g, z = advance C s g := by
  cases ht : s.2.oneLeft <;> simp [children, ht] at hz
  all_goals rcases hz with rfl | rfl | rfl <;> exact ⟨_,rfl⟩

private theorem three_path {E V : Type*} (l r : E → V) (a b c : E)
    (hab : r a = l b) (hbc : r b = l c) :
    Path l r (l a) [a,b,c] (r c) := by
  apply Path.cons
  rw [hab]
  apply Path.cons
  rw [hbc]
  exact .cons _ (.nil _)

theorem children_path (s : Cell C) :
    Path (left C) (right C) (blind C (left C s)) (children C s) (blind C (right C s)) := by
  cases ht : s.2.oneLeft
  · have h := three_path (left C) (right C)
      (advance C s .left) (advance C s .both) (advance C s .right)
    convert h ?_ ?_ using 1 <;>
      simp [children, left, right, blind, advance, step, ht,
        FinitePairedPhysicalController.advanceControls]
  · have h := three_path (left C) (right C)
      (advance C s .right) (advance C s .both) (advance C s .left)
    convert h ?_ ?_ using 1 <;>
      simp [children, left, right, blind, advance, step, ht,
        FinitePairedPhysicalController.advanceControls]

def row : Nat → List (Cell C)
  | 0 => [root C]
  | n+1 => (row n).flatMap (children C)

theorem row_path (n : Nat) : Path (left C) (right C)
    ((blind C)^[n] (left C (root C))) (row C n) ((blind C)^[n] (right C (root C))) := by
  induction n with
  | zero => exact .cons _ (.nil _)
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using ih.refine (children C) (blind C) (children_path C)

theorem row_length (n : Nat) : (row C n).length = 3 ^ n := by
  have aux : ∀ xs : List (Cell C), (xs.flatMap (children C)).length = 3 * xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons s xs ih =>
      cases ht : s.2.oneLeft <;> simp [List.flatMap_cons, children, ht, ih] <;> omega
  induction n with
  | zero => rfl
  | succ n ih => rw [row, aux, ih, pow_succ, Nat.mul_comm]

theorem row_reachable (n : Nat) : ∀ s ∈ row C n, Reachable C s := by
  induction n with
  | zero => intro s hs; simp only [row,List.mem_singleton] at hs; subst s; exact ⟨[],rfl⟩
  | succ n ih =>
    intro s hs
    obtain ⟨z,hz,hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨g,rfl⟩ := mem_children C hs
    exact reachable_advance C (ih z hz) g

theorem row_checked (hwin : Winning C) (n : Nat) {s : Cell C} (hs : s ∈ row C (n+1)) :
    ∃ previous d, Checked C s previous d := by
  obtain ⟨z,hz,hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨g,rfl⟩ := mem_children C hs
  exact ⟨_,_,advance_checked C z g (reachable_good C hwin (reachable_advance C (row_reachable C n z hz) g))⟩

theorem row_previous (n : Nat) {s : Cell C} (hs : s ∈ row C (n+1)) :
    s.2.previous = some (plan C s) := by
  obtain ⟨z,hz,hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨g,rfl⟩ := mem_children C hs
  exact advance_previous C z g

def ray (g : Graph) (n : Nat) : Cell C := (fun s ↦ advance C s g)^[n] (root C)

theorem ray_succ (g : Graph) (n : Nat) : ray C g (n+1) = advance C (ray C g n) g :=
  Function.iterate_succ_apply' _ _ _

theorem ray_reachable (g : Graph) (n : Nat) : Reachable C (ray C g n) := by
  induction n with
  | zero => exact ⟨[],rfl⟩
  | succ n ih => rw [ray_succ]; exact reachable_advance C ih g

theorem right_ray_flags (n : Nat) :
    (ray C .right n).2.oneLeft = true ∧ (ray C .right n).2.leftBoundary = true := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => rw [ray_succ]; simp [advance,step,digit,ih.1,ih.2]

theorem left_ray_flags (n : Nat) :
    (ray C .left n).2.oneLeft = true ∧ (ray C .left n).2.rightBoundary = true := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => rw [ray_succ]; simp [advance,step,digit,ih.1,ih.2]

theorem right_ray_end (n : Nat) :
    left C (ray C .right n) = (blind C)^[n] (left C (root C)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ray_succ, Function.iterate_succ_apply', ← ih]
    simp [left,blind,advance,step,FinitePairedPhysicalController.advanceControls,(right_ray_flags C n).1]

theorem left_ray_end (n : Nat) :
    right C (ray C .left n) = (blind C)^[n] (right C (root C)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ray_succ, Function.iterate_succ_apply', ← ih]
    simp [right,blind,advance,step,FinitePairedPhysicalController.advanceControls,(left_ray_flags C n).1]

theorem boundary_carries (hwin : Winning C) (n : Nat) :
    carry C ((blind C)^[n+1] (left C (root C))) = 0 ∧
      carry C ((blind C)^[n+1] (right C (root C))) = 0 := by
  have hl := advance_checked C (ray C .right n) .right
    (reachable_good C hwin (reachable_advance C (ray_reachable C .right n) .right))
  have hr := advance_checked C (ray C .left n) .left
    (reachable_good C hwin (reachable_advance C (ray_reachable C .left n) .left))
  rw [← right_ray_end, ← left_ray_end]
  have hlf := (right_ray_flags C (n+1)).2
  have hrf := (left_ray_flags C (n+1)).2
  simp only [ray_succ] at hlf hrf ⊢
  exact ⟨hl.2.2.2.1 hlf, hr.2.2.2.2.1 hrf⟩

def rowMode (n : Nat) : Nat := mode C ((blind C)^[n+1] (left C (root C)))
def rowMass (n : Nat) : Nat := ((row C (n+1)).map (weight C)).sum

theorem row_uniform (hwin : Winning C) (n : Nat) :
    ∀ s ∈ row C (n+1), mode C (left C s) = rowMode C n := by
  apply ((row_path C (n+1)).uniform (mode C) ?_).2
  intro s hs
  obtain ⟨p,d,h⟩ := row_checked C hwin n hs
  change (if (emit C (left C s)).up then 4 else 2) =
    (if (emit C (right C s)).up then 4 else 2)
  rw [h.1]

theorem children_weight_sum (hwin : Winning C) {s : Cell C} (hs : Reachable C s)
    (hp : s.2.previous = some (plan C s)) :
    ((children C s).map (weight C)).sum = promised C s := by
  have heq (g : Graph) : weight C (advance C s g) = (plan C s).childValue (digit s.2.oneLeft g) :=
    (advance_checked C s g (reachable_good C hwin (reachable_advance C hs g))).2.2.2.2.2 _ hp
  cases ht : s.2.oneLeft <;>
    simp [children,ht,heq,digit,promised,Nat.add_assoc]

/-- The recurrence is extracted from all literal finite-controller rows;
no common-mode or conservation certificate is assumed. -/
theorem row_recurrence (hwin : Winning C) (n : Nat) :
    rowMass C (n+1) = rowMode C n * rowMass C n := by
  have hu := row_uniform C hwin n
  have hb := (row_path C (n+1)).balance (carry C) (weight C) (promised C) (rowMode C n) ?_
  · have hboundary := boundary_carries C hwin n
    rw [hboundary.1,hboundary.2,Nat.add_zero,Nat.add_zero] at hb
    change (((row C (n+1)).flatMap (children C)).map (weight C)).sum = _
    rw [List.map_flatMap]
    simp only [List.flatMap_def, List.sum_flatten, List.map_map, Function.comp_def]
    have heq : (row C (n+1)).map (fun s ↦ ((children C s).map (weight C)).sum) =
        (row C (n+1)).map (promised C) := by
      apply List.map_congr_left
      intro s hs
      exact children_weight_sum C hwin (row_reachable C (n+1) s hs) (row_previous C n hs)
    rw [heq]
    simpa only [Nat.add_zero] using hb
  · intro s hs
    obtain ⟨p,d,h⟩ := row_checked C hwin n hs
    have hc := h.2.2.1
    change promised C s + carry C (left C s) = mode C (left C s) * weight C s + carry C (right C s) at hc
    rw [← hu s hs]
    exact hc

theorem row_mass_bounds (n : Nat) :
    2 * 3 ^ (1+n) ≤ rowMass C n ∧ rowMass C n ≤ 4 * 3 ^ (1+n) := by
  have h := ScalingRow.sum_bounds (row C (n+1)) (weight C)
    (fun s _ ↦ plan_value_bounds (plan C s))
  simpa only [row_length, Nat.add_comm 1 n] using h

theorem row_mode_cases (n : Nat) : rowMode C n = 2 ∨ rowMode C n = 4 :=
  label_multiplier_cases _

end DistributedSynthesis.ScalingSafety.Physical
