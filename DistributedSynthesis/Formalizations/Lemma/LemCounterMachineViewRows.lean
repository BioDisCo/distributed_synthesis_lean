/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Formalizations.Lemma.LemCounterMachineMonitor

/-! # Actual perfect-recall strategy rows; no finite-controller hypothesis -/
namespace DistributedSynthesis.CounterMachine.Rows
open ScalingRow

abbrev Vertex := View Unit Unit .one ⊕ View Unit Unit .two
abbrev Cell (Q : Type*) := (View Unit Unit .one × View Unit Unit .two) × State Q

variable {Q : Type*} [DecidableEq Q] [Fintype Q]
variable (M : Machine Q) (σ : StrategyPair Unit Unit (Label Q) (Label Q))

def root : Cell Q := ((.empty .one,.empty .two),⟨true,true,true,none,true⟩)
def emit : Vertex → Label Q := Sum.elim σ.one σ.two
def blind : Vertex → Vertex
  | .inl v => .inl (.noRecv v (.inl ()))
  | .inr v => .inr (.noRecv v (.inr ()))
def left (s : Cell Q) : Vertex := if s.2.oneLeft then .inl s.1.1 else .inr s.1.2
def right (s : Cell Q) : Vertex := if s.2.oneLeft then .inr s.1.2 else .inl s.1.1
def label (s : Cell Q) : Label Q := emit σ (left s)
def plan (s : Cell Q) (k : Fin 2) : Plan := (label σ s).right k
def bit (k : Fin 2) (s : Cell Q) : Fin 2 := (plan σ s k).weight
def weight (k : Fin 2) (s : Cell Q) : Nat := (bit σ k s).val
def promised (k : Fin 2) (s : Cell Q) : Nat := (plan σ s k).promised
def carry (k : Fin 2) (v : Vertex) : Nat := ((emit σ v).carry k).val
def header (v : Vertex) : Q × (Fin 2 → Bool) := ((emit σ v).control,(emit σ v).zero)

def advance (s : Cell Q) (g : Graph) : Cell Q :=
  let v := advanceViewsWithEnvironment s.1 ⟨(),(),g⟩
  (v,step M s.2 ⟨(),(),g,σ.one v.1,σ.two v.2⟩)
def nodeState (path : List Graph) : Cell Q := path.foldl (advance M σ) root
def Reachable (s : Cell Q) : Prop := ∃ path, nodeState M σ path = s

theorem at_append (path : List Graph) (g : Graph) :
    nodeState M σ (path ++ [g]) = advance M σ (nodeState M σ path) g := by
  simp [nodeState,List.foldl_append]
theorem reachable_advance {s : Cell Q} (h : Reachable M σ s) (g : Graph) :
    Reachable M σ (advance M σ s g) := by
  obtain ⟨path,rfl⟩ := h
  exact ⟨path ++ [g],at_append M σ path g⟩

def trace (env : EnvironmentSequence Unit Unit) : Nat → Cell Q
  | 0 => root
  | n+1 => advance M σ (trace env n) (env n).graph

theorem trace_views (env : EnvironmentSequence Unit Unit) (n : Nat) :
    (trace M σ env n).1 = ScalingSafety.ResidueLTL.views env n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change advanceViewsWithEnvironment (trace M σ env n).1 ⟨(),(),(env n).graph⟩ = _
    rw [ih]
    rfl

theorem trace_monitor (env : EnvironmentSequence Unit Unit) (n : Nat) :
    (trace M σ env n).2 = (objective M).run (execution σ env) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [(objective M).run_succ,ScalingSafety.ResidueLTL.execution_record]
    change step M (trace M σ env n).2
      ⟨(),(),(env n).graph,σ.one (trace M σ env (n+1)).1.1,
        σ.two (trace M σ env (n+1)).1.2⟩ = _
    rw [ih,trace_views]
    rfl

theorem trace_at (env : EnvironmentSequence Unit Unit) (n : Nat) :
    trace M σ env n = nodeState M σ (branchNode (fun k ↦ (env k).graph) n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [branchNode,at_append,trace,ih]

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
      ih (by omega),List.getD_eq_getElem path .both (by omega),
      List.take_add_one,List.getElem?_eq_getElem (by omega)]
    rfl

def Winning : Prop := ∀ env, (objective M).Accepts (execution σ env)

theorem reachable_good (hwin : Winning M σ) {s : Cell Q} (hs : Reachable M σ s) :
    s.2.good = true := by
  obtain ⟨path,rfl⟩ := hs
  have h := (accepts_iff_good M _).mp (hwin (extend path)) path.length
  rw [← trace_monitor,trace_at,extend_prefix path _ le_rfl,List.take_length] at h
  exact h

def Checked (s : Cell Q) (prev : Option (Snapshot Q)) (d : Fin 3) : Prop :=
  Valid M s.2.leftBoundary s.2.rightBoundary prev d (label σ s) (emit σ (right s))

theorem advance_checked (s : Cell Q) (g : Graph)
    (h : (advance M σ s g).2.good = true) :
    Checked M σ (advance M σ s g) s.2.previous (ScalingSafety.digit s.2.oneLeft g) := by
  have hv := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  cases ht : s.2.oneLeft <;> cases g <;>
    simpa [Checked,advance,step,left,right,emit,label,ScalingSafety.Source.turn,ht] using hv

theorem advance_previous (s : Cell Q) (g : Graph) :
    (advance M σ s g).2.previous = some (label σ (advance M σ s g)).snapshot := by
  cases ht : s.2.oneLeft <;> cases g <;>
    simp [advance,step,left,emit,label,ScalingSafety.Source.turn,ht]

def children (s : Cell Q) : List (Cell Q) := if s.2.oneLeft then
  [advance M σ s .right,advance M σ s .both,advance M σ s .left] else
  [advance M σ s .left,advance M σ s .both,advance M σ s .right]
theorem mem_children {s z : Cell Q} (hz : z ∈ children M σ s) :
    ∃ g, z = advance M σ s g := by
  cases ht : s.2.oneLeft <;> simp [children,ht] at hz
  all_goals rcases hz with rfl | rfl | rfl <;> exact ⟨_,rfl⟩

private theorem three_path {E V : Type*} (l r : E → V) (a b c : E)
    (hab : r a = l b) (hbc : r b = l c) : Path l r (l a) [a,b,c] (r c) := by
  apply Path.cons
  rw [hab]
  apply Path.cons
  rw [hbc]
  exact .cons _ (.nil _)

theorem children_path (s : Cell Q) :
    Path left right (blind (left s)) (children M σ s) (blind (right s)) := by
  cases ht : s.2.oneLeft
  · have h := three_path left right
      (advance M σ s .left) (advance M σ s .both) (advance M σ s .right)
    convert h ?_ ?_ using 1 <;>
      simp [children,left,right,blind,advance,step,ScalingSafety.Source.turn,ht,advanceViewsWithEnvironment]
  · have h := three_path left right
      (advance M σ s .right) (advance M σ s .both) (advance M σ s .left)
    convert h ?_ ?_ using 1 <;>
      simp [children,left,right,blind,advance,step,ScalingSafety.Source.turn,ht,advanceViewsWithEnvironment]

def row : Nat → List (Cell Q)
  | 0 => [root]
  | n+1 => (row n).flatMap (children M σ)
theorem row_path (n : Nat) : Path left right
    (blind^[n] (left (root : Cell Q))) (row M σ n) (blind^[n] (right (root : Cell Q))) := by
  induction n with
  | zero => exact .cons _ (.nil _)
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using ih.refine (children M σ) blind (children_path M σ)
theorem row_length (n : Nat) : (row M σ n).length = 3^n := by
  have aux : ∀ xs : List (Cell Q), (xs.flatMap (children M σ)).length = 3*xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons s xs ih =>
      cases ht : s.2.oneLeft <;> simp [List.flatMap_cons,children,ht,ih] <;> omega
  induction n with
  | zero => rfl
  | succ n ih => rw [row,aux,ih,pow_succ,Nat.mul_comm]
theorem row_reachable (n : Nat) : ∀ s ∈ row M σ n, Reachable M σ s := by
  induction n with
  | zero => intro s hs; simp only [row,List.mem_singleton] at hs; subst s; exact ⟨[],rfl⟩
  | succ n ih =>
    intro s hs
    obtain ⟨z,hz,hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨g,rfl⟩ := mem_children M σ hs
    exact reachable_advance M σ (ih z hz) g
theorem row_checked (hwin : Winning M σ) (n : Nat) {s : Cell Q} (hs : s ∈ row M σ (n+1)) :
    ∃ prev d, Checked M σ s prev d := by
  obtain ⟨z,hz,hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨g,rfl⟩ := mem_children M σ hs
  exact ⟨_,_,advance_checked M σ z g
    (reachable_good M σ hwin (reachable_advance M σ (row_reachable M σ n z hz) g))⟩
theorem row_previous (n : Nat) {s : Cell Q} (hs : s ∈ row M σ (n+1)) :
    s.2.previous = some (label σ s).snapshot := by
  obtain ⟨z,hz,hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨g,rfl⟩ := mem_children M σ hs
  exact advance_previous M σ z g

end DistributedSynthesis.CounterMachine.Rows
