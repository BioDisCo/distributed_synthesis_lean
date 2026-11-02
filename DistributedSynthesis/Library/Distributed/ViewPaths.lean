/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.Views
import DistributedSynthesis.Library.Combinatorics.Paths

/-! # The path of singleton-input full views

The vertices below are the existing model's tagged `View`s, not a substitute
observation model. Cells record the two actual views and their order on the
path. Every graph history occurs in the row at its depth.
-/

namespace DistributedSynthesis.FullViewPath
open ScalingRow

abbrev Vertex := View Unit Unit .one ⊕ View Unit Unit .two

def depth : {p : Proc} → View Unit Unit p → Nat
  | _, .empty _ => 0
  | _, .noRecv v _ => depth v + 1
  | _, .recv v _ _ _ => depth v + 1

structure Cell where
  one : View Unit Unit .one
  two : View Unit Unit .two
  oneLeft : Bool

def root : Cell := ⟨.empty .one, .empty .two, true⟩
def left (s : Cell) : Vertex := if s.oneLeft then .inl s.one else .inr s.two
def right (s : Cell) : Vertex := if s.oneLeft then .inr s.two else .inl s.one
def blind : Vertex → Vertex
  | .inl v => .inl (.noRecv v (.inl ()))
  | .inr v => .inr (.noRecv v (.inr ()))

def advance (s : Cell) (g : Graph) : Cell :=
  let v := advanceViews (s.one, s.two)
    (⟨(), (), g, (), ()⟩ : RoundRecord Unit Unit Graph Unit Unit)
  ⟨v.1, v.2, if g = .both then !s.oneLeft else s.oneLeft⟩

def evaluate (h : List Graph) : Cell := h.foldl advance root

@[simp] theorem at_nil : evaluate [] = root := rfl
@[simp] theorem at_append (h : List Graph) (g : Graph) :
    evaluate (h ++ [g]) = advance (evaluate h) g := by simp [evaluate, List.foldl_append]

/-- This evaluation is precisely the model's history evaluation with singleton
inputs and irrelevant singleton outputs. -/
theorem at_views (h : List Graph) :
    ((evaluate h).one, (evaluate h).two) = viewPair
      (h.map fun g ↦ (⟨(), (), g, (), ()⟩ : RoundRecord Unit Unit Graph Unit Unit)) := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h g ih =>
    rw [at_append, List.map_append]
    change advanceViews ((evaluate h).one, (evaluate h).two) _ = viewPair (_ ++ [_])
    rw [ih]
    exact (viewPair_append _ _).symm

theorem at_depth (h : List Graph) :
    depth (evaluate h).one = h.length ∧ depth (evaluate h).two = h.length := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton h g ih =>
    rw [at_append]
    cases g <;> simp [advance, advanceViews, depth, ih]

/-- Arbitrary past outputs have no effect on the full views. Thus the path
evaluation applies to the actual histories produced by any strategy pair. -/
theorem evaluate_graphSequence {Out₁ Out₂ : Type*}
    (h : History Unit Unit Graph Out₁ Out₂) :
    ((evaluate (History.graphSequence h)).one, (evaluate (History.graphSequence h)).two) =
      viewPair h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h r ih =>
    rw [show History.graphSequence (h ++ [r]) = History.graphSequence h ++ [r.graph] from
      History.graphSequence_append h r, at_append]
    change advanceViews ((evaluate (History.graphSequence h)).one,
      (evaluate (History.graphSequence h)).two) _ = viewPair (h ++ [r])
    rw [ih, show viewPair (h ++ [r]) = advanceViews (viewPair h) r from viewPair_append h r]
    cases r with
    | mk i j g o p => cases i; cases j; rfl

def children (s : Cell) : List Cell := if s.oneLeft then
  [advance s .right, advance s .both, advance s .left] else
  [advance s .left, advance s .both, advance s .right]

theorem mem_children (s z : Cell) : z ∈ children s ↔ ∃ g, z = advance s g := by
  cases ht : s.oneLeft <;> simp only [children, ht, Bool.false_eq_true,
    ↓reduceIte, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  all_goals
    constructor
    · intro h
      rcases h with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    · rintro ⟨g, rfl⟩
      cases g <;> simp

private theorem three_path {E V : Type*} (l r : E → V) (a b c : E)
    (hab : r a = l b) (hbc : r b = l c) : Path l r (l a) [a,b,c] (r c) := by
  apply Path.cons
  rw [hab]
  apply Path.cons
  rw [hbc]
  exact .cons _ (.nil _)

theorem children_path (s : Cell) :
    Path left right (blind (left s)) (children s) (blind (right s)) := by
  cases ht : s.oneLeft
  · have h := three_path left right
      (advance s .left) (advance s .both) (advance s .right)
    convert h ?_ ?_ using 1 <;>
      simp [children, left, right, blind, advance, ht, advanceViews]
  · have h := three_path left right
      (advance s .right) (advance s .both) (advance s .left)
    convert h ?_ ?_ using 1 <;>
      simp [children, left, right, blind, advance, ht, advanceViews]

def row : Nat → List Cell
  | 0 => [root]
  | t+1 => (row t).flatMap children

theorem row_path (t : Nat) : Path left right
    (blind^[t] (left root)) (row t) (blind^[t] (right root)) := by
  induction t with
  | zero => exact .cons _ (.nil _)
  | succ t ih =>
    simpa only [Function.iterate_succ_apply'] using
      ih.refine children blind children_path

theorem mem_row_iff (t : Nat) (s : Cell) :
    s ∈ row t ↔ ∃ h : List Graph, h.length = t ∧ evaluate h = s := by
  induction t generalizing s with
  | zero => simp [row, List.length_eq_zero_iff, evaluate, root, eq_comm]
  | succ t ih =>
    constructor
    · intro hs
      obtain ⟨z, hz, hs⟩ := List.mem_flatMap.mp hs
      obtain ⟨h, ht, rfl⟩ := (ih z).mp hz
      obtain ⟨g, rfl⟩ := (mem_children _ _).mp hs
      exact ⟨h ++ [g], by simp [ht], at_append h g⟩
    · rintro ⟨h, ht, rfl⟩
      cases h using List.reverseRecOn with
      | nil => simp at ht
      | append_singleton h g =>
        rw [at_append]
        apply List.mem_flatMap.mpr
        refine ⟨evaluate h, (ih _).mpr ⟨h, by simpa using ht, rfl⟩, ?_⟩
        exact (mem_children _ _).mpr ⟨g, rfl⟩

theorem left_visited {a b : Vertex} {xs : List Cell}
    (h : Path left right a xs b) {s : Cell} (hs : s ∈ xs) :
    Path.Visits right a xs (left s) := by
  induction h with
  | nil => simp at hs
  | cons e h ih =>
    rcases List.mem_cons.mp hs with rfl | hs
    · exact Or.inl rfl
    · exact (Path.visits_cons h).mpr (Or.inr (ih hs))

theorem endpoints_visited {t : Nat} {s : Cell} (hs : s ∈ row t) :
    Path.Visits right (blind^[t] (left root)) (row t) (left s) ∧
    Path.Visits right (blind^[t] (left root)) (row t) (right s) :=
  ⟨left_visited (row_path t) hs, Or.inr ⟨s, hs, rfl⟩⟩

end DistributedSynthesis.FullViewPath
