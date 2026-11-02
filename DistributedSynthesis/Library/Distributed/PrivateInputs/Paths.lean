/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphExecutions

/-! # The communication view paths encoded by private ternary inputs

`none`, `some true`, and `some false` represent the displacements 0, +1,
and -1. No existing graph or view definition is extended. Equality of the
private words is proved equivalent to equality of the original full views.
-/

namespace DistributedSynthesis.PrivateInputs
open FullViewPath PaddingProjection

abbrev Symbol := Option Bool
abbrev Input := Symbol × Symbol

def pair (s : Bool) : Graph → Input
  | .right => (none, some (!s))
  | .both => (some s, some (!s))
  | .left => (some s, none)

def incoming : Input → Bool
  | (some s, _) => s
  | (none, some s) => !s
  | (none, none) => true

def graph : Input → Graph
  | (none, _) => .right
  | (_, none) => .left
  | _ => .both

def turn (s : Bool) (g : Graph) : Bool := if g = .both then !s else s
def outgoing (a : Input) : Bool := turn (incoming a) (graph a)
def Valid (a : Input) : Prop := a = pair (incoming a) (graph a)

@[simp] theorem incoming_pair (s : Bool) (g : Graph) : incoming (pair s g) = s := by
  cases s <;> cases g <;> rfl
@[simp] theorem graph_pair (s : Bool) (g : Graph) : graph (pair s g) = g := by
  cases s <;> cases g <;> rfl
@[simp] theorem outgoing_pair (s : Bool) (g : Graph) : outgoing (pair s g) = turn s g := by
  simp [outgoing]
@[simp] theorem valid_pair (s : Bool) (g : Graph) : Valid (pair s g) := by
  simp [Valid]

def word : {p : Proc} → View Unit Unit p → List Symbol
  | _, .empty _ => []
  | _, .noRecv v _ => word v ++ [none]
  | _, .recv v _ u _ => word v ++ [some (decide (project (fun _ ↦ true) v <
      project (fun _ ↦ true) u))]

@[simp] theorem word_length {p : Proc} (v : View Unit Unit p) :
    (word v).length = depth v := by
  induction v with
  | empty => rfl
  | noRecv v a ih => simp [word, depth, ih]
  | recv v a u b ihv ihu => simp [word, depth, ihv]

def positionStep (p : Nat) : Symbol → Nat
  | none => 3*p
  | some true => 3*p+2
  | some false => 3*p-2

def position (p : Proc) (w : List Symbol) : Nat :=
  w.foldl positionStep (if p = .one then 0 else 1)

theorem gap (h : List Graph) :
    if (evaluate h).oneLeft then
      project (fun _ ↦ true) (evaluate h).two = project (fun _ ↦ true) (evaluate h).one + 1
    else project (fun _ ↦ true) (evaluate h).one = project (fun _ ↦ true) (evaluate h).two + 1 := by
  have hh := projected_gap (fun _ ↦ true) h
  cases hs : (evaluate h).oneLeft <;>
    simpa [vertexProject, left, right, hs] using hh

theorem word_advance (h : List Graph) (g : Graph) :
    word (evaluate (h ++ [g])).one = word (evaluate h).one ++ [ (pair (evaluate h).oneLeft g).1 ] ∧
    word (evaluate (h ++ [g])).two = word (evaluate h).two ++ [ (pair (evaluate h).oneLeft g).2 ] := by
  have hg := gap h
  rw [at_append]
  cases hs : (evaluate h).oneLeft <;> cases g <;>
    simp [hs] at hg <;>
    simp [advance, advanceViews, word, pair, hs, Proc.other, hg]

theorem word_position (h : List Graph) :
    position .one (word (evaluate h).one) = project (fun _ ↦ true) (evaluate h).one ∧
    position .two (word (evaluate h).two) = project (fun _ ↦ true) (evaluate h).two := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton h g ih =>
    rw [(word_advance h g).1, (word_advance h g).2]
    simp only [position, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih.1, ih.2, at_append]
    have hg := gap h
    cases hs : (evaluate h).oneLeft <;> cases g <;>
      simp [hs] at hg <;>
      simp [pair, hs, positionStep, advance, advanceViews, project, Proc.other] <;> omega

theorem word_one_eq_iff (h k : List Graph) :
    word (evaluate h).one = word (evaluate k).one ↔ (evaluate h).one = (evaluate k).one := by
  constructor
  · intro hw
    have ht : h.length = k.length := by
      have := congrArg List.length hw
      simpa only [word_length, (at_depth h).1, (at_depth k).1] using this
    have hp := congrArg (position .one) hw
    rw [(word_position h).1, (word_position k).1] at hp
    have hv := coordinate_injective
      (u := .inl (evaluate h).one) (v := .inl (evaluate k).one)
      (by exact ⟨h, rfl, Or.inl rfl⟩)
      (by exact ⟨k, ht.symm, Or.inl rfl⟩) hp
    exact Sum.inl.inj hv
  · exact congrArg word

theorem word_two_eq_iff (h k : List Graph) :
    word (evaluate h).two = word (evaluate k).two ↔ (evaluate h).two = (evaluate k).two := by
  constructor
  · intro hw
    have ht : h.length = k.length := by
      have := congrArg List.length hw
      simpa only [word_length, (at_depth h).2, (at_depth k).2] using this
    have hp := congrArg (position .two) hw
    rw [(word_position h).2, (word_position k).2] at hp
    have hv := coordinate_injective
      (u := .inr (evaluate h).two) (v := .inr (evaluate k).two)
      (by exact ⟨h, rfl, Or.inr rfl⟩)
      (by exact ⟨k, ht.symm, Or.inr rfl⟩) hp
    exact Sum.inr.inj hv
  · exact congrArg word

end DistributedSynthesis.PrivateInputs
