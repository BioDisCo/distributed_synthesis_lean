/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.Undecidability.ResidualUndecidability

/-! Local implementations of adding a fixed past and forgetting a fixed past.
Neither transformation tests whether the actual graph history has that past. -/

namespace Characterisation
open DistributedSynthesis FullViewPath

/-- Replace the empty leaves by the two views of a fixed history. -/
def seedView (h : List Graph) : {p : Proc} → View Unit Unit p → View Unit Unit p
  | .one, .empty _ => (evaluate h).one
  | .two, .empty _ => (evaluate h).two
  | _, .noRecv v i => .noRecv (seedView h v) i
  | _, .recv v i w j => .recv (seedView h v) i (seedView h w) j

/-- Retain only the last `n` rounds, including in received views. -/
def suffixView : (n : Nat) → {p : Proc} → View Unit Unit p → View Unit Unit p
  | 0, p, _ => .empty p
  | _ + 1, _, .empty p => .empty p
  | n + 1, _, .noRecv v i => .noRecv (suffixView n v) i
  | n + 1, _, .recv v i w j => .recv (suffixView n v) i (suffixView n w) j

theorem seedView_evaluate (h u : List Graph) :
    seedView h (evaluate u).one = (evaluate (h ++ u)).one ∧
    seedView h (evaluate u).two = (evaluate (h ++ u)).two := by
  induction u using List.reverseRecOn with
  | nil => simp [evaluate, root, seedView]
  | append_singleton u g ih =>
    simp only [← List.append_assoc, at_append]
    cases g <;> simp [advance, advanceViews, seedView, Proc.other, ih]

theorem suffixView_evaluate (h u : List Graph) :
    suffixView u.length (evaluate (h ++ u)).one = (evaluate u).one ∧
    suffixView u.length (evaluate (h ++ u)).two = (evaluate u).two := by
  induction u using List.reverseRecOn with
  | nil => simp [suffixView, evaluate, root]
  | append_singleton u g ih =>
    simp only [List.length_append, List.length_singleton, ← List.append_assoc, at_append]
    cases g <;> simp [advance, advanceViews, suffixView, Proc.other, ih]

/-- Run an original strategy after a locally simulated fixed past. -/
def seedStrategy {O₁ O₂ : Type*} (h : List Graph) (σ : StrategyPair Unit Unit O₁ O₂) :
    StrategyPair Unit Unit O₁ O₂ :=
  ⟨fun v => σ.one (seedView h v), fun v => σ.two (seedView h v)⟩

/-- Restart after `m` rounds. The round number is recoverable from the local view. -/
def resetStrategy {O₁ O₂ : Type*} (m : Nat) (σ : StrategyPair Unit Unit O₁ O₂) :
    StrategyPair Unit Unit O₁ O₂ :=
  ⟨fun v => σ.one (suffixView (depth v - m) v),
   fun v => σ.two (suffixView (depth v - m) v)⟩

theorem resetStrategy_evaluate {O₁ O₂ : Type*} (h u : List Graph)
    (σ : StrategyPair Unit Unit O₁ O₂) :
    (resetStrategy h.length σ).one (evaluate (h ++ u)).one = σ.one (evaluate u).one ∧
    (resetStrategy h.length σ).two (evaluate (h ++ u)).two = σ.two (evaluate u).two := by
  simp only [resetStrategy, (at_depth (h ++ u)).1, (at_depth (h ++ u)).2,
    List.length_append, Nat.add_sub_cancel_left]
  exact ⟨congrArg σ.one (suffixView_evaluate h u).1,
    congrArg σ.two (suffixView_evaluate h u).2⟩

end Characterisation
