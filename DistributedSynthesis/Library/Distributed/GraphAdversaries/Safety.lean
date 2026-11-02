/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Tactic
import DistributedSynthesis.Library.Distributed.Views

/-! Safety objectives cannot distinguish adversaries with the same finite
prefixes, for any fixed causal execution map. This is a semantic theorem,
not yet the effective reduction for the manuscript's encoded LTL instances. -/

namespace Characterisation

variable {α β : Type*}

def AgreeBefore (n : Nat) (x y : Nat → α) : Prop :=
  ∀ t, t < n → x t = y t

def PrefixDense (A : Set (Nat → α)) : Prop :=
  ∀ x n, ∃ y ∈ A, AgreeBefore n x y

def Causal (run : (Nat → α) → (Nat → β)) : Prop :=
  ∀ x y n, AgreeBefore n x y → AgreeBefore n (run x) (run y)

def IsSafety (S : Set (Nat → β)) : Prop :=
  ∀ x, x ∉ S → ∃ n, ∀ y, AgreeBefore n x y → y ∉ S

theorem safety_transfer (A : Set (Nat → α)) (dense : PrefixDense A)
    (run : (Nat → α) → (Nat → β)) (causal : Causal run)
    (S : Set (Nat → β)) (safety : IsSafety S) :
    (∀ x ∈ A, run x ∈ S) ↔ (∀ x, run x ∈ S) := by
  constructor
  · intro win x
    by_contra hx
    obtain ⟨n, hn⟩ := safety (run x) hx
    obtain ⟨y, hy, agree⟩ := dense x n
    exact hn (run y) (causal x y n agree) (win y hy)
  · intro win x _
    exact win x

/-- The adversary promising a constant suffix preserves all finite prefixes. -/
theorem eventually_constant_prefixDense (a : α) :
    PrefixDense {x | ∃ N, ∀ t, N ≤ t → x t = a} := by
  intro x n
  let y : Nat → α := fun t => if t < n then x t else a
  refine ⟨y, ⟨n, ?_⟩, ?_⟩
  · intro t ht
    simp [y, Nat.not_lt.mpr ht]
  · intro t ht
    simp [y, ht]

/-- In particular, eventual permanent bidirectional communication has the
same winning causal runs as unrestricted communication for safety objectives. -/
theorem eventually_both_safety_transfer
    (run : (Nat → DistributedSynthesis.Graph) → (Nat → β))
    (causal : Causal run) (S : Set (Nat → β)) (safety : IsSafety S) :
    (∀ x, (∃ N, ∀ t, N ≤ t → x t = .both) → run x ∈ S) ↔
      (∀ x, run x ∈ S) :=
  safety_transfer _ (eventually_constant_prefixDense DistributedSynthesis.Graph.both) run causal S safety

theorem exclude_constant_prefixDense (a b : α) (different : b ≠ a) :
    PrefixDense {x | x ≠ fun _ => a} := by
  intro x n
  let y : Nat → α := fun t => if t < n then x t else b
  refine ⟨y, ?_, ?_⟩
  · intro heq
    have hn := congrFun heq n
    simp only [y, lt_self_iff_false, ↓reduceIte] at hn
    exact different hn
  · intro t ht
    simp [y, ht]

end Characterisation
