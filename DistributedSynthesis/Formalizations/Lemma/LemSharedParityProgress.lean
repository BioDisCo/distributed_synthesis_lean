/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmDPACombinators
import Mathlib.Order.WellFounded

/-!
# Acceptance under replacements sharing one parity progress certificate

The outputs of a replacement controller may differ from those of the named
winning strategy. What must survive every replacement, including a reversal,
is progress measured on the actual objective-DPA run.

For each odd priority `p`, a rank cannot increase on a step whose source
priority is at least `p`, and must decrease when that priority is exactly `p`.
A smaller source priority permits the rank to reset. The same rank family
must govern ordinary steps and replacement steps. These local conditions
imply acceptance even when replacements occur infinitely often.

The rank order is any well-founded linear order. In particular this interface
does not assume that an infinite semantic source admits natural-number ranks
or a finite rank bound. Nor does a proof-side rank supply an endpoint with
access to hidden information: locality of the chosen replacement is separate.
-/

namespace DistributedSynthesis

namespace DetParityAutomaton

universe u v r c

/-- A decreasing rank for every odd cutoff rules out every rejecting run.
The ranks may depend on the entire proof-side execution context. -/
theorem acceptsFrom_of_shared_wellFounded_progress
    {Alphabet : Type u} (A : DetParityAutomaton.{u, v} Alphabet)
    (initial : A.State) (word : OmegaWord Alphabet)
    {Rank : Type r} [LinearOrder Rank] [WellFoundedLT Rank]
    (rank : Nat → Nat → Rank)
    (hweak : ∀ p, ¬ NatEven p → ∀ n,
      p ≤ A.priority (A.runFrom initial word n) →
        rank p (n + 1) ≤ rank p n)
    (hstrict : ∀ p, ¬ NatEven p → ∀ n,
      A.priority (A.runFrom initial word n) = p →
        rank p (n + 1) < rank p n) :
    A.AcceptsFrom initial word := by
  classical
  by_contra hreject
  obtain ⟨p, q, N, hq, hseen, hlower, hodd⟩ :=
    A.exists_recurrent_runState_min_priority_not_even_and_eventually_ge_of_not_acceptsFrom
      initial word hreject
  have hmono : Antitone (fun k ↦ rank p (N + k)) := by
    apply antitone_nat_of_succ_le
    intro k
    exact hweak p hodd (N + k) (hlower (N + k) (by omega))
  obtain ⟨least, ⟨k, hk⟩, hleast⟩ :=
    (wellFounded_lt : WellFounded ((· < ·) : Rank → Rank → Prop)).has_min
      (Set.range (fun k ↦ rank p (N + k))) ⟨rank p N, 0, by simp⟩
  obtain ⟨m, hm, hstate⟩ := hseen (N + k)
  have hle : rank p m ≤ rank p (N + k) := by
    have h := hmono (show k ≤ m - N by omega)
    simpa only [Nat.add_sub_of_le (show N ≤ m by omega)] using h
  have hdecrease : rank p (m + 1) < rank p m :=
    hstrict p hodd m (hstate ▸ hq)
  have hmem : rank p (m + 1) ∈ Set.range (fun k ↦ rank p (N + k)) :=
    ⟨m + 1 - N, by simp only [Nat.add_sub_of_le (show N ≤ m + 1 by omega)]⟩
  apply hleast _ hmem
  rw [← hk]
  exact lt_of_lt_of_le hdecrease hle

/-- One proof-side certificate for the union of all allowed operational and
replacement edges. The objective coordinate refers to the actual emitted
word, not to a semantic parent code. -/
structure SharedParityProgress
    {Alphabet : Type u} (A : DetParityAutomaton.{u, v} Alphabet)
    {Context : Type c} (objective : Context → A.State)
    (edge : Context → Context → Prop)
    (Rank : Type r) [LinearOrder Rank] where
  rank : Nat → Context → Rank
  nonincrease : ∀ p, ¬ NatEven p → ∀ source target,
    edge source target → p ≤ A.priority (objective source) →
      rank p target ≤ rank p source
  decrease : ∀ p, ¬ NatEven p → ∀ source target,
    edge source target → A.priority (objective source) = p →
      rank p target < rank p source

/-- Arbitrarily many changes of controller are sound when their transitions
all belong to one relation certified by the same rank family. No equality
with the outputs of the original strategy is required. -/
theorem SharedParityProgress.acceptsFrom
    {Alphabet : Type u} {A : DetParityAutomaton.{u, v} Alphabet}
    {Context : Type c} {objective : Context → A.State}
    {edge : Context → Context → Prop}
    {Rank : Type r} [LinearOrder Rank] [WellFoundedLT Rank]
    (certificate : SharedParityProgress A objective edge Rank)
    (path : Nat → Context) (hpath : ∀ n, edge (path n) (path (n + 1)))
    (initial : A.State) (word : OmegaWord Alphabet)
    (hobjective : ∀ n, objective (path n) = A.runFrom initial word n) :
    A.AcceptsFrom initial word := by
  apply A.acceptsFrom_of_shared_wellFounded_progress initial word
    (fun p n ↦ certificate.rank p (path n))
  · intro p hodd n hlower
    exact certificate.nonincrease p hodd _ _ (hpath n)
      (by rwa [hobjective])
  · intro p hodd n heq
    exact certificate.decrease p hodd _ _ (hpath n)
      (by rwa [hobjective])

end DetParityAutomaton

end DistributedSynthesis
