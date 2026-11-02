/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting
import DistributedSynthesis.Formalizations.Theorem.ThmUniversalThreadDeterminization
import DistributedSynthesis.Formalizations.Definition.DefHistory

/-!
# Boundary decomposition of plays

This file applies the parity pasting machinery to real plays of the
two-process model: the synchronization boundaries of an omega word are
round zero and every round following a `both` round, and when there are
unboundedly many `both` rounds their enumeration decomposes the play
into consecutive finite blocks, each ending with its closing `both`
round and containing no interior one.

The value-transfer endpoint is `accepts_iff_syncBlockMin`: acceptance
of the play by the objective parity automaton is equivalent to the
min-even parity of the per-block priority minima along the boundary
enumeration.  This is the priority interface the boundary game of the
readback-upgrade plan emits: one priority per boundary step, the block
minimum.  Plays with only finitely many `both` rounds are decided on
their infinite tail via `accepts_iff_tail_parity` (prefix invariance of
the parity value).
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/--
Synchronization boundaries of a play: round zero, and every round
directly following a `both` round.
-/
def SyncBoundary
    (w : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat) : Prop :=
  n = 0 ∨ (w (n - 1)).graph = Graph.both

instance (w : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)) :
    DecidablePred (SyncBoundary w) := fun n =>
  inferInstanceAs (Decidable (n = 0 ∨ (w (n - 1)).graph = Graph.both))

/-- Unboundedly many `both` rounds give unboundedly many boundaries. -/
theorem syncBoundary_unbounded
    (w : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ (w m).graph = Graph.both) :
    ∀ n : Nat, ∃ m : Nat, n < m ∧ SyncBoundary w m := by
  intro n
  rcases hinf n with ⟨m, hm, hboth⟩
  exact ⟨m + 1, by omega, Or.inr (by simpa using hboth)⟩

/-- The boundary times of a play with unboundedly many `both` rounds. -/
def syncCuts
    (w : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ (w m).graph = Graph.both) :
    Nat -> Nat :=
  cutSeq (B := SyncBoundary w) (syncBoundary_unbounded w hinf)

@[simp]
theorem syncCuts_zero
    (w : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ (w m).graph = Graph.both) :
    syncCuts w hinf 0 = 0 :=
  rfl

theorem syncCuts_strictMono
    (w : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ (w m).graph = Graph.both) :
    StrictMono (syncCuts w hinf) :=
  cutSeq_strictMono (syncBoundary_unbounded w hinf)

/-- Every block ends with its closing `both` round. -/
theorem syncCuts_closing
    (w : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ (w m).graph = Graph.both)
    (k : Nat) :
    (w (syncCuts w hinf (k + 1) - 1)).graph = Graph.both := by
  have hmark : SyncBoundary w (syncCuts w hinf (k + 1)) :=
    marked_cutSeq_succ (syncBoundary_unbounded w hinf) k
  have hpos : 0 < syncCuts w hinf (k + 1) := by
    have := syncCuts_strictMono w hinf (Nat.succ_pos k)
    simpa using this
  rcases hmark with hzero | hboth
  · omega
  · exact hboth

/-- No block contains an interior `both` round. -/
theorem syncCuts_interior
    (w : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ (w m).graph = Graph.both)
    (k : Nat) {j : Nat}
    (h1 : syncCuts w hinf k ≤ j)
    (h2 : j + 1 < syncCuts w hinf (k + 1)) :
    (w j).graph ≠ Graph.both := by
  intro hboth
  refine
    not_marked_between (syncBoundary_unbounded w hinf)
      (show syncCuts w hinf k < j + 1 by omega) h2 ?_
  exact Or.inr (by simpa using hboth)

/-- Every positive boundary time is a cut. -/
theorem syncCuts_exhaustive
    (w : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ (w m).graph = Graph.both)
    {n : Nat} (hboth : (w n).graph = Graph.both) :
    ∃ k : Nat, syncCuts w hinf (k + 1) = n + 1 :=
  cutSeq_exhaustive (syncBoundary_unbounded w hinf)
    (Or.inr (by simpa using hboth)) (Nat.succ_pos n)

/--
Value transfer along the boundary decomposition: acceptance of a play
with unboundedly many `both` rounds is equivalent to the min-even
parity of the per-block priority minima along the boundary times.
-/
theorem accepts_iff_syncBlockMin
    (A :
      DetParityAutomaton.{max u v x y, s}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (w : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ (w m).graph = Graph.both) :
    A.Accepts w ↔
      NatSeqMinEvenParity
        (cutBlockMin (fun n => A.priority (A.run w n))
          (syncCuts w hinf)) := by
  rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
  exact (natSeqMinEvenParity_cutSeq _ _).symm

/--
Prefix invariance of the parity value: acceptance is decided on any
tail of the run priorities.  This is the value transfer for plays with
finitely many `both` rounds, whose final infinite block starts at the
last boundary.
-/
theorem accepts_iff_tail_parity
    (A :
      DetParityAutomaton.{max u v x y, s}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (w : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (N : Nat) :
    A.Accepts w ↔
      NatSeqMinEvenParity
        (fun n => A.priority (A.run w (N + n))) := by
  rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
  exact (natSeqMinEvenParity_shift _ N).symm

end DistributedSynthesis
