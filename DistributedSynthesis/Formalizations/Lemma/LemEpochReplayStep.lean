/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmBoundaryDecomposition

/-!
# The per-epoch replay step and the epoch-summary acceptance transfer

Replay step for `prop:starsound` (`hsound` of the summary fold): the
multi-block composition run inside the epoch abstraction, where an epoch is
one block and the only data a block contributes to parity acceptance is its
finite summary -- the minimum run priority over the block together with the
automaton state at its exit.  This file proves that principle in full
generality, for an arbitrary deterministic parity automaton over an arbitrary
alphabet:

* `run_agree_of_segment_agree` -- the per-epoch replay step: two omega words
  that agree along one segment, possibly placed at different global times,
  with agreeing runs at the segment entries, have agreeing runs along the
  whole segment, exit included;
* `cutBlockMin_eq_of_segment_agree` -- the per-epoch summary transport: under
  the same hypotheses the two block min-priority summaries coincide and the
  entry matching recurses to the next epoch;
* `accepts_iff_of_cutBlockMin_eq` -- the composition principle: acceptance
  transfers between two words whose per-epoch min-priority sequences agree
  pointwise, for arbitrary independent strictly monotone epoch decompositions
  starting at zero.  No word equality across infinitely many boundaries is
  required; the omega composition is decided by the finite summary sequence
  alone.  This is exactly why the per-block transports of the replay bricks
  (`LemThetaBarReplayTable`, `LemArenaReplaySimulation`) compose across
  infinitely many boundaries once they are read per epoch;
* `accepts_iff_of_epoch_segments` -- the assembled endpoint: a word whose
  epochs replay, segment by segment, the epochs of a reference word from a
  matching entry state -- the reference epochs starting after an arbitrary
  finite prefix -- is accepted iff the reference is.

Everything here is word-level mathematics consuming only the parity pasting
machinery (`ThmParityBlockPasting`) and the run semantics
(`DefOmegaAutomata`); the model enters only through the downstream bricks
that supply the per-epoch record agreement.
-/

namespace DistributedSynthesis

universe u v

/-- Congruence of range minima under a pointwise segment matching at
possibly different base points. -/
theorem rangeMin_congr {s s' : Nat -> Nat} {a a' : Nat} :
    ∀ n : Nat,
      (∀ i : Nat, i ≤ n -> s (a + i) = s' (a' + i)) ->
        rangeMin s a n = rangeMin s' a' n
  | 0, h => h 0 (Nat.le_refl 0)
  | n + 1, h => by
      rw [
        rangeMin,
        rangeMin,
        rangeMin_congr n (fun i hi => h i (Nat.le_succ_of_le hi)),
        h (n + 1) (Nat.le_refl (n + 1))
      ]

/-- Shifting a sequence by the zeroth cut and rebasing the cuts leaves the
per-block minima unchanged. -/
theorem cutBlockMin_shift (s : Nat -> Nat) {c : Nat -> Nat}
    (hmono : StrictMono c) (k : Nat) :
    cutBlockMin (fun n => s (c 0 + n)) (fun j => c j - c 0) k =
      cutBlockMin s c k := by
  have hk : c 0 ≤ c k := hmono.monotone (Nat.zero_le k)
  have hk1 : c 0 ≤ c (k + 1) := hmono.monotone (Nat.zero_le (k + 1))
  have hlen : c (k + 1) - c 0 - (c k - c 0) = c (k + 1) - c k := by omega
  rw [cutBlockMin, cutBlockMin, hlen]
  exact
    rangeMin_congr _ (fun i _ => by
      have hbase : c 0 + (c k - c 0 + i) = c k + i := by omega
      simpa using congrArg s hbase)

namespace DetParityAutomaton

variable {Alphabet : Type u}
variable (A : DetParityAutomaton.{u, v} Alphabet)

/-- **The per-epoch replay step.**  If the runs of two words agree at the
entries of one segment and the words agree along the segment -- the segment
sitting at different global times in the two words -- then the runs agree
along the whole segment, exit included. -/
theorem run_agree_of_segment_agree
    (w w' : OmegaWord Alphabet) (a a' n : Nat)
    (hentry : A.run w a = A.run w' a')
    (hrec : ∀ j : Nat, j < n -> w (a + j) = w' (a' + j)) :
    ∀ j : Nat, j ≤ n -> A.run w (a + j) = A.run w' (a' + j) := by
  intro j
  induction j with
  | zero => intro _; exact hentry
  | succ j ih =>
      intro hj
      have hjn : j < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      show A.run w ((a + j) + 1) = A.run w' ((a' + j) + 1)
      rw [run_succ, run_succ, ih (Nat.le_of_lt hjn), hrec j hjn]

/-- **The per-epoch summary transport.**  A segment matching of epoch `k`
transports its finite summary: the block min-priority summaries coincide,
and the run matching recurses to the entry of epoch `k + 1`. -/
theorem cutBlockMin_eq_of_segment_agree
    (w w' : OmegaWord Alphabet) {c c' : Nat -> Nat}
    (hmono : StrictMono c) (hmono' : StrictMono c') (k : Nat)
    (hentry : A.run w (c k) = A.run w' (c' k))
    (hlen : c (k + 1) - c k = c' (k + 1) - c' k)
    (hrec : ∀ j : Nat, j < c (k + 1) - c k -> w (c k + j) = w' (c' k + j)) :
    cutBlockMin (fun n => A.priority (A.run w n)) c k =
        cutBlockMin (fun n => A.priority (A.run w' n)) c' k ∧
      A.run w (c (k + 1)) = A.run w' (c' (k + 1)) := by
  have hlt : c k < c (k + 1) := hmono (Nat.lt_succ_self k)
  have hlt' : c' k < c' (k + 1) := hmono' (Nat.lt_succ_self k)
  have hagree :=
    A.run_agree_of_segment_agree w w' (c k) (c' k) (c (k + 1) - c k)
      hentry hrec
  constructor
  · rw [cutBlockMin, cutBlockMin, ← hlen]
    exact
      rangeMin_congr _ (fun i hi => by
        rw [hagree i (by omega)])
  · have hexit := hagree (c (k + 1) - c k) (Nat.le_refl _)
    have hcut : c k + (c (k + 1) - c k) = c (k + 1) := by omega
    have hcut' : c' k + (c (k + 1) - c k) = c' (k + 1) := by omega
    rwa [hcut, hcut'] at hexit

/-- Iterating the per-epoch step: entry matching at epoch zero and segment
matching of every epoch give run matching at every cut and pointwise equal
per-epoch min-priority summaries. -/
theorem epoch_run_and_cutBlockMin_agree
    (w w' : OmegaWord Alphabet) {c c' : Nat -> Nat}
    (hmono : StrictMono c) (hmono' : StrictMono c')
    (hentry : A.run w (c 0) = A.run w' (c' 0))
    (hlen : ∀ k : Nat, c (k + 1) - c k = c' (k + 1) - c' k)
    (hrec :
      ∀ k j : Nat,
        j < c (k + 1) - c k -> w (c k + j) = w' (c' k + j)) :
    (∀ k : Nat, A.run w (c k) = A.run w' (c' k)) ∧
      ∀ k : Nat,
        cutBlockMin (fun n => A.priority (A.run w n)) c k =
          cutBlockMin (fun n => A.priority (A.run w' n)) c' k := by
  have hstates : ∀ k : Nat, A.run w (c k) = A.run w' (c' k) := by
    intro k
    induction k with
    | zero => exact hentry
    | succ k ih =>
        exact
          (A.cutBlockMin_eq_of_segment_agree w w' hmono hmono' k ih
            (hlen k) (hrec k)).2
  exact
    ⟨hstates, fun k =>
      (A.cutBlockMin_eq_of_segment_agree w w' hmono hmono' k (hstates k)
        (hlen k) (hrec k)).1⟩

/-- **The epoch-summary composition principle.**  Acceptance transfers
between two words whose per-epoch min-priority sequences agree pointwise,
along arbitrary independent strictly monotone epoch decompositions starting
at zero.  The omega composition is decided by the finite summary sequence
alone; no word equality across boundaries is needed. -/
theorem accepts_iff_of_cutBlockMin_eq
    (w w' : OmegaWord Alphabet) {c c' : Nat -> Nat}
    (hmono : StrictMono c) (h0 : c 0 = 0)
    (hmono' : StrictMono c') (h0' : c' 0 = 0)
    (hmin :
      ∀ k : Nat,
        cutBlockMin (fun n => A.priority (A.run w n)) c k =
          cutBlockMin (fun n => A.priority (A.run w' n)) c' k) :
    A.Accepts w ↔ A.Accepts w' := by
  rw [
    A.accepts_iff_natSeqMinEvenParity w,
    A.accepts_iff_natSeqMinEvenParity w',
    ← natSeqMinEvenParity_cutBlockMin
      (fun n => A.priority (A.run w n)) hmono h0,
    ← natSeqMinEvenParity_cutBlockMin
      (fun n => A.priority (A.run w' n)) hmono' h0',
    funext hmin
  ]

/-- **The assembled per-epoch transfer endpoint.**  A word whose epochs
replay, segment by segment, the epochs of a reference word from a matching
entry state is accepted iff the reference is.  The reference epochs may
start after an arbitrary finite prefix (`c' 0` free); prefix invariance of
the parity value absorbs it. -/
theorem accepts_iff_of_epoch_segments
    (w w' : OmegaWord Alphabet) {c c' : Nat -> Nat}
    (hmono : StrictMono c) (h0 : c 0 = 0) (hmono' : StrictMono c')
    (hentry : A.run w (c 0) = A.run w' (c' 0))
    (hlen : ∀ k : Nat, c (k + 1) - c k = c' (k + 1) - c' k)
    (hrec :
      ∀ k j : Nat,
        j < c (k + 1) - c k -> w (c k + j) = w' (c' k + j)) :
    A.Accepts w ↔ A.Accepts w' := by
  obtain ⟨_, hmin⟩ :=
    A.epoch_run_and_cutBlockMin_agree w w' hmono hmono' hentry hlen hrec
  have hmonod : StrictMono (fun j => c' j - c' 0) := by
    intro k l hkl
    have hbase : c' 0 ≤ c' k := hmono'.monotone (Nat.zero_le k)
    have hstep : c' k < c' l := hmono' hkl
    simp only
    omega
  have hshift :
      A.Accepts w' ↔
        NatSeqMinEvenParity
          (fun n => A.priority (A.run w' (c' 0 + n))) := by
    rw [A.accepts_iff_natSeqMinEvenParity w']
    exact
      (natSeqMinEvenParity_shift
        (fun n => A.priority (A.run w' n)) (c' 0)).symm
  rw [
    A.accepts_iff_natSeqMinEvenParity w,
    ← natSeqMinEvenParity_cutBlockMin
      (fun n => A.priority (A.run w n)) hmono h0,
    hshift,
    ← natSeqMinEvenParity_cutBlockMin
      (fun n => A.priority (A.run w' (c' 0 + n))) hmonod (by simp)
  ]
  have hblocks :
      cutBlockMin (fun n => A.priority (A.run w n)) c =
        cutBlockMin (fun n => A.priority (A.run w' (c' 0 + n)))
          (fun j => c' j - c' 0) := by
    funext k
    rw [cutBlockMin_shift (fun n => A.priority (A.run w' n)) hmono' k]
    exact hmin k
  rw [hblocks]

end DetParityAutomaton

end DistributedSynthesis
