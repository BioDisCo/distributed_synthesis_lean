/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankOperationalCutPath

/-!
# Local receive bits at operational cuts

This file isolates the Boolean part of the operational-block argument from
the concrete linked controller.  The hypotheses describe only what the two
endpoint-local receive bits contain after one physical round.  They neither
give a process the current graph nor expose a strict-leader bit at runtime.

At the beginning of a maximal strict block the receiver's bit is `false`:
either this is time zero, the preceding block had the other strict side, or
the preceding round was simultaneous.  At the closing receive it is `false`
exactly for a singleton block.  Hence the local bit selects the canonical
bank row `.first`/`.both` fixed by the operational-close clock.

Both the receiver-only phase restart and the full sender-and-receiver restart
can instantiate this lemma from their trace-level bit equations.
-/

namespace DistributedSynthesis

namespace DetParityAutomaton

/-! ## Controller-independent open-block induction -/

/-- Iterate any one-round invariant through the `openLength` homogeneous
rounds preceding an operational closing receive.  This lemma is independent
of the controller and of the particular strict side. -/
theorem OperationalCloseCutPackage.propagate_homogeneous_open
    {graphs : Nat → Graph}
    (cuts : OperationalCloseCutPackage graphs)
    (P : Nat → Prop) (k : Nat)
    (hstep : ∀ n : Nat, P n →
      graphs n = graphs (cuts.cuts k) → P (n + 1))
    (hstart : P (cuts.cuts k)) :
    P (cuts.cuts k + cuts.openLength k) := by
  have hprefix : ∀ j : Nat, j ≤ cuts.openLength k →
      P (cuts.cuts k + j) := by
    intro j hj
    induction j with
    | zero => simpa using hstart
    | succ j ih =>
        have hjle : j ≤ cuts.openLength k := by omega
        have hjlt : j < cuts.openLength k := by omega
        have hcurrent := ih hjle
        have hgraph := cuts.homogeneous k j hjlt
        have hnext := hstep (cuts.cuts k + j) hcurrent hgraph
        simpa only [Nat.add_assoc, Nat.add_one] using hnext
  exact hprefix (cuts.openLength k) (Nat.le_refl _)

/-- A proof-side view of two endpoint-local receive bits.  The transition
equations say which endpoint received in the preceding physical round.  This
is an invariant of a distributed controller; `graphs` is used only in the
proof and is not an argument of either endpoint transition. -/
structure OperationalReceivePhaseBits (graphs : Nat → Graph) where
  one : Nat → Bool
  two : Nat → Bool
  initial : one 0 = false ∧ two 0 = false
  step : ∀ n : Nat,
    match graphs n with
    | .right => one (n + 1) = false ∧ two (n + 1) = true
    | .left => one (n + 1) = true ∧ two (n + 1) = false
    | .both => one (n + 1) = false ∧ two (n + 1) = false

namespace OperationalReceivePhaseBits

/-- At the entry of a strict-right operational block, process two is about
to receive after either no preceding round or a round on a different side;
its local receive bit is therefore `false`. -/
theorem two_at_cut_eq_false_of_right
    {graphs : Nat → Graph}
    (cuts : OperationalCloseCutPackage graphs)
    (bits : OperationalReceivePhaseBits graphs)
    (k : Nat) (hgraph : graphs (cuts.cuts k) = .right) :
    bits.two (cuts.cuts k) = false := by
  cases k with
  | zero =>
      simpa [cuts.cuts_zero] using bits.initial.2
  | succ k =>
      have hpositive : 0 < cuts.cuts (k + 1) := by
        have hmono := cuts.cuts_strictMono (Nat.zero_lt_succ k)
        simpa [cuts.cuts_zero] using hmono
      have hpredSucc : cuts.cuts (k + 1) - 1 + 1 = cuts.cuts (k + 1) := by
        omega
      have hclosing := cuts.closing_graph_eq k
      cases hprevious : graphs (cuts.cuts k) with
      | right =>
          have hstrict : graphs (cuts.cuts k) ≠ .both := by
            simp [hprevious]
          have hne := cuts.maximal_of_strict k hstrict
          exact False.elim (hne (hgraph.trans hprevious.symm))
      | left =>
          have hstep := bits.step (cuts.cuts (k + 1) - 1)
          rw [hclosing, hprevious] at hstep
          rw [← hpredSucc]
          exact hstep.2
      | both =>
          have hstep := bits.step (cuts.cuts (k + 1) - 1)
          rw [hclosing, hprevious] at hstep
          rw [← hpredSucc]
          exact hstep.2

/-- Process-one mirror at a strict-left operational-block entry. -/
theorem one_at_cut_eq_false_of_left
    {graphs : Nat → Graph}
    (cuts : OperationalCloseCutPackage graphs)
    (bits : OperationalReceivePhaseBits graphs)
    (k : Nat) (hgraph : graphs (cuts.cuts k) = .left) :
    bits.one (cuts.cuts k) = false := by
  cases k with
  | zero =>
      simpa [cuts.cuts_zero] using bits.initial.1
  | succ k =>
      have hpositive : 0 < cuts.cuts (k + 1) := by
        have hmono := cuts.cuts_strictMono (Nat.zero_lt_succ k)
        simpa [cuts.cuts_zero] using hmono
      have hpredSucc : cuts.cuts (k + 1) - 1 + 1 = cuts.cuts (k + 1) := by
        omega
      have hclosing := cuts.closing_graph_eq k
      cases hprevious : graphs (cuts.cuts k) with
      | right =>
          have hstep := bits.step (cuts.cuts (k + 1) - 1)
          rw [hclosing, hprevious] at hstep
          rw [← hpredSucc]
          exact hstep.1
      | left =>
          have hstrict : graphs (cuts.cuts k) ≠ .both := by
            simp [hprevious]
          have hne := cuts.maximal_of_strict k hstrict
          exact False.elim (hne (hgraph.trans hprevious.symm))
      | both =>
          have hstep := bits.step (cuts.cuts (k + 1) - 1)
          rw [hclosing, hprevious] at hstep
          rw [← hpredSucc]
          exact hstep.1

/-- At a strict-right block's closing receive, process two's local phase bit
selects exactly the canonical operational bank row. -/
theorem right_closing_row_eq_bankOperationalRowAt
    {graphs : Nat → Graph}
    (cuts : OperationalCloseCutPackage graphs)
    (bits : OperationalReceivePhaseBits graphs)
    (k : Nat) (hgraph : graphs (cuts.cuts k) = .right) :
    (if bits.two (cuts.cuts k + cuts.openLength k)
      then PairedEntryRow.both else PairedEntryRow.first) =
        DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.bankOperationalRowAt
          cuts k := by
  by_cases hzero : cuts.openLength k = 0
  · have hbit := bits.two_at_cut_eq_false_of_right cuts k hgraph
    simp [DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.bankOperationalRowAt,
      hzero, hbit]
  · have hpositive : 0 < cuts.openLength k := Nat.pos_of_ne_zero hzero
    have hoffset : cuts.openLength k - 1 < cuts.openLength k := by omega
    have hbefore := cuts.homogeneous k (cuts.openLength k - 1) hoffset
    rw [hgraph] at hbefore
    have hstep := bits.step (cuts.cuts k + (cuts.openLength k - 1))
    rw [hbefore] at hstep
    have hindex :
        cuts.cuts k + (cuts.openLength k - 1) + 1 =
          cuts.cuts k + cuts.openLength k := by
      omega
    have hbit : bits.two (cuts.cuts k + cuts.openLength k) = true := by
      rw [← hindex]
      exact hstep.2
    simp [DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.bankOperationalRowAt,
      hzero, hbit]

/-- Process-one mirror for a strict-left block. -/
theorem left_closing_row_eq_bankOperationalRowAt
    {graphs : Nat → Graph}
    (cuts : OperationalCloseCutPackage graphs)
    (bits : OperationalReceivePhaseBits graphs)
    (k : Nat) (hgraph : graphs (cuts.cuts k) = .left) :
    (if bits.one (cuts.cuts k + cuts.openLength k)
      then PairedEntryRow.both else PairedEntryRow.first) =
        DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.bankOperationalRowAt
          cuts k := by
  by_cases hzero : cuts.openLength k = 0
  · have hbit := bits.one_at_cut_eq_false_of_left cuts k hgraph
    simp [DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.bankOperationalRowAt,
      hzero, hbit]
  · have hpositive : 0 < cuts.openLength k := Nat.pos_of_ne_zero hzero
    have hoffset : cuts.openLength k - 1 < cuts.openLength k := by omega
    have hbefore := cuts.homogeneous k (cuts.openLength k - 1) hoffset
    rw [hgraph] at hbefore
    have hstep := bits.step (cuts.cuts k + (cuts.openLength k - 1))
    rw [hbefore] at hstep
    have hindex :
        cuts.cuts k + (cuts.openLength k - 1) + 1 =
          cuts.cuts k + cuts.openLength k := by
      omega
    have hbit : bits.one (cuts.cuts k + cuts.openLength k) = true := by
      rw [← hindex]
      exact hstep.1
    simp [DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.bankOperationalRowAt,
      hzero, hbit]

end OperationalReceivePhaseBits

end DetParityAutomaton

end DistributedSynthesis
