/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankOperationalCutPath

/-!
# Strict-side alternation at operational bank cuts

After the finite prefix preceding a persistent strict-reversal tail has been
discarded, every operational cut starts with a strict graph.  Maximality of
the represented homogeneous block then forces the next cut to start with the
opposite strict graph.  Consequently the proof-side actual directions carried
by the canonical bank schedule alternate their hidden lineage side exactly.

This is graph/certificate bookkeeping only.  The selected actual directions
and their sides are not inputs of either endpoint controller.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev ActualDirection :=
  ProfiledRawJointActualDirection (I := Unit) (In₁ := In₁) (In₂ := In₂)

private abbrev OperationalSchedule
    (env : EnvironmentSequence In₁ In₂) :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule
    (In₁ := In₁) (In₂ := In₂) env

/-! ## Strict directions at every cut -/

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- A cut whose starting graph is strict carries an actual strict direction
of exactly that graph side. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule.exists_strictActual
    {env : EnvironmentSequence In₁ In₂}
    (schedule : OperationalSchedule (In₁ := In₁) (In₂ := In₂) env)
    (k : Nat) (hstrict : (env (schedule.cut k)).graph ≠ .both) :
    ∃ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
      schedule.direction k = .strict actual ∧
        match (env (schedule.cut k)).graph with
        | .right => actual.side = .right
        | .left => actual.side = .left
        | .both => False := by
  have hstep := schedule.step k
  cases hgraph : (env (schedule.cut k)).graph with
  | right =>
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
        hgraph] at hstep
      rcases hstep.2 with ⟨actual, hside, hdirection⟩
      exact ⟨actual, hdirection, hside⟩
  | left =>
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
        hgraph] at hstep
      rcases hstep.2 with ⟨actual, hside, hdirection⟩
      exact ⟨actual, hdirection, hside⟩
  | both => exact False.elim (hstrict hgraph)

/-- All proof-side data needed by the hidden alternating-lineage monitor on a
no-`BOTH` operational schedule. -/
structure
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalStrictAlternation
    {env : EnvironmentSequence In₁ In₂}
    (schedule : OperationalSchedule (In₁ := In₁) (In₂ := In₂) env) where
  actual : Nat → ActualDirection (In₁ := In₁) (In₂ := In₂)
  direction_eq : ∀ k : Nat, schedule.direction k = .strict (actual k)
  side_succ : ∀ k : Nat, (actual (k + 1)).side = (actual k).side.other

/-! ## Maximal strict blocks alternate -/

/-- If every cut starts in a strict graph, maximality forces the selected
actual directions to alternate sides. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule.strictAlternation
    {env : EnvironmentSequence In₁ In₂}
    (schedule : OperationalSchedule (In₁ := In₁) (In₂ := In₂) env)
    (hstrict : ∀ k : Nat, (env (schedule.cut k)).graph ≠ .both) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalStrictAlternation
      (In₁ := In₁) (In₂ := In₂) schedule := by
  let actual : Nat → ActualDirection (In₁ := In₁) (In₂ := In₂) :=
    fun k ↦ Classical.choose (schedule.exists_strictActual k (hstrict k))
  have hspec : ∀ k : Nat,
      schedule.direction k = .strict (actual k) ∧
        match (env (schedule.cut k)).graph with
        | .right => (actual k).side = .right
        | .left => (actual k).side = .left
        | .both => False :=
    fun k ↦ Classical.choose_spec
      (schedule.exists_strictActual k (hstrict k))
  refine {
    actual := actual
    direction_eq := fun k ↦ (hspec k).1
    side_succ := ?_ }
  intro k
  have hstep := schedule.step k
  cases hcurrent : (env (schedule.cut k)).graph with
  | right =>
      have hside : (actual k).side = .right := by
        simpa [hcurrent] using (hspec k).2
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
        hcurrent] at hstep
      have hnext_ne_right :
          (env (schedule.cut (k + 1))).graph ≠ .right := hstep.1.2.2
      cases hnext : (env (schedule.cut (k + 1))).graph with
      | right => exact False.elim (hnext_ne_right hnext)
      | left =>
          have hnextSide : (actual (k + 1)).side = .left := by
            simpa [hnext] using (hspec (k + 1)).2
          simpa [hside, hnextSide, IndexedLineageSide.other]
      | both => exact False.elim (hstrict (k + 1) hnext)
  | left =>
      have hside : (actual k).side = .left := by
        simpa [hcurrent] using (hspec k).2
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
        hcurrent] at hstep
      have hnext_ne_left :
          (env (schedule.cut (k + 1))).graph ≠ .left := hstep.1.2.2
      cases hnext : (env (schedule.cut (k + 1))).graph with
      | right =>
          have hnextSide : (actual (k + 1)).side = .right := by
            simpa [hnext] using (hspec (k + 1)).2
          simpa [hside, hnextSide, IndexedLineageSide.other]
      | left => exact False.elim (hnext_ne_left hnext)
      | both => exact False.elim (hstrict (k + 1) hnext)
  | both => exact False.elim (hstrict k hcurrent)

/-! ## The eventual strict-reversal tail -/

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Operational cuts are strictly increasing.  This is derived from the
positive length of every represented close block, rather than added as a
second schedule field. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule.cut_strictMono
    {env : EnvironmentSequence In₁ In₂}
    (schedule : OperationalSchedule (In₁ := In₁) (In₂ := In₂) env) :
    StrictMono schedule.cut :=
  strictMono_nat_of_lt_succ fun k ↦ (schedule.step k).lt

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Cut `k` occurs no earlier than physical round `k`. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule.index_le_cut
    {env : EnvironmentSequence In₁ In₂}
    (schedule : OperationalSchedule (In₁ := In₁) (In₂ := In₂) env)
    (k : Nat) : k ≤ schedule.cut k :=
  schedule.cut_strictMono.id_le k

/-- Alternating proof-side strict directions after an arbitrary cut index.
The offset is used only by the correctness proof; it is not part of either
endpoint's controller state. -/
structure
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalStrictAlternationFrom
    {env : EnvironmentSequence In₁ In₂}
    (schedule : OperationalSchedule (In₁ := In₁) (In₂ := In₂) env)
    (startIndex : Nat) where
  actual : Nat → ActualDirection (In₁ := In₁) (In₂ := In₂)
  direction_eq : ∀ k : Nat,
    schedule.direction (startIndex + k) = .strict (actual k)
  side_succ : ∀ k : Nat, (actual (k + 1)).side = (actual k).side.other

/-- Once every later cut is strict, maximality gives strict-side alternation
from that cut onward. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule.strictAlternationFrom
    {env : EnvironmentSequence In₁ In₂}
    (schedule : OperationalSchedule (In₁ := In₁) (In₂ := In₂) env)
    (startIndex : Nat)
    (hstrict : ∀ k : Nat,
      (env (schedule.cut (startIndex + k))).graph ≠ .both) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalStrictAlternationFrom
      (In₁ := In₁) (In₂ := In₂) schedule startIndex := by
  let actual : Nat → ActualDirection (In₁ := In₁) (In₂ := In₂) :=
    fun k ↦ Classical.choose
      (schedule.exists_strictActual (startIndex + k) (hstrict k))
  have hspec : ∀ k : Nat,
      schedule.direction (startIndex + k) = .strict (actual k) ∧
        match (env (schedule.cut (startIndex + k))).graph with
        | .right => (actual k).side = .right
        | .left => (actual k).side = .left
        | .both => False :=
    fun k ↦ Classical.choose_spec
      (schedule.exists_strictActual (startIndex + k) (hstrict k))
  refine {
    actual := actual
    direction_eq := fun k ↦ (hspec k).1
    side_succ := ?_ }
  intro k
  have hindex : startIndex + (k + 1) = (startIndex + k) + 1 := by omega
  have hspecNext := hspec (k + 1)
  rw [hindex] at hspecNext
  have hstrictNext :
      (env (schedule.cut ((startIndex + k) + 1))).graph ≠ .both := by
    simpa [hindex] using hstrict (k + 1)
  have hstep := schedule.step (startIndex + k)
  cases hcurrent : (env (schedule.cut (startIndex + k))).graph with
  | right =>
      have hside : (actual k).side = .right := by
        simpa [hcurrent] using (hspec k).2
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
        hcurrent] at hstep
      have hnext_ne_right :
          (env (schedule.cut ((startIndex + k) + 1))).graph ≠ .right :=
        hstep.1.2.2
      cases hnext :
          (env (schedule.cut ((startIndex + k) + 1))).graph with
      | right => exact False.elim (hnext_ne_right hnext)
      | left =>
          have hnextSide : (actual (k + 1)).side = .left := by
            simpa [hnext] using hspecNext.2
          simpa [hside, hnextSide, IndexedLineageSide.other]
      | both => exact False.elim (hstrictNext hnext)
  | left =>
      have hside : (actual k).side = .left := by
        simpa [hcurrent] using (hspec k).2
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
        hcurrent] at hstep
      have hnext_ne_left :
          (env (schedule.cut ((startIndex + k) + 1))).graph ≠ .left :=
        hstep.1.2.2
      cases hnext :
          (env (schedule.cut ((startIndex + k) + 1))).graph with
      | right =>
          have hnextSide : (actual (k + 1)).side = .right := by
            simpa [hnext] using hspecNext.2
          simpa [hside, hnextSide, IndexedLineageSide.other]
      | left => exact False.elim (hnext_ne_left hnext)
      | both => exact False.elim (hstrictNext hnext)
  | both => exact False.elim (hstrict k hcurrent)

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Every operational schedule for a persistent strict-reversal environment
has a suffix whose proof-side bank directions alternate.  The deliberately
coarse choice `startIndex = noBothThreshold` avoids any inverse-cut search:
strict growth guarantees cut `k` is at least physical round `k`. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule.exists_eventualStrictAlternation
    {env : EnvironmentSequence In₁ In₂}
    (schedule : OperationalSchedule (In₁ := In₁) (In₂ := In₂) env)
    (hreversal : PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    ∃ startIndex : Nat,
      Nonempty
        (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalStrictAlternationFrom
          (In₁ := In₁) (In₂ := In₂) schedule startIndex) := by
  rcases hreversal.1 with ⟨threshold, hnoBoth⟩
  refine ⟨threshold, ⟨schedule.strictAlternationFrom threshold ?_⟩⟩
  intro k
  apply hnoBoth
  have hindex : threshold + k ≤ schedule.cut (threshold + k) :=
    schedule.index_le_cut (threshold + k)
  omega

end

end DetParityAutomaton

end DistributedSynthesis
