/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartAnchorRowBlock
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOperationalCut

/-!
# Constant entry rows on actual operational blocks

This lifts receiver-anchor preservation to the semantic trace of the finite
controller.  Every maximal strict block starts after the receiving endpoint's
phase bit is false, hence its selected relay is restarted with false anchors.
Relay advance then preserves that row through the complete block.  Therefore
every strict record, including the closing record, uses `.first`.
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

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

/-- Both receiver bases selected before a semantic round use `.first`. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowsFirstAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Prop :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
      A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt
        A strategy hwin initialTag env n) = .first ∧
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
      A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt
        A strategy hwin initialTag env n) = .first

/-! ## One actual homogeneous step preserves the row -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt_succ_rightRow
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .right) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt
          A strategy hwin initialTag env (n + 1)) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt
          A strategy hwin initialTag env n) := by
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt_succ_of_right_eq_advance
      A strategy hwin initialTag env n hgraph]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance_rightRow
      A strategy hwin _ _

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt_succ_leftRow
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .left) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt
          A strategy hwin initialTag env (n + 1)) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt
          A strategy hwin initialTag env n) := by
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt_succ_of_left_eq_advance
      A strategy hwin initialTag env n hgraph]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance_leftRow
      A strategy hwin _ _

/-! ## Constancy on finite homogeneous intervals -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt_add_rightRow
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start length : Nat)
    (hall : ∀ t : Nat, t < length → (env (start + t)).graph = .right) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt
          A strategy hwin initialTag env (start + length)) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt
          A strategy hwin initialTag env start) := by
  induction length with
  | zero => rfl
  | succ length ih =>
      rw [Nat.add_succ]
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt_succ_rightRow
          A strategy hwin initialTag env (start + length)
            (hall length (Nat.lt_succ_self length))]
      exact ih (fun t ht ↦ hall t (Nat.lt.step ht))

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt_add_leftRow
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start length : Nat)
    (hall : ∀ t : Nat, t < length → (env (start + t)).graph = .left) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt
          A strategy hwin initialTag env (start + length)) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt
          A strategy hwin initialTag env start) := by
  induction length with
  | zero => rfl
  | succ length ih =>
      rw [Nat.add_succ]
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt_succ_leftRow
          A strategy hwin initialTag env (start + length)
            (hall length (Nat.lt_succ_self length))]
      exact ih (fun t ht ↦ hall t (Nat.lt.step ht))

/-! ## Every operational block is the constant `.first` row -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt_cut_rightRow
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)) = .first := by
  have hbit :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceivePhaseBits
      A strategy hwin initialTag env).two_at_cut_eq_false_of_right cuts k hgraph
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase_rightRow_of_not_lastRecv
      A strategy hwin
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceivePhaseBits]
    using hbit

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt_cut_leftRow
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)) = .first := by
  have hbit :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceivePhaseBits
      A strategy hwin initialTag env).one_at_cut_eq_false_of_left cuts k hgraph
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase_leftRow_of_not_lastRecv
      A strategy hwin
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceivePhaseBits]
    using hbit

/-- Every right-block position through the closing record uses `.first`. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt_cut_add_rightRow
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k j : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (hj : j ≤ cuts.openLength k) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k + j)) = .first := by
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt_add_rightRow
      A strategy hwin initialTag env (cuts.cuts k) j]
  · exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt_cut_rightRow
        A strategy hwin initialTag env cuts k hgraph
  · intro t ht
    exact (cuts.homogeneous k t (Nat.lt_of_lt_of_le ht hj)).trans hgraph

/-- Every left-block position through the closing record uses `.first`. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt_cut_add_leftRow
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k j : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (hj : j ≤ cuts.openLength k) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k + j)) = .first := by
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt_add_leftRow
      A strategy hwin initialTag env (cuts.cuts k) j]
  · exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt_cut_leftRow
        A strategy hwin initialTag env cuts k hgraph
  · intro t ht
    exact (cuts.homogeneous k t (Nat.lt_of_lt_of_le ht hj)).trans hgraph

/-! ## Global reachable-row invariant -/

/-- The semantic trace never selects a non-`.first` receiver base.  On a
same-orientation step this follows from relay-row preservation; on a switch
or simultaneous close it follows from the false phase bit and the fresh
false-anchor restart. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowsFirstAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowsFirstAt
      A strategy hwin initialTag env n := by
  induction n with
  | zero =>
      have hbits :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticPairAt_zero_selected_lastRecv
          A strategy hwin initialTag env
      constructor
      · apply
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase_rightRow_of_not_lastRecv
            A strategy hwin
        exact hbits.2
      · apply
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase_leftRow_of_not_lastRecv
            A strategy hwin
        exact hbits.1
  | succ n ih =>
      have hbits :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticPairAt_succ_selected_lastRecv
          A strategy hwin initialTag env n
      cases hgraph : (env n).graph with
      | right =>
          rw [hgraph] at hbits
          constructor
          · rw [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt_succ_rightRow
                A strategy hwin initialTag env n hgraph]
            exact ih.1
          · apply
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase_leftRow_of_not_lastRecv
                A strategy hwin
            exact hbits.1
      | left =>
          rw [hgraph] at hbits
          constructor
          · apply
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase_rightRow_of_not_lastRecv
                A strategy hwin
            exact hbits.2
          · rw [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt_succ_leftRow
                A strategy hwin initialTag env n hgraph]
            exact ih.2
      | both =>
          rw [hgraph] at hbits
          constructor
          · apply
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase_rightRow_of_not_lastRecv
                A strategy hwin
            exact hbits.2
          · apply
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase_leftRow_of_not_lastRecv
                A strategy hwin
            exact hbits.1

end

end DetParityAutomaton

end DistributedSynthesis
