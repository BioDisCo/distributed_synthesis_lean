/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceive

/-!
# Constant-row strict blocks of the anchor-row full-restart controller

The receive map reads the semantic row from the selected relay and stores an
advance of that same relay.  Since relay advance preserves both receiver
anchors, repeated receives in one strict block use one constant row.  A
receive after a blind round restarts with false anchors and therefore starts
the new strict occurrence on `.first`.
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

private abbrev LinkedOne :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
    A strategy hwin

private abbrev LinkedTwo :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
    A strategy hwin

/-! ## One-step row laws -/

/-- A newly restarted right occurrence has the `.first` anchor row. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase_rightRow_of_not_lastRecv
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (hlast : two.2.1 = false) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
          A strategy hwin one two) = .first := by
  rcases two with ⟨output, lastRecv, relay, child⟩
  cases lastRecv with
  | false => rfl
  | true => simp at hlast

/-- A newly restarted left occurrence has the `.first` anchor row. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase_leftRow_of_not_lastRecv
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (hlast : one.2.1 = false) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
          A strategy hwin one two) = .first := by
  rcases one with ⟨output, lastRecv, relay, child⟩
  cases lastRecv with
  | false => rfl
  | true => simp at hlast

/-- A right receive records that it was the receiving endpoint. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo_lastRecv
    (state : LinkedTwo A strategy hwin) (own : In₂)
    (partner : LinkedOne A strategy hwin) (delivered : In₁) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo
      A strategy hwin state own partner delivered).2.1 = true := by
  rfl

/-- A right receive stores a relay with exactly the row it just used. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo_relayRightRow
    (state : LinkedTwo A strategy hwin) (own : In₂)
    (partner : LinkedOne A strategy hwin) (delivered : In₁) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo
          A strategy hwin state own partner delivered).2.2.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
          A strategy hwin partner state) := by
  simp [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay]

/-- A left receive records that it was the receiving endpoint. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne_lastRecv
    (state : LinkedOne A strategy hwin) (own : In₁)
    (partner : LinkedTwo A strategy hwin) (delivered : In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne
      A strategy hwin state own partner delivered).2.1 = true := by
  rfl

/-- Left-receive mirror. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne_relayLeftRow
    (state : LinkedOne A strategy hwin) (own : In₁)
    (partner : LinkedTwo A strategy hwin) (delivered : In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne
          A strategy hwin state own partner delivered).2.2.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
          A strategy hwin state partner) := by
  simp [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay]

/-- On the following right receive, the phase selector reads the same row,
independently of the new blind partner state. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo_nextBase_rightRow
    (state : LinkedTwo A strategy hwin) (own : In₂)
    (partner nextPartner : LinkedOne A strategy hwin) (delivered : In₁) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
          A strategy hwin nextPartner
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo
              A strategy hwin state own partner delivered)) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
          A strategy hwin partner state) := by
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo_lastRecv,
    ↓reduceIte]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo_relayRightRow
      A strategy hwin state own partner delivered

/-- Left-receive mirror. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne_nextBase_leftRow
    (state : LinkedOne A strategy hwin) (own : In₁)
    (partner nextPartner : LinkedTwo A strategy hwin) (delivered : In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
          A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne
              A strategy hwin state own partner delivered)
            nextPartner) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
          A strategy hwin state partner) := by
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne_lastRecv,
    ↓reduceIte]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne_relayLeftRow
      A strategy hwin state own partner delivered

/-! ## Arbitrarily long homogeneous receive runs -/

/-- Iterate process two's receives through one right-oriented block.  The
partner sequence is arbitrary because after the first receive it cannot
affect the selected receiver relay. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwoRun
    (state : LinkedTwo A strategy hwin)
    (partners : Nat → LinkedOne A strategy hwin)
    (inputs : Nat → In₁ × In₂) : Nat → LinkedTwo A strategy hwin
  | 0 => state
  | n + 1 =>
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwoRun
            state partners inputs n)
          (inputs n).2 (partners n) (inputs n).1

/-- Left-oriented mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOneRun
    (state : LinkedOne A strategy hwin)
    (partners : Nat → LinkedTwo A strategy hwin)
    (inputs : Nat → In₁ × In₂) : Nat → LinkedOne A strategy hwin
  | 0 => state
  | n + 1 =>
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOneRun
            state partners inputs n)
          (inputs n).1 (partners n) (inputs n).2

/-- Every receive position of a right block selects its initial semantic row. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwoRun_baseRow
    (state : LinkedTwo A strategy hwin)
    (partners : Nat → LinkedOne A strategy hwin)
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
          A strategy hwin (partners n)
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwoRun
              A strategy hwin state partners inputs n)) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
          A strategy hwin (partners 0) state) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwoRun]
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo_nextBase_rightRow]
      exact ih

/-- Every receive position of a left block selects its initial semantic row. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOneRun_baseRow
    (state : LinkedOne A strategy hwin)
    (partners : Nat → LinkedTwo A strategy hwin)
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
          A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOneRun
              A strategy hwin state partners inputs n)
            (partners n)) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
          A strategy hwin state (partners 0)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOneRun]
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne_nextBase_leftRow]
      exact ih

end

end DetParityAutomaton

end DistributedSynthesis
