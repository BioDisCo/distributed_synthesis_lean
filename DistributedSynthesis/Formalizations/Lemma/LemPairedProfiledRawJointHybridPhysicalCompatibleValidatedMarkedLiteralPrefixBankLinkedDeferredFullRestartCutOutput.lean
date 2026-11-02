/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartOperationalCut

/-!
# Physical output alignment at full-restart cuts

The operational-cut invariant locates an exact linked pair, but acceptance
also needs the executable controller's physical output to be the output of
that pair.  This file tests and packages that final local seam.

At a genuine orientation switch the blind sender and the receiver both
restart at the same stored child.  At time zero their complete relays may use
different receiver anchors, but sender initialization is anchor-independent.
Thus the output alignment is literal; no union carrier or hierarchy oracle is
needed on the persistent strict suffix.
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

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev LinkedRelay :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelay A
    strategy hwin

private abbrev LinkedOne :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
    A strategy hwin

private abbrev LinkedTwo :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
    A strategy hwin

private abbrev Payload :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload A
    strategy hwin

private abbrev OneControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedOne A strategy hwin) (Payload A strategy hwin) PUnit.{1}

private abbrev TwoControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedTwo A strategy hwin) (Payload A strategy hwin) PUnit.{1}

/-! ## Open-member provenance on a no-`both` suffix -/

/-- With no simultaneous round, both semantic controls remain in the open
pending member.  This is the temporal fact needed to identify a blind
endpoint's executable shared state with its proof-side selected state. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_open_of_noBoth
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both) : ∀ n : Nat,
    ∃ one : LinkedOne A strategy hwin,
      ∃ payloadOne : Payload A strategy hwin,
        ∃ two : LinkedTwo A strategy hwin,
          ∃ payloadTwo : Payload A strategy hwin,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                A strategy hwin initialTag env n =
              ((.inl (false, one, payloadOne) : OneControl A strategy hwin),
                (.inl (false, two, payloadTwo) : TwoControl A strategy hwin)) := by
  intro n
  induction n with
  | zero =>
      refine ⟨
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin initialTag).1,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
          A strategy hwin initialTag.1,
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin initialTag).2,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
          A strategy hwin initialTag.1, ?_⟩
      rfl
  | succ n ih =>
      rcases ih with ⟨one, payloadOne, two, payloadTwo, hcurrent⟩
      have hnext :
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
              A strategy hwin initialTag env (n + 1) =
            match (env n).graph with
            | .right =>
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
                    A strategy hwin
                      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                        A strategy hwin initialTag env n).1
                      (env n).inputOne).1,
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
                    A strategy hwin
                      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                        A strategy hwin initialTag)
                      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                        A strategy hwin initialTag env n).2
                      (env n).inputTwo
                      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                        A strategy hwin initialTag env n).1
                      (env n).inputOne).1)
            | .left =>
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
                    A strategy hwin
                      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                        A strategy hwin initialTag)
                      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                        A strategy hwin initialTag env n).1
                      (env n).inputOne
                      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                        A strategy hwin initialTag env n).2
                      (env n).inputTwo).1,
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
                    A strategy hwin
                      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                        A strategy hwin initialTag env n).2
                      (env n).inputTwo).1)
            | .both =>
                profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                      A strategy hwin initialTag)
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                      A strategy hwin initialTag env n).1
                    (env n).inputOne
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                      A strategy hwin initialTag env n).2
                    (env n).inputTwo := by
        rw [
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
          FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace]
        rfl
      cases hgraph : (env n).graph with
      | right =>
          refine ⟨
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne
              A strategy hwin one (env n).inputOne), payloadOne,
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
              A strategy hwin
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                  A strategy hwin initialTag)
                (.inl (false, two, payloadTwo)) (env n).inputTwo
                (.inl (false, one, payloadOne)) (env n).inputOne).1,
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
              A strategy hwin
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                  A strategy hwin initialTag)
                (.inl (false, two, payloadTwo)) (env n).inputTwo
                (.inl (false, one, payloadOne)) (env n).inputOne).2, ?_⟩
          rw [hnext, hgraph, hcurrent]
          rfl
      | left =>
          refine ⟨
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
              A strategy hwin
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                  A strategy hwin initialTag)
                (.inl (false, one, payloadOne)) (env n).inputOne
                (.inl (false, two, payloadTwo)) (env n).inputTwo).1,
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
              A strategy hwin
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                  A strategy hwin initialTag)
                (.inl (false, one, payloadOne)) (env n).inputOne
                (.inl (false, two, payloadTwo)) (env n).inputTwo).2,
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo
              A strategy hwin two (env n).inputTwo), payloadTwo, ?_⟩
          rw [hnext, hgraph, hcurrent]
          rfl
      | both => exact False.elim (hnoBoth n hgraph)

/-! ## The relay actually used by a blind endpoint -/

/-- Right-blind process one's locally selected relay before round `n`. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    LinkedRelay A strategy hwin :=
  let one :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
      A strategy hwin initialTag env n
  if one.2.1 then
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
      A strategy hwin (one.child A strategy hwin) false false
  else one.2.2.1

/-- Left-blind process two's mirror relay before round `n`. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    LinkedRelay A strategy hwin :=
  let two :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
      A strategy hwin initialTag env n
  if two.2.1 then
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
      A strategy hwin (two.child A strategy hwin) false false
  else two.2.2.1

/-- At the initial cut the right sender agrees with the fresh receiver base.
Receiver anchor metadata is deliberately not claimed equal. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt_zero_sender
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
        A strategy hwin initialTag env 0).1.1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env 0).1.1 := by
  rfl

/-- Initial left-sender mirror. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt_zero_sender
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
        A strategy hwin initialTag env 0).2.1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env 0).2.1 := by
  rfl

/-- Immediately after a left round the blind process-one relay and the
right-receive base are literally the same fresh relay. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt_succ_of_left
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .left) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
        A strategy hwin initialTag env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env (n + 1) := by
  have hbits :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_succ_selected_lastRecv
      A strategy hwin initialTag env n
  rw [hgraph] at hbits
  have hone :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
        A strategy hwin initialTag env (n + 1)).2.1 = true := by
    simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt]
      using hbits.1
  have htwo :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
        A strategy hwin initialTag env (n + 1)).2.1 = false := by
    simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt]
      using hbits.2
  simp [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase,
    hone, htwo]

/-- Immediately after a right round, left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt_succ_of_right
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .right) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
        A strategy hwin initialTag env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env (n + 1) := by
  have hbits :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_succ_selected_lastRecv
      A strategy hwin initialTag env n
  rw [hgraph] at hbits
  have hone :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
        A strategy hwin initialTag env (n + 1)).2.1 = false := by
    simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt]
      using hbits.1
  have htwo :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
        A strategy hwin initialTag env (n + 1)).2.1 = true := by
    simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt]
      using hbits.2
  simp [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase,
    hone, htwo]

/-! ## Exact sender alignment at every persistent-strict cut -/

/-- On a no-`both` operational decomposition, the sender actually used by
process one at every right cut is the sender of the receiver-selected exact
pair.  The initial case needs only sender equality; every later case is full
relay equality by the local restart. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt_cut_sender
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
        A strategy hwin initialTag env (cuts.cuts k)).1.1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env (cuts.cuts k)).1.1 := by
  cases k with
  | zero =>
      rw [cuts.cuts_zero]
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt_zero_sender
          A strategy hwin initialTag env
  | succ k =>
      have hstrict : (env (cuts.cuts k)).graph ≠ .both := hnoBoth _
      have hchange := cuts.maximal_of_strict k hstrict
      have hprevious : (env (cuts.cuts k)).graph = .left := by
        cases hp : (env (cuts.cuts k)).graph with
        | left => rfl
        | right => exact False.elim (hchange (hgraph.trans hp.symm))
        | both => exact False.elim (hstrict hp)
      have hclosingIndex :
          cuts.cuts (k + 1) - 1 = cuts.cuts k + cuts.openLength k := by
        rw [cuts.step_eq]
        omega
      have hclosing :
          (env (cuts.cuts k + cuts.openLength k)).graph = .left := by
        have h := cuts.closing_graph_eq k
        rw [hclosingIndex, hprevious] at h
        exact h
      have hbase :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt_succ_of_left
          A strategy hwin initialTag env
            (cuts.cuts k + cuts.openLength k) hclosing
      have hnext :
          cuts.cuts (k + 1) = cuts.cuts k + cuts.openLength k + 1 :=
        cuts.step_eq k
      rw [hnext]
      exact congrArg (fun relay ↦ relay.1.1) hbase

/-- Left-cut mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt_cut_sender
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
        A strategy hwin initialTag env (cuts.cuts k)).2.1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env (cuts.cuts k)).2.1 := by
  cases k with
  | zero =>
      rw [cuts.cuts_zero]
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt_zero_sender
          A strategy hwin initialTag env
  | succ k =>
      have hstrict : (env (cuts.cuts k)).graph ≠ .both := hnoBoth _
      have hchange := cuts.maximal_of_strict k hstrict
      have hprevious : (env (cuts.cuts k)).graph = .right := by
        cases hp : (env (cuts.cuts k)).graph with
        | right => rfl
        | left => exact False.elim (hchange (hgraph.trans hp.symm))
        | both => exact False.elim (hstrict hp)
      have hclosingIndex :
          cuts.cuts (k + 1) - 1 = cuts.cuts k + cuts.openLength k := by
        rw [cuts.step_eq]
        omega
      have hclosing :
          (env (cuts.cuts k + cuts.openLength k)).graph = .right := by
        have h := cuts.closing_graph_eq k
        rw [hclosingIndex, hprevious] at h
        exact h
      have hbase :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt_succ_of_right
          A strategy hwin initialTag env
            (cuts.cuts k + cuts.openLength k) hclosing
      have hnext :
          cuts.cuts (k + 1) = cuts.cuts k + cuts.openLength k + 1 :=
        cuts.step_eq k
      rw [hnext]
      exact congrArg (fun relay ↦ relay.2.1) hbase

/-! ## Fresh occurrence at every operational cut -/

/-- Every strict-right operational cut starts from a freshly reinstalled
linked relay at the authoritative bank parent.  The previous theorem needed
only sender equality; the state/priority induction needs this stronger full
relay equation. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt_cut_eq_restartRelay
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env (cuts.cuts k) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
            A strategy hwin initialTag env (cuts.cuts k)) false false := by
  cases k with
  | zero =>
      rw [cuts.cuts_zero,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt_zero,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt_zero]
  | succ k =>
      have hstrict : (env (cuts.cuts k)).graph ≠ .both := hnoBoth _
      have hchange := cuts.maximal_of_strict k hstrict
      have hprevious : (env (cuts.cuts k)).graph = .left := by
        cases hp : (env (cuts.cuts k)).graph with
        | left => rfl
        | right => exact False.elim (hchange (hgraph.trans hp.symm))
        | both => exact False.elim (hstrict hp)
      have hclosingIndex :
          cuts.cuts (k + 1) - 1 =
            cuts.cuts k + cuts.openLength k := by
        rw [cuts.step_eq]
        omega
      have hclosing :
          (env (cuts.cuts k + cuts.openLength k)).graph = .left := by
        have h := cuts.closing_graph_eq k
        rw [hclosingIndex, hprevious] at h
        exact h
      have hbase :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt_succ_of_left
          A strategy hwin initialTag env
            (cuts.cuts k + cuts.openLength k) hclosing
      have hnext :
          cuts.cuts (k + 1) = cuts.cuts k + cuts.openLength k + 1 :=
        cuts.step_eq k
      rw [hnext]
      exact hbase

/-- Strict-left fresh-occurrence mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt_cut_eq_restartRelay
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env (cuts.cuts k) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
            A strategy hwin initialTag env (cuts.cuts k)) false false := by
  cases k with
  | zero =>
      rw [cuts.cuts_zero,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt_zero,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt_zero]
  | succ k =>
      have hstrict : (env (cuts.cuts k)).graph ≠ .both := hnoBoth _
      have hchange := cuts.maximal_of_strict k hstrict
      have hprevious : (env (cuts.cuts k)).graph = .right := by
        cases hp : (env (cuts.cuts k)).graph with
        | right => rfl
        | left => exact False.elim (hchange (hgraph.trans hp.symm))
        | both => exact False.elim (hstrict hp)
      have hclosingIndex :
          cuts.cuts (k + 1) - 1 =
            cuts.cuts k + cuts.openLength k := by
        rw [cuts.step_eq]
        omega
      have hclosing :
          (env (cuts.cuts k + cuts.openLength k)).graph = .right := by
        have h := cuts.closing_graph_eq k
        rw [hclosingIndex, hprevious] at h
        exact h
      have hbase :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt_succ_of_right
          A strategy hwin initialTag env
            (cuts.cuts k + cuts.openLength k) hclosing
      have hnext :
          cuts.cuts (k + 1) = cuts.cuts k + cuts.openLength k + 1 :=
        cuts.step_eq k
      rw [hnext]
      exact hbase

/-- A right cut begins at literal prefix `[]` of one exact semantic
occurrence.  This strengthens the extensional `PairAtPrefix` invariant with
the freshness needed by the block-state induction. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightCut_freshOccurrence
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
            A strategy hwin initialTag env (cuts.cuts k))) :
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
        A strategy hwin initialTag env (cuts.cuts k)
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env (cuts.cuts k)
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
        (direction : ProfiledRawJointFamilyDirection
          (I := Unit) (In₁ := In₁) (In₂ := In₂))
        (semanticMember : ProcOnePairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).right () =
          some semanticMember,
        base.1.1 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
              A strategy hwin root family direction semanticMember hmember [] ∧
          base.1.2 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
              A strategy hwin root family direction semanticMember hmember false
                [] := by
  dsimp only
  let root :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
      A strategy hwin initialTag env (cuts.cuts k)
  have hbase :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt_cut_eq_restartRelay
      A strategy hwin initialTag env cuts hnoBoth k hgraph
  change
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env (cuts.cuts k) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin root false false at hbase
  change
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
      A strategy hwin root at hready
  rcases hready with ⟨code, slot, hreachable, hcode, hlive⟩
  obtain ⟨oldMove, hmove, hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  rcases hrebuild with
    ⟨_hmarker, _hreachable', parent, old, rawDirection, family, direction,
      semanticMember, hmember, _hsource, _hannotation, _haligned, _hold,
        hlinked⟩
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
      A strategy hwin root
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
          A strategy hwin family direction semanticMember hmember false)
        [] default⟩
  refine ⟨family, direction, semanticMember, hmember, ?_, ?_⟩
  · rw [hbase]
    change
      profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial A
          (root.linkedRightMove A strategy hwin) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember []
    rw [hlinked]
    change
      finiteCrossAnchorDescriptorFirstTwoSenderInitial _ _ _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
            A strategy hwin root family direction semanticMember hmember) =
        ⟨_, finiteCrossAnchorSenderAtPrefix
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
            A strategy hwin root family direction semanticMember hmember).2 []⟩
    rw [finiteCrossAnchorSenderAtPrefix_nil]
    rfl
  · rw [hbase]
    change
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A
          (root.linkedRightMove A strategy hwin) false =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false []
    rw [hlinked]
    change
      finiteCrossAnchorDescriptorFirstTwoReceiverInitial _ _ _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
            A strategy hwin root family direction semanticMember hmember) false =
        ⟨_, finiteCrossAnchorReceiverAtPrefix
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
            A strategy hwin root family direction semanticMember hmember).2 false []⟩
    rw [finiteCrossAnchorReceiverAtPrefix_nil]
    rfl

/-- Fresh strict-left occurrence mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftCut_freshOccurrence
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
            A strategy hwin initialTag env (cuts.cuts k))) :
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
        A strategy hwin initialTag env (cuts.cuts k)
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env (cuts.cuts k)
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
        (direction : ProfiledRawJointFamilyDirection
          (I := Unit) (In₁ := In₁) (In₂ := In₂))
        (semanticMember : ProcTwoPairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).left () =
          some semanticMember,
        base.2.1 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
              A strategy hwin root family direction semanticMember hmember [] ∧
          base.2.2 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
              A strategy hwin root family direction semanticMember hmember false
                [] := by
  dsimp only
  let root :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
      A strategy hwin initialTag env (cuts.cuts k)
  have hbase :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt_cut_eq_restartRelay
      A strategy hwin initialTag env cuts hnoBoth k hgraph
  change
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env (cuts.cuts k) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin root false false at hbase
  change
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
      A strategy hwin root at hready
  rcases hready with ⟨code, slot, hreachable, hcode, hlive⟩
  obtain ⟨oldMove, hmove, hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  rcases hrebuild with
    ⟨_hmarker, _hreachable', parent, old, rawDirection, family, direction,
      semanticMember, hmember, _hsource, _hannotation, _haligned, _hold,
        hlinked⟩
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
      A strategy hwin root
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
          A strategy hwin family direction semanticMember hmember false)
        [] default⟩
  refine ⟨family, direction, semanticMember, hmember, ?_, ?_⟩
  · rw [hbase]
    change
      profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial A
          (root.linkedLeftMove A strategy hwin) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember []
    rw [hlinked]
    change
      finiteCrossAnchorDescriptorFirstTwoSenderInitial _ _ _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin root family direction semanticMember hmember) =
        ⟨_, finiteCrossAnchorSenderAtPrefix
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin root family direction semanticMember hmember).2 []⟩
    rw [finiteCrossAnchorSenderAtPrefix_nil]
    rfl
  · rw [hbase]
    change
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A
          (root.linkedLeftMove A strategy hwin) false =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false []
    rw [hlinked]
    change
      finiteCrossAnchorDescriptorFirstTwoReceiverInitial _ _ _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin root family direction semanticMember hmember) false =
        ⟨_, finiteCrossAnchorReceiverAtPrefix
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin root family direction semanticMember hmember).2 false []⟩
    rw [finiteCrossAnchorReceiverAtPrefix_nil]
    rfl

/-! ## Exact same-block state recurrences -/

/-- During a right block, the receiver-selected complete relay advances by
one ordinary linked-table round. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt_succ_of_right_eq_advance
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (n : Nat) (hgraph : (env n).graph = .right) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
            A strategy hwin initialTag env n)
          ((env n).inputOne, (env n).inputTwo) := by
  obtain ⟨one, payloadOne, two, payloadTwo, hpair⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_open_of_noBoth
      A strategy hwin initialTag env hnoBoth n
  have hnext :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin initialTag env (n + 1) =
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                A strategy hwin initialTag env n).1 (env n).inputOne).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin initialTag)
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                A strategy hwin initialTag env n).2 (env n).inputTwo
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                A strategy hwin initialTag env n).1 (env n).inputOne).1) := by
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
      hgraph]
    rfl
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt]
  rw [hnext, hpair]
  rfl

/-- Left-block mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt_succ_of_left_eq_advance
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (n : Nat) (hgraph : (env n).graph = .left) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
            A strategy hwin initialTag env n)
          ((env n).inputOne, (env n).inputTwo) := by
  obtain ⟨one, payloadOne, two, payloadTwo, hpair⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_open_of_noBoth
      A strategy hwin initialTag env hnoBoth n
  have hnext :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin initialTag env (n + 1) =
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin initialTag)
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                A strategy hwin initialTag env n).1 (env n).inputOne
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                A strategy hwin initialTag env n).2 (env n).inputTwo).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                A strategy hwin initialTag env n).2 (env n).inputTwo).1) := by
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
      hgraph]
    rfl
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt]
  rw [hnext, hpair]
  rfl

/-- The actually blind right sender obeys the same one-round sender
recurrence. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt_succ_of_right_sender
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (n : Nat) (hgraph : (env n).graph = .right) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
        A strategy hwin initialTag env (n + 1)).1.1 =
      (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
          A strategy hwin initialTag env n).1.1 (env n).inputOne).2 := by
  obtain ⟨one, payloadOne, two, payloadTwo, hpair⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_open_of_noBoth
      A strategy hwin initialTag env hnoBoth n
  have hnext :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin initialTag env (n + 1) =
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                A strategy hwin initialTag env n).1 (env n).inputOne).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin initialTag)
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                A strategy hwin initialTag env n).2 (env n).inputTwo
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                A strategy hwin initialTag env n).1 (env n).inputOne).1) := by
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
      hgraph]
    rfl
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt]
  rw [hnext, hpair]
  rfl

/-- Blind left-sender mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt_succ_of_left_sender
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (n : Nat) (hgraph : (env n).graph = .left) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
        A strategy hwin initialTag env (n + 1)).2.1 =
      (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
          A strategy hwin initialTag env n).2.1 (env n).inputTwo).2 := by
  obtain ⟨one, payloadOne, two, payloadTwo, hpair⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_open_of_noBoth
      A strategy hwin initialTag env hnoBoth n
  have hnext :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin initialTag env (n + 1) =
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin initialTag)
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                A strategy hwin initialTag env n).1 (env n).inputOne
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                A strategy hwin initialTag env n).2 (env n).inputTwo).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                A strategy hwin initialTag env n).2 (env n).inputTwo).1) := by
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
      hgraph]
    rfl
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt]
  rw [hnext, hpair]
  rfl

/-! ## Pair-run alignment from an arbitrary strict start -/

/-- The actual blind sender and selected right receiver at offset `j` are
exactly the pure linked pair run from the block entry. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightPairRun_eq_operational
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (start j : Nat)
    (hstart :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
          A strategy hwin initialTag env start).1.1 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env start).1.1)
    (hgraph : ∀ t : Nat, t < j → (env (start + t)).graph = .right) :
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env start
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env (start + t)).inputOne, (env (start + t)).inputTwo)
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
        A strategy hwin initialTag env (start + j)).1.1,
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env (start + j)).1.2) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun
        A strategy hwin base.1.1 base.1.2 inputs j := by
  dsimp only
  induction j with
  | zero =>
      apply Prod.ext
      · simpa using hstart
      · rfl
  | succ j ih =>
      have hjgraph := hgraph j (Nat.lt_succ_self j)
      have hblind :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt_succ_of_right_sender
          A strategy hwin initialTag env hnoBoth (start + j) hjgraph
      have hbase :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt_succ_of_right_eq_advance
          A strategy hwin initialTag env hnoBoth (start + j) hjgraph
      have ih' := ih (fun t ht ↦ hgraph t (Nat.lt_trans ht (Nat.lt_succ_self j)))
      rw [show start + (j + 1) = start + j + 1 by omega, hblind, hbase]
      rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun]
      rw [← ih']
      rfl

/-- Left pair-run mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftPairRun_eq_operational
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (start j : Nat)
    (hstart :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
          A strategy hwin initialTag env start).2.1 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env start).2.1)
    (hgraph : ∀ t : Nat, t < j → (env (start + t)).graph = .left) :
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env start
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env (start + t)).inputOne, (env (start + t)).inputTwo)
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
        A strategy hwin initialTag env (start + j)).2.1,
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env (start + j)).2.2) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun
        A strategy hwin base.2.1 base.2.2 inputs j := by
  dsimp only
  induction j with
  | zero =>
      apply Prod.ext
      · simpa using hstart
      · rfl
  | succ j ih =>
      have hjgraph := hgraph j (Nat.lt_succ_self j)
      have hblind :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt_succ_of_left_sender
          A strategy hwin initialTag env hnoBoth (start + j) hjgraph
      have hbase :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt_succ_of_left_eq_advance
          A strategy hwin initialTag env hnoBoth (start + j) hjgraph
      have ih' := ih (fun t ht ↦ hgraph t (Nat.lt_trans ht (Nat.lt_succ_self j)))
      rw [show start + (j + 1) = start + j + 1 by omega, hblind, hbase]
      rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun]
      rw [← ih']
      rfl

/-! ## One-round physical output equality -/

/-- The output pair named by the controller's proved reference word. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Out₁ × Out₂ :=
  let controller :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
      A strategy hwin initialTag
  let word :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceInvariant
      A strategy hwin initialTag env).referenceWord controller
  ((word n).outputOne, (word n).outputTwo)

/-- The same output pair exposed directly from the deterministic semantic
controls. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticOutputPairAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Out₁ × Out₂ :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
      A strategy hwin initialTag env n
  match (env n).graph with
  | .right =>
      ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
          A strategy hwin pair.1 (env n).inputOne).2,
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
          A strategy hwin fallback pair.2 (env n).inputTwo pair.1
            (env n).inputOne).2)
  | .left =>
      ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
          A strategy hwin fallback pair.1 (env n).inputOne pair.2
            (env n).inputTwo).2,
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
          A strategy hwin pair.2 (env n).inputTwo).2)
  | .both =>
      ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
          A strategy hwin fallback pair.1 (env n).inputOne pair.2
            (env n).inputTwo).2,
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
          A strategy hwin fallback pair.2 (env n).inputTwo pair.1
            (env n).inputOne).2)

/-- The trace invariant records exactly the explicit semantic output pair. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_eq_semantic
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
        A strategy hwin initialTag env n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticOutputPairAt
        A strategy hwin initialTag env n := by
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceInvariant,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartMealyTraceInvariant,
    FinitePairedMealyController.LiteralCrossMealyTraceInvariant.toMooreTraceInvariant,
    FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord,
    FiniteAcknowledgedDelayedCarrier.ExactClosingSelectedTraceLaws.toMealyTraceInvariant,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputOne,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticOutputPairAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt]
  cases hgraph : (env n).graph <;> rfl

/-- Open pending controls expose the shared full-restart output directly. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne_open_output
    (one : LinkedOne A strategy hwin) (payload : Payload A strategy hwin)
    (input : In₁) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin
          (.inl (false, one, payload) : OneControl A strategy hwin) input).2 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne
        A strategy hwin one input).1 := by
  rfl

/-- Open right receive exposes the selected linked receiver output. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo_open_output
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : LinkedTwo A strategy hwin) (payloadTwo : Payload A strategy hwin)
    (one : LinkedOne A strategy hwin) (payloadOne : Payload A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin fallback
          (.inl (false, two, payloadTwo) : TwoControl A strategy hwin) input.2
          (.inl (false, one, payloadOne) : OneControl A strategy hwin)
          input.1).2 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo
        A strategy hwin two input.2 one input.1).1 := by
  rfl

/-- Open process-two mirror blind output. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo_open_output
    (two : LinkedTwo A strategy hwin) (payload : Payload A strategy hwin)
    (input : In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin
          (.inl (false, two, payload) : TwoControl A strategy hwin) input).2 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo
        A strategy hwin two input).1 := by
  rfl

/-- Open left receive mirror. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne_open_output
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : LinkedOne A strategy hwin) (payloadOne : Payload A strategy hwin)
    (two : LinkedTwo A strategy hwin) (payloadTwo : Payload A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin fallback
          (.inl (false, one, payloadOne) : OneControl A strategy hwin) input.1
          (.inl (false, two, payloadTwo) : TwoControl A strategy hwin)
          input.2).2 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne
        A strategy hwin one input.1 two input.2).1 := by
  rfl

set_option maxHeartbeats 1000000 in
/-- At a marked bank root, the first right-round reference output is exactly
the canonical uniform-activation output selected by that bank. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRoot_referenceOutput_zero_right
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hgraph : (env 0).graph = .right) :
    let state :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control
    let world :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world
    let installed :=
      profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
    let activation :=
      profiledRawJointHybridExactRightUniformActivation A strategy hwin
        installed
    let children :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRootTag
            A strategy hwin control)
          env 0 =
      (pairedRightSenderStrategy activation.lambda [] (env 0).inputOne,
        pairedRightInformedForRow .first
          (profiledRawJointRightFinitePayloadLinkedSiblingReceiver A
            activation children [] ((env 0).inputTwo, (env 0).inputOne)
            ).physical) := by
  dsimp only
  have hroot :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRoot_strictRight_initial_output
      A strategy hwin control ((env 0).inputOne, (env 0).inputTwo)
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_eq_semantic,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticOutputPairAt,
    hgraph]
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRootTag,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInstall,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_open]
    using hroot

set_option maxHeartbeats 1000000 in
/-- At a marked bank root, the first left-round reference output is the mirror
canonical uniform-activation output selected by that bank. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRoot_referenceOutput_zero_left
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hgraph : (env 0).graph = .left) :
    let state :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control
    let world :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world
    let installed :=
      profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
    let activation :=
      profiledRawJointHybridExactLeftUniformActivation A strategy hwin
        installed
    let children :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRootTag
            A strategy hwin control)
          env 0 =
      (pairedLeftInformedForRow .first
          (profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A
            activation children [] ((env 0).inputOne, (env 0).inputTwo)
            ).physical,
        pairedLeftSenderStrategy activation.lambda [] (env 0).inputTwo) := by
  dsimp only
  have hroot :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRoot_strictLeft_initial_output
      A strategy hwin control ((env 0).inputOne, (env 0).inputTwo)
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_eq_semantic,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticOutputPairAt,
    hgraph]
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRootTag,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInstall,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_open]
    using hroot

/-- **Frozen-entry physical seam, right case.** At every operational right cut,
the reference output is exactly round zero of the rooted linked pair in its
`.first` entry row. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_rightCut_eq_pairOutput_zero
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right) :
    let n := cuts.cuts k
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env n
    let row : PairedEntryRow := .first
    let inputs : Nat → In₁ × In₂ := fun j ↦
      ((env (n + j)).inputOne, (env (n + j)).inputTwo)
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
        A strategy hwin initialTag env n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput
        A strategy hwin base.1.1 base.1.2 row inputs 0 := by
  dsimp only
  let n := cuts.cuts k
  obtain ⟨one, payloadOne, two, payloadTwo, hpair⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_open_of_noBoth
      A strategy hwin initialTag env hnoBoth n
  have hselectedOne :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
          A strategy hwin initialTag env n = one := by
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
      hpair]
  have hselectedTwo :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
          A strategy hwin initialTag env n = two := by
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt,
      hpair]
  have hsender :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt_cut_sender
      A strategy hwin initialTag env cuts hnoBoth k hgraph
  change
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
        A strategy hwin initialTag env n).1.1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env n).1.1 at hsender
  dsimp only [n] at hpair hselectedOne hselectedTwo hsender ⊢
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_eq_semantic]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticOutputPairAt,
    hgraph, hpair]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne_open_output,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo_open_output,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun,
    Nat.add_zero]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt,
    hselectedOne, hselectedTwo] at hsender ⊢
  rw [hsender]

/-- Left-cut mirror of the fail-fast physical seam. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_leftCut_eq_pairOutput_zero
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left) :
    let n := cuts.cuts k
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env n
    let row : PairedEntryRow := .first
    let inputs : Nat → In₁ × In₂ := fun j ↦
      ((env (n + j)).inputOne, (env (n + j)).inputTwo)
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
        A strategy hwin initialTag env n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput
        A strategy hwin base.2.1 base.2.2 row inputs 0 := by
  dsimp only
  let n := cuts.cuts k
  obtain ⟨one, payloadOne, two, payloadTwo, hpair⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_open_of_noBoth
      A strategy hwin initialTag env hnoBoth n
  have hselectedOne :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
          A strategy hwin initialTag env n = one := by
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
      hpair]
  have hselectedTwo :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
          A strategy hwin initialTag env n = two := by
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt,
      hpair]
  have hsender :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt_cut_sender
      A strategy hwin initialTag env cuts hnoBoth k hgraph
  change
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
        A strategy hwin initialTag env n).2.1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env n).2.1 at hsender
  dsimp only [n] at hpair hselectedOne hselectedTwo hsender ⊢
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_eq_semantic]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticOutputPairAt,
    hgraph, hpair]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo_open_output,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne_open_output,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun,
    Nat.add_zero]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt,
    hselectedOne, hselectedTwo] at hsender ⊢
  rw [hsender]

/-! ## Whole-block physical output equality -/

/-- The locally selected row in a strict-right block is `.first` exactly at
the cut and `.both` at every later position, including the closing receive.
This is a proof of the local receive-bit evolution, not a direction oracle. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_add_row_eq
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k j : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (hj : j ≤ cuts.openLength k) :
    (if
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
          A strategy hwin initialTag env (cuts.cuts k + j)).2.1
      then PairedEntryRow.both else PairedEntryRow.first) =
        if j = 0 then PairedEntryRow.first else PairedEntryRow.both := by
  let bits :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartOperationalReceivePhaseBits
      A strategy hwin initialTag env
  by_cases hzero : j = 0
  · subst j
    have hbit := bits.two_at_cut_eq_false_of_right cuts k hgraph
    simpa [bits,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartOperationalReceivePhaseBits]
      using hbit
  · have hpositive : 0 < j := Nat.pos_of_ne_zero hzero
    have hoffset : j - 1 < cuts.openLength k := by omega
    have hbefore := cuts.homogeneous k (j - 1) hoffset
    rw [hgraph] at hbefore
    have hstep := bits.step (cuts.cuts k + (j - 1))
    rw [hbefore] at hstep
    have hindex : cuts.cuts k + (j - 1) + 1 = cuts.cuts k + j := by
      omega
    have hbit :
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
          A strategy hwin initialTag env (cuts.cuts k + j)).2.1 = true := by
      rw [← hindex]
      simpa [bits,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartOperationalReceivePhaseBits]
        using hstep.2
    simp [hzero, hbit]

/-- Process-one mirror of the first-then-both row law. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_add_row_eq
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k j : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (hj : j ≤ cuts.openLength k) :
    (if
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
          A strategy hwin initialTag env (cuts.cuts k + j)).2.1
      then PairedEntryRow.both else PairedEntryRow.first) =
        if j = 0 then PairedEntryRow.first else PairedEntryRow.both := by
  let bits :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartOperationalReceivePhaseBits
      A strategy hwin initialTag env
  by_cases hzero : j = 0
  · subst j
    have hbit := bits.one_at_cut_eq_false_of_left cuts k hgraph
    simpa [bits,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartOperationalReceivePhaseBits]
      using hbit
  · have hpositive : 0 < j := Nat.pos_of_ne_zero hzero
    have hoffset : j - 1 < cuts.openLength k := by omega
    have hbefore := cuts.homogeneous k (j - 1) hoffset
    rw [hgraph] at hbefore
    have hstep := bits.step (cuts.cuts k + (j - 1))
    rw [hbefore] at hstep
    have hindex : cuts.cuts k + (j - 1) + 1 = cuts.cuts k + j := by
      omega
    have hbit :
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
          A strategy hwin initialTag env (cuts.cuts k + j)).2.1 = true := by
      rw [← hindex]
      simpa [bits,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartOperationalReceivePhaseBits]
        using hstep.1
    simp [hzero, hbit]

/-- Throughout a maximal strict-right block, including its closing receive,
the controller's physical output is exactly the output of the rooted linked
pair run in the frozen `.first` entry row.  The receive-phase bit remains
available for restart detection but no longer changes the semantic DPA row. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_rightCut_add_eq_pairOutput
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k j : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (hj : j ≤ cuts.openLength k) :
    let start := cuts.cuts k
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env start
    let row : PairedEntryRow := .first
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env (start + t)).inputOne, (env (start + t)).inputTwo)
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
        A strategy hwin initialTag env (start + j) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput
        A strategy hwin base.1.1 base.1.2 row inputs j := by
  dsimp only
  let start := cuts.cuts k
  have hhomogeneous : ∀ t : Nat, t < j →
      (env (start + t)).graph = .right := by
    intro t ht
    have htOpen : t < cuts.openLength k := by omega
    exact (cuts.homogeneous k t htOpen).trans hgraph
  have hcurrent : (env (start + j)).graph = .right := by
    by_cases hclose : j = cuts.openLength k
    · rw [hclose]
      have hclosing := cuts.closing_graph_eq k
      have hclosingIndex :
          cuts.cuts (k + 1) - 1 = start + cuts.openLength k := by
        dsimp only [start]
        rw [cuts.step_eq]
        omega
      rw [hclosingIndex, hgraph] at hclosing
      exact hclosing
    · have hjOpen : j < cuts.openLength k := by omega
      exact (cuts.homogeneous k j hjOpen).trans hgraph
  have hstart :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt_cut_sender
      A strategy hwin initialTag env cuts hnoBoth k hgraph
  change
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
        A strategy hwin initialTag env start).1.1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env start).1.1 at hstart
  have hrun :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightPairRun_eq_operational
      A strategy hwin initialTag env hnoBoth start j hstart hhomogeneous
  obtain ⟨one, payloadOne, two, payloadTwo, hpair⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_open_of_noBoth
      A strategy hwin initialTag env hnoBoth (start + j)
  have hselectedOne :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
          A strategy hwin initialTag env (start + j) = one := by
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
      hpair]
  have hselectedTwo :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
          A strategy hwin initialTag env (start + j) = two := by
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt,
      hpair]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_eq_semantic]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticOutputPairAt,
    hcurrent, hpair]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput,
    ← hrun]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne_open_output,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo_open_output]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt,
    hselectedOne, hselectedTwo]

/-- Strict-left mirror of whole-block physical output equality. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_leftCut_add_eq_pairOutput
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k j : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (hj : j ≤ cuts.openLength k) :
    let start := cuts.cuts k
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env start
    let row : PairedEntryRow := .first
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env (start + t)).inputOne, (env (start + t)).inputTwo)
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
        A strategy hwin initialTag env (start + j) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput
        A strategy hwin base.2.1 base.2.2 row inputs j := by
  dsimp only
  let start := cuts.cuts k
  have hhomogeneous : ∀ t : Nat, t < j →
      (env (start + t)).graph = .left := by
    intro t ht
    have htOpen : t < cuts.openLength k := by omega
    exact (cuts.homogeneous k t htOpen).trans hgraph
  have hcurrent : (env (start + j)).graph = .left := by
    by_cases hclose : j = cuts.openLength k
    · rw [hclose]
      have hclosing := cuts.closing_graph_eq k
      have hclosingIndex :
          cuts.cuts (k + 1) - 1 = start + cuts.openLength k := by
        dsimp only [start]
        rw [cuts.step_eq]
        omega
      rw [hclosingIndex, hgraph] at hclosing
      exact hclosing
    · have hjOpen : j < cuts.openLength k := by omega
      exact (cuts.homogeneous k j hjOpen).trans hgraph
  have hstart :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt_cut_sender
      A strategy hwin initialTag env cuts hnoBoth k hgraph
  change
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
        A strategy hwin initialTag env start).2.1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env start).2.1 at hstart
  have hrun :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftPairRun_eq_operational
      A strategy hwin initialTag env hnoBoth start j hstart hhomogeneous
  obtain ⟨one, payloadOne, two, payloadTwo, hpair⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_open_of_noBoth
      A strategy hwin initialTag env hnoBoth (start + j)
  have hselectedOne :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
          A strategy hwin initialTag env (start + j) = one := by
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
      hpair]
  have hselectedTwo :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
          A strategy hwin initialTag env (start + j) = two := by
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt,
      hpair]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_eq_semantic]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticOutputPairAt,
    hcurrent, hpair]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput,
    ← hrun]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo_open_output,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne_open_output]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt,
    hselectedOne, hselectedTwo]

/-- Consumer-facing right-block form: every round uses the frozen `.first`
entry row. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_rightCut_add_eq_pairOutput_frozenFirst
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k j : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (hj : j ≤ cuts.openLength k) :
    let start := cuts.cuts k
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env start
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env (start + t)).inputOne, (env (start + t)).inputTwo)
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
        A strategy hwin initialTag env (start + j) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput
        A strategy hwin base.1.1 base.1.2 .first inputs j := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_rightCut_add_eq_pairOutput
      A strategy hwin initialTag env cuts hnoBoth k j hgraph hj

/-- Consumer-facing left-block mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_leftCut_add_eq_pairOutput_frozenFirst
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k j : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (hj : j ≤ cuts.openLength k) :
    let start := cuts.cuts k
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env start
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env (start + t)).inputOne, (env (start + t)).inputTwo)
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
        A strategy hwin initialTag env (start + j) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput
        A strategy hwin base.2.1 base.2.2 .first inputs j := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_leftCut_add_eq_pairOutput
      A strategy hwin initialTag env cuts hnoBoth k j hgraph hj

end

end DetParityAutomaton

end DistributedSynthesis
