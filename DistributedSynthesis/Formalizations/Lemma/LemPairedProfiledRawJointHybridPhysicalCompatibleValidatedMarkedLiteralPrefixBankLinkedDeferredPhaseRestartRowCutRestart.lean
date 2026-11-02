/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowMixedPacket
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankOperationalSemanticCloseConstructor

/-!
# Fresh restart relays at row-aware operational cuts

The row-aware phase controller retains a table inside a homogeneous strict
block.  At the next strict block entry, however, the receiving endpoint's
local phase bit is false.  Hence its executable base is exactly the fresh
restart relay at the authoritative marked-bank parent.  These equations are
the cut-level adapter needed to apply the mixed-row packet.
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

/-! ## Exact executable bases at strict cut entries -/

/-- At a strict-right operational cut, process two's local bit chooses the
fresh relay at the common authoritative parent. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt_cut_eq_restartRelay
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
        A strategy hwin initialTag env (cuts.cuts k) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
            A strategy hwin initialTag env (cuts.cuts k)) false false := by
  let one :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOneAt
      A strategy hwin initialTag env (cuts.cuts k)
  let two :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwoAt
      A strategy hwin initialTag env (cuts.cuts k)
  have hbit :=
    OperationalReceivePhaseBits.two_at_cut_eq_false_of_right cuts
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivePhaseBits
        A strategy hwin initialTag env) k hgraph
  change two.2.1 = false at hbit
  have hparentTwo :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentTwoAt
          A strategy hwin initialTag env (cuts.cuts k) =
        one.child A strategy hwin := by
    change
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
          A strategy hwin one two = one.child A strategy hwin
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo_eq_childOne_of_restart
        A strategy hwin one two hbit
  have hparents :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentsAt_eq
      A strategy hwin initialTag env (cuts.cuts k)
  have hchild :
      one.child A strategy hwin =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
          A strategy hwin initialTag env (cuts.cuts k) :=
    (hparents.trans hparentTwo).symm
  change
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
        A strategy hwin one two = _
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase,
    hbit, Bool.false_eq_true, ↓reduceIte]
  exact congrArg
    (fun state : BankControl A strategy hwin ↦
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin state false false) hchild

/-- Strict-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt_cut_eq_restartRelay
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
        A strategy hwin initialTag env (cuts.cuts k) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
            A strategy hwin initialTag env (cuts.cuts k)) false false := by
  let one :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOneAt
      A strategy hwin initialTag env (cuts.cuts k)
  let two :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwoAt
      A strategy hwin initialTag env (cuts.cuts k)
  have hbit :=
    OperationalReceivePhaseBits.one_at_cut_eq_false_of_left cuts
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivePhaseBits
        A strategy hwin initialTag env) k hgraph
  change one.2.1 = false at hbit
  have hparentOne :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
          A strategy hwin initialTag env (cuts.cuts k) =
        two.child A strategy hwin := by
    change
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
          A strategy hwin one two = two.child A strategy hwin
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne_eq_childTwo_of_restart
        A strategy hwin one two hbit
  change
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
        A strategy hwin one two = _
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase,
    hbit, Bool.false_eq_true, ↓reduceIte]
  exact congrArg
    (fun state : BankControl A strategy hwin ↦
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin state false false) hparentOne.symm

/-! ## Cut-root initialization -/

/-- Readiness initializes the exact right rooted-pair invariant at a strict
right cut. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightPairRootedAt_cut_of_ready
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
            A strategy hwin initialTag env (cuts.cuts k))) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightPairRootedAt
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
          A strategy hwin initialTag env (cuts.cuts k))
        initialTag env (cuts.cuts k) := by
  change
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
          A strategy hwin initialTag env (cuts.cuts k))
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.2
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt_cut_eq_restartRelay
      A strategy hwin initialTag env cuts k hgraph]
  exact hready.restartPair A strategy hwin false false

/-- Left cut mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftPairRootedAt_cut_of_ready
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
            A strategy hwin initialTag env (cuts.cuts k))) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftPairRootedAt
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
          A strategy hwin initialTag env (cuts.cuts k))
        initialTag env (cuts.cuts k) := by
  change
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
          A strategy hwin initialTag env (cuts.cuts k))
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.2
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt_cut_eq_restartRelay
      A strategy hwin initialTag env cuts k hgraph]
  exact hready.restartPair A strategy hwin false false

/-! ## Exact row-aware payloads at strict closes -/

/-- A rooted right receiver exposes the exact strict child selected by its
local pre-round receive bit. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightReceiverPayload
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (root : BankControl A strategy hwin) (n : Nat)
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightPairRootedAt
        A strategy hwin root initialTag env n)
    (hgraph : (env n).graph = .right) :
    ∃ semanticPast : List (In₂ × In₁), ∃ semanticInput : In₂ × In₁,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
          A strategy hwin initialTag env (n + 1) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin root
            (.strict
              (profiledRawJointUnitRightActualDirection
                (In₁ := In₁) (In₂ := In₂)
                (if
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwoAt
                    A strategy hwin initialTag env n).2.1
                then .both else .first)
                semanticPast semanticInput)) := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 pair.1
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 pair.2
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
      A strategy hwin selectedOne selectedTwo
  have hpair' :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
        A strategy hwin root base.1.1 base.1.2 := by
    exact hpair
  let row : PairedEntryRow := if selectedTwo.2.1 then .both else .first
  rcases hpair'.payload_exists A strategy hwin
      ((env n).inputTwo, (env n).inputOne) row with
    ⟨semanticPast, semanticInput, hpayload⟩
  refine ⟨semanticPast, semanticInput, ?_⟩
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt_succ_of_right
      A strategy hwin initialTag env n hgraph]
  change
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedTwo
      A strategy hwin fallback pair.2 (env n).inputTwo pair.1
        (env n).inputOne).child A strategy hwin = _
  simpa only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwoAt,
    selectedTwo, selectedOne, base, row] using hpayload

/-- Left receiver mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftReceiverPayload
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (root : BankControl A strategy hwin) (n : Nat)
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftPairRootedAt
        A strategy hwin root initialTag env n)
    (hgraph : (env n).graph = .left) :
    ∃ semanticPast : List (In₁ × In₂), ∃ semanticInput : In₁ × In₂,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
          A strategy hwin initialTag env (n + 1) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin root
            (.strict
              (profiledRawJointUnitLeftActualDirection
                (In₁ := In₁) (In₂ := In₂)
                (if
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOneAt
                    A strategy hwin initialTag env n).2.1
                then .both else .first)
                semanticPast semanticInput)) := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 pair.1
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 pair.2
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
      A strategy hwin selectedOne selectedTwo
  have hpair' :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
        A strategy hwin root base.2.1 base.2.2 := by
    exact hpair
  let row : PairedEntryRow := if selectedOne.2.1 then .both else .first
  rcases hpair'.payload_exists A strategy hwin
      ((env n).inputOne, (env n).inputTwo) row with
    ⟨semanticPast, semanticInput, hpayload⟩
  refine ⟨semanticPast, semanticInput, ?_⟩
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt_succ_of_left
      A strategy hwin initialTag env n hgraph]
  change
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedOne
      A strategy hwin fallback pair.1 (env n).inputOne pair.2
        (env n).inputTwo).child A strategy hwin = _
  simpa only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOneAt,
    selectedTwo, selectedOne, base, row] using hpayload

/-! ## Cross-cut readiness with the actual closing row -/

/-- A complete strict-right block replaces its live right root by the exact
live left child selected by the receiver's actual closing row. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightCut_nextReady
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
            A strategy hwin initialTag env (cuts.cuts k))) :
    (env (cuts.cuts (k + 1))).graph = .left ∧
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
            A strategy hwin initialTag env (cuts.cuts (k + 1))) := by
  let root :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
      A strategy hwin initialTag env (cuts.cuts k)
  let closing := cuts.cuts k + cuts.openLength k
  have hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightPairRootedAt
        A strategy hwin root initialTag env (cuts.cuts k) := by
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightPairRootedAt_cut_of_ready
        A strategy hwin initialTag env cuts k hgraph hready
  have hclosingPair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightPairRootedAt
        A strategy hwin root initialTag env closing := by
    exact hpair.propagate_open A strategy hwin cuts k hgraph
  have hclosingGraph : (env closing).graph = .right := by
    have hclosing := cuts.closing_graph_eq k
    have hindex : cuts.cuts (k + 1) - 1 = closing := by
      rw [cuts.step_eq]
      omega
    rw [hindex] at hclosing
    exact hclosing.trans hgraph
  rcases
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightReceiverPayload
        A strategy hwin initialTag env root closing hclosingPair hclosingGraph
    with ⟨semanticPast, semanticInput, hpayload⟩
  let row : PairedEntryRow :=
    if
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwoAt
        A strategy hwin initialTag env closing).2.1
    then .both else .first
  let child :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
      hwin root
        (.strict
          (profiledRawJointUnitRightActualDirection
            (In₁ := In₁) (In₂ := In₂) row semanticPast semanticInput))
  have hnextRoot :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
          A strategy hwin initialTag env (cuts.cuts (k + 1)) = child := by
    rw [cuts.step_eq]
    exact hpayload
  have hchildReady :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin child := by
    exact hready.strictRightChild A strategy hwin row semanticPast semanticInput
  have hnextGraph : (env (cuts.cuts (k + 1))).graph = .left := by
    have hne := cuts.maximal_of_strict k (hnoBoth (cuts.cuts k))
    cases hnext : (env (cuts.cuts (k + 1))).graph with
    | right => exact False.elim (hne (hnext.trans hgraph.symm))
    | left => rfl
    | both => exact False.elim (hnoBoth _ hnext)
  exact ⟨hnextGraph, hnextRoot ▸ hchildReady⟩

/-- Strict-left mirror of the row-aware cross-cut readiness step. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftCut_nextReady
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
            A strategy hwin initialTag env (cuts.cuts k))) :
    (env (cuts.cuts (k + 1))).graph = .right ∧
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
            A strategy hwin initialTag env (cuts.cuts (k + 1))) := by
  let root :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
      A strategy hwin initialTag env (cuts.cuts k)
  let closing := cuts.cuts k + cuts.openLength k
  have hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftPairRootedAt
        A strategy hwin root initialTag env (cuts.cuts k) := by
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftPairRootedAt_cut_of_ready
        A strategy hwin initialTag env cuts k hgraph hready
  have hclosingPair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftPairRootedAt
        A strategy hwin root initialTag env closing := by
    exact hpair.propagate_open A strategy hwin cuts k hgraph
  have hclosingGraph : (env closing).graph = .left := by
    have hclosing := cuts.closing_graph_eq k
    have hindex : cuts.cuts (k + 1) - 1 = closing := by
      rw [cuts.step_eq]
      omega
    rw [hindex] at hclosing
    exact hclosing.trans hgraph
  rcases
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftReceiverPayload
        A strategy hwin initialTag env root closing hclosingPair hclosingGraph
    with ⟨semanticPast, semanticInput, hpayload⟩
  let row : PairedEntryRow :=
    if
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOneAt
        A strategy hwin initialTag env closing).2.1
    then .both else .first
  let child :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
      hwin root
        (.strict
          (profiledRawJointUnitLeftActualDirection
            (In₁ := In₁) (In₂ := In₂) row semanticPast semanticInput))
  have hnextRoot :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
          A strategy hwin initialTag env (cuts.cuts (k + 1)) = child := by
    rw [cuts.step_eq]
    exact hpayload
  have hchildReady :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin child := by
    exact hready.strictLeftChild A strategy hwin row semanticPast semanticInput
  have hnextGraph : (env (cuts.cuts (k + 1))).graph = .right := by
    have hne := cuts.maximal_of_strict k (hnoBoth (cuts.cuts k))
    cases hnext : (env (cuts.cuts (k + 1))).graph with
    | right => rfl
    | left => exact False.elim (hne (hnext.trans hgraph.symm))
    | both => exact False.elim (hnoBoth _ hnext)
  exact ⟨hnextGraph, hnextRoot ▸ hchildReady⟩

/-! ## Controller-parametric cut closure -/

/-- The only proof-side assumption still needed at strict cut entries: the
authoritative parent has the live lane selected by that strict side.  A
simultaneous cut needs no one-sided readiness package. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowCutReady
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph)) : Prop :=
  ∀ k : Nat,
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
        A strategy hwin initialTag env (cuts.cuts k)
    match (env (cuts.cuts k)).graph with
    | .right =>
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
          A strategy hwin root
    | .left =>
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
          A strategy hwin root
    | .both => True

/-- On a strict-only tail, the first live root supplied by the front handoff
propagates through all row-aware operational cuts. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_cutReady_of_noBoth
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hfirst :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
        A strategy hwin initialTag env) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowCutReady
      A strategy hwin initialTag env cuts := by
  rw [
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowCutReady]
  intro k
  induction k with
  | zero =>
      have hcut0 : cuts.cuts 0 = 0 := cuts.cuts_zero
      cases hgraph : (env 0).graph with
      | right =>
          have hready :
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
                A strategy hwin initialTag.1 := by
            simpa [
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady,
              hgraph] using hfirst
          simpa [hcut0, hgraph] using hready
      | left =>
          have hready :
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
                A strategy hwin initialTag.1 := by
            simpa [
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady,
              hgraph] using hfirst
          simpa [hcut0, hgraph] using hready
      | both => exact False.elim (hnoBoth 0 hgraph)
  | succ k ih =>
      cases hgraph : (env (cuts.cuts k)).graph with
      | right =>
          have hcurrent :
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
                A strategy hwin
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
                    A strategy hwin initialTag env (cuts.cuts k)) := by
            simpa [hgraph] using ih
          rcases
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightCut_nextReady
                A strategy hwin initialTag env cuts hnoBoth k hgraph hcurrent
            with ⟨hnextGraph, hnextReady⟩
          simpa [hnextGraph] using hnextReady
      | left =>
          have hcurrent :
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
                A strategy hwin
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
                    A strategy hwin initialTag env (cuts.cuts k)) := by
            simpa [hgraph] using ih
          rcases
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftCut_nextReady
                A strategy hwin initialTag env cuts hnoBoth k hgraph hcurrent
            with ⟨hnextGraph, hnextReady⟩
          simpa [hnextGraph] using hnextReady
      | both => exact False.elim (hnoBoth (cuts.cuts k) hgraph)

/-- Under the sharp cut-readiness invariant, the row-aware controller
satisfies the complete generic semantic-close interface. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOperationalSemanticCloseLaws
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowCutReady
        A strategy hwin initialTag env cuts) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseLaws
      A strategy hwin env cuts
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
          A strategy hwin initialTag env) where
  rightRooted := fun root n ↦
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightPairRootedAt
      A strategy hwin root initialTag env n
  leftRooted := fun root n ↦
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftPairRootedAt
      A strategy hwin root initialTag env n
  phaseBits :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivePhaseBits
      A strategy hwin initialTag env
  rightAtCut := by
    intro k hgraph
    have hk := hready k
    simp only [hgraph] at hk
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightPairRootedAt_cut_of_ready
        A strategy hwin initialTag env cuts k hgraph hk
  leftAtCut := by
    intro k hgraph
    have hk := hready k
    simp only [hgraph] at hk
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftPairRootedAt_cut_of_ready
        A strategy hwin initialTag env cuts k hgraph hk
  rightSameRoot := by
    intro root n hpair hgraph
    exact hpair.step A strategy hwin hgraph
  leftSameRoot := by
    intro root n hpair hgraph
    exact hpair.step A strategy hwin hgraph
  rightReceiverPayload := by
    intro root n hpair hgraph
    simpa only [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivePhaseBits]
      using
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightReceiverPayload
          A strategy hwin initialTag env root n hpair hgraph)
  leftReceiverPayload := by
    intro root n hpair hgraph
    simpa only [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivePhaseBits]
      using
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftReceiverPayload
          A strategy hwin initialTag env root n hpair hgraph)
  bothPayload := by
    intro n hgraph
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt_succ_of_both
        A strategy hwin initialTag env n hgraph

/-- Consequently, cut readiness is sufficient for the exact semantic bank
recurrence at every operational close, including `.both` rows. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_operationalSemanticCloseWitness
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowCutReady
        A strategy hwin initialTag env cuts) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness
      A strategy hwin env cuts
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
          A strategy hwin initialTag env) := by
  exact
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOperationalSemanticCloseLaws
      A strategy hwin initialTag env cuts hready).toOperationalSemanticCloseWitness

/-- The front handoff and absence of later simultaneous graphs discharge the
readiness premise, yielding the exact dynamic-row close recurrence directly. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_operationalSemanticCloseWitness_of_noBoth
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hfirst :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
        A strategy hwin initialTag env) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness
      A strategy hwin env cuts
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
          A strategy hwin initialTag env) := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_operationalSemanticCloseWitness
      A strategy hwin initialTag env cuts
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_cutReady_of_noBoth
          A strategy hwin initialTag env cuts hnoBoth hfirst)

end

end DetParityAutomaton

end DistributedSynthesis
