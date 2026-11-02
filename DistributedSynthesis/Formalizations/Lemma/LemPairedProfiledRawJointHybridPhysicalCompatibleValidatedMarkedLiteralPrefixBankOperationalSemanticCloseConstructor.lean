/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankOperationalSemanticCutPath
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankOperationalPhaseBits

/-!
# Controller-parametric semantic closes

This module is the small adapter between a locally implemented linked
controller and the semantic bank path.  It assumes only three kinds of facts:

* a rooted receiver exposes an exact semantic child at its closing receive
  (and the simultaneous transition exposes its exact child);
* the same root is installed at a strict cut and is preserved by every
  same-side nonclosing round; and
* the endpoint-local receive bits satisfy their graph-case recurrence.

The operational-close clock supplies all block arithmetic.  In particular,
the adapter neither assumes literal physical-prefix fidelity of a narrowed
finite table nor gives either process a side or strict-leader oracle.
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

/-- The exact local obligations needed to turn a controller trace into a
semantic bank path at operational cuts.

`rightRooted root n` and `leftRooted root n` are proof-side predicates on the
pre-round controller state.  A concrete instance normally says that its
sender/receiver table pair is a linked pair at a prefix rooted at `root`.
They are not runtime tags. -/
structure
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseLaws
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (trace : Nat → BankControl A strategy hwin) where
  rightRooted : BankControl A strategy hwin → Nat → Prop
  leftRooted : BankControl A strategy hwin → Nat → Prop
  phaseBits : OperationalReceivePhaseBits (fun n ↦ (env n).graph)
  rightAtCut : ∀ k : Nat, (env (cuts.cuts k)).graph = .right →
    rightRooted (trace (cuts.cuts k)) (cuts.cuts k)
  leftAtCut : ∀ k : Nat, (env (cuts.cuts k)).graph = .left →
    leftRooted (trace (cuts.cuts k)) (cuts.cuts k)
  rightSameRoot : ∀ (root : BankControl A strategy hwin) (n : Nat),
    rightRooted root n → (env n).graph = .right →
      rightRooted root (n + 1)
  leftSameRoot : ∀ (root : BankControl A strategy hwin) (n : Nat),
    leftRooted root n → (env n).graph = .left →
      leftRooted root (n + 1)
  rightReceiverPayload :
    ∀ (root : BankControl A strategy hwin) (n : Nat),
      rightRooted root n → (env n).graph = .right →
        ∃ semanticPast : List (In₂ × In₁), ∃ semanticInput : In₂ × In₁,
          trace (n + 1) =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
              strategy hwin root
                (.strict
                  (profiledRawJointUnitRightActualDirection
                    (In₁ := In₁) (In₂ := In₂)
                    (if phaseBits.two n then .both else .first)
                    semanticPast semanticInput))
  leftReceiverPayload :
    ∀ (root : BankControl A strategy hwin) (n : Nat),
      leftRooted root n → (env n).graph = .left →
        ∃ semanticPast : List (In₁ × In₂), ∃ semanticInput : In₁ × In₂,
          trace (n + 1) =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
              strategy hwin root
                (.strict
                  (profiledRawJointUnitLeftActualDirection
                    (In₁ := In₁) (In₂ := In₂)
                    (if phaseBits.one n then .both else .first)
                    semanticPast semanticInput))
  bothPayload : ∀ n : Nat, (env n).graph = .both →
    trace (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin (trace n)
          (.simultaneous ((env n).inputOne, (env n).inputTwo))

namespace
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseLaws

variable {A strategy hwin}
variable {env : EnvironmentSequence In₁ In₂}
variable {cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph)}
variable {trace : Nat → BankControl A strategy hwin}

/-- The controller-parametric close constructor.  All finite-block induction,
closing-index arithmetic, and `.first`/`.both` row normalization are discharged
here once and for all. -/
theorem toOperationalSemanticCloseWitness
    (laws :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseLaws
        A strategy hwin env cuts trace) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness
      A strategy hwin env cuts trace := by
  rw [
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness]
  intro k
  cases hgraph : (env (cuts.cuts k)).graph with
  | right =>
      simp only
      let root := trace (cuts.cuts k)
      have hrooted :
          laws.rightRooted root (cuts.cuts k + cuts.openLength k) := by
        apply
          DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.propagate_homogeneous_open
            cuts
            (P := fun n ↦ laws.rightRooted root n) k
        · intro n hcurrent hsame
          exact laws.rightSameRoot root n hcurrent (hsame.trans hgraph)
        · exact laws.rightAtCut k hgraph
      have hclosingGraph :
          (env (cuts.cuts k + cuts.openLength k)).graph = .right := by
        have hclosing := cuts.closing_graph_eq k
        have hindex :
            cuts.cuts (k + 1) - 1 =
              cuts.cuts k + cuts.openLength k := by
          rw [cuts.step_eq]
          omega
        rw [hindex] at hclosing
        exact hclosing.trans hgraph
      rcases laws.rightReceiverPayload root
          (cuts.cuts k + cuts.openLength k) hrooted hclosingGraph with
        ⟨semanticPast, semanticInput, hpayload⟩
      refine ⟨semanticPast, semanticInput, ?_⟩
      have hrow :=
        OperationalReceivePhaseBits.right_closing_row_eq_bankOperationalRowAt
          cuts laws.phaseBits k hgraph
      have hnext :
          cuts.cuts (k + 1) =
            cuts.cuts k + cuts.openLength k + 1 := cuts.step_eq k
      rw [hnext]
      rw [← hrow]
      exact hpayload
  | left =>
      simp only
      let root := trace (cuts.cuts k)
      have hrooted :
          laws.leftRooted root (cuts.cuts k + cuts.openLength k) := by
        apply
          DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.propagate_homogeneous_open
            cuts
            (P := fun n ↦ laws.leftRooted root n) k
        · intro n hcurrent hsame
          exact laws.leftSameRoot root n hcurrent (hsame.trans hgraph)
        · exact laws.leftAtCut k hgraph
      have hclosingGraph :
          (env (cuts.cuts k + cuts.openLength k)).graph = .left := by
        have hclosing := cuts.closing_graph_eq k
        have hindex :
            cuts.cuts (k + 1) - 1 =
              cuts.cuts k + cuts.openLength k := by
          rw [cuts.step_eq]
          omega
        rw [hindex] at hclosing
        exact hclosing.trans hgraph
      rcases laws.leftReceiverPayload root
          (cuts.cuts k + cuts.openLength k) hrooted hclosingGraph with
        ⟨semanticPast, semanticInput, hpayload⟩
      refine ⟨semanticPast, semanticInput, ?_⟩
      have hrow :=
        OperationalReceivePhaseBits.left_closing_row_eq_bankOperationalRowAt
          cuts laws.phaseBits k hgraph
      have hnext :
          cuts.cuts (k + 1) =
            cuts.cuts k + cuts.openLength k + 1 := cuts.step_eq k
      rw [hnext]
      rw [← hrow]
      exact hpayload
  | both =>
      simp only
      have hzero := cuts.zero_open_of_both k hgraph
      have hnext : cuts.cuts (k + 1) = cuts.cuts k + 1 := by
        rw [cuts.step_eq, hzero]
      rw [hnext]
      exact laws.bothPayload (cuts.cuts k) hgraph

end ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseLaws

end

end DetParityAutomaton

end DistributedSynthesis
