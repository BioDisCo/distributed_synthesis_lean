/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledExactViewTree
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefLocalPresentationReadback

/-!
# Direct Bérard rational-tree readback

This file isolates a route to `ReadbackUpgrade` which does not use the
root-pinned or raw-joint controller stacks.  A transition-rational global
action tree is already a finite *central* Moore machine: after one environment
round its state stores the new tree control and the output pair selected at
the old control.  If that finite machine has an honest graph-blind local
presentation, the existing finite-belief construction turns it directly into
a local-summary readback.

The missing mathematical assertion on this route is therefore not ordinary
input-free rationality.  It is `BerardLocallyPresentableRationalTreeExtraction`:
the rational tree must be selectable together with a local presentation.
This is exactly where a shared blind lambda has to survive hierarchy switches.
Neither the finite machine nor its local presentation gives a process a graph,
orientation, active-side, or strict-leader signal.
-/

namespace DistributedSynthesis

universe u v x y s c a b o

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Fintype In₁] [Fintype In₂]
variable [Fintype Out₁] [Fintype Out₂]
variable [Inhabited Out₁] [Inhabited Out₂]

/-- A finite global action tree of the exact-view presentation. -/
abbrev BerardGlobalActionTree :=
  TransitionRationalTree.{max u v, max u v x y, c}
    (EnvironmentRound In₁ In₂)
    (ExactViewGlobalActionTable
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))

namespace BerardGlobalActionTree

variable (tree : BerardGlobalActionTree
  (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))

/--
The finite centralized round machine induced by a rational action tree.

The first coordinate is the control for the next tree node.  The other two
coordinates remember the outputs emitted by the just-consumed round, matching
the post-update timing of `FiniteGlobalRoundMachine.globalMachineTraceWord`.
-/
def roundMachine :
    FiniteGlobalRoundMachine.{u, v, max c x y} In₁ In₂ where
  State :=
    ULift.{max c x y, c} tree.Control ×
      ULift.{max c x y, x} Out₁ × ULift.{max c x y, y} Out₂
  stateFinite := inferInstance
  initial := (ULift.up tree.initial, ULift.up default, ULift.up default)
  step state env :=
    (ULift.up (tree.step state.1.down env),
      ULift.up (tree.labelOf state.1.down env).1,
      ULift.up (tree.labelOf state.1.down env).2)

/-- Process-one Moore output of the centralized tree machine. -/
def outputOne : tree.roundMachine.State → Out₁ :=
  fun state => state.2.1.down

/-- Process-two Moore output of the centralized tree machine. -/
def outputTwo : tree.roundMachine.State → Out₂ :=
  fun state => state.2.2.down

section
omit [Fintype In₁] [Fintype In₂]

/-- The tree-control coordinate after `n` rounds is the control at the
corresponding environment-tree node. -/
theorem globalStateTrace_fst (env : EnvironmentSequence In₁ In₂) : ∀ n,
    (tree.roundMachine.globalStateTrace env n).1.down =
      tree.controlAt (branchNode env n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      change tree.step (tree.roundMachine.globalStateTrace env n).1.down (env n) = _
      rw [ih]
      rw [show branchNode env (n + 1) = branchNode env n ++ [env n] from rfl]
      simp [TransitionRationalTree.controlAt, List.foldl_append]

/-- The output stored by the post-update machine state is exactly the action
table at the preceding tree node, applied to the current environment round. -/
theorem globalStateTrace_outputs (env : EnvironmentSequence In₁ In₂)
    (n : Nat) :
    (tree.outputOne (tree.roundMachine.globalStateTrace env (n + 1)),
      tree.outputTwo (tree.roundMachine.globalStateTrace env (n + 1))) =
      tree.labeledTree (branchNode env n) (env n) := by
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
  change
    ((tree.labelOf (tree.roundMachine.globalStateTrace env n).1.down (env n)).1,
      (tree.labelOf (tree.roundMachine.globalStateTrace env n).1.down (env n)).2) = _
  rw [tree.globalStateTrace_fst env n]
  rfl

/-- The explicit global-machine word is definitionally the word read along
the rational action tree. -/
theorem globalMachineTraceWord_eq_exactViewGlobalTreeWord
    (env : EnvironmentSequence In₁ In₂) :
    tree.roundMachine.globalMachineTraceWord tree.outputOne tree.outputTwo env =
      exactViewGlobalTreeWord tree.labeledTree env := by
  funext n
  have houtputs := tree.globalStateTrace_outputs env n
  have hone := congrArg Prod.fst houtputs
  have htwo := congrArg Prod.snd houtputs
  change tree.outputOne (tree.roundMachine.globalStateTrace env (n + 1)) =
    (tree.labeledTree (branchNode env n) (env n)).1 at hone
  change tree.outputTwo (tree.roundMachine.globalStateTrace env (n + 1)) =
    (tree.labeledTree (branchNode env n) (env n)).2 at htwo
  unfold FiniteGlobalRoundMachine.globalMachineTraceWord
    exactViewGlobalTreeWord exactViewGlobalTreeRound
  rw [hone, htwo]

/-- Universal winningness of the rational tree transfers to its finite
centralized machine without any strategy- or hierarchy-specific adapter. -/
theorem globalMachine_accepts
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hwins : ExactViewGlobalTreeWinning A tree.labeledTree) :
    ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts
        (tree.roundMachine.globalMachineTraceWord
          tree.outputOne tree.outputTwo env) := by
  intro env
  rw [tree.globalMachineTraceWord_eq_exactViewGlobalTreeWord env]
  exact hwins env

end

end BerardGlobalActionTree

/--
The exact extra extraction theorem needed by the direct Bérard route.

Ordinary input-free rationality supplies the finite `tree`; it does not supply
the final field.  That field asserts a graph-blind local presentation of the
centralized rational tree and is the direct-route form of lambda uniformity.
-/
def BerardLocallyPresentableRationalTreeExtraction
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)) : Prop :=
  ∀ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ environment : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy environment)) →
      ∃ tree : TransitionRationalTree.{max u v, max u v x y, c}
          (EnvironmentRound In₁ In₂)
          (ExactViewGlobalActionTable
            (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)),
        ExactViewGlobalTreeWinning A tree.labeledTree ∧
          Nonempty
            (FiniteGlobalRoundMachine.LocalPresentation.{u, v, max c x y,
              x, y, a, b}
              (BerardGlobalActionTree.roundMachine tree)
              (BerardGlobalActionTree.outputOne tree)
              (BerardGlobalActionTree.outputTwo tree))

/-- The locally presentable rational-tree extraction supplies exactly the
finite-global belief package consumed by readback. -/
theorem perStrategyWinningFiniteGlobalBeliefMachine_of_berardRationalTree
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (fallback : LocalSummaryAutomaton.{u, v, max c x y} In₁ In₂)
    (hextract : BerardLocallyPresentableRationalTreeExtraction.{u, v, x, y,
      s, c, a, b}
      A) :
    PerStrategyWinningFiniteGlobalBeliefMachine A fallback := by
  unfold BerardLocallyPresentableRationalTreeExtraction at hextract
  intro strategy hstrategy
  obtain ⟨tree, hwins, ⟨presentation⟩⟩ := hextract strategy hstrategy
  refine ⟨BerardGlobalActionTree.roundMachine tree,
    BerardGlobalActionTree.outputOne tree,
    BerardGlobalActionTree.outputTwo tree, ?_, ?_⟩
  · exact FiniteGlobalRoundMachine.LocalPresentation.reachableBeliefsUniform
      (BerardGlobalActionTree.roundMachine tree)
      (BerardGlobalActionTree.outputOne tree)
      (BerardGlobalActionTree.outputTwo tree) presentation
  · exact BerardGlobalActionTree.globalMachine_accepts tree A hwins

/-- Direct `ReadbackUpgrade` endpoint for the independent Bérard route. -/
theorem exists_readbackUpgrade_of_berardRationalTree
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (fallback : LocalSummaryAutomaton.{u, v, max c x y} In₁ In₂)
    (hextract : BerardLocallyPresentableRationalTreeExtraction.{u, v, x, y,
      s, c, a, b}
      A) :
    ∃ M : LocalSummaryAutomaton.{u, v, max c x y} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_finiteGlobalBeliefMachine A fallback
    (perStrategyWinningFiniteGlobalBeliefMachine_of_berardRationalTree
      A fallback hextract)

end DetParityAutomaton

end DistributedSynthesis
