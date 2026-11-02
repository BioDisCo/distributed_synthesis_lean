/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmDynamicHierarchyFiniteState
import DistributedSynthesis.Formalizations.Theorem.ThmSummaryEpochCertificate

/-!
# Compiling finite controller memory into local summaries

The dynamic-hierarchy synthesis theorem produces finite Moore controllers.
It does not produce memoryless functions on the original observations.  This
file supplies the missing, elementary compilation step: product each local
summary automaton with the corresponding Moore memory.  The controller output
then becomes a memoryless table on the enriched summary.
-/

namespace DistributedSynthesis

universe u

namespace MooreController

variable {In₁ In₂ Out : Type u}
  {M : LocalSummaryAutomaton.{u, u, u} In₁ In₂}
  {d : Proc}
  (C : MooreController.{u, u, u} (M.Summary d) Out)

/-- Controller memory obtained while recursively reading a concrete local
view through `M`. -/
def runOnView : View In₁ In₂ d -> C.Memory
  | .empty _ => C.initial
  | .noRecv previous input =>
      let summary := M.stepNoRecv d (M.read previous) input
      C.update (runOnView previous) summary
  | .recv previous input previousOther inputOther =>
      let summary :=
        M.stepRecv d (M.read previous) input (M.read previousOther) inputOther
      C.update (runOnView previous) summary

@[simp]
theorem runOnView_empty :
    C.runOnView (View.empty d : View In₁ In₂ d) = C.initial := rfl

@[simp]
theorem runOnView_noRecv (previous : View In₁ In₂ d)
    (input : PSum In₁ In₂) :
    C.runOnView (.noRecv previous input) =
      C.update (C.runOnView previous)
        (M.stepNoRecv d (M.read previous) input) := rfl

@[simp]
theorem runOnView_recv (previous : View In₁ In₂ d)
    (input : PSum In₁ In₂) (previousOther : View In₁ In₂ d.other)
    (inputOther : PSum In₁ In₂) :
    C.runOnView (.recv previous input previousOther inputOther) =
      C.update (C.runOnView previous)
        (M.stepRecv d (M.read previous) input (M.read previousOther) inputOther) := rfl

end MooreController

namespace LocalSummaryAutomaton

variable {In₁ In₂ Out₁ Out₂ : Type u}
  (M : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
  (C₁ : MooreController.{u, u, u} (M.Summary Proc.one) Out₁)
  (C₂ : MooreController.{u, u, u} (M.Summary Proc.two) Out₂)

/-- Product of a local summary automaton with two private Moore memories. -/
def withMooreControllers : LocalSummaryAutomaton.{u, u, u} In₁ In₂ where
  Summary
    | .one => M.Summary Proc.one × C₁.Memory
    | .two => M.Summary Proc.two × C₂.Memory
  finite
    | .one => inferInstance
    | .two => inferInstance
  initial
    | .one => (M.initial Proc.one, C₁.initial)
    | .two => (M.initial Proc.two, C₂.initial)
  stepNoRecv
    | .one, previous, input =>
        let summary := M.stepNoRecv Proc.one previous.1 input
        (summary, C₁.update previous.2 summary)
    | .two, previous, input =>
        let summary := M.stepNoRecv Proc.two previous.1 input
        (summary, C₂.update previous.2 summary)
  stepRecv
    | .one, previous, input, previousOther, inputOther =>
        let summary :=
          M.stepRecv Proc.one previous.1 input previousOther.1 inputOther
        (summary, C₁.update previous.2 summary)
    | .two, previous, input, previousOther, inputOther =>
        let summary :=
          M.stepRecv Proc.two previous.1 input previousOther.1 inputOther
        (summary, C₂.update previous.2 summary)

/-- Expected enriched summary for a view of either process. -/
def withMooreControllersExpected :
    (d : Proc) -> View In₁ In₂ d ->
      (M.withMooreControllers C₁ C₂).Summary d
  | .one, view => (M.read view, C₁.runOnView view)
  | .two, view => (M.read view, C₂.runOnView view)

/-- Reading any view through the product automaton computes the base summary
and the corresponding process's Moore memory. -/
theorem withMooreControllers_read (d : Proc) (view : View In₁ In₂ d) :
    (M.withMooreControllers C₁ C₂).read view =
      M.withMooreControllersExpected C₁ C₂ d view := by
  induction view with
  | empty p =>
      cases p <;> rfl
  | @noRecv p previous input ih =>
      simp only [LocalSummaryAutomaton.read,
        MooreController.runOnView_noRecv]
      rw [ih]
      cases p <;> rfl
  | @recv p previous input previousOther inputOther ih ihOther =>
      simp only [LocalSummaryAutomaton.read,
        MooreController.runOnView_recv]
      rw [ih, ihOther]
      cases p <;> rfl

/-- Process-1 specialization of `withMooreControllers_read`. -/
@[simp] theorem withMooreControllers_read_one
    (view : View In₁ In₂ Proc.one) :
    (M.withMooreControllers C₁ C₂).read view =
      (M.read view, C₁.runOnView view) := by
  simpa [withMooreControllersExpected] using
    M.withMooreControllers_read C₁ C₂ Proc.one view

/-- Process-2 specialization of `withMooreControllers_read`. -/
@[simp] theorem withMooreControllers_read_two
    (view : View In₁ In₂ Proc.two) :
    (M.withMooreControllers C₁ C₂).read view =
      (M.read view, C₂.runOnView view) := by
  simpa [withMooreControllersExpected] using
    M.withMooreControllers_read C₁ C₂ Proc.two view

/-- The strategy that runs the two finite controllers directly on local
views. -/
def mooreReadbackStrategy : StrategyPair In₁ In₂ Out₁ Out₂ where
  one := fun view => C₁.output (C₁.runOnView view)
  two := fun view => C₂.output (C₂.runOnView view)

/-- Memoryless output table for process 1 on the enriched summary. -/
def mooreOutputOne :
    (M.withMooreControllers C₁ C₂).Summary Proc.one -> Out₁ :=
  fun summary => C₁.output summary.2

/-- Memoryless output table for process 2 on the enriched summary. -/
def mooreOutputTwo :
    (M.withMooreControllers C₁ C₂).Summary Proc.two -> Out₂ :=
  fun summary => C₂.output summary.2

/-- Compiling the controller memories into the summary does not change the
induced distributed strategy. -/
theorem readbackStrategy_withMooreControllers :
    (M.withMooreControllers C₁ C₂).readbackStrategy
        (M.mooreOutputOne C₁ C₂) (M.mooreOutputTwo C₁ C₂) =
      M.mooreReadbackStrategy C₁ C₂ := by
  apply congrArg₂ StrategyPair.mk
  · funext view
    simp [LocalSummaryAutomaton.readbackStrategy, mooreOutputOne,
      mooreReadbackStrategy, withMooreControllers_read_one]
  · funext view
    simp [LocalSummaryAutomaton.readbackStrategy, mooreOutputTwo,
      mooreReadbackStrategy, withMooreControllers_read_two]

/-- A fixed winning pair of finite controllers yields the readback upgrade
for the summary automaton enriched with their memories.  The supplied winning
strategy in the premise of `ReadbackUpgrade` is irrelevant: once realizability
holds, the finite-state extraction has already selected one winning pair. -/
theorem readbackUpgrade_withMooreControllers
    (A : DetParityAutomaton.{u, u}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hwins : ∀ environment : EnvironmentSequence In₁ In₂,
      A.Accepts (execution (M.mooreReadbackStrategy C₁ C₂) environment)) :
    (M.withMooreControllers C₁ C₂).ReadbackUpgrade A := by
  intro _strategy _hstrategy
  refine ⟨M.mooreOutputOne C₁ C₂, M.mooreOutputTwo C₁ C₂, ?_⟩
  intro environment
  rw [M.readbackStrategy_withMooreControllers C₁ C₂]
  exact hwins environment

/-- Finite-state completeness relative to a base summary: whenever the
objective is realizable, some pair of Moore controllers reading the successive
base summaries realizes it.  Unlike `ReadbackUpgrade`, the controller memory
types are allowed to be selected by the extraction theorem. -/
def FiniteStateReadbackComplete
    (A : DetParityAutomaton.{u, u}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)) : Prop :=
  ∀ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ environment : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy environment)) ->
      ∃ (C₁ : MooreController.{u, u, u} (M.Summary Proc.one) Out₁)
        (C₂ : MooreController.{u, u, u} (M.Summary Proc.two) Out₂),
        ∀ environment : EnvironmentSequence In₁ In₂,
          A.Accepts (execution (M.mooreReadbackStrategy C₁ C₂) environment)

/-- The correct quantifier bridge.  Finite-state completeness yields *some*
finite local summary automaton with `ReadbackUpgrade`: in the realizable case,
select one extracted controller pair and product its memories with `M`; in the
unrealizable case, the upgrade premise is vacuous. -/
theorem exists_readbackUpgrade_of_finiteStateReadbackComplete
    (A : DetParityAutomaton.{u, u}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hcomplete : M.FiniteStateReadbackComplete A) :
    ∃ M' : LocalSummaryAutomaton.{u, u, u} In₁ In₂,
      M'.ReadbackUpgrade A := by
  classical
  let P : Prop :=
      ∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ environment : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy environment)
  letI : Decidable P := Classical.propDecidable P
  by_cases hrealizable : P
  · obtain ⟨strategy, hstrategy⟩ := hrealizable
    obtain ⟨C₁, C₂, hcontrollers⟩ := hcomplete strategy hstrategy
    exact
      ⟨M.withMooreControllers C₁ C₂,
        M.readbackUpgrade_withMooreControllers C₁ C₂ A hcontrollers⟩
  · refine ⟨M, ?_⟩
    intro strategy hstrategy
    exact False.elim (hrealizable ⟨strategy, hstrategy⟩)

end LocalSummaryAutomaton

end DistributedSynthesis
