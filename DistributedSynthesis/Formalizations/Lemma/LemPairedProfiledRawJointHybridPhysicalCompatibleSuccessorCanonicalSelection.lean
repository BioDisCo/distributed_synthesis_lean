/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorRootWholeTraceBridge
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorWholeTraceMain
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorInstalledOutputTail

/-!
# Canonical quantifier selection for the compatible-successor controller

The whole-trace endpoint permits an arbitrary initial common world and an
arbitrary compatible rational policy.  The concrete construction does not
need that freedom.  This file chooses the genuine round-zero world at the
default input pair and then chooses one compatible rational policy once for
that world and winning strategy.

After those two unconditional selections, the only remaining construction
hypothesis is
`PerStrategyWinningLiteralCompatibleSuccessorCanonicalControllerTraceBookkeeping`:
one finite physical controller, chosen before the environment, whose own word
has the hard-regime whole-trace witnesses and the two fixed-tail witnesses for
every environment.  The theorem below proves that this hypothesis is exactly
sufficient for the existing strategy-indexed whole-trace endpoint.  It does
not claim that the controller trace hypothesis has already been discharged.
-/

namespace DistributedSynthesis

universe u v x y s w

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

private abbrev CompatiblePolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

/-! ## Once-per-strategy canonical data -/

/-- The genuine empty-prefix common world, with the fixed default input pair.
It depends on the strategy but not on an environment. -/
def profiledRawJointHybridPhysicalCompatibleCanonicalInitial
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    ProfiledRawJointCommonBaseWorld A strategy :=
  profiledRawJointInitialCommonBaseWorld A strategy default default

/-- Choose one compatible rational policy for the canonical common world.
Existence is the unconditional rationalization theorem already proved for
every initial common world.  The choice is made before any environment is
quantified. -/
noncomputable def profiledRawJointHybridPhysicalCompatibleCanonicalPolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    CompatiblePolicy A strategy hwin
      (profiledRawJointHybridPhysicalCompatibleCanonicalInitial A strategy) :=
  Classical.choice
    (nonempty_profiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy
      hwin
      (profiledRawJointHybridPhysicalCompatibleCanonicalInitial A strategy))

/-! ## The exact remaining controller trace hypothesis -/

/-- The remaining positive construction, with all quantifiers in their final
order.

For each winning strategy, `controller` is selected once.  The canonical
initial world and canonical compatible policy above are already fixed.  Only
the proof-side hard-regime and fixed-tail witnesses may depend on `env`.
Every field concerns the physical word of this same controller.

This proposition is deliberately the named open hypothesis: the theorem
below consumes it but does not assume that a literature theorem provides it. -/
def
    PerStrategyWinningLiteralCompatibleSuccessorCanonicalControllerTraceBookkeeping :
    Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    ∃ controller :
        FinitePairedPhysicalController.{u, v, x, y, w, w}
          In₁ In₂ Out₁ Out₂,
      (∀ env : EnvironmentSequence In₁ In₂,
        ProfiledRawJointHybridPhysicalCompatibleHardRegimeWholeTraceBookkeeping
          A strategy hwin
            (profiledRawJointHybridPhysicalCompatibleCanonicalPolicy A strategy
              hwin)
            controller.globalMachine controller.globalOutputOne
              controller.globalOutputTwo env) ∧
      (∀ env : EnvironmentSequence In₁ In₂,
        EventuallyInstalledFixedTailBookkeeping A
          (controller.globalMachine.globalMachineTraceWord
            controller.globalOutputOne controller.globalOutputTwo env)
          (fun n ↦ (env n).graph))

/-- More concrete final target for the fixed-tail half.  The controller only
has to identify its two output coordinates with the installed table; the
environment supplies the input and eventual graph coordinates. -/
def
    PerStrategyWinningLiteralCompatibleSuccessorCanonicalControllerOutputTraceBookkeeping :
    Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    ∃ controller :
        FinitePairedPhysicalController.{u, v, x, y, w, w}
          In₁ In₂ Out₁ Out₂,
      (∀ env : EnvironmentSequence In₁ In₂,
        ProfiledRawJointHybridPhysicalCompatibleHardRegimeWholeTraceBookkeeping
          A strategy hwin
            (profiledRawJointHybridPhysicalCompatibleCanonicalPolicy A strategy
              hwin)
            controller.globalMachine controller.globalOutputOne
              controller.globalOutputTwo env) ∧
      (∀ env : EnvironmentSequence In₁ In₂,
        EventuallyInstalledOutputTailBookkeeping A controller env)

/-! ## Quantifier-order adapter -/

/-- Canonical controller trace bookkeeping supplies the existing whole-trace
endpoint.  In particular, this theorem proves that no environment-dependent
choice of initial world, rational policy, or controller is hidden in the
handoff. -/
theorem
    perStrategyWinningWholeTraceBookkeeping_of_canonicalControllerTrace
    (hcanonical :
      PerStrategyWinningLiteralCompatibleSuccessorCanonicalControllerTraceBookkeeping.{u,
        v, x, y, s, w} A) :
    PerStrategyWinningLiteralCompatibleSuccessorWholeTraceBookkeeping.{u, v,
      x, y, s, w} A := by
  intro strategy hwin
  let initial :=
    profiledRawJointHybridPhysicalCompatibleCanonicalInitial A strategy
  let policy :=
    profiledRawJointHybridPhysicalCompatibleCanonicalPolicy A strategy hwin
  obtain ⟨controller, hhard, hfixed⟩ := hcanonical strategy hwin
  refine ⟨initial, policy, controller, fun env ↦ ?_⟩
  exact {
    hard := hhard env
    fixed := hfixed env }

/-- Output-only fixed-tail bookkeeping supplies the canonical full-trace
hypothesis.  This is the form a local controller invariant should discharge. -/
theorem
    perStrategyWinningCanonicalControllerTrace_of_outputTrace
    (houtput :
      PerStrategyWinningLiteralCompatibleSuccessorCanonicalControllerOutputTraceBookkeeping.{u,
        v, x, y, s, w} A) :
    PerStrategyWinningLiteralCompatibleSuccessorCanonicalControllerTraceBookkeeping.{u,
      v, x, y, s, w} A := by
  intro strategy hwin
  obtain ⟨controller, hhard, hfixed⟩ := houtput strategy hwin
  refine ⟨controller, hhard, fun env ↦ ?_⟩
  exact
    (hfixed env).toEventuallyInstalledFixedTailBookkeeping A

/-- Consequently the output-level controller invariant already reaches the
whole-trace endpoint. -/
theorem
    perStrategyWinningWholeTraceBookkeeping_of_canonicalControllerOutputTrace
    (houtput :
      PerStrategyWinningLiteralCompatibleSuccessorCanonicalControllerOutputTraceBookkeeping.{u,
        v, x, y, s, w} A) :
    PerStrategyWinningLiteralCompatibleSuccessorWholeTraceBookkeeping.{u, v,
      x, y, s, w} A :=
  perStrategyWinningWholeTraceBookkeeping_of_canonicalControllerTrace A
    (perStrategyWinningCanonicalControllerTrace_of_outputTrace A houtput)

/-- The same canonical construction therefore supplies the already consumed
resolved-controller premise in one arrow. -/
theorem
    perStrategyWinningResolvedController_of_canonicalControllerTrace
    (hcanonical :
      PerStrategyWinningLiteralCompatibleSuccessorCanonicalControllerTraceBookkeeping.{u,
        v, x, y, s, w} A) :
    PerStrategyWinningLiteralCompatibleSuccessorResolvedControllerBookkeeping.{u,
      v, x, y, s, w} A :=
  perStrategyWinningResolvedController_of_wholeTraceBookkeeping A
    (perStrategyWinningWholeTraceBookkeeping_of_canonicalControllerTrace A
      hcanonical)

end

end DetParityAutomaton

end DistributedSynthesis
