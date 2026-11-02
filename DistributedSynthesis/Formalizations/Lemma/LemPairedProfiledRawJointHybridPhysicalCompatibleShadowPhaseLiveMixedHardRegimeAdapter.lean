/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailHardRegimeAdapter

/-!
# Direct recurrent acceptance with a tagged reversal stream

Recurrent `.both` executions need not remain in one delayed-tag fibre.  For
example, on `right, both, right, both, ...`, every `.both` round may close the
current strict occurrence and the next strict round creates a new tag.  It is
therefore unnecessarily strong, and generally the wrong operational shape,
to demand one fixed tag-indexed root-aligned stream in the recurrent branch.

The repository already has tag-free recurrent acceptance interfaces based on
common-tail automatic slices and canonical literal-cross epoch couplings.
This module gives them the smallest adapter into the final physical-acceptance
split: recurrent `.both` supplies acceptance of the actual controller word
directly, while persistent strict reversal still supplies the fixed tagged
operational-cut stream.  Eventually fixed strict tails keep the existing
output-only bookkeeping.

The recurrent field remains a genuine concrete obligation: a caller must
still prove that the *actual fixed controller trace* has the common-tail
automatic slices or canonical literal-cross alignment used to obtain its
acceptance.  This adapter removes only the unsound demand that those recurrent
cuts inhabit one fixed delayed-tag fibre; it supplies no trace equality by
itself.

This is proof-side regime assembly.  It changes no executable controller and
does not expose a graph, orientation, leader bit, history, or tag to a local
transition.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev PhysicalController :=
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂

/-- Honest mixed hard-regime boundary.  The recurrent branch may be supplied
by the common-tail/canonical-literal-cross machinery and owes no persistent
tag, but its acceptance statement is still about this controller's actual
trace.  Only the reversal branch is based in one delayed tail fibre. -/
structure
    ProfiledRawJointHybridShadowPhaseLiveMixedHardRegimeBookkeeping
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) : Prop where
  recurrent :
    GraphBothRecurrent (fun n ↦ (env n).graph) →
      A.Accepts
        (controller.globalMachine.globalMachineTraceWord
          controller.globalOutputOne controller.globalOutputTwo env)
  reversal :
    ∀ hreversal : PersistentStrictReversalTail (fun n ↦ (env n).graph),
      Nonempty
        (ProfiledRawJointHybridShadowPhaseLiveOperationalCutStreamWitness A
          strategy hwin controller env
            (operationalCloseCutPackageOfPersistentStrictReversalTail
              (fun n ↦ (env n).graph) hreversal))
  fixed : EventuallyInstalledOutputTailBookkeeping A controller env

namespace
  ProfiledRawJointHybridShadowPhaseLiveMixedHardRegimeBookkeeping

/-- The mixed boundary is already sufficient for the repository's exhaustive
four-regime physical-acceptance interface. -/
noncomputable def physicalAcceptance
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridShadowPhaseLiveMixedHardRegimeBookkeeping A
        strategy hwin controller env) :
    A.FiniteGlobalMachinePhysicalAcceptance controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo env := by
  let fixed := bookkeeping.fixed.toEventuallyInstalledFixedTailBookkeeping A
  exact {
    recurrent := fun hboth ↦ by
      let direct := A.finiteGlobalMachinePhysicalAcceptance_of_accepts
        controller.globalMachine controller.globalOutputOne
          controller.globalOutputTwo env (bookkeeping.recurrent hboth)
      exact direct.recurrent hboth
    alternatingTail := fun hreversal ↦ by
      let witness := Classical.choice (bookkeeping.reversal hreversal)
      let bundle := witness.publicHardCertificateBundle A strategy hwin
      let certificate := bundle.2.2.2
      let direct := A.finiteGlobalMachinePhysicalAcceptance_of_accepts
        controller.globalMachine controller.globalOutputOne
          controller.globalOutputTwo env
            (certificate.accepts A strategy hwin)
      exact direct.alternatingTail hreversal
    strictRightTail := fixed.rightTailParity A
    strictLeftTail := fixed.leftTailParity A }

/-- The older all-tagged hard-regime boundary implies the mixed one.  This
also proves that the new interface is a weakening only in the recurrent
branch, not a different acceptance argument. -/
noncomputable def ofOperationalHardRegimeBookkeeping
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridShadowPhaseLiveOperationalHardRegimeBookkeeping A
        strategy hwin controller env) :
    ProfiledRawJointHybridShadowPhaseLiveMixedHardRegimeBookkeeping A strategy
      hwin controller env where
  recurrent hboth := by
    let witness := Classical.choice (bookkeeping.recurrent hboth)
    let bundle := witness.publicHardCertificateBundle A strategy hwin
    exact bundle.2.2.2.accepts A strategy hwin
  reversal := bookkeeping.reversal
  fixed := bookkeeping.fixed

end
  ProfiledRawJointHybridShadowPhaseLiveMixedHardRegimeBookkeeping

end

end DetParityAutomaton

end DistributedSynthesis
