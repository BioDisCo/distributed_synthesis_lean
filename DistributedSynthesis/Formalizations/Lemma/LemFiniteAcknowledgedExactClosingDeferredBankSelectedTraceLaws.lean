/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredFamily
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingBankSelectedTraceLaws

/-!
# Selected traces for a bank of deferred exact-closing fibres

The concrete literal construction is presented as a dependent family of
pending/recurrent fibres.  Its semantic invariant, however, is proved inside
one selected fibre.  This file composes the two generic adapters in one arrow:
the deferred presentation supplies all exact-close and arbitrary blind-depth
laws, and the fibrewise selected trace supplies the model-specific graph-step
equations.

No new mathematical premise is introduced.  In particular, the executable
controller receives no graph, orientation, hierarchy side, leader bit,
strict-leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y k a b c d e f

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace FiniteDeferredExactClosingFamily

variable {Key : Type k}
variable
  (family : FiniteDeferredExactClosingFamily.{u, v, x, y, k, a, b, c, d, e, f}
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      Key)

noncomputable section

private abbrev OneControl (key : Key) :=
  DeferredOrRecurrent (family.SharedOne key) (family.PayloadOne key)
    (family.RecurrentOne key)

private abbrev TwoControl (key : Key) :=
  DeferredOrRecurrent (family.SharedTwo key) (family.PayloadTwo key)
    (family.RecurrentTwo key)

/-- A selected trace in one deferred fibre yields the complete acknowledged
bank Mealy trace invariant. -/
noncomputable def bankMealyTraceInvariant_of_fibre
    [Fintype Key]
    (key : Key)
    (Selected : OneControl family key → TwoControl family key → Nat → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (expectedOutputOne : Nat → Out₁)
    (expectedOutputTwo : Nat → Out₂)
    (fibreLaws : ExactClosingSelectedTraceLaws
      (family.initialOne key) (family.initialTwo key)
      (deferredOrRecurrentNoRecv (family.pendingStepOne key)
        (family.recurrentStepOne key))
      (deferredOrRecurrentNoRecv (family.pendingStepTwo key)
        (family.recurrentStepTwo key))
      (family.openRecvOne key) (family.openRecvTwo key) (family.close key)
      (family.Rel key) Selected env expectedOutputOne expectedOutputTwo) :
    (family.toExactClosingBlindFamily.base.bankPairedMealyController key
      ).LiteralCrossMealyTraceInvariant env :=
  family.toExactClosingBlindFamily.bankMealyTraceInvariant_of_fibre key
    Selected env expectedOutputOne expectedOutputTwo fibreLaws

/-- Moore-facing form of `bankMealyTraceInvariant_of_fibre`, ready for the
canonical literal-cross extraction endpoint. -/
noncomputable def bankMooreTraceInvariant_of_fibre
    [Fintype Key] [Fintype Out₁] [Fintype Out₂]
    [Inhabited Out₁] [Inhabited Out₂]
    (key : Key)
    (Selected : OneControl family key → TwoControl family key → Nat → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (expectedOutputOne : Nat → Out₁)
    (expectedOutputTwo : Nat → Out₂)
    (fibreLaws : ExactClosingSelectedTraceLaws
      (family.initialOne key) (family.initialTwo key)
      (deferredOrRecurrentNoRecv (family.pendingStepOne key)
        (family.recurrentStepOne key))
      (deferredOrRecurrentNoRecv (family.pendingStepTwo key)
        (family.recurrentStepTwo key))
      (family.openRecvOne key) (family.openRecvTwo key) (family.close key)
      (family.Rel key) Selected env expectedOutputOne expectedOutputTwo) :
    ((family.toExactClosingBlindFamily.base.bankPairedMealyController key
      ).mooreize).LiteralCrossGraphTraceInvariant env :=
  (family.bankMealyTraceInvariant_of_fibre key Selected env expectedOutputOne
    expectedOutputTwo fibreLaws).toMooreTraceInvariant _

end

end FiniteDeferredExactClosingFamily

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
