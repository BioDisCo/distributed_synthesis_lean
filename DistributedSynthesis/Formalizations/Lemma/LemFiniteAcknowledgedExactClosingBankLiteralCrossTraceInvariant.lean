/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDependentBank
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingLiteralCrossTraceInvariant

/-!
# Literal-cross trace adapter for a dependent exact-closing bank

This is the short consumption surface for a concrete finite bank (including a
parallel product of the two seam orientations).  All relation and blind-fork
laws are inherited from `FiniteExactClosingBlindFamily`; the caller supplies
only the indexed selected-control trace laws.

The bank key is fixed construction data.  No executable transition receives a
graph, orientation, hierarchy side, leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y k c₁ c₂

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace FiniteExactClosingBlindFamily

variable {Key : Type k}
variable
  (family : FiniteExactClosingBlindFamily.{u, v, x, y, k, c₁, c₂}
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) Key)

noncomputable section

/-- The exact selected-control obligations left to one concrete bank trace.
All acknowledgement and arbitrary blind-depth laws are already present in
`family`. -/
abbrev BankSelectedTraceLaws
    (key : Key)
    (Selected :
      family.base.BankOneControl → family.base.BankTwoControl → Nat → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (expectedOutputOne : Nat → Out₁)
    (expectedOutputTwo : Nat → Out₂) :=
  ExactClosingSelectedTraceLaws
    (family.base.bankInitialOne key) (family.base.bankInitialTwo key)
    family.base.bankNoRecvOne family.base.bankNoRecvTwo
    family.base.bankOpenRecvOne family.base.bankOpenRecvTwo
    family.base.bankClose family.base.BankRel Selected env
    expectedOutputOne expectedOutputTwo

/-- A bank's selected-control trace laws lift directly to the repository's
Mealy literal-cross trace invariant. -/
noncomputable def bankMealyTraceInvariant
    [Fintype Key]
    (key : Key)
    (Selected :
      family.base.BankOneControl → family.base.BankTwoControl → Nat → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (expectedOutputOne : Nat → Out₁)
    (expectedOutputTwo : Nat → Out₂)
    (traceLaws : family.BankSelectedTraceLaws key Selected env
      expectedOutputOne expectedOutputTwo) :
    (family.base.bankPairedMealyController key).LiteralCrossMealyTraceInvariant
      env := by
  exact traceLaws.toMealyTraceInvariant
    (family.base.bankInitialOne key) (family.base.bankInitialTwo key)
    family.base.bankNoRecvOne family.base.bankNoRecvTwo
    family.base.bankOpenRecvOne family.base.bankOpenRecvTwo
    family.base.bankClose family.base.BankRel family.BankBlindOne
    family.BankBlindTwo Selected env expectedOutputOne expectedOutputTwo
    (family.bankBlindForkLaws key)

/-- Moore-facing form consumed directly by canonical literal-cross
extraction. -/
noncomputable def bankMooreTraceInvariant
    [Fintype Key] [Fintype Out₁] [Fintype Out₂]
    [Inhabited Out₁] [Inhabited Out₂]
    (key : Key)
    (Selected :
      family.base.BankOneControl → family.base.BankTwoControl → Nat → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (expectedOutputOne : Nat → Out₁)
    (expectedOutputTwo : Nat → Out₂)
    (traceLaws : family.BankSelectedTraceLaws key Selected env
      expectedOutputOne expectedOutputTwo) :
    ((family.base.bankPairedMealyController key).mooreize
      ).LiteralCrossGraphTraceInvariant env :=
  (family.bankMealyTraceInvariant key Selected env expectedOutputOne
    expectedOutputTwo traceLaws).toMooreTraceInvariant _

end

end FiniteExactClosingBlindFamily

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
