/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyLeaderFreeKernel

/-!
# A canonical unreachable front for a re-rooted Unit-policy kernel

The recurrent-simulation theorems compare an indexed carrier with a
fixed-policy carrier re-rooted in an ordinary matched/cross control.  The
fixed-policy kernel's type nevertheless asks for initial and exceptional
transition fields.  None of those fields is reachable below that re-root.

This file supplies a canonical total adapter for the unused front.  Every
front transition returns the distinguished initial control and default
output.  This is executable plumbing only: no correctness proposition is a
field, and ordinary recurrent transitions are still the verified Unit-policy
ones.
-/

namespace DistributedSynthesis

universe u v x y s i₁ i₂ e₁ e₂

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
  (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
  (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (initial.code A))
  (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)

/-- A total initial/exceptional adapter whose fields are irrelevant after a
recurrent re-root.  Keeping the caller's front types lets the result be used
directly by the indexed recurrent-state relation. -/
noncomputable def profiledRawJointUnitPolicyDummyExceptionalAdapter
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Inhabited InitialOne] [Inhabited InitialTwo] :
    ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial policy
      bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo where
  initialOne := default
  initialTwo := default
  initialOutputOne := default
  initialOutputTwo := default
  initialNoRecvOne := fun _ _ ↦ (default, .initial default)
  exceptionalNoRecvOne := fun _ _ ↦ (default, .initial default)
  initialNoRecvTwo := fun _ _ ↦ (default, .initial default)
  exceptionalNoRecvTwo := fun _ _ ↦ (default, .initial default)
  otherRecvOne := fun _ _ _ _ ↦ (default, .initial default)
  otherRecvTwo := fun _ _ _ _ ↦ (default, .initial default)

end

end DetParityAutomaton

end DistributedSynthesis
