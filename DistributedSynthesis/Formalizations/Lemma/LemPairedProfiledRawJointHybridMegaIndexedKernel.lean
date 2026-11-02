/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaChildFamily
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointIndexedPolicyLeaderFreeKernel

/-!
# The recurrent hybrid family in the indexed leader-free kernel

This is the definitional adapter from the four-way hybrid child family to the
generic indexed recurrent kernel.  All remaining construction work is now in
the finite root/exceptional adapter; below a selected mega child the existing
fixed-policy transition table is used pointwise.
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
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

/-! ## Specialized local controls and finite-front seam -/

abbrev ProfiledRawJointHybridMegaOneControl
    (InitialOne : Type i₁) (ExceptionalOne : Type e₁) :=
  ProfiledRawJointIndexedPolicyOneControl A strategy
    (ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank)
    (profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank)
    InitialOne ExceptionalOne

abbrev ProfiledRawJointHybridMegaTwoControl
    (InitialTwo : Type i₂) (ExceptionalTwo : Type e₂) :=
  ProfiledRawJointIndexedPolicyTwoControl A strategy
    (ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank)
    (profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank)
    InitialTwo ExceptionalTwo

/-- The only executable data still owed by the hybrid construction: the
finite root and one-round exceptional table. -/
abbrev ProfiledRawJointHybridMegaExceptionalAdapter
    (InitialOne : Type i₁) (InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂) :=
  ProfiledRawJointIndexedPolicyExceptionalAdapter A strategy
    (ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank)
    (profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank)
    InitialOne InitialTwo ExceptionalOne ExceptionalTwo

/-! ## Complete recurrent kernel below such an adapter -/

/-- Once the finite front table is supplied, the complete physical kernel is
obtained without further mathematical assumptions. -/
noncomputable def profiledRawJointHybridMegaLeaderFreeKernel
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridMegaExceptionalAdapter A strategy hwin
      initialBank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :
    ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂ InitialOne
      InitialTwo ExceptionalOne ExceptionalTwo
      (ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
      (ProfiledRawJointHybridMegaRightOwner A strategy hwin initialBank)
      (ProfiledRawJointHybridMegaLeftReceiver A strategy hwin initialBank)
      (ProfiledRawJointHybridMegaRightReceiver A strategy hwin initialBank)
      (ProfiledRawJointHybridMegaLeftOwner A strategy hwin initialBank) := by
  classical
  exact profiledRawJointIndexedPolicyLeaderFreeKernel A strategy
    (ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank)
    (profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank)
    adapter

end

end DetParityAutomaton

end DistributedSynthesis
