/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefPhysicalAcceptanceSplit
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointIndexedPolicyRecurrentSimulation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitDummyExceptionalAdapter

/-!
# Physical-acceptance handoff at an indexed recurrent state

An indexed carrier may reach its selected fixed-policy kernel only after a
finite physical prefix.  The DPA must therefore check the fixed-policy suffix
from the state reached by that prefix, not from `A.initial`.

The existing four-regime physical package already supports this without a
second acceptance theory: instantiate it for `A.withInitial state`.  The first
definition below gives this use a structural name.  The generic theorem turns
that package into `AcceptsFrom`; the final theorem combines it with the exact
same-key recurrent simulation and the finite-prefix reroot theorem.

No checker is restarted, and no graph, orientation, or leader bit is exposed
to either local controller.
-/

namespace DistributedSynthesis

universe u v w x y s k i₁ i₂ e₁ e₂

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-! ## Generic state-relative four-regime package -/

/-- The existing physical-acceptance split, based at an explicit DPA state.
This is definitionally the ordinary package for `A.withInitial state`; hence
all four graph regimes and all their existing consumers are reused verbatim. -/
abbrev FiniteGlobalMachinePhysicalAcceptanceFrom
    (state : A.State)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) : Type _ :=
  (A.withInitial state).FiniteGlobalMachinePhysicalAcceptance G outputOne
    outputTwo env

/-- A state-relative four-regime package proves acceptance from that exact
state.  This is the `AcceptsFrom` companion of
`finiteGlobalMachineTraceWord_accepts_of_physicalAcceptance`. -/
theorem finiteGlobalMachineTraceWord_acceptsFrom_of_physicalAcceptanceFrom
    (state : A.State)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (physical : A.FiniteGlobalMachinePhysicalAcceptanceFrom state G outputOne
      outputTwo env) :
    A.AcceptsFrom state
      (G.globalMachineTraceWord outputOne outputTwo env) := by
  rw [← A.withInitial_accepts_iff state]
  exact
    (A.withInitial state).finiteGlobalMachineTraceWord_accepts_of_physicalAcceptance
      G outputOne outputTwo env physical

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (ChildCode : Type k)
  (source : ChildCode →
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
  (policy : (key : ChildCode) →
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((source key).code A))
  (bank : (key : ChildCode) →
    ProfiledRawJointUnitPolicyControllerBank A strategy (source key)
      (policy key))

/-! ## Indexed finite-prefix handoff -/

/-- Once an indexed execution reaches a same-key recurrent pair, the existing
four-regime physical proof for the corresponding fixed-policy reroot closes
the complete indexed trace.  Crucially, the package is based at the actual
DPA state after the indexed prefix. -/
theorem profiledRawJointIndexedPolicy_accepts_of_recurrentAt_physicalAcceptance
    [Fintype ChildCode] [DecidableEq ChildCode]
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Inhabited InitialOne] [Inhabited InitialTwo]
    (indexedAdapter : ProfiledRawJointIndexedPolicyExceptionalAdapter A
      strategy ChildCode source policy bank InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (key : ChildCode)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (unitState :
      (ProfiledRawJointUnitPolicyOneControl A strategy (source key) (policy key)
          (bank key) InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointUnitPolicyTwoControl A strategy (source key) (policy key)
          (bank key) InitialTwo ExceptionalTwo × Out₂))
    (hrel : ProfiledRawJointIndexedPolicyRecurrentAt A strategy ChildCode
      source policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo
        key
        ((profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
          source policy bank indexedAdapter).globalMachine.globalStateTrace
            env start)
        unitState)
    (physical :
      let indexedKernel :=
        profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
          source policy bank indexedAdapter
      let unitKernel :=
        profiledRawJointUnitPolicyLeaderFreeKernel A strategy (source key)
          (policy key) (bank key)
          (profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy
            (source key) (policy key) (bank key) (InitialOne := InitialOne)
              (InitialTwo := InitialTwo) (ExceptionalOne := ExceptionalOne)
              (ExceptionalTwo := ExceptionalTwo))
      A.FiniteGlobalMachinePhysicalAcceptanceFrom
        (A.run
          (indexedKernel.globalMachine.globalMachineTraceWord
            indexedKernel.globalOutputOne indexedKernel.globalOutputTwo env)
          start)
        (unitKernel.globalMachine.reroot unitState)
        unitKernel.globalOutputOne unitKernel.globalOutputTwo
        (OmegaWord.drop env start)) :
    A.Accepts
      ((profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
        source policy bank indexedAdapter).globalMachine.globalMachineTraceWord
          (profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
            source policy bank indexedAdapter).globalOutputOne
          (profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
            source policy bank indexedAdapter).globalOutputTwo env) := by
  let indexedKernel :=
    profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode source
      policy bank indexedAdapter
  let unitKernel :=
    profiledRawJointUnitPolicyLeaderFreeKernel A strategy (source key)
      (policy key) (bank key)
      (profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy
        (source key) (policy key) (bank key) (InitialOne := InitialOne)
          (InitialTwo := InitialTwo) (ExceptionalOne := ExceptionalOne)
          (ExceptionalTwo := ExceptionalTwo))
  apply profiledRawJointIndexedPolicy_accepts_of_recurrentAt A strategy
    ChildCode source policy bank indexedAdapter key
      (profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy
        (source key) (policy key) (bank key) (InitialOne := InitialOne)
          (InitialTwo := InitialTwo) (ExceptionalOne := ExceptionalOne)
          (ExceptionalTwo := ExceptionalTwo)) env start unitState hrel
  exact A.finiteGlobalMachineTraceWord_acceptsFrom_of_physicalAcceptanceFrom
    (A.run
      (indexedKernel.globalMachine.globalMachineTraceWord
        indexedKernel.globalOutputOne indexedKernel.globalOutputTwo env)
      start)
    (unitKernel.globalMachine.reroot unitState) unitKernel.globalOutputOne
      unitKernel.globalOutputTwo (OmegaWord.drop env start) physical

end

end DetParityAutomaton

end DistributedSynthesis
