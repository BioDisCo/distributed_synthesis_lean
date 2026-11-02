/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatiblePathAcceptance

/-!
# Compatible-path acceptance for an arbitrary finite physical machine

A finite physical machine is described by its exact block minima and
target roots. A compatible policy supplies a coherent accepting path
with those block priorities.

This file records that smallest interface.  One coherent path of the fixed
compatible policy supplies the parity sequence.  Any finite physical machine
whose cut blocks have those priorities is accepting.  No local endpoint is
given a path state, side, graph, row, hierarchy bit, or leader bit.
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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatiblePath
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleTargetPath A strategy hwin policy

/-! ## Machine-independent alignment -/

/-- Exact parity interface between one finite physical machine and one
coherent path of the fixed compatible policy.  The path is proof-side; the
machine is already fixed before the environment is read. -/
structure ProfiledRawJointHybridPhysicalCompatibleMachinePathAlignment
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (path : CompatiblePath A strategy hwin policy)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) where
  start : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  blockMin_eq_rootPriority : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts k =
      profiledRawJointThreadRootPriority A (path.rootAt k)

namespace ProfiledRawJointHybridPhysicalCompatibleMachinePathAlignment

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {path : CompatiblePath A strategy hwin policy}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}

/-- The linked code-lineage parity and the physical block equations assemble
directly into the repository's ordinary epoch coupling. -/
noncomputable def epochCoupling
    (alignment :
      ProfiledRawJointHybridPhysicalCompatibleMachinePathAlignment A strategy
        hwin policy path G outputOne outputTwo env) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env := by
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  let priorities := fun n ↦
    (codedAlternatingIndexedLineageCodeThreadSystem initialCode
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun initialCode
        (profiledRawJointHybridCurrentSlots A)
        (path.codeWord A strategy hwin) path.initialSide () n)
  let epochPriority := fun k ↦
    profiledRawJointThreadRootPriority A (path.rootAt k)
  have hfull : NatSeqMinEvenParity priorities := by
    simpa only [priorities, initialCode] using
      path.threadPriority_parity A strategy hwin path.initialSide
  have hshift : NatSeqMinEvenParity (fun k ↦ priorities (1 + k)) :=
    (natSeqMinEvenParity_shift priorities 1).mpr hfull
  have hepoch : NatSeqMinEvenParity epochPriority := by
    convert hshift using 1
    funext k
    have hlive := path.lineage_live_at_target A strategy hwin k
    simp only [priorities, initialCode]
    rw [show 1 + k = k + 1 by omega, hlive]
    rfl
  exact {
    start := alignment.start
    cuts := alignment.cuts
    cuts_strictMono := alignment.cuts_strictMono
    cuts_zero := alignment.cuts_zero
    epochPriority := epochPriority
    epochParity := hepoch
    blockMin_eq_epochPriority := alignment.blockMin_eq_rootPriority }

/-- Any finite machine satisfying the linked path block equations accepts its
actual physical word. -/
theorem accepts
    (alignment :
      ProfiledRawJointHybridPhysicalCompatibleMachinePathAlignment A strategy
        hwin policy path G outputOne outputTwo env) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  exact A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling G outputOne
    outputTwo env (alignment.epochCoupling A strategy hwin)

end ProfiledRawJointHybridPhysicalCompatibleMachinePathAlignment

end

end DetParityAutomaton

end DistributedSynthesis
