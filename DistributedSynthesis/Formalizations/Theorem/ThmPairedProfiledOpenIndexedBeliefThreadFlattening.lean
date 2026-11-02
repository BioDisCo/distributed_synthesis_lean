/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedBeliefThreadSystem
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenPointedSemanticUnfolding

/-!
# Flattening persistent indexed threads to genuine semantic executions

The indexed belief monitor has two kinds of canonical hidden threads.  A
lineage can become inactive, after which its priority is constantly the even
sink priority zero.  Otherwise the model construction must identify its live
tail with one pointed semantic unfolding of the original winning strategy.

This file proves that this dichotomy is sufficient for the complete universal
thread acceptance obligation.  The side and lineage are objective-monitor
coordinates only; neither is observed by either process.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Literal semantic chains -/

/-- A chain of pointed semantic states whose retained raw memories are
literal operational successors.  Unlike the older convenience unfolding,
this interface does not prescribe how a finite family-controller node was
queried; in particular it applies to the correlated shared-node readout. -/
structure ProfiledOpenPointedSemanticChain
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) where
  state : Nat → ProfiledOpenPointedSemanticState A strategy hwin basis
  direction : Nat → PairedEntryDirection (In₁ := In₁) (In₂ := In₂)
  memory_step : ∀ n,
    (state (n + 1)).memory A =
      PairedStrategyMemory.step (A := A) ((state n).memory A) (direction n)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every state of a literal semantic chain is the raw strategy memory
reached along the preceding recovered directions. -/
theorem ProfiledOpenPointedSemanticChain.memory_eq_atNode
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    (chain : ProfiledOpenPointedSemanticChain A strategy hwin basis)
    (n : Nat) :
    (chain.state n).memory A =
      PairedStrategyMemory.atNode (A := A) ((chain.state 0).memory A)
        (branchNode chain.direction n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [chain.memory_step n, ih]
      rw [show branchNode chain.direction (n + 1) =
        branchNode chain.direction n ++ [chain.direction n] from rfl]
      rw [PairedStrategyMemory.atNode_append]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every literal semantic chain has min-even root priorities, directly from
the original winning strategy. -/
theorem ProfiledOpenPointedSemanticChain.minEven
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (chain : ProfiledOpenPointedSemanticChain A strategy hwin basis) :
    NatSeqMinEvenParity (fun n => (chain.state n).priority A) := by
  have hparity : NatSeqMinEvenParity (fun n =>
      pairedEntryPriority A
        (PairedStrategyMemory.run (A := A) ((chain.state 0).memory A)
          (branchNode chain.direction n))) :=
    PairedStrategyMemory.switchingAccepts_of_winning (A := A) hwin
      ((chain.state 0).memory A) chain.direction
  convert hparity using 1
  funext n
  rw [ProfiledOpenPointedSemanticState.priority_eq_memory,
    chain.memory_eq_atNode A n]
  rfl

/-- A canonical indexed lineage is harmless if it eventually dies, or if its
live priority tail is pointwise the priority sequence of one genuine pointed
semantic unfolding.  The equality begins after the monitor's artificial
initial state, whose priority is zero. -/
def ProfiledOpenIndexedLineageFlattens
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (word : OmegaWord
      (ProfiledOpenIndexedBiBeliefMove A ×
        ProfiledOpenIndexedBiBeliefDirection
          (I := I) (In₁ := In₁) (In₂ := In₂)))
    (initialSide : IndexedLineageSide) (lineage : I) : Prop :=
  (∃ n,
      (profiledOpenIndexedBiBeliefThreadRun A initialCode word initialSide
        lineage n).2 = .dead) ∨
    ∃ chain : ProfiledOpenPointedSemanticChain A strategy hwin basis,
      ∀ n,
        (profiledOpenIndexedBiBeliefThreadSystem A initialCode).priority
            (profiledOpenIndexedBiBeliefThreadRun A initialCode word
              initialSide lineage (n + 1)) =
          (chain.state n).priority A

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The dead-or-genuine-execution dichotomy discharges the global universal
hidden-thread parity condition. -/
theorem profiledOpenIndexedBiBeliefThreadSystem_accepts_of_flattens
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (word : OmegaWord
      (ProfiledOpenIndexedBiBeliefMove A ×
        ProfiledOpenIndexedBiBeliefDirection
          (I := I) (In₁ := In₁) (In₂ := In₂)))
    (hflatten : ∀ initialSide lineage,
      ProfiledOpenIndexedLineageFlattens A (hwin := hwin) (basis := basis)
        initialCode word initialSide lineage) :
    (profiledOpenIndexedBiBeliefThreadSystem A initialCode).universalRunDPA.Accepts
      word := by
  rw [profiledOpenIndexedBiBeliefThreadSystem_accepts_iff]
  intro initialSide lineage
  rcases hflatten initialSide lineage with hdead | hlive
  · rcases hdead with ⟨n, hdead⟩
    exact codedAlternatingIndexedLineageRun_minEven_of_eventually_dead
      initialCode (profiledOpenIndexedBiBeliefNext A)
      (profiledOpenIndexedBiBeliefCurrentSlots A)
      (profiledOpenIndexedBiBeliefChildCode A)
      (profiledOpenIndexedRootPriority A) word initialSide lineage hdead
  · rcases hlive with ⟨chain, hpriority⟩
    let priorities := fun n =>
      (profiledOpenIndexedBiBeliefThreadSystem A initialCode).priority
        (profiledOpenIndexedBiBeliefThreadRun A initialCode word initialSide
          lineage n)
    have hsemantic := chain.minEven A hwin basis
    have htail : NatSeqMinEvenParity (fun n => priorities (1 + n)) := by
      convert hsemantic using 1
      funext n
      simpa [priorities, Nat.add_comm] using hpriority n
    exact (natSeqMinEvenParity_shift priorities 1).mp htail

end

end DetParityAutomaton

end DistributedSynthesis
