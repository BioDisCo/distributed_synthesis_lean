/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailChargedLocalTable
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPolicyRecurrentTrace

/-!
# Charged automatic cuts expose the generic scheduled physical slices

The charged switching adapter is responsible only for an operational fact at
each proof-side cut: its current DPA state is the scheduled query's entry
state, the next cut has the literal query length, and the records it emits up
to that cut are exactly the query records.  These are precisely the three
fields of the already established `PhysicalSlice` interface.

This file gives that residual an adapter-facing name and packages pointwise
charged-cut witnesses into `ProfiledRawJointUnitPolicyScheduledPhysicalSlices`.
No new parity, policy-coherence, graph, orientation, or leader premise is
introduced.
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
  (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
  (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (initial.code A))
  (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)

/-! ## One adapter-facing cut -/

/-- The exact operational information exposed by one charged automatic cut.
The names emphasize what the switching adapter proves; the conversion below
shows that this is neither stronger nor weaker than the generic slice seam. -/
structure ProfiledRawJointGuardedCommonTailChargedPhysicalCut
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) (cuts : Nat → Nat) (k : Nat) : Prop where
  entryState_eq :
    A.run word (start + cuts k) =
      query.entryState A strategy initial policy
  literal_length_eq :
    (query.records A strategy initial policy bank).length =
      cuts (k + 1) - cuts k - 1
  emitted_records_eq :
    omegaPrefix (OmegaWord.drop word (start + cuts k))
        (query.records A strategy initial policy bank).length =
      query.records A strategy initial policy bank

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A charged operational cut is exactly a generic scheduled physical slice.
This is the smallest handoff consumed by the hard-regime parity route. -/
theorem
    ProfiledRawJointGuardedCommonTailChargedPhysicalCut.toPhysicalSlice
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root}
    {word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {start : Nat} {cuts : Nat → Nat} {k : Nat}
    (cut : ProfiledRawJointGuardedCommonTailChargedPhysicalCut A strategy
      initial policy bank query word start cuts k) :
    query.PhysicalSlice A strategy initial policy bank word start cuts k := by
  exact ⟨cut.entryState_eq, cut.literal_length_eq, cut.emitted_records_eq⟩

/-! ## Pointwise cuts to the generic scheduled package -/

/-- Adapter-facing family of charged cut witnesses for one fixed scheduled
policy thread. -/
structure ProfiledRawJointGuardedCommonTailChargedScheduledCutAlignment
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (start : Nat) (cuts : Nat → Nat) : Prop where
  cutAt : ∀ k : Nat,
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k
    let query := schedule k root
    ProfiledRawJointGuardedCommonTailChargedPhysicalCut A strategy initial
      policy bank query
        (G.globalMachineTraceWord outputOne outputTwo env) start cuts k

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- All charged automatic cuts hand off at once to the unchanged generic
scheduled-slice/parity development. -/
theorem
    ProfiledRawJointGuardedCommonTailChargedScheduledCutAlignment.toScheduledPhysicalSlices
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy}
    {start : Nat} {cuts : Nat → Nat}
    (alignment :
      ProfiledRawJointGuardedCommonTailChargedScheduledCutAlignment A strategy
        initial policy bank G outputOne outputTwo env seed schedule start cuts) :
    ProfiledRawJointUnitPolicyScheduledPhysicalSlices A strategy initial policy
      bank G outputOne outputTwo env seed schedule start cuts := by
  refine ⟨fun k ↦ ?_⟩
  exact (alignment.cutAt k).toPhysicalSlice A strategy initial policy bank

end

end DetParityAutomaton

end DistributedSynthesis
