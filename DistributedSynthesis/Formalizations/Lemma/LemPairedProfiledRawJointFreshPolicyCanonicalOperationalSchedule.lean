/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFreshPolicyCanonicalPhysicalSchedule

/-!
# Canonical fixed-policy schedule on operational close cuts

The root-oriented physical schedule is useful when a proof-side root may be
temporarily misaligned with the graph.  In the two genuinely hard physical
regimes there is a simpler clock already available: `operationalCloseCuts`
consumes every simultaneous round as a singleton and every strict run as one
maximal block.

This file threads one fixed policy through those cuts.  At cut `k` it reads
the literal physical input interval, forms the corresponding typed close
query at the current root, and uses that query's checked target as the next
root.  Thus the schedule is non-circular, and its represented record length
is constructionally the operational open length.

All roots, rows, and cuts remain proof-side data.  Neither process receives a
graph, direction, row, or block boundary.
-/

namespace DistributedSynthesis

universe u v x y s

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

/-- The fixed-policy root reached after the first `k` operational physical
blocks.  The cuts are independent of the root, so only the root itself needs
to be threaded recursively. -/
noncomputable def profiledRawJointUnitPolicyOperationalThreadRoot
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow) : Nat →
      ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A) policy
  | 0 => seed
  | k + 1 =>
      let cuts := operationalCloseCuts
        (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
      let root := profiledRawJointUnitPolicyOperationalThreadRoot physicalEnv
        base hterm seed rowAt k
      let query := profiledRawJointUnitPolicyPhysicalCloseQuery A strategy
        initial policy physicalEnv (base + cuts k) (base + cuts (k + 1))
          (rowAt k) root
      query.target A strategy initial policy bank

/-- The close schedule projected from the operational cuts and the literal
physical interval.  Its value at roots other than the scheduled one is merely
the total dependent-function extension and is never used by the proof. -/
noncomputable def profiledRawJointUnitPolicyOperationalCloseSchedule
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (rowAt : Nat → PairedEntryRow) :
    ProfiledRawJointUnitPolicyCloseSchedule A strategy initial policy :=
  fun k root ↦
    let cuts := operationalCloseCuts
      (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
    profiledRawJointUnitPolicyPhysicalCloseQuery A strategy initial policy
      physicalEnv (base + cuts k) (base + cuts (k + 1)) (rowAt k) root

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Scheduled roots are exactly the roots of the simultaneous operational
recursion. -/
theorem profiledRawJointUnitPolicyScheduledRoot_operationalCloseSchedule
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow) : ∀ k : Nat,
    profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank seed
        (profiledRawJointUnitPolicyOperationalCloseSchedule A strategy initial
          policy physicalEnv base hterm rowAt) k =
      profiledRawJointUnitPolicyOperationalThreadRoot A strategy initial policy
        bank physicalEnv base hterm seed rowAt k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [profiledRawJointUnitPolicyScheduledRoot_succ, ih]
      rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The canonical operational query has exactly the open length represented
by the operational close clock. -/
theorem profiledRawJointUnitPolicyOperationalCloseSchedule_recordsLengthAt
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow) (k : Nat) :
    let schedule :=
      profiledRawJointUnitPolicyOperationalCloseSchedule A strategy initial
        policy physicalEnv base hterm rowAt
    ((schedule k
      (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k)).records A strategy initial policy bank).length =
      operationalCloseOpenLength
        (profiledRawJointPhysicalGraphTail physicalEnv base) hterm k := by
  dsimp only
  simp only [profiledRawJointUnitPolicyOperationalCloseSchedule]
  rw [ProfiledRawJointUnitPolicyCloseQuery.records_length_eq_inputListLength]
  rw [profiledRawJointUnitPolicyPhysicalCloseQuery_inputListLength]
  unfold operationalCloseOpenLength
  omega

/-! ## Acceptance adapter -/

private abbrev UnitKernel
    {InitialOne : Type*} {InitialTwo : Type*}
    {ExceptionalOne : Type*} {ExceptionalTwo : Type*}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :=
  profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
    adapter

/-- Exact residual for the canonical operational schedule.  Query lengths
have disappeared: they follow from the construction above.  Simultaneous
cuts need only the entry-state equation; the strict field is requested only
when the current operational block is strict. -/
structure ProfiledRawJointUnitPolicyCanonicalOperationalCloseAlignment
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow) : Prop where
  entryStateAt : ∀ k : Nat,
    let schedule :=
      profiledRawJointUnitPolicyOperationalCloseSchedule A strategy initial
        policy physicalEnv base hterm rowAt
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k
    A.run
        ((UnitKernel A strategy initial policy bank adapter
          ).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter
              ).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter
              ).globalOutputTwo physicalEnv)
        (base + operationalCloseCuts
          (profiledRawJointPhysicalGraphTail physicalEnv base) hterm k) =
      (schedule k root).entryState A strategy initial policy
  traceOperationalAt_of_strict : ∀ k : Nat,
    let schedule :=
      profiledRawJointUnitPolicyOperationalCloseSchedule A strategy initial
        policy physicalEnv base hterm rowAt
    let cuts := operationalCloseCuts
      (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k
    profiledRawJointPhysicalGraphTail physicalEnv base (cuts k) ≠ .both →
      (schedule k root).TraceOperationalAt A strategy initial policy bank
        adapter physicalEnv base cuts k

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The canonical two-field residual supplies the older operational-close
alignment verbatim. -/
theorem
    ProfiledRawJointUnitPolicyCanonicalOperationalCloseAlignment.toOperationalCloseAlignment
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo}
    {physicalEnv : EnvironmentSequence In₁ In₂} {base : Nat}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {rowAt : Nat → PairedEntryRow}
    (alignment :
      ProfiledRawJointUnitPolicyCanonicalOperationalCloseAlignment A strategy
        initial policy bank adapter physicalEnv base hterm seed rowAt) :
    ProfiledRawJointUnitPolicyOperationalCloseAlignment A strategy initial
      policy bank adapter physicalEnv base hterm seed
        (profiledRawJointUnitPolicyOperationalCloseSchedule A strategy initial
          policy physicalEnv base hterm rowAt) where
  entryStateAt := alignment.entryStateAt
  recordsLengthAt k :=
    profiledRawJointUnitPolicyOperationalCloseSchedule_recordsLengthAt A
      strategy initial policy bank physicalEnv base hterm seed rowAt k
  traceOperationalAt_of_strict := alignment.traceOperationalAt_of_strict

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- End-to-end acceptance from the canonical operational schedule.  The only
model-specific obligations left are checker-state propagation and strict-cut
matched/cross trace alignment. -/
theorem profiledRawJointUnitPolicy_accepts_of_canonicalOperationalCloseAlignment
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run [])
    (alignment :
      ProfiledRawJointUnitPolicyCanonicalOperationalCloseAlignment A strategy
        initial policy bank adapter physicalEnv base hterm seed rowAt) :
    A.Accepts
      ((UnitKernel A strategy initial policy bank adapter
        ).globalMachine.globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv) := by
  exact profiledRawJointUnitPolicy_accepts_of_operationalCloseAlignment A
    strategy initial policy bank adapter physicalEnv base hterm seed
      (profiledRawJointUnitPolicyOperationalCloseSchedule A strategy initial
        policy physicalEnv base hterm rowAt) hseed
      alignment.toOperationalCloseAlignment

end

end DetParityAutomaton

end DistributedSynthesis
