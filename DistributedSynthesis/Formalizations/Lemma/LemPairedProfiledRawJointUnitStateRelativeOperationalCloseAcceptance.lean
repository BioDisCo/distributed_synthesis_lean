/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFreshPolicyCanonicalOperationalSchedule
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointAlignedCanonicalPhysicalSchedule
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitFixedPolicyStateRelativeThreadAlignment

/-!
# State-relative acceptance on canonical operational close cuts

After a finite guarded handoff the original checker is already in a literal
row coordinate of one fixed policy root.  Restarting the DPA at its global
initial state would therefore be wrong.  This file is the state-relative
counterpart of the scheduled physical-slice endpoint.

For the canonical operational schedule, a concrete carrier owes only:

* the actual `runFrom` state at each cut; and
* the emitted strict-record slice at strict cuts.

Lengths follow from the canonical schedule.  At a simultaneous cut the open
record list is empty, so no controller-shape or output equation is needed.
The fixed policy's accepted alternating thread then proves `AcceptsFrom` for
the physical suffix.
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

/-- State-relative analogue of one scheduled physical slice. -/
structure ProfiledRawJointUnitPolicyCloseQuery.StateRelativePhysicalSlice
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat) : Prop where
  entryState_eq : A.runFrom physicalState word (cuts k) =
    query.entryState A strategy initial policy
  records_length :
    (query.records A strategy initial policy bank).length =
      cuts (k + 1) - cuts k - 1
  records_eq_slice :
    omegaPrefix (OmegaWord.drop word (cuts k))
        (query.records A strategy initial policy bank).length =
      query.records A strategy initial policy bank

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- One state-relative literal slice identifies the physical block minimum
with the fixed-policy query priority. -/
theorem
    ProfiledRawJointUnitPolicyCloseQuery.StateRelativePhysicalSlice.cutBlockMin_eq_blockPriority
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root}
    {physicalState : A.State}
    {word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {cuts : Nat → Nat} {k : Nat}
    (slice : query.StateRelativePhysicalSlice A strategy initial policy bank
      physicalState word cuts k) :
    cutBlockMin
        (fun n ↦ A.priority (A.runFrom physicalState word n)) cuts k =
      query.blockPriority A strategy initial policy bank := by
  rw [query.blockPriority_eq A strategy initial policy bank]
  exact cutBlockMin_runFrom_eq_priority_blockMinState_of_slice_alignment A
    physicalState word cuts k
      (query.entryState A strategy initial policy)
      (query.records A strategy initial policy bank) slice.entryState_eq
        slice.records_length slice.records_eq_slice

/-- Minimal concrete state-relative invariant on the canonical operational
schedule.  Simultaneous cuts intentionally have no emitted-record field. -/
structure ProfiledRawJointUnitPolicyCanonicalOperationalStateRelativeAlignment
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow) : Prop where
  entryStateAt : ∀ k : Nat,
    let schedule :=
      profiledRawJointUnitPolicyOperationalCloseSchedule A strategy initial
        policy physicalEnv 0 hterm rowAt
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k
    A.runFrom physicalState word
        (operationalCloseCuts
          (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k) =
      (schedule k root).entryState A strategy initial policy
  recordsAt_of_strict : ∀ k : Nat,
    let schedule :=
      profiledRawJointUnitPolicyOperationalCloseSchedule A strategy initial
        policy physicalEnv 0 hterm rowAt
    let cuts := operationalCloseCuts
      (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k
    profiledRawJointPhysicalGraphTail physicalEnv 0 (cuts k) ≠ .both →
      omegaPrefix (OmegaWord.drop word (cuts k))
          ((schedule k root).records A strategy initial policy bank).length =
        (schedule k root).records A strategy initial policy bank

namespace ProfiledRawJointUnitPolicyCanonicalOperationalStateRelativeAlignment

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The minimal canonical invariant supplies a state-relative physical slice
at every operational cut. -/
theorem sliceAt
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {physicalState : A.State}
    {word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {rowAt : Nat → PairedEntryRow}
    (alignment :
      ProfiledRawJointUnitPolicyCanonicalOperationalStateRelativeAlignment A
        strategy initial policy bank physicalEnv physicalState word hterm seed
          rowAt)
    (k : Nat) :
    let schedule :=
      profiledRawJointUnitPolicyOperationalCloseSchedule A strategy initial
        policy physicalEnv 0 hterm rowAt
    let cuts := operationalCloseCuts
      (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k
    (schedule k root).StateRelativePhysicalSlice A strategy initial policy
      bank physicalState word cuts k := by
  dsimp only
  let schedule :=
    profiledRawJointUnitPolicyOperationalCloseSchedule A strategy initial
      policy physicalEnv 0 hterm rowAt
  let cuts := operationalCloseCuts
    (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
  let root :=
    profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank seed
      schedule k
  let query := schedule k root
  have hlength :
      (query.records A strategy initial policy bank).length =
        cuts (k + 1) - cuts k - 1 := by
    have hcanonical :=
      profiledRawJointUnitPolicyOperationalCloseSchedule_recordsLengthAt A
        strategy initial policy bank physicalEnv 0 hterm seed rowAt k
    simpa [schedule, cuts, query, operationalCloseOpenLength] using hcanonical
  refine {
    entryState_eq := alignment.entryStateAt k
    records_length := hlength
    records_eq_slice := ?_ }
  by_cases hgraph :
      profiledRawJointPhysicalGraphTail physicalEnv 0 (cuts k) = .both
  · have hopen : operationalCloseOpenLength
        (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k = 0 :=
      operationalCloseOpenLength_eq_zero_of_both
        (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k hgraph
    have hempty : query.records A strategy initial policy bank = [] := by
      apply List.length_eq_zero_iff.mp
      have hcanonical :=
        profiledRawJointUnitPolicyOperationalCloseSchedule_recordsLengthAt A
          strategy initial policy bank physicalEnv 0 hterm seed rowAt k
      simpa [schedule, query, hopen] using hcanonical
    rw [hempty]
    simp [omegaPrefix]
  · exact alignment.recordsAt_of_strict k (by simpa [cuts] using hgraph)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The accepted alternating thread of the unchanged policy converts the
state-relative operational slices into acceptance from the actual checker
state. -/
theorem acceptsFrom
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {physicalState : A.State}
    {word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {rowAt : Nat → PairedEntryRow}
    (alignment :
      ProfiledRawJointUnitPolicyCanonicalOperationalStateRelativeAlignment A
        strategy initial policy bank physicalEnv physicalState word hterm seed
          rowAt)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run []) :
    A.AcceptsFrom physicalState word := by
  let schedule :=
    profiledRawJointUnitPolicyOperationalCloseSchedule A strategy initial
      policy physicalEnv 0 hterm rowAt
  let cuts := operationalCloseCuts
    (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
  let thread :=
    profiledRawJointUnitPolicyScheduledAlternatingThread A strategy initial
      policy bank seed schedule hseed
  apply thread.physicalTail_acceptsFrom_of_threadRootPriority A policy
    physicalState word 0 cuts
  · exact operationalCloseCuts_strictMono
      (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
  · exact operationalCloseCuts_zero
      (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
  · intro k
    have hslice := alignment.sliceAt A strategy initial policy bank k
    have hblock := hslice.cutBlockMin_eq_blockPriority A strategy initial
      policy bank
    have htarget :=
      profiledRawJointUnitPolicyScheduledAlternatingThread_targetPriority A
        strategy initial policy bank seed schedule hseed k
    simpa [thread, schedule, cuts] using hblock.trans htarget.symm

end ProfiledRawJointUnitPolicyCanonicalOperationalStateRelativeAlignment

end

end DetParityAutomaton

end DistributedSynthesis
