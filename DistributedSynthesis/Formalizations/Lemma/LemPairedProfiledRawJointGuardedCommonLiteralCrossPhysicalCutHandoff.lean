/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossLocalRound
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailChargedPhysicalSlices
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFreshPolicyCanonicalPhysicalSchedule

/-!
# Pointwise literal-cross rounds hand off to charged physical cuts

The local literal-cross equations are naturally proved one round at a time,
whereas the hard-regime parity seam asks for equality of a complete finite
record slice.  This file is the lossless adapter between those two statement
shapes.

At one scheduled cut the operational construction owes exactly three facts:

* the current DPA state is the query entry state;
* the numerical gap has the query's literal length; and
* every emitted round at a valid literal offset is the corresponding query
  record.

The last point is converted here to the list equality required by
`ProfiledRawJointGuardedCommonTailChargedPhysicalCut`.  Thus a consumer of the
literal-cross carrier never has to reconstruct the older semantic pending
controls.  The word, cuts, and offsets are proof-side trace data; no local
transition receives a graph, orientation, leader, or history argument.
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

/-! ## One pointwise cut -/

/-- Pointwise form of the exact operational information at one literal-cross
cut.  Unlike an old charged pending state, this contains no semantic control:
the final field talks only about the actual trace and the scheduled literal
record list. -/
structure ProfiledRawJointGuardedCommonLiteralCrossPointwisePhysicalCut
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
  emitted_round_eq : ∀ (j : Nat)
      (hj : j < (query.records A strategy initial policy bank).length),
    word (start + cuts k + j) =
      (query.records A strategy initial policy bank)[j]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Pointwise literal-round alignment is exactly enough to build the charged
physical cut consumed by the hard-regime development. -/
theorem
    ProfiledRawJointGuardedCommonLiteralCrossPointwisePhysicalCut.toChargedPhysicalCut
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root}
    {word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {start : Nat} {cuts : Nat → Nat} {k : Nat}
    (cut :
      ProfiledRawJointGuardedCommonLiteralCrossPointwisePhysicalCut A strategy
        initial policy bank query word start cuts k) :
    ProfiledRawJointGuardedCommonTailChargedPhysicalCut A strategy initial
      policy bank query word start cuts k := by
  refine ⟨cut.entryState_eq, cut.literal_length_eq, ?_⟩
  apply List.ext_get
  · simp [omegaPrefix]
  · intro j hjLeft hjRight
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [omegaPrefix, List.getElem_ofFn, OmegaWord.drop_apply]
    exact cut.emitted_round_eq j (by simpa using hjRight)

/-! ## A complete scheduled family -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A pointwise witness at every scheduled cut converts directly to the
charged scheduled alignment.  This is the final structural handoff expected
from a literal-cross trace induction. -/
theorem
    profiledRawJointGuardedCommonTailChargedScheduledCutAlignment_of_literalCrossPointwise
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (start : Nat) (cuts : Nat → Nat)
    (pointwiseAt : ∀ k : Nat,
      let root :=
        profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          seed schedule k
      let query := schedule k root
      ProfiledRawJointGuardedCommonLiteralCrossPointwisePhysicalCut A strategy
        initial policy bank query
          (G.globalMachineTraceWord outputOne outputTwo env) start cuts k) :
    ProfiledRawJointGuardedCommonTailChargedScheduledCutAlignment A strategy
      initial policy bank G outputOne outputTwo env seed schedule start cuts := by
  refine ⟨fun k ↦ ?_⟩
  exact (pointwiseAt k).toChargedPhysicalCut A strategy initial policy bank

/-! ## Canonical cuts remove the numerical field -/

/-- For the canonical physical close schedule, cut arithmetic already fixes
the query length.  Consequently the concrete literal-cross carrier owes only
the entry-state equation and the pointwise emitted-round equation.

This is the smallest exact proposition left at the operational/parity seam.
It contains no old pending controls and no runtime hierarchy information. -/
structure
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalTraceAlignment
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow) : Prop where
  entryStateAt : ∀ k : Nat,
    let schedule :=
      profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
        bank physicalEnv base hterm seed rowAt
    let cuts :=
      profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
        physicalEnv base hterm seed schedule
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k
    let query := schedule k root
    A.run (G.globalMachineTraceWord outputOne outputTwo physicalEnv)
        (base + cuts k) =
      query.entryState A strategy initial policy
  emittedRoundAt : ∀ k : Nat,
    let schedule :=
      profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
        bank physicalEnv base hterm seed rowAt
    let cuts :=
      profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
        physicalEnv base hterm seed schedule
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k
    let query := schedule k root
    ∀ (j : Nat)
      (hj : j < (query.records A strategy initial policy bank).length),
      G.globalMachineTraceWord outputOne outputTwo physicalEnv
          (base + cuts k + j) =
        (query.records A strategy initial policy bank)[j]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The canonical trace alignment supplies the complete charged alignment.
The length equation is proved from the canonical schedule, rather than being
assumed from the local carrier. -/
theorem
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalTraceAlignment.toChargedScheduledCutAlignment
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂} {base : Nat}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {rowAt : Nat → PairedEntryRow}
    (alignment :
      ProfiledRawJointGuardedCommonLiteralCrossCanonicalTraceAlignment A
        strategy initial policy bank G outputOne outputTwo physicalEnv base
          hterm seed rowAt) :
    let schedule :=
      profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
        bank physicalEnv base hterm seed rowAt
    let cuts :=
      profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
        physicalEnv base hterm seed schedule
    ProfiledRawJointGuardedCommonTailChargedScheduledCutAlignment A strategy
      initial policy bank G outputOne outputTwo physicalEnv seed schedule base
        cuts := by
  dsimp only
  apply
    profiledRawJointGuardedCommonTailChargedScheduledCutAlignment_of_literalCrossPointwise
      A strategy initial policy bank G outputOne outputTwo physicalEnv seed
  intro k
  let schedule :=
    profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
      bank physicalEnv base hterm seed rowAt
  let cuts :=
    profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
      physicalEnv base hterm seed schedule
  let root :=
    profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank seed
      schedule k
  let query := schedule k root
  refine {
    entryState_eq := alignment.entryStateAt k
    literal_length_eq := ?_
    emitted_round_eq := ?_ }
  · rw [ProfiledRawJointUnitPolicyCloseQuery.records_length_eq_inputListLength]
    have hlength :=
      profiledRawJointUnitPolicyPhysicalCloseSchedule_inputListLengthAt A
        strategy initial policy bank physicalEnv base hterm seed rowAt k
    simpa [schedule, cuts, query,
      profiledRawJointUnitPolicyRootOrientedOpenLength,
      profiledRawJointUnitPolicyRootOrientedCuts,
      rootOrientedCloseOpenLength] using hlength
  · intro j hj
    exact alignment.emittedRoundAt k j hj

end

end DetParityAutomaton

end DistributedSynthesis
