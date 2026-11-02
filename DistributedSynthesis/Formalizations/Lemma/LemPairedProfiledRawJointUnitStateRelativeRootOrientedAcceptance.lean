/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitStateRelativeOperationalCloseAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitRootOrientedCloseCuts

/-!
# State-relative acceptance on root-oriented close cuts

The root-oriented clock consumes a complete strict block when the physical
graph agrees with the scheduled fixed-policy root and one singleton round
otherwise.  In the mismatch case the scheduled record list is empty, so a
state-relative physical slice needs no controller-output equation.

This file is the state-relative counterpart of
`ProfiledRawJointUnitPolicyFixedRerootInvariant`.  It is designed for a
guarded handoff: the caller supplies the actual checker state and the word of
an explicitly rerooted Unit machine rather than restarting either object at
its global initial state.
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

/-- Minimal state-relative invariant for a root-oriented fixed-policy
schedule.  At a matching cut the caller identifies the literal record slice;
at a mismatch the clock proves that the record list is empty. -/
structure ProfiledRawJointUnitPolicyRootOrientedStateRelativeAlignment
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) : Prop where
  entryStateAt : ∀ k : Nat,
    let cuts := profiledRawJointUnitPolicyRootOrientedCuts A strategy initial
      policy bank physicalEnv 0 hterm seed schedule
    let root := profiledRawJointUnitPolicyScheduledRoot A strategy initial
      policy bank seed schedule k
    A.runFrom physicalState word (cuts k) =
      (schedule k root).entryState A strategy initial policy
  recordsLengthAt : ∀ k : Nat,
    let cuts := profiledRawJointUnitPolicyRootOrientedCuts A strategy initial
      policy bank physicalEnv 0 hterm seed schedule
    let root := profiledRawJointUnitPolicyScheduledRoot A strategy initial
      policy bank seed schedule k
    ((schedule k root).records A strategy initial policy bank).length =
      cuts (k + 1) - cuts k - 1
  recordsAt_of_match : ∀ k : Nat,
    let cuts := profiledRawJointUnitPolicyRootOrientedCuts A strategy initial
      policy bank physicalEnv 0 hterm seed schedule
    let root := profiledRawJointUnitPolicyScheduledRoot A strategy initial
      policy bank seed schedule k
    profiledRawJointPhysicalGraphTail physicalEnv 0 (cuts k) =
        root.graph A strategy initial policy →
      omegaPrefix (OmegaWord.drop word (cuts k))
          ((schedule k root).records A strategy initial policy bank).length =
        (schedule k root).records A strategy initial policy bank

namespace ProfiledRawJointUnitPolicyRootOrientedStateRelativeAlignment

/-- The root-oriented invariant supplies a state-relative physical slice at
every cut.  Mismatch cuts are discharged solely from their zero open length. -/
theorem sliceAt
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {physicalState : A.State}
    {word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy}
    (alignment :
      ProfiledRawJointUnitPolicyRootOrientedStateRelativeAlignment A strategy
        initial policy bank physicalEnv physicalState word hterm seed schedule)
    (k : Nat) :
    let cuts := profiledRawJointUnitPolicyRootOrientedCuts A strategy initial
      policy bank physicalEnv 0 hterm seed schedule
    let root := profiledRawJointUnitPolicyScheduledRoot A strategy initial
      policy bank seed schedule k
    (schedule k root).StateRelativePhysicalSlice A strategy initial policy
      bank physicalState word cuts k := by
  dsimp only
  let graphs := profiledRawJointPhysicalGraphTail physicalEnv 0
  let expected := profiledRawJointUnitPolicyScheduledGraph A strategy initial
    policy bank seed schedule
  let cuts := profiledRawJointUnitPolicyRootOrientedCuts A strategy initial
    policy bank physicalEnv 0 hterm seed schedule
  let root := profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
    bank seed schedule k
  let query := schedule k root
  refine {
    entryState_eq := alignment.entryStateAt k
    records_length := alignment.recordsLengthAt k
    records_eq_slice := ?_ }
  by_cases hmatch : graphs (cuts k) = expected k
  · exact alignment.recordsAt_of_match k (by
      simpa [graphs, expected, cuts, root,
        profiledRawJointUnitPolicyScheduledGraph] using hmatch)
  · have hopen : rootOrientedCloseOpenLength graphs hterm expected k = 0 :=
      rootOrientedCloseOpenLength_eq_zero_of_mismatch graphs hterm expected k
        hmatch
    have hlength :
        (query.records A strategy initial policy bank).length =
          rootOrientedCloseOpenLength graphs hterm expected k := by
      simpa [query, root, cuts,
        profiledRawJointUnitPolicyRootOrientedCuts,
        rootOrientedCloseOpenLength, graphs, expected] using
          alignment.recordsLengthAt k
    have hempty : query.records A strategy initial policy bank = [] :=
      query.records_eq_nil_of_rootOriented_mismatch A strategy initial policy
        bank graphs hterm expected k hlength hmatch
    rw [hempty]
    simp [omegaPrefix]

/-- The accepted alternating thread of the fixed policy converts the
state-relative root-oriented slices into acceptance from the actual checker
state. -/
theorem acceptsFrom
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {physicalState : A.State}
    {word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy}
    (alignment :
      ProfiledRawJointUnitPolicyRootOrientedStateRelativeAlignment A strategy
        initial policy bank physicalEnv physicalState word hterm seed schedule)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run []) :
    A.AcceptsFrom physicalState word := by
  let cuts := profiledRawJointUnitPolicyRootOrientedCuts A strategy initial
    policy bank physicalEnv 0 hterm seed schedule
  let thread := profiledRawJointUnitPolicyScheduledAlternatingThread A strategy
    initial policy bank seed schedule hseed
  apply thread.physicalTail_acceptsFrom_of_threadRootPriority A policy
    physicalState word 0 cuts
  · exact rootOrientedCloseCuts_strictMono
      (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
      (profiledRawJointUnitPolicyScheduledGraph A strategy initial policy bank
        seed schedule)
  · rfl
  · intro k
    have hslice := alignment.sliceAt A strategy initial policy bank k
    have hblock := hslice.cutBlockMin_eq_blockPriority A strategy initial
      policy bank
    have htarget :=
      profiledRawJointUnitPolicyScheduledAlternatingThread_targetPriority A
        strategy initial policy bank seed schedule hseed k
    simpa [thread, cuts] using hblock.trans htarget.symm

end ProfiledRawJointUnitPolicyRootOrientedStateRelativeAlignment

end

end DetParityAutomaton

end DistributedSynthesis
