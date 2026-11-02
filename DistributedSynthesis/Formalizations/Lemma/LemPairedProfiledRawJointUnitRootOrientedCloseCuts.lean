/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitOperationalCloseAcceptance

/-!
# Root-oriented operational close cuts

The pure graph clock may begin a nonempty strict block while the scheduled
policy root has the opposite orientation.  That cannot be repaired by a
runtime leader bit.  Instead this file refines only the proof-side clock.

If the current graph agrees with the proof-side expected orientation, the
clock consumes the maximal homogeneous run.  Otherwise it consumes exactly
one physical round.  The latter block has no represented open record, so its
closing round is not falsely identified with a strict certificate record; it
only advances the scheduled alternating root.  Simultaneous rounds are
handled by the same singleton rule whenever they mismatch, and by the old
zero-open rule if selected through the matching branch.

The two fail-fast properties are proved below: every step advances, and every
mismatched step has an empty represented record list once the ordinary
length alignment is supplied.  Root orientation remains proof-side data.
-/

namespace DistributedSynthesis

universe u v w x y s i₁ i₂ e₁ e₂

/-! ## Generic expected-orientation clock -/

/-- Take the maximal operational close when the current graph has the
expected proof-side orientation; otherwise consume one singleton round. -/
noncomputable def rootOrientedCloseNext
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (expected : Graph) (n : Nat) : Nat :=
  if graphs n = expected then operationalCloseNext graphs hterm n else n + 1

/-- Fail-fast property one: every oriented close consumes a physical round. -/
theorem lt_rootOrientedCloseNext
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (expected : Graph) (n : Nat) :
    n < rootOrientedCloseNext graphs hterm expected n := by
  by_cases hmatch : graphs n = expected
  · simp only [rootOrientedCloseNext, hmatch, if_pos]
    exact lt_operationalCloseNext graphs hterm n
  · simp [rootOrientedCloseNext, hmatch]

@[simp] theorem rootOrientedCloseNext_of_mismatch
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (expected : Graph) {n : Nat} (hmismatch : graphs n ≠ expected) :
    rootOrientedCloseNext graphs hterm expected n = n + 1 := by
  simp [rootOrientedCloseNext, hmismatch]

theorem rootOrientedCloseNext_of_match
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (expected : Graph) {n : Nat} (hmatch : graphs n = expected) :
    rootOrientedCloseNext graphs hterm expected n =
      operationalCloseNext graphs hterm n := by
  simp [rootOrientedCloseNext, hmatch]

/-- Iterate the root-oriented close, using the expected proof-side graph of
block `k`. -/
noncomputable def rootOrientedCloseCuts
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (expected : Nat → Graph) : Nat → Nat
  | 0 => 0
  | k + 1 => rootOrientedCloseNext graphs hterm (expected k)
      (rootOrientedCloseCuts graphs hterm expected k)

@[simp] theorem rootOrientedCloseCuts_zero
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (expected : Nat → Graph) :
    rootOrientedCloseCuts graphs hterm expected 0 = 0 :=
  rfl

@[simp] theorem rootOrientedCloseCuts_succ
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (expected : Nat → Graph) (k : Nat) :
    rootOrientedCloseCuts graphs hterm expected (k + 1) =
      rootOrientedCloseNext graphs hterm (expected k)
        (rootOrientedCloseCuts graphs hterm expected k) :=
  rfl

/-- The iterated root-oriented clock is productive. -/
theorem rootOrientedCloseCuts_strictMono
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (expected : Nat → Graph) :
    StrictMono (rootOrientedCloseCuts graphs hterm expected) :=
  strictMono_nat_of_lt_succ fun k ↦ by
    rw [rootOrientedCloseCuts_succ]
    exact lt_rootOrientedCloseNext graphs hterm (expected k) _

/-- Number of represented open records; the final singleton closing round is
excluded exactly as in `CloseQuery.records`. -/
noncomputable def rootOrientedCloseOpenLength
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (expected : Nat → Graph) (k : Nat) : Nat :=
  rootOrientedCloseCuts graphs hterm expected (k + 1) -
    rootOrientedCloseCuts graphs hterm expected k - 1

/-- A mismatched graph consumes exactly one physical round. -/
theorem rootOrientedCloseCuts_succ_eq_add_one_of_mismatch
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (expected : Nat → Graph) (k : Nat)
    (hmismatch :
      graphs (rootOrientedCloseCuts graphs hterm expected k) ≠ expected k) :
    rootOrientedCloseCuts graphs hterm expected (k + 1) =
      rootOrientedCloseCuts graphs hterm expected k + 1 := by
  rw [rootOrientedCloseCuts_succ,
    rootOrientedCloseNext_of_mismatch graphs hterm (expected k) hmismatch]

/-- Fail-fast property two: a mismatched strict singleton has no represented
open record. -/
theorem rootOrientedCloseOpenLength_eq_zero_of_mismatch
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (expected : Nat → Graph) (k : Nat)
    (hmismatch :
      graphs (rootOrientedCloseCuts graphs hterm expected k) ≠ expected k) :
    rootOrientedCloseOpenLength graphs hterm expected k = 0 := by
  unfold rootOrientedCloseOpenLength
  rw [rootOrientedCloseCuts_succ_eq_add_one_of_mismatch graphs hterm expected k
    hmismatch]
  omega

/-- Consequently any query whose ordinary length invariant is tied to this
clock has a literally empty represented record list at a mismatch. -/
theorem DetParityAutomaton.ProfiledRawJointUnitPolicyCloseQuery.records_eq_nil_of_rootOriented_mismatch
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : DetParityAutomaton.ProfiledRawJointOneSidedSemanticState A
      strategy (I := Unit))
    (policy : DetParityAutomaton.ProfiledRawJointOneSidedProvenanceRationalPolicy
      A strategy (initial.code A))
    (bank : DetParityAutomaton.ProfiledRawJointUnitPolicyControllerBank A
      strategy initial policy)
    {root : DetParityAutomaton.ProfiledRawJointUnitFixedPolicyRoot A strategy
      (initial.code A) policy}
    (query : DetParityAutomaton.ProfiledRawJointUnitPolicyCloseQuery A strategy
      initial policy root)
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (expected : Nat → Graph) (k : Nat)
    (hlength : (query.records A strategy initial policy bank).length =
      rootOrientedCloseOpenLength graphs hterm expected k)
    (hmismatch :
      graphs (rootOrientedCloseCuts graphs hterm expected k) ≠ expected k) :
    query.records A strategy initial policy bank = [] := by
  apply List.length_eq_zero_iff.mp
  rw [hlength,
    rootOrientedCloseOpenLength_eq_zero_of_mismatch graphs hterm expected k
      hmismatch]

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

/-! ## Scheduled roots determine the expected orientation -/

/-- Proof-side orientation of a typed fixed-policy root. -/
def ProfiledRawJointUnitFixedPolicyRoot.graph
    (root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) : Graph :=
  match root with
  | .inl _ => .right
  | .inr _ => .left

/-- Strict orientation flip.  The `.both` case is included only to make this
a total proof-side function; fixed-policy roots never map to `.both`. -/
def profiledRawJointStrictGraphFlip : Graph → Graph
  | .right => .left
  | .left => .right
  | .both => .both

@[simp] theorem profiledRawJointStrictGraphFlip_right :
    profiledRawJointStrictGraphFlip .right = .left := rfl

@[simp] theorem profiledRawJointStrictGraphFlip_left :
    profiledRawJointStrictGraphFlip .left = .right := rfl

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- A typed query has exactly its source root's orientation. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.graph_eq_root_graph
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) :
    query.graph A strategy initial policy = root.graph A strategy initial
      policy := by
  cases query <;> rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Taking a literal close target flips the root orientation. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.target_graph
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) :
    (query.target A strategy initial policy bank).graph A strategy initial
        policy =
      profiledRawJointStrictGraphFlip
        (root.graph A strategy initial policy) := by
  cases query <;> rfl

/-- Expected graph at block `k`, extracted only from the scheduled proof
root. -/
noncomputable def profiledRawJointUnitPolicyScheduledGraph
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) (k : Nat) : Graph :=
  (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank seed
    schedule k).graph A strategy initial policy

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The scheduled orientation really flips after every close, including a
zero-open mismatched singleton.  This is proved from the typed query target;
it is not a runtime signal. -/
theorem profiledRawJointUnitPolicyScheduledGraph_succ
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) (k : Nat) :
    profiledRawJointUnitPolicyScheduledGraph A strategy initial policy bank
        seed schedule (k + 1) =
      profiledRawJointStrictGraphFlip
        (profiledRawJointUnitPolicyScheduledGraph A strategy initial policy
          bank seed schedule k) := by
  rw [profiledRawJointUnitPolicyScheduledGraph,
    profiledRawJointUnitPolicyScheduledRoot_succ]
  exact (schedule k
    (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
      seed schedule k)).target_graph A strategy initial policy bank

/-! ## Root-oriented scheduled physical slices -/

private abbrev UnitKernel
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :=
  profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
    adapter

/-- Canonical proof-side cuts oriented by the currently scheduled root. -/
noncomputable def profiledRawJointUnitPolicyRootOrientedCuts
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) : Nat → Nat :=
  rootOrientedCloseCuts (profiledRawJointPhysicalGraphTail physicalEnv base)
    hterm
      (profiledRawJointUnitPolicyScheduledGraph A strategy initial policy bank
        seed schedule)

/-- Open-record length of the root-oriented scheduled block. -/
noncomputable def profiledRawJointUnitPolicyRootOrientedOpenLength
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) (k : Nat) : Nat :=
  rootOrientedCloseOpenLength
    (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
      (profiledRawJointUnitPolicyScheduledGraph A strategy initial policy bank
        seed schedule) k

/-- Smallest remaining fixed-policy reroot invariant at the scheduled cuts.

The clock, root alternation, all zero-open mismatch cases, finite-slice
causality, and parity transfer are no longer fields.  The actual carrier owes
only:

* its original-DPA state agrees with the scheduled query entry;
* the query's finite input list has the clock-computed open length; and
* on a graph/root match, the actual matched-or-cross receiver carries the
  query target and row, equivalently the already-proved `TraceOperationalAt`.

The four transition-table constructors in
`LemPairedProfiledRawJointUnitOperationalCloseAcceptance` discharge the last
field from exact matched/cross control, target, and row equations. -/
structure ProfiledRawJointUnitPolicyFixedRerootInvariant
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) : Prop where
  entryStateAt : ∀ k : Nat,
    A.run
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv)
        (base + profiledRawJointUnitPolicyRootOrientedCuts A strategy initial
          policy bank physicalEnv base hterm seed schedule k) =
      (schedule k
        (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          seed schedule k)).entryState A strategy initial policy
  recordsLengthAt : ∀ k : Nat,
    ((schedule k
      (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k)).records A strategy initial policy bank).length =
      profiledRawJointUnitPolicyRootOrientedOpenLength A strategy initial
        policy bank physicalEnv base hterm seed schedule k
  traceOperationalAt_of_match : ∀ k : Nat,
    profiledRawJointPhysicalGraphTail physicalEnv base
        (profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy
          bank physicalEnv base hterm seed schedule k) =
      profiledRawJointUnitPolicyScheduledGraph A strategy initial policy bank
        seed schedule k →
      (schedule k
        (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          seed schedule k)).TraceOperationalAt A strategy initial policy bank
            adapter physicalEnv base
              (profiledRawJointUnitPolicyRootOrientedCuts A strategy initial
                policy bank physicalEnv base hterm seed schedule) k

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The fixed-reroot invariant closes every scheduled physical slice.  On a
mismatch, the clock theorem supplies `records = []`; on a match, the verified
selection trace supplies the literal finite record slice. -/
theorem ProfiledRawJointUnitPolicyFixedRerootInvariant.toPhysicalSlices
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo}
    {physicalEnv : EnvironmentSequence In₁ In₂} {base : Nat}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy}
    (invariant : ProfiledRawJointUnitPolicyFixedRerootInvariant A strategy
      initial policy bank adapter physicalEnv base hterm seed schedule) :
    ProfiledRawJointUnitPolicyScheduledPhysicalSlices A strategy initial policy
      bank (UnitKernel A strategy initial policy bank adapter).globalMachine
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        physicalEnv seed schedule base
          (profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy
            bank physicalEnv base hterm seed schedule) where
  sliceAt k := by
    let graphs := profiledRawJointPhysicalGraphTail physicalEnv base
    let expected := profiledRawJointUnitPolicyScheduledGraph A strategy initial
      policy bank seed schedule
    let cuts := profiledRawJointUnitPolicyRootOrientedCuts A strategy initial
      policy bank physicalEnv base hterm seed schedule
    let query := schedule k
      (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k)
    have hlength :
        (query.records A strategy initial policy bank).length =
          cuts (k + 1) - cuts k - 1 := by
      simpa [query, cuts, profiledRawJointUnitPolicyRootOrientedCuts,
        profiledRawJointUnitPolicyRootOrientedOpenLength,
        rootOrientedCloseOpenLength, graphs, expected] using
          invariant.recordsLengthAt k
    have hweak : query.TraceOperationalOrEmptyAt A strategy initial policy bank
        adapter physicalEnv base cuts k := by
      by_cases hmatch : graphs (cuts k) = expected k
      · exact Or.inr (invariant.traceOperationalAt_of_match k hmatch)
      · apply Or.inl
        apply List.length_eq_zero_iff.mp
        rw [invariant.recordsLengthAt k]
        exact rootOrientedCloseOpenLength_eq_zero_of_mismatch graphs hterm
          expected k hmatch
    exact query.physicalSlice_of_traceOperationalOrEmptyAt A strategy initial
      policy bank adapter physicalEnv base cuts k hweak
        (invariant.entryStateAt k) hlength

/-! ## Final fixed-policy recurrent endpoint -/

/-- Root-oriented slices give the exact epoch coupling.  This is the sole
fixed-policy endpoint; the maximal-only clock is not used here. -/
noncomputable def profiledRawJointUnitPolicyRootOrientedEpochCoupling
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run [])
    (invariant : ProfiledRawJointUnitPolicyFixedRerootInvariant A strategy
      initial policy bank adapter physicalEnv base hterm seed schedule) :
    A.FiniteGlobalMachineEpochCoupling
      (UnitKernel A strategy initial policy bank adapter).globalMachine
      (UnitKernel A strategy initial policy bank adapter).globalOutputOne
      (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
      physicalEnv :=
  profiledRawJointUnitPolicyScheduledSlicesEpochCoupling A strategy initial
    policy bank
      (UnitKernel A strategy initial policy bank adapter).globalMachine
      (UnitKernel A strategy initial policy bank adapter).globalOutputOne
      (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
      physicalEnv seed schedule hseed base
        (profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy
          bank physicalEnv base hterm seed schedule)
        (rootOrientedCloseCuts_strictMono
          (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
          (profiledRawJointUnitPolicyScheduledGraph A strategy initial policy
            bank seed schedule))
        rfl invariant.toPhysicalSlices

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Acceptance of the complete physical word from the smallest fixed-reroot
carrier invariant. -/
theorem profiledRawJointUnitPolicy_accepts_of_fixedRerootInvariant
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run [])
    (invariant : ProfiledRawJointUnitPolicyFixedRerootInvariant A strategy
      initial policy bank adapter physicalEnv base hterm seed schedule) :
    A.Accepts
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        physicalEnv) := by
  exact A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling
    (UnitKernel A strategy initial policy bank adapter).globalMachine
    (UnitKernel A strategy initial policy bank adapter).globalOutputOne
    (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
    physicalEnv
      (profiledRawJointUnitPolicyRootOrientedEpochCoupling A strategy initial
        policy bank adapter physicalEnv base hterm seed schedule hseed
          invariant)

end

end DetParityAutomaton

end DistributedSynthesis
