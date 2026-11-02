/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPersistentStrictCutCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitStateRelativeOperationalCloseAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitFixedPolicyThreadSpliceAcceptance

/-!
# Acceptance of a persistent strict Unit tail

The concrete Unit carrier and the canonical close checker now advance on the
same maximal operational cuts.  This file packages their simultaneous
induction and exposes the state-relative acceptance endpoint needed after a
guarded fresh handoff.
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

private abbrev UnitKernel
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :=
  profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
    adapter

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Starting in the `.first` state of the seed root, the original checker is
in the `.first` state of the recursively threaded root at every strict cut. -/
theorem profiledRawJointUnitPersistentStrict_checkerStateAt
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (origin : (UnitKernel A strategy initial policy bank adapter).globalMachine.State)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 n ≠ .both)
    (zero : ProfiledRawJointUnitPersistentStrictControlAt A strategy initial
      policy bank adapter origin physicalEnv hterm .first seed 0)
    (physicalState : A.State)
    (hphysicalState : physicalState =
      seed.entryStateForRow A strategy initial policy .first) :
    let cuts := operationalCloseCuts
      (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
    let word :=
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        origin).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv
    ∀ k : Nat,
      A.runFrom physicalState word (cuts k) =
        (profiledRawJointUnitPersistentStrictRootAt A strategy initial policy
          bank physicalEnv hterm .first seed k).entryStateForRow A strategy initial
            policy .first := by
  dsimp only
  let graphs := profiledRawJointPhysicalGraphTail physicalEnv 0
  let cuts := operationalCloseCuts graphs hterm
  let word :=
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      origin).globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        physicalEnv
  have carrierAt := zero.all A strategy initial policy bank hnoboth
  intro k
  induction k with
  | zero =>
      simpa [cuts, word, operationalCloseCuts_zero,
        profiledRawJointUnitPersistentStrictRootAt,
        profiledRawJointUnitPolicyOperationalThreadRoot,
        DetParityAutomaton.runFrom] using hphysicalState
  | succ k ih =>
      let query := profiledRawJointUnitPersistentStrictQueryAt A strategy
        initial policy bank physicalEnv hterm .first seed k
      have hrecords :=
        (carrierAt k).records_and_closing A strategy initial policy bank
      have hentry : A.runFrom physicalState word (cuts k) =
          query.entryState A strategy initial policy := by
        exact ih.trans
          (profiledRawJointUnitPersistentStrictQueryAt_entryState A strategy
            initial policy bank physicalEnv hterm .first seed k).symm
      have hlength :
          (query.records A strategy initial policy bank).length =
            cuts (k + 1) - cuts k - 1 := by
        simpa [query, cuts, graphs] using
          (profiledRawJointUnitPersistentStrictQueryAt_records_length A
            strategy initial policy bank physicalEnv hterm .first seed k)
      have hcut : cuts k < cuts (k + 1) :=
        operationalCloseCuts_strictMono graphs hterm (Nat.lt_succ_self k)
      have hstep :=
        query.runFrom_at_nextCut_eq_target_first A strategy initial policy bank
          physicalState word cuts k hcut hentry hlength
            (by simpa [query, cuts, word, graphs] using hrecords.1)
            (by simpa [query, cuts, word, graphs] using hrecords.2)
      rw [profiledRawJointUnitPersistentStrictRootAt_succ A strategy initial
        policy bank physicalEnv hterm .first seed k]
      exact hstep

/-- The concrete all-strict carrier supplies the complete state-relative
canonical operational alignment. -/
theorem profiledRawJointUnitPersistentStrict_stateRelativeAlignment
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (origin : (UnitKernel A strategy initial policy bank adapter).globalMachine.State)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 n ≠ .both)
    (zero : ProfiledRawJointUnitPersistentStrictControlAt A strategy initial
      policy bank adapter origin physicalEnv hterm .first seed 0)
    (physicalState : A.State)
    (hphysicalState : physicalState =
      seed.entryStateForRow A strategy initial policy .first) :
    let word :=
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        origin).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv
    ProfiledRawJointUnitPolicyCanonicalOperationalStateRelativeAlignment A
      strategy initial policy bank physicalEnv physicalState word hterm seed
        (fun _ ↦ .first) := by
  dsimp only
  let word :=
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      origin).globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        physicalEnv
  let schedule :=
    profiledRawJointUnitPolicyOperationalCloseSchedule A strategy initial
      policy physicalEnv 0 hterm (fun _ ↦ .first)
  let cuts := operationalCloseCuts
    (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
  have carrierAt := zero.all A strategy initial policy bank hnoboth
  have checkerAt := profiledRawJointUnitPersistentStrict_checkerStateAt A
    strategy initial policy bank adapter origin physicalEnv hterm seed
      hnoboth zero physicalState hphysicalState
  refine {
    entryStateAt := ?_
    recordsAt_of_strict := ?_ }
  · intro k
    dsimp only
    have hscheduled :
        profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
            seed schedule k =
          profiledRawJointUnitPersistentStrictRootAt A strategy initial policy
            bank physicalEnv hterm .first seed k := by
      simpa [schedule, profiledRawJointUnitPersistentStrictRootAt] using
        (profiledRawJointUnitPolicyScheduledRoot_operationalCloseSchedule A
          strategy initial policy bank physicalEnv 0 hterm seed
            (fun _ ↦ .first) k)
    rw [hscheduled]
    have hentry := profiledRawJointUnitPersistentStrictQueryAt_entryState A
      strategy initial policy bank physicalEnv hterm .first seed k
    exact (checkerAt k).trans (by
      simpa [schedule, cuts, word,
        profiledRawJointUnitPolicyOperationalCloseSchedule,
        profiledRawJointUnitPersistentStrictQueryAt] using hentry.symm)
  · intro k
    dsimp only
    intro _hstrict
    have hscheduled :
        profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
            seed schedule k =
          profiledRawJointUnitPersistentStrictRootAt A strategy initial policy
            bank physicalEnv hterm .first seed k := by
      simpa [schedule, profiledRawJointUnitPersistentStrictRootAt] using
        (profiledRawJointUnitPolicyScheduledRoot_operationalCloseSchedule A
          strategy initial policy bank physicalEnv 0 hterm seed
            (fun _ ↦ .first) k)
    rw [hscheduled]
    have hrecords :=
      (carrierAt k).records_and_closing A strategy initial policy bank
    simpa [schedule, cuts, word,
      profiledRawJointUnitPolicyOperationalCloseSchedule,
      profiledRawJointUnitPersistentStrictQueryAt] using hrecords.1

/-- State-relative acceptance of an all-strict persistent Unit tail. -/
theorem profiledRawJointUnitPersistentStrict_acceptsFrom
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (origin : (UnitKernel A strategy initial policy bank adapter).globalMachine.State)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 n ≠ .both)
    (zero : ProfiledRawJointUnitPersistentStrictControlAt A strategy initial
      policy bank adapter origin physicalEnv hterm .first seed 0)
    (physicalState : A.State)
    (hphysicalState : physicalState =
      seed.entryStateForRow A strategy initial policy .first)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run []) :
    let word :=
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        origin).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv
    A.AcceptsFrom physicalState word := by
  dsimp only
  let word :=
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      origin).globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        physicalEnv
  have alignment :=
    profiledRawJointUnitPersistentStrict_stateRelativeAlignment A strategy
      initial policy bank adapter origin physicalEnv hterm seed hnoboth
        zero physicalState hphysicalState
  exact alignment.acceptsFrom A strategy initial policy bank hseed

/-- State-relative acceptance after a finite checked prefix of the selected
policy.  The concrete strict carrier starts at `current`; `chain` remembers
that this root is a finite descendant of the genuinely accepted policy root.
This is the form needed by an activated recurrent handoff. -/
theorem profiledRawJointUnitPersistentStrict_acceptsFrom_of_prefix
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (origin : (UnitKernel A strategy initial policy bank adapter).globalMachine.State)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (acceptedSeed current :
      ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A) policy)
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 n ≠ .both)
    (zero : ProfiledRawJointUnitPersistentStrictControlAt A strategy initial
      policy bank adapter origin physicalEnv hterm .first current 0)
    (physicalState : A.State)
    (hphysicalState : physicalState =
      current.entryStateForRow A strategy initial policy .first)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy acceptedSeed =
      policy.run [])
    (chain : ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix A policy
      acceptedSeed current) :
    let word :=
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        origin).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv
    A.AcceptsFrom physicalState word := by
  dsimp only
  let word :=
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      origin).globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        physicalEnv
  let rowAt : Nat → PairedEntryRow := fun _ ↦ .first
  let schedule :=
    profiledRawJointUnitPolicyOperationalCloseSchedule A strategy initial
      policy physicalEnv 0 hterm rowAt
  let cuts := operationalCloseCuts
    (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
  let future :=
    profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
      current schedule
  have alignment :=
    profiledRawJointUnitPersistentStrict_stateRelativeAlignment A strategy
      initial policy bank adapter origin physicalEnv hterm current hnoboth zero
        physicalState hphysicalState
  have hfutureStep : ∀ n : Nat,
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep A policy
        (future n) (future (n + 1)) := by
    intro n
    simpa [future] using
      (schedule n
        (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          current schedule n)).alternatingStep A strategy initial policy bank
  apply chain.physicalTail_acceptsFrom_of_futureRootPriority A hseed future rfl
    hfutureStep physicalState word cuts
  · exact operationalCloseCuts_strictMono
      (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
  · exact operationalCloseCuts_zero
      (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
  · intro k
    have hslice := alignment.sliceAt A strategy initial policy bank k
    have hblock := hslice.cutBlockMin_eq_blockPriority A strategy initial
      policy bank
    have htarget :=
      (schedule k
        (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          current schedule k)).targetPriority A strategy initial policy bank
    simpa [future, cuts, schedule, rowAt, word] using
      hblock.trans htarget.symm

/-- Fresh-right specialization of persistent strict acceptance. -/
theorem profiledRawJointUnitFreshMatchedRight_persistentStrict_acceptsFrom
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 n ≠ .both)
    (hgraph : (physicalEnv 0).graph = .right)
    (hseed : source.state = policy.run []) :
    A.AcceptsFrom (pairedCodeStateForRow A .first source.slot.1.1)
      (((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        (profiledRawJointUnitFreshMatchedRightState A strategy initial policy
          bank adapter source .first oldOutputOne oldOutputTwo)
        ).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv) := by
  let fresh := profiledRawJointUnitFreshMatchedRightState A strategy initial
    policy bank adapter source .first oldOutputOne oldOutputTwo
  have zero := profiledRawJointUnitPersistentStrictControlAt_zero_freshRight A
    strategy initial policy bank adapter source oldOutputOne oldOutputTwo
      physicalEnv hterm .first hgraph
  exact profiledRawJointUnitPersistentStrict_acceptsFrom A strategy initial
    policy bank adapter fresh physicalEnv hterm (.inl source) hnoboth zero
      (pairedCodeStateForRow A .first source.slot.1.1) rfl hseed

/-- Fresh-left mirror. -/
theorem profiledRawJointUnitFreshMatchedLeft_persistentStrict_acceptsFrom
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 n ≠ .both)
    (hgraph : (physicalEnv 0).graph = .left)
    (hseed : source.state = policy.run []) :
    A.AcceptsFrom (pairedCodeStateForRow A .first source.slot.1.1)
      (((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        (profiledRawJointUnitFreshMatchedLeftState A strategy initial policy
          bank adapter source .first oldOutputOne oldOutputTwo)
        ).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv) := by
  let fresh := profiledRawJointUnitFreshMatchedLeftState A strategy initial
    policy bank adapter source .first oldOutputOne oldOutputTwo
  have zero := profiledRawJointUnitPersistentStrictControlAt_zero_freshLeft A
    strategy initial policy bank adapter source oldOutputOne oldOutputTwo
      physicalEnv hterm .first hgraph
  exact profiledRawJointUnitPersistentStrict_acceptsFrom A strategy initial
    policy bank adapter fresh physicalEnv hterm (.inr source) hnoboth zero
      (pairedCodeStateForRow A .first source.slot.1.1) rfl hseed

/-- Matched-left entry specialization.  This is the state naturally left by
the preceding left block when the all-strict suffix starts with right. -/
theorem profiledRawJointUnitMatchedLeft_persistentStrict_acceptsFrom
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 n ≠ .both)
    (hgraph : (physicalEnv 0).graph = .right)
    (htarget : profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
      policy bank left = source)
    (hrow : left.2.1 = .first)
    (hseed : source.state = policy.run []) :
    A.AcceptsFrom (pairedCodeStateForRow A .first source.slot.1.1)
      (((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        (profiledRawJointUnitMatchedLeftState A strategy initial policy bank
          adapter left owner oldOutputOne oldOutputTwo)
        ).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv) := by
  let matched := profiledRawJointUnitMatchedLeftState A strategy initial policy
    bank adapter left owner oldOutputOne oldOutputTwo
  have zero :=
    profiledRawJointUnitPersistentStrictControlAt_zero_matchedLeft A strategy
      initial policy bank adapter left owner oldOutputOne oldOutputTwo
        physicalEnv hterm source .first hgraph htarget hrow
  exact profiledRawJointUnitPersistentStrict_acceptsFrom A strategy initial
    policy bank adapter matched physicalEnv hterm (.inl source) hnoboth zero
      (pairedCodeStateForRow A .first source.slot.1.1) rfl hseed

/-- Matched-right mirror. -/
theorem profiledRawJointUnitMatchedRight_persistentStrict_acceptsFrom
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 n ≠ .both)
    (hgraph : (physicalEnv 0).graph = .left)
    (htarget : profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
      policy bank right = source)
    (hrow : right.2.1 = .first)
    (hseed : source.state = policy.run []) :
    A.AcceptsFrom (pairedCodeStateForRow A .first source.slot.1.1)
      (((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        (profiledRawJointUnitMatchedRightState A strategy initial policy bank
          adapter owner right oldOutputOne oldOutputTwo)
        ).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv) := by
  let matched := profiledRawJointUnitMatchedRightState A strategy initial policy
    bank adapter owner right oldOutputOne oldOutputTwo
  have zero :=
    profiledRawJointUnitPersistentStrictControlAt_zero_matchedRight A strategy
      initial policy bank adapter owner right oldOutputOne oldOutputTwo
        physicalEnv hterm source .first hgraph htarget hrow
  exact profiledRawJointUnitPersistentStrict_acceptsFrom A strategy initial
    policy bank adapter matched physicalEnv hterm (.inr source) hnoboth zero
      (pairedCodeStateForRow A .first source.slot.1.1) rfl hseed

end

end

end DetParityAutomaton

end DistributedSynthesis
