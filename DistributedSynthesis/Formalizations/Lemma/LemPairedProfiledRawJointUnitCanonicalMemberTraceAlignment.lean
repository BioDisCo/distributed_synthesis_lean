/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitCloseQueryStatePropagation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossPhysicalCutHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitStateRelativeRootOrientedAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitFixedPolicyThreadSpliceAcceptance

/-!
# Iterating exact member-aware closes along the canonical schedule

The local close-query theorem already proves the difficult checker step:
an exact strict close installs the selected target's `.first` coordinate,
whereas an exact simultaneous close installs its `.both` coordinate.  This
file iterates that theorem along the canonical physical schedule.

The entry row is no longer an independent alignment assumption.  It is
defined recursively from the proof-side close member.  Consequently an
initial checker equation, exact open-record slices, and exact closing records
produce both fields of the canonical literal-cross trace alignment.
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

/-! ## Rows forced by the acknowledged close member -/

/-- Entry row at canonical block `k`.  The first row is supplied by the
initial anchor; every later row is forced by the preceding physical close. -/
def profiledRawJointCanonicalMemberRows
    (initialRow : PairedEntryRow) (memberAt : Nat → Bool) : Nat →
    PairedEntryRow
  | 0 => initialRow
  | k + 1 => profiledRawJointCloseRowOfMember (memberAt k)

@[simp] theorem profiledRawJointCanonicalMemberRows_zero
    (initialRow : PairedEntryRow) (memberAt : Nat → Bool) :
    profiledRawJointCanonicalMemberRows initialRow memberAt 0 = initialRow :=
  rfl

@[simp] theorem profiledRawJointCanonicalMemberRows_succ
    (initialRow : PairedEntryRow) (memberAt : Nat → Bool) (k : Nat) :
    profiledRawJointCanonicalMemberRows initialRow memberAt (k + 1) =
      profiledRawJointCloseRowOfMember (memberAt k) :=
  rfl

/-! ## Exact slices with member-aware closing records -/

/-- The data still owed by an executable trace after the checker transition
has been proved locally.  In particular there is no `entryStateAt` field for
positive cuts: it is derived by induction below. -/
structure ProfiledRawJointUnitCanonicalMemberSliceAlignment
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (initialRow : PairedEntryRow) (memberAt : Nat → Bool) : Prop where
  initialState_eq :
    A.run (G.globalMachineTraceWord outputOne outputTwo physicalEnv) base =
      seed.entryStateForRow A strategy initial policy initialRow
  recordsAt : ∀ k : Nat,
    let rowAt := profiledRawJointCanonicalMemberRows initialRow memberAt
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
    let word := G.globalMachineTraceWord outputOne outputTwo physicalEnv
    omegaPrefix (OmegaWord.drop (OmegaWord.drop word base) (cuts k))
        (query.records A strategy initial policy bank).length =
      query.records A strategy initial policy bank
  closingAt : ∀ k : Nat,
    let rowAt := profiledRawJointCanonicalMemberRows initialRow memberAt
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
    let word := G.globalMachineTraceWord outputOne outputTwo physicalEnv
    OmegaWord.drop (OmegaWord.drop word base) (cuts k)
        (query.records A strategy initial policy bank).length =
      query.closingRecordForMember A strategy initial policy bank (memberAt k)

namespace ProfiledRawJointUnitCanonicalMemberSliceAlignment

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact member-aware slices force the original DPA state at every
canonical cut.  This is the recurrent simultaneous-close induction that was
missing from the canonical trace interface. -/
theorem entryStateAt
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂} {base : Nat}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {initialRow : PairedEntryRow} {memberAt : Nat → Bool}
    (alignment : ProfiledRawJointUnitCanonicalMemberSliceAlignment A strategy
      initial policy bank G outputOne outputTwo physicalEnv base hterm seed
        initialRow memberAt) (k : Nat) :
    let rowAt := profiledRawJointCanonicalMemberRows initialRow memberAt
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
      query.entryState A strategy initial policy := by
  let rowAt := profiledRawJointCanonicalMemberRows initialRow memberAt
  let schedule :=
    profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
      bank physicalEnv base hterm seed rowAt
  let cuts :=
    profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
      physicalEnv base hterm seed schedule
  let word := G.globalMachineTraceWord outputOne outputTwo physicalEnv
  let tail := OmegaWord.drop word base
  have hrelative : ∀ n : Nat,
      let root :=
        profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          seed schedule n
      let query := schedule n root
      A.runFrom (A.run word base) tail (cuts n) =
        query.entryState A strategy initial policy := by
    intro n
    induction n with
    | zero =>
        change A.run word base =
          (schedule 0 seed).entryState A strategy initial policy
        rw [alignment.initialState_eq]
        change seed.entryStateForRow A strategy initial policy initialRow =
          (profiledRawJointUnitPolicyPhysicalCloseQuery A strategy initial
            policy physicalEnv base
              (base + rootOrientedCloseNext
                (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
                (seed.graph A strategy initial policy) 0)
              initialRow seed).entryState A strategy initial policy
        cases seed <;> rfl
    | succ n ih =>
        let root :=
          profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
            bank seed schedule n
        let query := schedule n root
        have hcut : cuts n < cuts (n + 1) := by
          exact rootOrientedCloseCuts_strictMono
            (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
            (profiledRawJointUnitPolicyScheduledGraph A strategy initial policy
              bank seed schedule) (Nat.lt_succ_self n)
        have hlength :
            (query.records A strategy initial policy bank).length =
              cuts (n + 1) - cuts n - 1 := by
          rw [ProfiledRawJointUnitPolicyCloseQuery.records_length_eq_inputListLength]
          have h :=
            profiledRawJointUnitPolicyPhysicalCloseSchedule_inputListLengthAt A
              strategy initial policy bank physicalEnv base hterm seed rowAt n
          simpa [schedule, cuts, query,
            profiledRawJointUnitPolicyRootOrientedOpenLength,
            profiledRawJointUnitPolicyRootOrientedCuts,
            rootOrientedCloseOpenLength] using h
        have hnext :=
          query.runFrom_at_nextCut_eq_target_row A strategy initial policy bank
            (memberAt n) (A.run word base) tail cuts n hcut ih hlength
              (by simpa [rowAt, schedule, cuts, root, query, word, tail] using
                alignment.recordsAt n)
              (by simpa [rowAt, schedule, cuts, root, query, word, tail] using
                alignment.closingAt n)
        change A.runFrom (A.run word base) tail (cuts (n + 1)) =
          (schedule (n + 1)
            (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
              bank seed schedule (n + 1))).entryState A strategy initial policy
        rw [profiledRawJointUnitPolicyScheduledRoot_succ]
        change A.runFrom (A.run word base) tail (cuts (n + 1)) =
          (profiledRawJointUnitPolicyPhysicalCloseQuery A strategy initial
            policy physicalEnv _ _ (rowAt (n + 1))
              (query.target A strategy initial policy bank)).entryState A
                strategy initial policy
        have hrow : rowAt (n + 1) =
            profiledRawJointCloseRowOfMember (memberAt n) := rfl
        rw [hrow]
        cases htarget : query.target A strategy initial policy bank with
        | inl target =>
            rw [htarget] at hnext
            simpa [profiledRawJointUnitPolicyPhysicalCloseQuery,
              ProfiledRawJointUnitPolicyCloseQuery.entryState,
              ProfiledRawJointUnitFixedPolicyRoot.entryStateForRow] using hnext
        | inr target =>
            rw [htarget] at hnext
            simpa [profiledRawJointUnitPolicyPhysicalCloseQuery,
              ProfiledRawJointUnitPolicyCloseQuery.entryState,
              ProfiledRawJointUnitFixedPolicyRoot.entryStateForRow] using hnext
  dsimp only
  calc
    A.run word (base + cuts k) =
        A.runFrom (A.run word base) tail (cuts k) := by
      exact (A.runFrom_drop A.initial word base (cuts k)).symm
    _ = _ := hrelative k

/-- The same slice equality gives the pointwise literal-record field. -/
theorem emittedRoundAt
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂} {base : Nat}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {initialRow : PairedEntryRow} {memberAt : Nat → Bool}
    (alignment : ProfiledRawJointUnitCanonicalMemberSliceAlignment A strategy
      initial policy bank G outputOne outputTwo physicalEnv base hterm seed
        initialRow memberAt) (k j : Nat)
    (hj :
      let rowAt := profiledRawJointCanonicalMemberRows initialRow memberAt
      let schedule :=
        profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial
          policy bank physicalEnv base hterm seed rowAt
      let root :=
        profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          seed schedule k
      let query := schedule k root
      j < (query.records A strategy initial policy bank).length) :
    let rowAt := profiledRawJointCanonicalMemberRows initialRow memberAt
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
    G.globalMachineTraceWord outputOne outputTwo physicalEnv
        (base + cuts k + j) =
      (query.records A strategy initial policy bank)[j] := by
  let rowAt := profiledRawJointCanonicalMemberRows initialRow memberAt
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
  let word := G.globalMachineTraceWord outputOne outputTwo physicalEnv
  have hs := alignment.recordsAt k
  change omegaPrefix (OmegaWord.drop (OmegaWord.drop word base) (cuts k))
      (query.records A strategy initial policy bank).length =
    query.records A strategy initial policy bank at hs
  have hjq : j < (query.records A strategy initial policy bank).length := by
    simpa [rowAt, schedule, root, query] using hj
  have hp : j <
      (omegaPrefix (OmegaWord.drop (OmegaWord.drop word base) (cuts k))
        (query.records A strategy initial policy bank).length).length := by
    simpa [omegaPrefix] using hjq
  let fallback : RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
    ⟨default, default, .both, default, default⟩
  have hget := congrArg (fun xs ↦ xs.getD j fallback) hs
  change
    (omegaPrefix (OmegaWord.drop (OmegaWord.drop word base) (cuts k))
      (query.records A strategy initial policy bank).length).getD j fallback =
    (query.records A strategy initial policy bank).getD j fallback at hget
  rw [List.getD_eq_getElem _ _ hp,
    List.getD_eq_getElem _ _ hjq] at hget
  change word (base + cuts k + j) =
    (query.records A strategy initial policy bank)[j]
  simpa [omegaPrefix, OmegaWord.drop, Nat.add_assoc] using hget

/-- Exact initial state, slices, and member-aware closes are therefore a
complete canonical trace alignment. -/
noncomputable def toCanonicalTraceAlignment
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂} {base : Nat}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {initialRow : PairedEntryRow} {memberAt : Nat → Bool}
    (alignment : ProfiledRawJointUnitCanonicalMemberSliceAlignment A strategy
      initial policy bank G outputOne outputTwo physicalEnv base hterm seed
        initialRow memberAt) :
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalTraceAlignment A
      strategy initial policy bank G outputOne outputTwo physicalEnv base hterm
        seed (profiledRawJointCanonicalMemberRows initialRow memberAt) where
  entryStateAt k := alignment.entryStateAt A strategy initial policy bank k
  emittedRoundAt k j hj :=
    alignment.emittedRoundAt A strategy initial policy bank k j hj

end ProfiledRawJointUnitCanonicalMemberSliceAlignment

/-! ## State-relative suffixes after a guarded handoff -/

/-- State-relative version of the member-aware slice package.  This is the
interface needed after a phase controller has handed control to a rerooted
Unit child: the original checker starts in `physicalState`, and `word` is the
actual suffix from that handoff point. -/
structure ProfiledRawJointUnitCanonicalMemberStateRelativeSliceAlignment
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (initialRow : PairedEntryRow) (memberAt : Nat → Bool) : Prop where
  initialState_eq :
    physicalState =
      seed.entryStateForRow A strategy initial policy initialRow
  recordsAt : ∀ k : Nat,
    let rowAt := profiledRawJointCanonicalMemberRows initialRow memberAt
    let schedule :=
      profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
        bank physicalEnv 0 hterm seed rowAt
    let cuts :=
      profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
        physicalEnv 0 hterm seed schedule
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k
    let query := schedule k root
    omegaPrefix (OmegaWord.drop word (cuts k))
        (query.records A strategy initial policy bank).length =
      query.records A strategy initial policy bank
  closingAt : ∀ k : Nat,
    let rowAt := profiledRawJointCanonicalMemberRows initialRow memberAt
    let schedule :=
      profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
        bank physicalEnv 0 hterm seed rowAt
    let cuts :=
      profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
        physicalEnv 0 hterm seed schedule
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k
    let query := schedule k root
    OmegaWord.drop word (cuts k)
        (query.records A strategy initial policy bank).length =
      query.closingRecordForMember A strategy initial policy bank (memberAt k)

namespace ProfiledRawJointUnitCanonicalMemberStateRelativeSliceAlignment

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Member-aware closing records force every future checker entry state, now
relative to the checker state and word at the handoff point. -/
theorem entryStateAt
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {physicalState : A.State}
    {word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {initialRow : PairedEntryRow} {memberAt : Nat → Bool}
    (alignment :
      ProfiledRawJointUnitCanonicalMemberStateRelativeSliceAlignment A
        strategy initial policy bank physicalEnv physicalState word hterm seed
          initialRow memberAt)
    (k : Nat) :
    let rowAt := profiledRawJointCanonicalMemberRows initialRow memberAt
    let schedule :=
      profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
        bank physicalEnv 0 hterm seed rowAt
    let cuts :=
      profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
        physicalEnv 0 hterm seed schedule
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k
    let query := schedule k root
    A.runFrom physicalState word (cuts k) =
      query.entryState A strategy initial policy := by
  let rowAt := profiledRawJointCanonicalMemberRows initialRow memberAt
  let schedule :=
    profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
      bank physicalEnv 0 hterm seed rowAt
  let cuts :=
    profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
      physicalEnv 0 hterm seed schedule
  intro
  induction k with
  | zero =>
      change physicalState =
        (schedule 0 seed).entryState A strategy initial policy
      rw [alignment.initialState_eq]
      cases seed <;> rfl
  | succ n ih =>
      let root :=
        profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          seed schedule n
      let query := schedule n root
      have hcut : cuts n < cuts (n + 1) := by
        exact rootOrientedCloseCuts_strictMono
          (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
          (profiledRawJointUnitPolicyScheduledGraph A strategy initial policy
            bank seed schedule) (Nat.lt_succ_self n)
      have hlength :
          (query.records A strategy initial policy bank).length =
            cuts (n + 1) - cuts n - 1 := by
        rw [ProfiledRawJointUnitPolicyCloseQuery.records_length_eq_inputListLength]
        have h :=
          profiledRawJointUnitPolicyPhysicalCloseSchedule_inputListLengthAt A
            strategy initial policy bank physicalEnv 0 hterm seed rowAt n
        simpa [schedule, cuts, query,
          profiledRawJointUnitPolicyRootOrientedOpenLength,
          profiledRawJointUnitPolicyRootOrientedCuts,
          rootOrientedCloseOpenLength] using h
      have hnext :=
        query.runFrom_at_nextCut_eq_target_row A strategy initial policy bank
          (memberAt n) physicalState word cuts n hcut ih hlength
            (by simpa [rowAt, schedule, cuts, root, query] using
              alignment.recordsAt n)
            (by simpa [rowAt, schedule, cuts, root, query] using
              alignment.closingAt n)
      change A.runFrom physicalState word (cuts (n + 1)) =
        (schedule (n + 1)
          (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
            bank seed schedule (n + 1))).entryState A strategy initial policy
      rw [profiledRawJointUnitPolicyScheduledRoot_succ]
      change A.runFrom physicalState word (cuts (n + 1)) =
        (profiledRawJointUnitPolicyPhysicalCloseQuery A strategy initial policy
          physicalEnv _ _ (rowAt (n + 1))
            (query.target A strategy initial policy bank)).entryState A
              strategy initial policy
      have hrow : rowAt (n + 1) =
          profiledRawJointCloseRowOfMember (memberAt n) := rfl
      rw [hrow]
      cases htarget : query.target A strategy initial policy bank with
      | inl target =>
          rw [htarget] at hnext
          simpa [profiledRawJointUnitPolicyPhysicalCloseQuery,
            ProfiledRawJointUnitPolicyCloseQuery.entryState,
            ProfiledRawJointUnitFixedPolicyRoot.entryStateForRow] using hnext
      | inr target =>
          rw [htarget] at hnext
          simpa [profiledRawJointUnitPolicyPhysicalCloseQuery,
            ProfiledRawJointUnitPolicyCloseQuery.entryState,
            ProfiledRawJointUnitFixedPolicyRoot.entryStateForRow] using hnext

/-- The state-relative member slices provide the older root-oriented
alignment automatically. -/
noncomputable def toRootOrientedStateRelativeAlignment
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {physicalState : A.State}
    {word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {initialRow : PairedEntryRow} {memberAt : Nat → Bool}
    (alignment :
      ProfiledRawJointUnitCanonicalMemberStateRelativeSliceAlignment A
        strategy initial policy bank physicalEnv physicalState word hterm seed
          initialRow memberAt) :
    let rowAt := profiledRawJointCanonicalMemberRows initialRow memberAt
    let schedule :=
      profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
        bank physicalEnv 0 hterm seed rowAt
    ProfiledRawJointUnitPolicyRootOrientedStateRelativeAlignment A strategy
      initial policy bank physicalEnv physicalState word hterm seed schedule := by
  dsimp only
  let rowAt := profiledRawJointCanonicalMemberRows initialRow memberAt
  let schedule :=
    profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
      bank physicalEnv 0 hterm seed rowAt
  let cuts :=
    profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
      physicalEnv 0 hterm seed schedule
  refine {
    entryStateAt := fun k ↦
      alignment.entryStateAt A strategy initial policy bank k
    recordsLengthAt := ?_
    recordsAt_of_match := ?_ }
  · intro k
    dsimp only
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k
    let query := schedule k root
    rw [ProfiledRawJointUnitPolicyCloseQuery.records_length_eq_inputListLength]
    have h :=
      profiledRawJointUnitPolicyPhysicalCloseSchedule_inputListLengthAt A
        strategy initial policy bank physicalEnv 0 hterm seed rowAt k
    simpa [schedule, cuts, root, query,
      profiledRawJointUnitPolicyRootOrientedOpenLength,
      profiledRawJointUnitPolicyRootOrientedCuts,
      rootOrientedCloseOpenLength] using h
  · intro k
    dsimp only
    intro _
    simpa [rowAt, schedule, cuts] using alignment.recordsAt k

/-- Direct state-relative acceptance endpoint for the rerooted Unit suffix. -/
theorem acceptsFrom
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {physicalState : A.State}
    {word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {initialRow : PairedEntryRow} {memberAt : Nat → Bool}
    (alignment :
      ProfiledRawJointUnitCanonicalMemberStateRelativeSliceAlignment A
        strategy initial policy bank physicalEnv physicalState word hterm seed
          initialRow memberAt)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run []) :
    A.AcceptsFrom physicalState word := by
  exact
    (alignment.toRootOrientedStateRelativeAlignment A strategy initial policy
      bank).acceptsFrom A strategy initial policy bank hseed

/-- Acceptance after a finite checked prefix of the selected policy.  The
member-aware schedule starts at the current post-handoff root, while `chain`
retains its finite lineage from the genuinely accepted policy root. -/
theorem acceptsFrom_of_prefix
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {physicalState : A.State}
    {word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0)}
    {acceptedSeed current :
      ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A) policy}
    {initialRow : PairedEntryRow} {memberAt : Nat → Bool}
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy acceptedSeed =
      policy.run [])
    (chain : ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix A policy
      acceptedSeed current)
    (alignment :
      ProfiledRawJointUnitCanonicalMemberStateRelativeSliceAlignment A
        strategy initial policy bank physicalEnv physicalState word hterm
          current initialRow memberAt) :
    A.AcceptsFrom physicalState word := by
  let rowAt := profiledRawJointCanonicalMemberRows initialRow memberAt
  let schedule :=
    profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial policy
      bank physicalEnv 0 hterm current rowAt
  let cuts :=
    profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
      physicalEnv 0 hterm current schedule
  let future :=
    profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
      current schedule
  let oldAlignment :=
    alignment.toRootOrientedStateRelativeAlignment A strategy initial policy
      bank
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
  · exact rootOrientedCloseCuts_strictMono
      (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
      (profiledRawJointUnitPolicyScheduledGraph A strategy initial policy bank
        current schedule)
  · rfl
  · intro k
    have hslice := oldAlignment.sliceAt A strategy initial policy bank k
    have hblock := hslice.cutBlockMin_eq_blockPriority A strategy initial
      policy bank
    have htarget :=
      (schedule k
        (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          current schedule k)).targetPriority A strategy initial policy bank
    simpa [oldAlignment, future, cuts, schedule] using
      hblock.trans htarget.symm

end ProfiledRawJointUnitCanonicalMemberStateRelativeSliceAlignment

end

end DetParityAutomaton

end DistributedSynthesis
