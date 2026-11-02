/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitFixedTailOperational
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPolicyRecurrentTrace

/-!
# Operational construction of raw-joint scheduled physical slices

This file turns proof-side control alignment at a scheduled cut into the exact
physical word slice required by
`ProfiledRawJointUnitPolicyScheduledPhysicalSlices`.  It uses only finite
prefix causality, re-rooting, and the fixed-tail trace identification.  No
orientation or leader flag is added to either local controller.

The final section also records a necessary condition of the existing
one-query-per-cut interface: the represented part of every cut segment is
graph-homogeneous.  Consequently an automatic strict-gap cut containing two
or more simultaneous suffix rounds cannot satisfy this interface without
refining the cuts.
-/

namespace DistributedSynthesis

universe u v w x y s i₁ i₂ e₁ e₂

namespace FiniteGlobalRoundMachine

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)

/-- A global state after `n` rounds depends only on the first `n`
environment rounds. -/
theorem globalStateTrace_eq_of_forall_lt
    (left right : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    (∀ k : Nat, k < n → left k = right k) →
      G.globalStateTrace left n = G.globalStateTrace right n := by
  intro n hprefix
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [globalStateTrace_succ, globalStateTrace_succ,
        ih (fun k hk ↦ hprefix k (by omega)), hprefix n (by omega)]

/-- Moore-timed global words have the same finite prefix under equal finite
environment prefixes. -/
theorem omegaPrefix_globalMachineTraceWord_eq_of_forall_lt
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (left right : EnvironmentSequence In₁ In₂) (n : Nat)
    (hprefix : ∀ k : Nat, k < n → left k = right k) :
    DetParityAutomaton.omegaPrefix
        (G.globalMachineTraceWord outputOne outputTwo left) n =
      DetParityAutomaton.omegaPrefix
        (G.globalMachineTraceWord outputOne outputTwo right) n := by
  apply List.ext_get
  · simp [DetParityAutomaton.omegaPrefix]
  · intro k hkLeft hkRight
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [DetParityAutomaton.omegaPrefix, List.getElem_ofFn]
    have hk : k < n := by
      simpa [DetParityAutomaton.omegaPrefix] using hkRight
    have hstate := G.globalStateTrace_eq_of_forall_lt left right (k + 1)
      (fun j hj ↦ hprefix j (by omega))
    simp only [globalMachineTraceWord]
    rw [hprefix k hk, hstate]

end FiniteGlobalRoundMachine

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
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :=
  profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
    adapter

/-! ## One scheduled right slice -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A fresh matched-right control at an actual cut, together with equality of
the finite environment prefix, supplies the complete right `PhysicalSlice`.
The DPA entry state and numerical gap are explicit and are not inferred from
controller data. -/
theorem profiledRawJointUnitRightPhysicalSlice_of_freshMatched
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (hcontrol :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
          physicalEnv (base + cuts k) =
        profiledRawJointUnitFreshMatchedRightState A strategy initial policy
          bank adapter source row oldOutputOne oldOutputTwo)
    (henv : ∀ j : Nat, j < past.length →
      OmegaWord.drop physicalEnv (base + cuts k) j =
        profiledRawJointUnitStrictRightEnvironment
          (omegaOfList (past ++ [move])) j)
    (hstate :
      A.run
          ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
              (UnitKernel A strategy initial policy bank adapter).globalOutputOne
              (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
              physicalEnv)
          (base + cuts k) = pairedCodeStateForRow A row source.slot.1.1)
    (hlength : past.length = cuts (k + 1) - cuts k - 1) :
    (ProfiledRawJointUnitPolicyCloseQuery.right source row past move).PhysicalSlice
      A strategy initial policy bank
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv) base cuts k := by
  refine ⟨hstate, ?_, ?_⟩
  · simpa [ProfiledRawJointUnitPolicyCloseQuery.records,
      profiledRawJointUnitRightPhysicalPrefixRecords, omegaPrefix] using hlength
  · let G := (UnitKernel A strategy initial policy bank adapter).globalMachine
    let outputOne :=
      (UnitKernel A strategy initial policy bank adapter).globalOutputOne
    let outputTwo :=
      (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
    let blockEnv : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
    have hreroot := G.reroot_globalMachineTraceWord_drop outputOne outputTwo
      physicalEnv (base + cuts k)
    rw [hcontrol] at hreroot
    have hcausal :=
      (G.reroot
        (profiledRawJointUnitFreshMatchedRightState A strategy initial policy
          bank adapter source row oldOutputOne oldOutputTwo)).omegaPrefix_globalMachineTraceWord_eq_of_forall_lt
          outputOne outputTwo
          (OmegaWord.drop physicalEnv (base + cuts k))
          (profiledRawJointUnitStrictRightEnvironment blockEnv) past.length
          (by simpa [blockEnv] using henv)
    rw [profiledRawJointUnitFreshMatchedRight_traceWord] at hcausal
    rw [← hreroot]
    simp only [ProfiledRawJointUnitPolicyCloseQuery.records]
    rw [show (profiledRawJointUnitRightPhysicalPrefixRecords A row
          (omegaPrefix
            (profiledRawJointUnitRightPolicyPlay A strategy initial policy bank
              source past move) past.length)).length = past.length by
      simp [profiledRawJointUnitRightPhysicalPrefixRecords, omegaPrefix]]
    rw [hcausal]
    simp [profiledRawJointUnitRightPhysicalPrefixRecords,
      profiledRawJointUnitRightPolicyPlay,
      profiledRawJointUnitRightPolicyOmegaPlay, blockEnv, omegaPrefix,
      Function.comp_def]

/-! ## One scheduled left slice -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Matched-left mirror of
`profiledRawJointUnitRightPhysicalSlice_of_freshMatched`. -/
theorem profiledRawJointUnitLeftPhysicalSlice_of_freshMatched
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (hcontrol :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
          physicalEnv (base + cuts k) =
        profiledRawJointUnitFreshMatchedLeftState A strategy initial policy bank
          adapter source row oldOutputOne oldOutputTwo)
    (henv : ∀ j : Nat, j < past.length →
      OmegaWord.drop physicalEnv (base + cuts k) j =
        profiledRawJointUnitStrictLeftEnvironment
          (omegaOfList (past ++ [move])) j)
    (hstate :
      A.run
          ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
              (UnitKernel A strategy initial policy bank adapter).globalOutputOne
              (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
              physicalEnv)
          (base + cuts k) = pairedCodeStateForRow A row source.slot.1.1)
    (hlength : past.length = cuts (k + 1) - cuts k - 1) :
    (ProfiledRawJointUnitPolicyCloseQuery.left source row past move).PhysicalSlice
      A strategy initial policy bank
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv) base cuts k := by
  refine ⟨hstate, ?_, ?_⟩
  · simpa [ProfiledRawJointUnitPolicyCloseQuery.records,
      profiledRawJointUnitLeftPhysicalPrefixRecords, omegaPrefix] using hlength
  · let G := (UnitKernel A strategy initial policy bank adapter).globalMachine
    let outputOne :=
      (UnitKernel A strategy initial policy bank adapter).globalOutputOne
    let outputTwo :=
      (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
    let blockEnv : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
    have hreroot := G.reroot_globalMachineTraceWord_drop outputOne outputTwo
      physicalEnv (base + cuts k)
    rw [hcontrol] at hreroot
    have hcausal :=
      (G.reroot
        (profiledRawJointUnitFreshMatchedLeftState A strategy initial policy
          bank adapter source row oldOutputOne oldOutputTwo)).omegaPrefix_globalMachineTraceWord_eq_of_forall_lt
          outputOne outputTwo
          (OmegaWord.drop physicalEnv (base + cuts k))
          (profiledRawJointUnitStrictLeftEnvironment blockEnv) past.length
          (by simpa [blockEnv] using henv)
    rw [profiledRawJointUnitFreshMatchedLeft_traceWord] at hcausal
    rw [← hreroot]
    simp only [ProfiledRawJointUnitPolicyCloseQuery.records]
    rw [show (profiledRawJointUnitLeftPhysicalPrefixRecords A row
          (omegaPrefix
            (profiledRawJointUnitLeftPolicyPlay A strategy initial policy bank
              source past move) past.length)).length = past.length by
      simp [profiledRawJointUnitLeftPhysicalPrefixRecords, omegaPrefix]]
    rw [hcausal]
    simp [profiledRawJointUnitLeftPhysicalPrefixRecords,
      profiledRawJointUnitLeftPolicyPlay,
      profiledRawJointUnitLeftPolicyOmegaPlay, blockEnv, omegaPrefix,
      Function.comp_def]

/-! ## Schedule-level operational residual -/

/-- Proof-side control and finite-environment alignment for one typed close
query. -/
def ProfiledRawJointUnitPolicyCloseQuery.OperationalAt
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat) : Prop :=
  match query with
  | .right source row past move =>
      ∃ oldOutputOne oldOutputTwo,
        (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
            physicalEnv (base + cuts k) =
          profiledRawJointUnitFreshMatchedRightState A strategy initial policy
            bank adapter source row oldOutputOne oldOutputTwo ∧
        ∀ j : Nat, j < past.length →
          OmegaWord.drop physicalEnv (base + cuts k) j =
            profiledRawJointUnitStrictRightEnvironment
              (omegaOfList (past ++ [move])) j
  | .left source row past move =>
      ∃ oldOutputOne oldOutputTwo,
        (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
            physicalEnv (base + cuts k) =
          profiledRawJointUnitFreshMatchedLeftState A strategy initial policy
            bank adapter source row oldOutputOne oldOutputTwo ∧
        ∀ j : Nat, j < past.length →
          OmegaWord.drop physicalEnv (base + cuts k) j =
            profiledRawJointUnitStrictLeftEnvironment
              (omegaOfList (past ++ [move])) j

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- One typed operational query supplies its exact physical slice. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.physicalSlice_of_operationalAt
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (hoperational : query.OperationalAt A strategy initial policy bank adapter
      physicalEnv base cuts k)
    (hentry :
      A.run
          ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv)
          (base + cuts k) = query.entryState A strategy initial policy)
    (hlength : (query.records A strategy initial policy bank).length =
      cuts (k + 1) - cuts k - 1) :
    query.PhysicalSlice A strategy initial policy bank
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        physicalEnv) base cuts k := by
  cases query with
  | right source row past move =>
      obtain ⟨oldOutputOne, oldOutputTwo, hcontrol, henv⟩ := hoperational
      apply profiledRawJointUnitRightPhysicalSlice_of_freshMatched A strategy
        initial policy bank adapter source row past move oldOutputOne
          oldOutputTwo physicalEnv base cuts k hcontrol henv
      · simpa [ProfiledRawJointUnitPolicyCloseQuery.entryState] using hentry
      · simpa [ProfiledRawJointUnitPolicyCloseQuery.records,
          profiledRawJointUnitRightPhysicalPrefixRecords, omegaPrefix] using
            hlength
  | left source row past move =>
      obtain ⟨oldOutputOne, oldOutputTwo, hcontrol, henv⟩ := hoperational
      apply profiledRawJointUnitLeftPhysicalSlice_of_freshMatched A strategy
        initial policy bank adapter source row past move oldOutputOne
          oldOutputTwo physicalEnv base cuts k hcontrol henv
      · simpa [ProfiledRawJointUnitPolicyCloseQuery.entryState] using hentry
      · simpa [ProfiledRawJointUnitPolicyCloseQuery.records,
          profiledRawJointUnitLeftPhysicalPrefixRecords, omegaPrefix] using
            hlength

/-- The exact operational facts still owed by the completed carrier at the
scheduled cuts.  Output-word equality is deliberately absent: the two
per-orientation theorems above derive it from these fields.

`controlAndEnvironmentAt` is proof-side indexed by the already-typed close
query.  It does not add a direction, leader, or row component to either local
machine. -/
structure ProfiledRawJointUnitPolicyScheduledOperationalAlignment
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (base : Nat) (cuts : Nat → Nat) : Prop where
  entryStateAt : ∀ k : Nat,
    A.run
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv)
        (base + cuts k) =
      (schedule k
        (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          seed schedule k)).entryState A strategy initial policy
  recordsLengthAt : ∀ k : Nat,
    ((schedule k
      (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k)).records A strategy initial policy bank).length =
      cuts (k + 1) - cuts k - 1
  controlAndEnvironmentAt : ∀ k : Nat,
    (schedule k
      (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k)).OperationalAt A strategy initial policy bank adapter
          physicalEnv base cuts k

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The operational alignment is sufficient for the complete scheduled slice
family.  Thus no separate global output-agreement field remains. -/
theorem ProfiledRawJointUnitPolicyScheduledOperationalAlignment.toPhysicalSlices
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy}
    {base : Nat} {cuts : Nat → Nat}
    (alignment : ProfiledRawJointUnitPolicyScheduledOperationalAlignment A
      strategy initial policy bank adapter physicalEnv seed schedule base cuts) :
    ProfiledRawJointUnitPolicyScheduledPhysicalSlices A strategy initial policy
      bank (UnitKernel A strategy initial policy bank adapter).globalMachine
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        physicalEnv seed schedule base cuts where
  sliceAt k :=
    (schedule k
      (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k)).physicalSlice_of_operationalAt A strategy initial
          policy bank adapter physicalEnv base cuts k
            (alignment.controlAndEnvironmentAt k) (alignment.entryStateAt k)
              (alignment.recordsLengthAt k)

/-! ## Necessary graph shape of the one-query interface -/

/-- Strict graph orientation represented by a close query. -/
def ProfiledRawJointUnitPolicyCloseQuery.graph
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) : Graph :=
  match query with
  | .right .. => .right
  | .left .. => .left

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every environment round represented by one query's records has its single
strict orientation.  This follows from `PhysicalSlice` itself, independently
of the positive operational constructor above. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.PhysicalSlice.graphs_eq_replicate
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (slice : query.PhysicalSlice A strategy initial policy bank
      (G.globalMachineTraceWord outputOne outputTwo physicalEnv) base cuts k) :
    (omegaPrefix (OmegaWord.drop physicalEnv (base + cuts k))
        (query.records A strategy initial policy bank).length).map
          EnvironmentRound.graph =
      List.replicate (query.records A strategy initial policy bank).length
        (query.graph A strategy initial policy) := by
  have hgraphs := congrArg
    (List.map (fun record : RoundRecord In₁ In₂ Graph Out₁ Out₂ ↦ record.graph))
    slice.records_eq_slice
  cases query with
  | right source row past move =>
      cases row <;>
        simpa [ProfiledRawJointUnitPolicyCloseQuery.records,
          ProfiledRawJointUnitPolicyCloseQuery.graph,
          profiledRawJointUnitRightPhysicalPrefixRecords,
          pairedRightRecordForRow, rightRoundRecord, omegaPrefix,
          OmegaWord.drop, FiniteGlobalRoundMachine.globalMachineTraceWord,
          Function.comp_def] using hgraphs
  | left source row past move =>
      cases row <;>
        simpa [ProfiledRawJointUnitPolicyCloseQuery.records,
          ProfiledRawJointUnitPolicyCloseQuery.graph,
          profiledRawJointUnitLeftPhysicalPrefixRecords,
          pairedLeftRecordForRow, leftRoundRecord, omegaPrefix,
          OmegaWord.drop, FiniteGlobalRoundMachine.globalMachineTraceWord,
          Function.comp_def] using hgraphs

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Hence no simultaneous round may occur before the one excluded closing
round of a scheduled physical slice. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.PhysicalSlice.both_not_mem
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (slice : query.PhysicalSlice A strategy initial policy bank
      (G.globalMachineTraceWord outputOne outputTwo physicalEnv) base cuts k) :
    .both ∉
      (omegaPrefix (OmegaWord.drop physicalEnv (base + cuts k))
        (query.records A strategy initial policy bank).length).map
          EnvironmentRound.graph := by
  rw [slice.graphs_eq_replicate A strategy initial policy bank]
  cases query <;>
    simp [ProfiledRawJointUnitPolicyCloseQuery.graph]

end

end DetParityAutomaton

end DistributedSynthesis
