/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitCloseQueryStatePropagation

/-!
# Persistent strict-reversal carrier for one fixed Unit policy

This file proves the concrete operational-cut invariant after a guarded close
has installed one fresh Unit-policy root.  The first local ingredient is a
finite-prefix packet: a rerooted matched trace gives both the query's open
record slice and its physical closing record.  It is shared by the fresh and
the two alternating matched cut shapes.
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

/-! ## Finite-prefix record packets -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A right-oriented reroot trace supplies both the open query slice and the
strict closing record on the actual physical word. -/
theorem profiledRawJointUnitRightQuery_records_and_closing_of_rerootTrace
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (origin current :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.State)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (cut : Nat)
    (hcontrol :
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        origin).globalStateTrace physicalEnv cut = current)
    (henv : ∀ j : Nat, j < past.length + 1 →
      OmegaWord.drop physicalEnv cut j =
        profiledRawJointUnitStrictRightEnvironment
          (omegaOfList (past ++ [move])) j)
    (htrace :
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        current).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          (profiledRawJointUnitStrictRightEnvironment
            (omegaOfList (past ++ [move]))) =
        fun n ↦ pairedRightRecordForRow row
          (profiledRawJointUnitRightPhysicalLetter A
            (profiledRawJointUnitRightPolicyOmegaPlay A bank source
              (omegaOfList (past ++ [move])) n))) :
    let query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
        (.inl source) := .right source row past move
    let word :=
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        origin).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv
    omegaPrefix (OmegaWord.drop word cut)
        (query.records A strategy initial policy bank).length =
      query.records A strategy initial policy bank ∧
    OmegaWord.drop word cut
        (query.records A strategy initial policy bank).length =
      query.strictClosingRecord A strategy initial policy bank := by
  dsimp only
  let G := (UnitKernel A strategy initial policy bank adapter).globalMachine
  let R := G.reroot origin
  let outputOne :=
    (UnitKernel A strategy initial policy bank adapter).globalOutputOne
  let outputTwo :=
    (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
  let blockEnv := profiledRawJointUnitStrictRightEnvironment
    (omegaOfList (past ++ [move]))
  let word := R.globalMachineTraceWord outputOne outputTwo physicalEnv
  have hreroot := R.reroot_globalMachineTraceWord_drop outputOne outputTwo
    physicalEnv cut
  rw [hcontrol] at hreroot
  have hopen :=
    (R.reroot current).omegaPrefix_globalMachineTraceWord_eq_of_forall_lt
      outputOne outputTwo (OmegaWord.drop physicalEnv cut) blockEnv past.length
        (fun j hj ↦ henv j (by omega))
  have htraceR :
      (R.reroot current).globalMachineTraceWord outputOne outputTwo blockEnv =
        fun n ↦ pairedRightRecordForRow row
          (profiledRawJointUnitRightPhysicalLetter A
            (profiledRawJointUnitRightPolicyOmegaPlay A bank source
              (omegaOfList (past ++ [move])) n)) := by
    simpa [R, G, FiniteGlobalRoundMachine.reroot, blockEnv] using htrace
  rw [htraceR] at hopen
  have hstateClose :=
    (R.reroot current).globalStateTrace_eq_of_forall_lt
      (OmegaWord.drop physicalEnv cut) blockEnv (past.length + 1) henv
  have hpoint :
      (R.reroot current).globalMachineTraceWord outputOne outputTwo
          (OmegaWord.drop physicalEnv cut) past.length =
        pairedRightRecordForRow row
          (profiledRawJointUnitRightPhysicalLetter A
            (profiledRawJointUnitRightPolicyOmegaPlay A bank source
              (omegaOfList (past ++ [move])) past.length)) := by
    calc
      _ = (R.reroot current).globalMachineTraceWord outputOne outputTwo blockEnv
            past.length := by
          simp only [FiniteGlobalRoundMachine.globalMachineTraceWord]
          rw [henv past.length (by omega), hstateClose]
      _ = _ := congrFun htraceR past.length
  constructor
  · rw [← hreroot]
    simpa [word, ProfiledRawJointUnitPolicyCloseQuery.records,
      profiledRawJointUnitRightPhysicalPrefixRecords,
      profiledRawJointUnitRightPolicyPlay,
      profiledRawJointUnitRightPolicyOmegaPlay, blockEnv, omegaPrefix,
      Function.comp_def] using hopen
  · rw [← hreroot]
    simpa [word, ProfiledRawJointUnitPolicyCloseQuery.records,
      ProfiledRawJointUnitPolicyCloseQuery.strictClosingRecord,
      profiledRawJointUnitRightPhysicalPrefixRecords,
      profiledRawJointUnitRightPolicyPlay,
      profiledRawJointUnitRightPolicyOmegaPlay, blockEnv, omegaPrefix,
      Function.comp_def] using hpoint

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-oriented mirror of
`profiledRawJointUnitRightQuery_records_and_closing_of_rerootTrace`. -/
theorem profiledRawJointUnitLeftQuery_records_and_closing_of_rerootTrace
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (origin current :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.State)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (cut : Nat)
    (hcontrol :
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        origin).globalStateTrace physicalEnv cut = current)
    (henv : ∀ j : Nat, j < past.length + 1 →
      OmegaWord.drop physicalEnv cut j =
        profiledRawJointUnitStrictLeftEnvironment
          (omegaOfList (past ++ [move])) j)
    (htrace :
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        current).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          (profiledRawJointUnitStrictLeftEnvironment
            (omegaOfList (past ++ [move]))) =
        fun n ↦ pairedLeftRecordForRow row
          (profiledRawJointUnitLeftPhysicalLetter A
            (profiledRawJointUnitLeftPolicyOmegaPlay A bank source
              (omegaOfList (past ++ [move])) n))) :
    let query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
        (.inr source) := .left source row past move
    let word :=
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        origin).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv
    omegaPrefix (OmegaWord.drop word cut)
        (query.records A strategy initial policy bank).length =
      query.records A strategy initial policy bank ∧
    OmegaWord.drop word cut
        (query.records A strategy initial policy bank).length =
      query.strictClosingRecord A strategy initial policy bank := by
  dsimp only
  let G := (UnitKernel A strategy initial policy bank adapter).globalMachine
  let R := G.reroot origin
  let outputOne :=
    (UnitKernel A strategy initial policy bank adapter).globalOutputOne
  let outputTwo :=
    (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
  let blockEnv := profiledRawJointUnitStrictLeftEnvironment
    (omegaOfList (past ++ [move]))
  let word := R.globalMachineTraceWord outputOne outputTwo physicalEnv
  have hreroot := R.reroot_globalMachineTraceWord_drop outputOne outputTwo
    physicalEnv cut
  rw [hcontrol] at hreroot
  have hopen :=
    (R.reroot current).omegaPrefix_globalMachineTraceWord_eq_of_forall_lt
      outputOne outputTwo (OmegaWord.drop physicalEnv cut) blockEnv past.length
        (fun j hj ↦ henv j (by omega))
  have htraceR :
      (R.reroot current).globalMachineTraceWord outputOne outputTwo blockEnv =
        fun n ↦ pairedLeftRecordForRow row
          (profiledRawJointUnitLeftPhysicalLetter A
            (profiledRawJointUnitLeftPolicyOmegaPlay A bank source
              (omegaOfList (past ++ [move])) n)) := by
    simpa [R, G, FiniteGlobalRoundMachine.reroot, blockEnv] using htrace
  rw [htraceR] at hopen
  have hstateClose :=
    (R.reroot current).globalStateTrace_eq_of_forall_lt
      (OmegaWord.drop physicalEnv cut) blockEnv (past.length + 1) henv
  have hpoint :
      (R.reroot current).globalMachineTraceWord outputOne outputTwo
          (OmegaWord.drop physicalEnv cut) past.length =
        pairedLeftRecordForRow row
          (profiledRawJointUnitLeftPhysicalLetter A
            (profiledRawJointUnitLeftPolicyOmegaPlay A bank source
              (omegaOfList (past ++ [move])) past.length)) := by
    calc
      _ = (R.reroot current).globalMachineTraceWord outputOne outputTwo blockEnv
            past.length := by
          simp only [FiniteGlobalRoundMachine.globalMachineTraceWord]
          rw [henv past.length (by omega), hstateClose]
      _ = _ := congrFun htraceR past.length
  constructor
  · rw [← hreroot]
    simpa [word, ProfiledRawJointUnitPolicyCloseQuery.records,
      profiledRawJointUnitLeftPhysicalPrefixRecords,
      profiledRawJointUnitLeftPolicyPlay,
      profiledRawJointUnitLeftPolicyOmegaPlay, blockEnv, omegaPrefix,
      Function.comp_def] using hopen
  · rw [← hreroot]
    simpa [word, ProfiledRawJointUnitPolicyCloseQuery.records,
      ProfiledRawJointUnitPolicyCloseQuery.strictClosingRecord,
      profiledRawJointUnitLeftPhysicalPrefixRecords,
      profiledRawJointUnitLeftPolicyPlay,
      profiledRawJointUnitLeftPolicyOmegaPlay, blockEnv, omegaPrefix,
      Function.comp_def] using hpoint

/-! ## Literal environment packets on one operational strict block -/

omit [Fintype In₁] [Fintype In₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The physical environment on a complete right operational block (open
rounds plus its closing round) is the literal all-right query environment. -/
theorem profiledRawJointOperationalRightBlock_environment_eq
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (k : Nat)
    (hgraph : profiledRawJointPhysicalGraphTail physicalEnv 0
        (operationalCloseCuts
          (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k) =
      .right) :
    let graphs := profiledRawJointPhysicalGraphTail physicalEnv 0
    let cuts := operationalCloseCuts graphs hterm
    let openLength := operationalCloseOpenLength graphs hterm k
    let inputs := profiledRawJointUnitPhysicalRightInputs physicalEnv (cuts k)
    let blockInputs := omegaOfList
      (omegaPrefix inputs openLength ++ [inputs openLength])
    ∀ j : Nat, j < openLength + 1 →
      OmegaWord.drop physicalEnv (cuts k) j =
        profiledRawJointUnitStrictRightEnvironment blockInputs j := by
  dsimp only
  let graphs := profiledRawJointPhysicalGraphTail physicalEnv 0
  let cuts := operationalCloseCuts graphs hterm
  let openLength := operationalCloseOpenLength graphs hterm k
  let inputs := profiledRawJointUnitPhysicalRightInputs physicalEnv (cuts k)
  let blockInputs := omegaOfList
    (omegaPrefix inputs openLength ++ [inputs openLength])
  intro j hj
  change j < openLength + 1 at hj
  have hgraphRoot : graphs (cuts k) = .right := by
    simpa [graphs, cuts, profiledRawJointPhysicalGraphTail] using hgraph
  have hword : blockInputs j = inputs j := by
    have hjWord : j <
        (omegaPrefix inputs openLength ++ [inputs openLength]).length := by
      simp [omegaPrefix]
      omega
    rw [show blockInputs j =
      (omegaPrefix inputs openLength ++ [inputs openLength])[j] by
        exact omegaOfList_eq_getElem _ j hjWord]
    by_cases hopen : j < openLength
    · rw [List.getElem_append_left (by simpa [omegaPrefix] using hopen)]
      simp [omegaPrefix]
    · have hjEq : j = openLength := by omega
      subst j
      simp [omegaPrefix]
  have hroundGraph : (physicalEnv (cuts k + j)).graph = .right := by
    by_cases hopen : j < openLength
    · have htail : graphs (cuts k + j) = .right := by
        rw [operationalCloseCuts_open_graph_eq graphs hterm k j hopen]
        exact hgraphRoot
      simpa [graphs, profiledRawJointPhysicalGraphTail] using htail
    · have hjEq : j = openLength := by omega
      subst j
      have htail : graphs (cuts k + openLength) = .right := by
        rw [← operationalCloseCuts_closing_eq_start_add_openLength graphs
          hterm k, operationalCloseCuts_closing_graph_eq graphs hterm k]
        exact hgraphRoot
      simpa [graphs, profiledRawJointPhysicalGraphTail] using htail
  apply EnvironmentRound.equivProd.injective
  apply Prod.ext
  · simpa [OmegaWord.drop, profiledRawJointUnitStrictRightEnvironment,
      inputs, profiledRawJointUnitPhysicalRightInputs] using
        (congrArg Prod.snd hword).symm
  · apply Prod.ext
    · simpa [OmegaWord.drop, profiledRawJointUnitStrictRightEnvironment,
        inputs, profiledRawJointUnitPhysicalRightInputs] using
          (congrArg Prod.fst hword).symm
    · simpa [OmegaWord.drop, profiledRawJointUnitStrictRightEnvironment]
        using hroundGraph

omit [Fintype In₁] [Fintype In₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left-oriented mirror of
`profiledRawJointOperationalRightBlock_environment_eq`. -/
theorem profiledRawJointOperationalLeftBlock_environment_eq
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (k : Nat)
    (hgraph : profiledRawJointPhysicalGraphTail physicalEnv 0
        (operationalCloseCuts
          (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k) =
      .left) :
    let graphs := profiledRawJointPhysicalGraphTail physicalEnv 0
    let cuts := operationalCloseCuts graphs hterm
    let openLength := operationalCloseOpenLength graphs hterm k
    let inputs := profiledRawJointUnitPhysicalLeftInputs physicalEnv (cuts k)
    let blockInputs := omegaOfList
      (omegaPrefix inputs openLength ++ [inputs openLength])
    ∀ j : Nat, j < openLength + 1 →
      OmegaWord.drop physicalEnv (cuts k) j =
        profiledRawJointUnitStrictLeftEnvironment blockInputs j := by
  dsimp only
  let graphs := profiledRawJointPhysicalGraphTail physicalEnv 0
  let cuts := operationalCloseCuts graphs hterm
  let openLength := operationalCloseOpenLength graphs hterm k
  let inputs := profiledRawJointUnitPhysicalLeftInputs physicalEnv (cuts k)
  let blockInputs := omegaOfList
    (omegaPrefix inputs openLength ++ [inputs openLength])
  intro j hj
  change j < openLength + 1 at hj
  have hgraphRoot : graphs (cuts k) = .left := by
    simpa [graphs, cuts, profiledRawJointPhysicalGraphTail] using hgraph
  have hword : blockInputs j = inputs j := by
    have hjWord : j <
        (omegaPrefix inputs openLength ++ [inputs openLength]).length := by
      simp [omegaPrefix]
      omega
    rw [show blockInputs j =
      (omegaPrefix inputs openLength ++ [inputs openLength])[j] by
        exact omegaOfList_eq_getElem _ j hjWord]
    by_cases hopen : j < openLength
    · rw [List.getElem_append_left (by simpa [omegaPrefix] using hopen)]
      simp [omegaPrefix]
    · have hjEq : j = openLength := by omega
      subst j
      simp [omegaPrefix]
  have hroundGraph : (physicalEnv (cuts k + j)).graph = .left := by
    by_cases hopen : j < openLength
    · have htail : graphs (cuts k + j) = .left := by
        rw [operationalCloseCuts_open_graph_eq graphs hterm k j hopen]
        exact hgraphRoot
      simpa [graphs, profiledRawJointPhysicalGraphTail] using htail
    · have hjEq : j = openLength := by omega
      subst j
      have htail : graphs (cuts k + openLength) = .left := by
        rw [← operationalCloseCuts_closing_eq_start_add_openLength graphs
          hterm k, operationalCloseCuts_closing_graph_eq graphs hterm k]
        exact hgraphRoot
      simpa [graphs, profiledRawJointPhysicalGraphTail] using htail
  apply EnvironmentRound.equivProd.injective
  apply Prod.ext
  · simpa [OmegaWord.drop, profiledRawJointUnitStrictLeftEnvironment,
      inputs, profiledRawJointUnitPhysicalLeftInputs] using
        (congrArg Prod.fst hword).symm
  · apply Prod.ext
    · simpa [OmegaWord.drop, profiledRawJointUnitStrictLeftEnvironment,
        inputs, profiledRawJointUnitPhysicalLeftInputs] using
          (congrArg Prod.snd hword).symm
    · simpa [OmegaWord.drop, profiledRawJointUnitStrictLeftEnvironment]
        using hroundGraph

/-! ## Transporting a literal block endpoint back to the physical run -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- If the physical suffix agrees with a literal block for all consumed
rounds, a close-endpoint computation on the re-rooted literal block is the
actual control at the physical block endpoint. -/
theorem profiledRawJointUnit_reroot_block_end_eq
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (origin current :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.State)
    (physicalEnv blockEnv : EnvironmentSequence In₁ In₂)
    (start total : Nat)
    (hcurrent :
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        origin).globalStateTrace physicalEnv start = current)
    (henv : ∀ j : Nat, j < total →
      OmegaWord.drop physicalEnv start j = blockEnv j) :
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        origin).globalStateTrace physicalEnv (start + total) =
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        current).globalStateTrace blockEnv total := by
  let G := (UnitKernel A strategy initial policy bank adapter).globalMachine
  let R := G.reroot origin
  rw [← R.reroot_globalStateTrace_drop physicalEnv start total]
  rw [hcurrent]
  exact (G.reroot current).globalStateTrace_eq_of_forall_lt
    (OmegaWord.drop physicalEnv start) blockEnv total henv

/-! ## The proof-only cut carrier -/

/-- Fixed-policy root threaded through the canonical operational cuts at a
fixed checker-entry row. -/
noncomputable def profiledRawJointUnitPersistentStrictRootAt
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (row : PairedEntryRow)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) (k : Nat) :
    ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A) policy :=
  profiledRawJointUnitPolicyOperationalThreadRoot A strategy initial policy
    bank physicalEnv 0 hterm seed (fun _ ↦ row) k

/-- Literal query at the `k`-th persistent strict cut. -/
noncomputable def profiledRawJointUnitPersistentStrictQueryAt
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (row : PairedEntryRow)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) (k : Nat) :
    ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      (profiledRawJointUnitPersistentStrictRootAt A strategy initial policy
        bank physicalEnv hterm row seed k) :=
  let cuts := operationalCloseCuts
    (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
  profiledRawJointUnitPolicyPhysicalCloseQuery A strategy initial policy
    physicalEnv (cuts k) (cuts (k + 1)) row
      (profiledRawJointUnitPersistentStrictRootAt A strategy initial policy bank
        physicalEnv hterm row seed k)

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The persistent root recursion advances by the target of its literal query. -/
theorem profiledRawJointUnitPersistentStrictRootAt_succ
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (row : PairedEntryRow)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) (k : Nat) :
    profiledRawJointUnitPersistentStrictRootAt A strategy initial policy bank
        physicalEnv hterm row seed (k + 1) =
      (profiledRawJointUnitPersistentStrictQueryAt A strategy initial policy
        bank physicalEnv hterm row seed k).target A strategy initial policy bank := by
  simp [profiledRawJointUnitPersistentStrictRootAt,
    profiledRawJointUnitPolicyOperationalThreadRoot,
    profiledRawJointUnitPersistentStrictQueryAt]

/-- A right-rooted persistent query is the literal maximal right block cut
from the physical environment. -/
theorem profiledRawJointUnitPersistentStrictQueryAt_target_right
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (row : PairedEntryRow)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) (k : Nat)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)
    (hroot : profiledRawJointUnitPersistentStrictRootAt A strategy initial
      policy bank physicalEnv hterm row seed k = .inl source) :
    let graphs := profiledRawJointPhysicalGraphTail physicalEnv 0
    let cuts := operationalCloseCuts graphs hterm
    let openLength := operationalCloseOpenLength graphs hterm k
    let inputs := profiledRawJointUnitPhysicalRightInputs physicalEnv (cuts k)
    let query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
        (.inl source) :=
      .right source row (omegaPrefix inputs openLength) (inputs openLength)
    (profiledRawJointUnitPersistentStrictQueryAt A strategy initial policy bank
        physicalEnv hterm row seed k).target A strategy initial policy bank =
      query.target A strategy initial policy bank := by
  dsimp only
  unfold profiledRawJointUnitPersistentStrictQueryAt
  rw [hroot]
  dsimp only
  rw [operationalCloseCuts_succ_eq_start_add_openLength_add_one]
  simp only [profiledRawJointUnitPolicyPhysicalCloseQuery]
  have hlength (a b : Nat) : a + b + 1 - a - 1 = b := by omega
  rw [hlength]

/-- Left-rooted mirror of
`profiledRawJointUnitPersistentStrictQueryAt_target_right`. -/
theorem profiledRawJointUnitPersistentStrictQueryAt_target_left
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (row : PairedEntryRow)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) (k : Nat)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)
    (hroot : profiledRawJointUnitPersistentStrictRootAt A strategy initial
      policy bank physicalEnv hterm row seed k = .inr source) :
    let graphs := profiledRawJointPhysicalGraphTail physicalEnv 0
    let cuts := operationalCloseCuts graphs hterm
    let openLength := operationalCloseOpenLength graphs hterm k
    let inputs := profiledRawJointUnitPhysicalLeftInputs physicalEnv (cuts k)
    let query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
        (.inr source) :=
      .left source row (omegaPrefix inputs openLength) (inputs openLength)
    (profiledRawJointUnitPersistentStrictQueryAt A strategy initial policy bank
        physicalEnv hterm row seed k).target A strategy initial policy bank =
      query.target A strategy initial policy bank := by
  dsimp only
  unfold profiledRawJointUnitPersistentStrictQueryAt
  rw [hroot]
  dsimp only
  rw [operationalCloseCuts_succ_eq_start_add_openLength_add_one]
  simp only [profiledRawJointUnitPolicyPhysicalCloseQuery]
  have hlength (a b : Nat) : a + b + 1 - a - 1 = b := by omega
  rw [hlength]

/-- Every persistent query starts at the selected coordinate stored by its
current fixed-policy root. -/
theorem profiledRawJointUnitPersistentStrictQueryAt_entryState
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (row : PairedEntryRow)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) (k : Nat) :
    (profiledRawJointUnitPersistentStrictQueryAt A strategy initial policy bank
        physicalEnv hterm row seed k).entryState A strategy initial policy =
      (profiledRawJointUnitPersistentStrictRootAt A strategy initial policy bank
        physicalEnv hterm row seed k).entryStateForRow A strategy initial policy
          row := by
  unfold profiledRawJointUnitPersistentStrictQueryAt
  dsimp only
  cases profiledRawJointUnitPersistentStrictRootAt A strategy initial policy
    bank physicalEnv hterm row seed k <;> rfl

/-- The persistent query's open-record length is exactly the gap between its
two operational cuts, excluding the closing round. -/
theorem profiledRawJointUnitPersistentStrictQueryAt_records_length
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (row : PairedEntryRow)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) (k : Nat) :
    let cuts := operationalCloseCuts
      (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
    ((profiledRawJointUnitPersistentStrictQueryAt A strategy initial policy bank
        physicalEnv hterm row seed k).records A strategy initial policy bank).length =
      cuts (k + 1) - cuts k - 1 := by
  dsimp only
  rw [ProfiledRawJointUnitPolicyCloseQuery.records_length_eq_inputListLength]
  exact profiledRawJointUnitPolicyPhysicalCloseQuery_inputListLength A strategy
    initial policy physicalEnv
      (operationalCloseCuts (profiledRawJointPhysicalGraphTail physicalEnv 0)
        hterm k)
      (operationalCloseCuts (profiledRawJointPhysicalGraphTail physicalEnv 0)
        hterm (k + 1)) row
      (profiledRawJointUnitPersistentStrictRootAt A strategy initial policy bank
        physicalEnv hterm row seed k)

end

/-- At a strict cut the current root, physical graph, and concrete Unit
control have one of the four aligned shapes: fresh right/left at activation,
or the opposite matched state left by the preceding maximal block. -/
def ProfiledRawJointUnitPersistentStrictControlAt
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (origin :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.State)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (row : PairedEntryRow)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) (k : Nat) : Prop :=
  let cuts := operationalCloseCuts
    (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
  let root := profiledRawJointUnitPersistentStrictRootAt A strategy initial
    policy bank physicalEnv hterm row seed k
  let control :=
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      origin).globalStateTrace physicalEnv (cuts k)
  match root with
  | .inl source =>
      profiledRawJointPhysicalGraphTail physicalEnv 0 (cuts k) = .right ∧
        ((∃ outputOne outputTwo,
            control = profiledRawJointUnitFreshMatchedRightState A strategy
              initial policy bank adapter source row outputOne outputTwo) ∨
          ∃ left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
              initial policy,
            ∃ owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy
              initial policy bank,
            ∃ outputOne outputTwo,
              control = profiledRawJointUnitMatchedLeftState A strategy initial
                policy bank adapter left owner outputOne outputTwo ∧
              profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
                policy bank left = source ∧
              left.2.1 = row)
  | .inr source =>
      profiledRawJointPhysicalGraphTail physicalEnv 0 (cuts k) = .left ∧
        ((∃ outputOne outputTwo,
            control = profiledRawJointUnitFreshMatchedLeftState A strategy
              initial policy bank adapter source row outputOne outputTwo) ∨
          ∃ owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy
              initial policy bank,
            ∃ right : ProfiledRawJointUnitRightPolicyReceiverControl A
              strategy initial policy,
            ∃ outputOne outputTwo,
              control = profiledRawJointUnitMatchedRightState A strategy initial
                policy bank adapter owner right outputOne outputTwo ∧
              profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
                policy bank right = source ∧
              right.2.1 = row)

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The genuine fresh-right state establishes the cut carrier at zero. -/
theorem profiledRawJointUnitPersistentStrictControlAt_zero_freshRight
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
    (row : PairedEntryRow)
    (hgraph : (physicalEnv 0).graph = .right) :
    ProfiledRawJointUnitPersistentStrictControlAt A strategy initial policy bank
      adapter
        (profiledRawJointUnitFreshMatchedRightState A strategy initial policy
          bank adapter source row oldOutputOne oldOutputTwo)
        physicalEnv hterm row (.inl source) 0 := by
  change (physicalEnv 0).graph = .right ∧ _
  exact ⟨hgraph, Or.inl ⟨oldOutputOne, oldOutputTwo, rfl⟩⟩

/-- Fresh-left mirror. -/
theorem profiledRawJointUnitPersistentStrictControlAt_zero_freshLeft
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
    (row : PairedEntryRow)
    (hgraph : (physicalEnv 0).graph = .left) :
    ProfiledRawJointUnitPersistentStrictControlAt A strategy initial policy bank
      adapter
        (profiledRawJointUnitFreshMatchedLeftState A strategy initial policy bank
          adapter source row oldOutputOne oldOutputTwo)
        physicalEnv hterm row (.inr source) 0 := by
  change (physicalEnv 0).graph = .left ∧ _
  exact ⟨hgraph, Or.inl ⟨oldOutputOne, oldOutputTwo, rfl⟩⟩

/-- A completed matched-left state is already the alternate zero shape for a
right-rooted strict block. -/
theorem profiledRawJointUnitPersistentStrictControlAt_zero_matchedLeft
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
    (row : PairedEntryRow)
    (hgraph : (physicalEnv 0).graph = .right)
    (htarget : profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
      policy bank left = source)
    (hrow : left.2.1 = row) :
    ProfiledRawJointUnitPersistentStrictControlAt A strategy initial policy bank
      adapter
        (profiledRawJointUnitMatchedLeftState A strategy initial policy bank
          adapter left owner oldOutputOne oldOutputTwo)
        physicalEnv hterm row (.inl source) 0 := by
  change (physicalEnv 0).graph = .right ∧ _
  exact ⟨hgraph, Or.inr
    ⟨left, owner, oldOutputOne, oldOutputTwo, rfl, htarget, hrow⟩⟩

/-- Completed matched-right mirror at a left-rooted strict block. -/
theorem profiledRawJointUnitPersistentStrictControlAt_zero_matchedRight
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
    (row : PairedEntryRow)
    (hgraph : (physicalEnv 0).graph = .left)
    (htarget : profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
      policy bank right = source)
    (hrow : right.2.1 = row) :
    ProfiledRawJointUnitPersistentStrictControlAt A strategy initial policy bank
      adapter
        (profiledRawJointUnitMatchedRightState A strategy initial policy bank
          adapter owner right oldOutputOne oldOutputTwo)
        physicalEnv hterm row (.inr source) 0 := by
  change (physicalEnv 0).graph = .left ∧ _
  exact ⟨hgraph, Or.inr
    ⟨owner, right, oldOutputOne, oldOutputTwo, rfl, htarget, hrow⟩⟩

/-- Every aligned strict carrier supplies the exact open slice and closing
record of its canonical query. -/
theorem ProfiledRawJointUnitPersistentStrictControlAt.records_and_closing
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo}
    {origin :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.State}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0)}
    {row : PairedEntryRow}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy} {k : Nat}
    (carrier : ProfiledRawJointUnitPersistentStrictControlAt A strategy initial
      policy bank adapter origin physicalEnv hterm row seed k) :
    let cuts := operationalCloseCuts
      (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm
    let query := profiledRawJointUnitPersistentStrictQueryAt A strategy initial
      policy bank physicalEnv hterm row seed k
    let word :=
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        origin).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv
    omegaPrefix (OmegaWord.drop word (cuts k))
        (query.records A strategy initial policy bank).length =
      query.records A strategy initial policy bank ∧
    OmegaWord.drop word (cuts k)
        (query.records A strategy initial policy bank).length =
      query.strictClosingRecord A strategy initial policy bank := by
  dsimp only
  let graphs := profiledRawJointPhysicalGraphTail physicalEnv 0
  let cuts := operationalCloseCuts graphs hterm
  let openLength := operationalCloseOpenLength graphs hterm k
  let root := profiledRawJointUnitPersistentStrictRootAt A strategy initial
    policy bank physicalEnv hterm row seed k
  let query := profiledRawJointUnitPersistentStrictQueryAt A strategy initial
    policy bank physicalEnv hterm row seed k
  change (match root with
    | .inl source => graphs (cuts k) = .right ∧ _
    | .inr source => graphs (cuts k) = .left ∧ _) at carrier
  cases hroot : root with
  | inl source =>
      rw [hroot] at carrier
      have hroot' :
          profiledRawJointUnitPersistentStrictRootAt A strategy initial policy
            bank physicalEnv hterm row seed k = .inl source := by
        simpa [root] using hroot
      unfold profiledRawJointUnitPersistentStrictQueryAt
      rw [hroot']
      dsimp only
      have hcut : operationalCloseCuts
            (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm (k + 1) =
          operationalCloseCuts
              (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k +
            operationalCloseOpenLength
              (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k + 1 :=
        operationalCloseCuts_succ_eq_start_add_openLength_add_one
          (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k
      rw [hcut]
      simp only [profiledRawJointUnitPolicyPhysicalCloseQuery]
      have hlength : operationalCloseCuts
              (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k +
            operationalCloseOpenLength
              (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k + 1 -
            operationalCloseCuts
              (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k - 1 =
          operationalCloseOpenLength
            (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k := by
        omega
      rw [hlength]
      rcases carrier with ⟨hgraph, hshape⟩
      let inputs := profiledRawJointUnitPhysicalRightInputs physicalEnv (cuts k)
      let past := omegaPrefix inputs openLength
      let move := inputs openLength
      let currentFresh outputOne outputTwo :=
        profiledRawJointUnitFreshMatchedRightState A strategy initial policy bank
          adapter source row outputOne outputTwo
      have henv : ∀ j, j < past.length + 1 →
          OmegaWord.drop physicalEnv (cuts k) j =
            profiledRawJointUnitStrictRightEnvironment
              (omegaOfList (past ++ [move])) j := by
        simpa [past, move, inputs, openLength, cuts, graphs, omegaPrefix] using
          (profiledRawJointOperationalRightBlock_environment_eq physicalEnv
            hterm k hgraph)
      rcases hshape with hfresh | hmatched
      · rcases hfresh with ⟨outputOne, outputTwo, hcontrol⟩
        have hresult :=
          profiledRawJointUnitRightQuery_records_and_closing_of_rerootTrace
          A strategy initial policy bank adapter origin
            (currentFresh outputOne outputTwo) source row past move physicalEnv
              (cuts k) hcontrol henv
          (profiledRawJointUnitFreshMatchedRight_traceWord A strategy initial
            policy bank adapter source row outputOne outputTwo
              (omegaOfList (past ++ [move])))
        simpa [cuts, graphs, openLength, inputs, past, move] using hresult
      · rcases hmatched with
          ⟨left, owner, outputOne, outputTwo, hcontrol, htarget, hrow⟩
        have htrace := profiledRawJointUnitMatchedLeft_right_traceWord A strategy
          initial policy bank adapter left owner outputOne outputTwo
            (omegaOfList (past ++ [move]))
        rw [htarget, hrow] at htrace
        have hresult :=
          profiledRawJointUnitRightQuery_records_and_closing_of_rerootTrace
          A strategy initial policy bank adapter origin
            (profiledRawJointUnitMatchedLeftState A strategy initial policy bank
              adapter left owner outputOne outputTwo)
            source row past move physicalEnv (cuts k) hcontrol henv htrace
        simpa [cuts, graphs, openLength, inputs, past, move] using hresult
  | inr source =>
      rw [hroot] at carrier
      have hroot' :
          profiledRawJointUnitPersistentStrictRootAt A strategy initial policy
            bank physicalEnv hterm row seed k = .inr source := by
        simpa [root] using hroot
      unfold profiledRawJointUnitPersistentStrictQueryAt
      rw [hroot']
      dsimp only
      have hcut : operationalCloseCuts
            (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm (k + 1) =
          operationalCloseCuts
              (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k +
            operationalCloseOpenLength
              (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k + 1 :=
        operationalCloseCuts_succ_eq_start_add_openLength_add_one
          (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k
      rw [hcut]
      simp only [profiledRawJointUnitPolicyPhysicalCloseQuery]
      have hlength : operationalCloseCuts
              (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k +
            operationalCloseOpenLength
              (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k + 1 -
            operationalCloseCuts
              (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k - 1 =
          operationalCloseOpenLength
            (profiledRawJointPhysicalGraphTail physicalEnv 0) hterm k := by
        omega
      rw [hlength]
      rcases carrier with ⟨hgraph, hshape⟩
      let inputs := profiledRawJointUnitPhysicalLeftInputs physicalEnv (cuts k)
      let past := omegaPrefix inputs openLength
      let move := inputs openLength
      let currentFresh outputOne outputTwo :=
        profiledRawJointUnitFreshMatchedLeftState A strategy initial policy bank
          adapter source row outputOne outputTwo
      have henv : ∀ j, j < past.length + 1 →
          OmegaWord.drop physicalEnv (cuts k) j =
            profiledRawJointUnitStrictLeftEnvironment
              (omegaOfList (past ++ [move])) j := by
        simpa [past, move, inputs, openLength, cuts, graphs, omegaPrefix] using
          (profiledRawJointOperationalLeftBlock_environment_eq physicalEnv
            hterm k hgraph)
      rcases hshape with hfresh | hmatched
      · rcases hfresh with ⟨outputOne, outputTwo, hcontrol⟩
        have hresult :=
          profiledRawJointUnitLeftQuery_records_and_closing_of_rerootTrace
          A strategy initial policy bank adapter origin
            (currentFresh outputOne outputTwo) source row past move physicalEnv
              (cuts k) hcontrol henv
          (profiledRawJointUnitFreshMatchedLeft_traceWord A strategy initial
            policy bank adapter source row outputOne outputTwo
              (omegaOfList (past ++ [move])))
        simpa [cuts, graphs, openLength, inputs, past, move] using hresult
      · rcases hmatched with
          ⟨owner, right, outputOne, outputTwo, hcontrol, htarget, hrow⟩
        have htrace := profiledRawJointUnitMatchedRight_left_traceWord A strategy
          initial policy bank adapter owner right outputOne outputTwo
            (omegaOfList (past ++ [move]))
        rw [htarget, hrow] at htrace
        have hresult :=
          profiledRawJointUnitLeftQuery_records_and_closing_of_rerootTrace
          A strategy initial policy bank adapter origin
            (profiledRawJointUnitMatchedRightState A strategy initial policy bank
              adapter owner right outputOne outputTwo)
            source row past move physicalEnv (cuts k) hcontrol henv htrace
        simpa [cuts, graphs, openLength, inputs, past, move] using hresult

/-- In an all-strict tail, one aligned carrier advances to the next maximal
operational block.  The concrete state is transported through the literal
block, and the fixed-policy root advances through the same close query. -/
theorem ProfiledRawJointUnitPersistentStrictControlAt.succ
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo}
    {origin :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.State}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0)}
    {row : PairedEntryRow}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy} {k : Nat}
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 n ≠ .both)
    (carrier : ProfiledRawJointUnitPersistentStrictControlAt A strategy initial
      policy bank adapter origin physicalEnv hterm row seed k) :
    ProfiledRawJointUnitPersistentStrictControlAt A strategy initial policy
      bank adapter origin physicalEnv hterm row seed (k + 1) := by
  let graphs := profiledRawJointPhysicalGraphTail physicalEnv 0
  let cuts := operationalCloseCuts graphs hterm
  let openLength := operationalCloseOpenLength graphs hterm k
  let root := profiledRawJointUnitPersistentStrictRootAt A strategy initial
    policy bank physicalEnv hterm row seed k
  change (match root with
    | .inl source => graphs (cuts k) = .right ∧ _
    | .inr source => graphs (cuts k) = .left ∧ _) at carrier
  cases hroot : root with
  | inl source =>
      rw [hroot] at carrier
      rcases carrier with ⟨hgraph, hshape⟩
      have hroot' :
          profiledRawJointUnitPersistentStrictRootAt A strategy initial policy
            bank physicalEnv hterm row seed k = .inl source := by
        simpa [root] using hroot
      let inputs := profiledRawJointUnitPhysicalRightInputs physicalEnv (cuts k)
      let past := omegaPrefix inputs openLength
      let move := inputs openLength
      let blockEnv := profiledRawJointUnitStrictRightEnvironment
        (omegaOfList (past ++ [move]))
      have henv : ∀ j : Nat, j < past.length + 1 →
          OmegaWord.drop physicalEnv (cuts k) j = blockEnv j := by
        simpa [blockEnv, past, move, inputs, openLength, cuts, graphs,
          omegaPrefix] using
          (profiledRawJointOperationalRightBlock_environment_eq physicalEnv
            hterm k hgraph)
      have hcut : cuts (k + 1) = cuts k + openLength + 1 :=
        operationalCloseCuts_succ_eq_start_add_openLength_add_one graphs hterm k
      have htime : cuts k + (past.length + 1) = cuts (k + 1) := by
        rw [hcut]
        simp [past, omegaPrefix]
        omega
      have hqueryTarget :=
        profiledRawJointUnitPersistentStrictQueryAt_target_right A strategy
          initial policy bank physicalEnv hterm row seed k source hroot'
      have hnextRoot :
          profiledRawJointUnitPersistentStrictRootAt A strategy initial policy
              bank physicalEnv hterm row seed (k + 1) =
            (ProfiledRawJointUnitPolicyCloseQuery.right source row past move
              ).target A strategy initial policy bank :=
        (profiledRawJointUnitPersistentStrictRootAt_succ A strategy initial
          policy bank physicalEnv hterm row seed k).trans (by
            simpa [past, move, inputs, openLength, cuts, graphs] using
              hqueryTarget)
      have hgraphNext : graphs (cuts (k + 1)) = .left := by
        have hstrict : graphs (cuts k) ≠ .both := by
          intro hboth
          exact (by simpa using hgraph.symm.trans hboth)
        have hne : graphs (cuts (k + 1)) ≠ graphs (cuts k) :=
          operationalCloseCuts_next_graph_ne_of_strict graphs hterm k hstrict
        have hneRight : graphs (cuts (k + 1)) ≠ .right := by
          intro hright
          apply hne
          rw [hright, hgraph]
        have hnb : graphs (cuts (k + 1)) ≠ .both := by
          simpa [graphs, cuts] using hnoboth (cuts (k + 1))
        cases hx : graphs (cuts (k + 1)) with
        | left => rfl
        | right => exact (hneRight hx).elim
        | both => exact (hnb hx).elim
      obtain ⟨nextOwner, nextReceiver, outputOne, outputTwo, hactual,
          hrootNext, hrowNext⟩ :
          ∃ nextOwner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy
              initial policy bank,
            ∃ nextReceiver : ProfiledRawJointUnitRightPolicyReceiverControl A
              strategy initial policy,
            ∃ outputOne outputTwo,
              ((UnitKernel A strategy initial policy bank adapter).globalMachine
                |>.reroot origin).globalStateTrace physicalEnv (cuts (k + 1)) =
                profiledRawJointUnitMatchedRightState A strategy initial policy
                  bank adapter nextOwner nextReceiver outputOne outputTwo ∧
              profiledRawJointUnitPersistentStrictRootAt A strategy initial
                  policy bank physicalEnv hterm row seed (k + 1) =
                .inr (profiledRawJointUnitPolicyRightReceiverTarget A strategy
                  initial policy bank nextReceiver) ∧
              nextReceiver.2.1 = row := by
        rcases hshape with hfresh | hmatched
        · rcases hfresh with ⟨oldOutputOne, oldOutputTwo, hcontrol⟩
          obtain ⟨nextOwner, nextReceiver, outputOne, outputTwo, hend,
              htarget, hrow⟩ :=
            profiledRawJointUnitFreshMatchedRight_close_endpoint A strategy
              initial policy bank adapter source row past move oldOutputOne
                oldOutputTwo
          have htransport := profiledRawJointUnit_reroot_block_end_eq A
            strategy initial policy bank adapter origin
              (profiledRawJointUnitFreshMatchedRightState A strategy initial
                policy bank adapter source row oldOutputOne oldOutputTwo)
              physicalEnv blockEnv (cuts k) (past.length + 1) hcontrol henv
          refine ⟨nextOwner, nextReceiver, outputOne, outputTwo, ?_, ?_, hrow⟩
          · rw [← htime]
            exact htransport.trans hend
          · exact hnextRoot.trans htarget.symm
        · rcases hmatched with
            ⟨left, owner, oldOutputOne, oldOutputTwo, hcontrol, htargetOld,
              hrowOld⟩
          obtain ⟨nextOwner, nextReceiver, outputOne, outputTwo, hend,
              htarget, hrow⟩ :=
            profiledRawJointUnitMatchedLeft_right_close_endpoint A strategy
              initial policy bank adapter source row past move left owner
                oldOutputOne oldOutputTwo htargetOld hrowOld
          have htransport := profiledRawJointUnit_reroot_block_end_eq A
            strategy initial policy bank adapter origin
              (profiledRawJointUnitMatchedLeftState A strategy initial policy
                bank adapter left owner oldOutputOne oldOutputTwo)
              physicalEnv blockEnv (cuts k) (past.length + 1) hcontrol henv
          refine ⟨nextOwner, nextReceiver, outputOne, outputTwo, ?_, ?_, hrow⟩
          · rw [← htime]
            exact htransport.trans hend
          · exact hnextRoot.trans htarget.symm
      change (match
        profiledRawJointUnitPersistentStrictRootAt A strategy initial policy
          bank physicalEnv hterm row seed (k + 1) with
        | .inl source => graphs (cuts (k + 1)) = .right ∧ _
        | .inr source => graphs (cuts (k + 1)) = .left ∧ _)
      rw [hrootNext]
      exact ⟨hgraphNext, Or.inr ⟨nextOwner, nextReceiver, outputOne,
        outputTwo, hactual, rfl, hrowNext⟩⟩
  | inr source =>
      rw [hroot] at carrier
      rcases carrier with ⟨hgraph, hshape⟩
      have hroot' :
          profiledRawJointUnitPersistentStrictRootAt A strategy initial policy
            bank physicalEnv hterm row seed k = .inr source := by
        simpa [root] using hroot
      let inputs := profiledRawJointUnitPhysicalLeftInputs physicalEnv (cuts k)
      let past := omegaPrefix inputs openLength
      let move := inputs openLength
      let blockEnv := profiledRawJointUnitStrictLeftEnvironment
        (omegaOfList (past ++ [move]))
      have henv : ∀ j : Nat, j < past.length + 1 →
          OmegaWord.drop physicalEnv (cuts k) j = blockEnv j := by
        simpa [blockEnv, past, move, inputs, openLength, cuts, graphs,
          omegaPrefix] using
          (profiledRawJointOperationalLeftBlock_environment_eq physicalEnv
            hterm k hgraph)
      have hcut : cuts (k + 1) = cuts k + openLength + 1 :=
        operationalCloseCuts_succ_eq_start_add_openLength_add_one graphs hterm k
      have htime : cuts k + (past.length + 1) = cuts (k + 1) := by
        rw [hcut]
        simp [past, omegaPrefix]
        omega
      have hqueryTarget :=
        profiledRawJointUnitPersistentStrictQueryAt_target_left A strategy
          initial policy bank physicalEnv hterm row seed k source hroot'
      have hnextRoot :
          profiledRawJointUnitPersistentStrictRootAt A strategy initial policy
              bank physicalEnv hterm row seed (k + 1) =
            (ProfiledRawJointUnitPolicyCloseQuery.left source row past move
              ).target A strategy initial policy bank :=
        (profiledRawJointUnitPersistentStrictRootAt_succ A strategy initial
          policy bank physicalEnv hterm row seed k).trans (by
            simpa [past, move, inputs, openLength, cuts, graphs] using
              hqueryTarget)
      have hgraphNext : graphs (cuts (k + 1)) = .right := by
        have hstrict : graphs (cuts k) ≠ .both := by
          intro hboth
          exact (by simpa using hgraph.symm.trans hboth)
        have hne : graphs (cuts (k + 1)) ≠ graphs (cuts k) :=
          operationalCloseCuts_next_graph_ne_of_strict graphs hterm k hstrict
        have hneLeft : graphs (cuts (k + 1)) ≠ .left := by
          intro hleft
          apply hne
          rw [hleft, hgraph]
        have hnb : graphs (cuts (k + 1)) ≠ .both := by
          simpa [graphs, cuts] using hnoboth (cuts (k + 1))
        cases hx : graphs (cuts (k + 1)) with
        | left => exact (hneLeft hx).elim
        | right => rfl
        | both => exact (hnb hx).elim
      obtain ⟨nextReceiver, nextOwner, outputOne, outputTwo, hactual,
          hrootNext, hrowNext⟩ :
          ∃ nextReceiver : ProfiledRawJointUnitLeftPolicyReceiverControl A
              strategy initial policy,
            ∃ nextOwner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy
              initial policy bank,
            ∃ outputOne outputTwo,
              ((UnitKernel A strategy initial policy bank adapter).globalMachine
                |>.reroot origin).globalStateTrace physicalEnv (cuts (k + 1)) =
                profiledRawJointUnitMatchedLeftState A strategy initial policy
                  bank adapter nextReceiver nextOwner outputOne outputTwo ∧
              profiledRawJointUnitPersistentStrictRootAt A strategy initial
                  policy bank physicalEnv hterm row seed (k + 1) =
                .inl (profiledRawJointUnitPolicyLeftReceiverTarget A strategy
                  initial policy bank nextReceiver) ∧
              nextReceiver.2.1 = row := by
        rcases hshape with hfresh | hmatched
        · rcases hfresh with ⟨oldOutputOne, oldOutputTwo, hcontrol⟩
          obtain ⟨nextReceiver, nextOwner, outputOne, outputTwo, hend,
              htarget, hrow⟩ :=
            profiledRawJointUnitFreshMatchedLeft_close_endpoint A strategy
              initial policy bank adapter source row past move oldOutputOne
                oldOutputTwo
          have htransport := profiledRawJointUnit_reroot_block_end_eq A
            strategy initial policy bank adapter origin
              (profiledRawJointUnitFreshMatchedLeftState A strategy initial
                policy bank adapter source row oldOutputOne oldOutputTwo)
              physicalEnv blockEnv (cuts k) (past.length + 1) hcontrol henv
          refine ⟨nextReceiver, nextOwner, outputOne, outputTwo, ?_, ?_, hrow⟩
          · rw [← htime]
            exact htransport.trans hend
          · exact hnextRoot.trans htarget.symm
        · rcases hmatched with
            ⟨owner, right, oldOutputOne, oldOutputTwo, hcontrol, htargetOld,
              hrowOld⟩
          obtain ⟨nextReceiver, nextOwner, outputOne, outputTwo, hend,
              htarget, hrow⟩ :=
            profiledRawJointUnitMatchedRight_left_close_endpoint A strategy
              initial policy bank adapter source row past move owner right
                oldOutputOne oldOutputTwo htargetOld hrowOld
          have htransport := profiledRawJointUnit_reroot_block_end_eq A
            strategy initial policy bank adapter origin
              (profiledRawJointUnitMatchedRightState A strategy initial policy
                bank adapter owner right oldOutputOne oldOutputTwo)
              physicalEnv blockEnv (cuts k) (past.length + 1) hcontrol henv
          refine ⟨nextReceiver, nextOwner, outputOne, outputTwo, ?_, ?_, hrow⟩
          · rw [← htime]
            exact htransport.trans hend
          · exact hnextRoot.trans htarget.symm
      change (match
        profiledRawJointUnitPersistentStrictRootAt A strategy initial policy
          bank physicalEnv hterm row seed (k + 1) with
        | .inl source => graphs (cuts (k + 1)) = .right ∧ _
        | .inr source => graphs (cuts (k + 1)) = .left ∧ _)
      rw [hrootNext]
      exact ⟨hgraphNext, Or.inr ⟨nextReceiver, nextOwner, outputOne,
        outputTwo, hactual, rfl, hrowNext⟩⟩

/-- The zero carrier and the successor theorem give aligned concrete control
at every operational cut of an all-strict tail. -/
theorem ProfiledRawJointUnitPersistentStrictControlAt.all
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo}
    {origin :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.State}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0)}
    {row : PairedEntryRow}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 n ≠ .both)
    (zero : ProfiledRawJointUnitPersistentStrictControlAt A strategy initial
      policy bank adapter origin physicalEnv hterm row seed 0) :
    ∀ k : Nat, ProfiledRawJointUnitPersistentStrictControlAt A strategy
      initial policy bank adapter origin physicalEnv hterm row seed k := by
  intro k
  induction k with
  | zero => exact zero
  | succ k ih => exact ih.succ A strategy initial policy bank hnoboth

end

end

end DetParityAutomaton

end DistributedSynthesis
