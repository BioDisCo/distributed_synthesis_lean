/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitFixedTailSoundness
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyLeaderFreeKernel
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyPhysicalPriority
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalMachineReroot
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointLeaderFreeReadback
import DistributedSynthesis.Formalizations.Theorem.ThmUniversalThreadDeterminization

/-!
# Operational fixed tails of the raw-joint leader-free carrier

This file identifies a leader-free Unit-policy kernel re-rooted at a fresh
matched right or left controller with the literal infinite controller play.
The arbitrary outputs stored in the re-root state disappear after the first
Moore transition.

The final acceptance bridge keeps the original DPA state at the physical
prefix explicit.  In particular, it never restarts the DPA at the selected
macro state without an equality proving that this is the actual post-prefix
state.
-/

namespace DistributedSynthesis

universe u v x y s i₁ i₂ e₁ e₂

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

/-! ## Constant strict environments -/

/-- A right-block input word as a physical all-right environment. -/
def profiledRawJointUnitStrictRightEnvironment
    (env : Nat → In₂ × In₁) : EnvironmentSequence In₁ In₂ :=
  fun n ↦
    { inputOne := (env n).2
      inputTwo := (env n).1
      graph := .right }

/-- A left-block input word as a physical all-left environment. -/
def profiledRawJointUnitStrictLeftEnvironment
    (env : Nat → In₁ × In₂) : EnvironmentSequence In₁ In₂ :=
  fun n ↦
    { inputOne := (env n).1
      inputTwo := (env n).2
      graph := .left }

/-! ## Fresh matched-right re-root -/

private abbrev UnitKernel
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :=
  profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
    adapter

/-- The joint Moore state at a fresh matched-right policy root. -/
noncomputable def profiledRawJointUnitFreshMatchedRightState
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) :
    (UnitKernel A strategy initial policy bank adapter).globalMachine.State :=
  (((.rightOwner ()
        (initialProfiledRawJointUnitRightPolicyOwner A strategy initial policy
          bank source)), oldOutputOne),
    ((.rightReceiver ()
        (initialProfiledRawJointUnitRightPolicyReceiver A strategy initial
          policy source row)), oldOutputTwo))

/-- The option staged by the latest right-controller round.  It is retained
only to state the exact local control invariant; continuing a fixed right
block does not inspect it. -/
noncomputable def profiledRawJointUnitRightStagedAfter
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (env : Nat → In₂ × In₁) : Nat →
      Option (ProfiledRawJointUnitLeftPolicyMacro A strategy
        (initial.code A) policy)
  | 0 => none
  | n + 1 =>
      let state := profiledRawJointUnitRightPolicyFiniteStateAfter A strategy
        initial policy bank source (omegaPrefix env n)
      (stepProfiledRawJointUnitRightPolicyReceiverFor A strategy initial
        policy bank source state.1 row state.2 (env n)).2.2

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact ordinary controls reached after `n` rounds of the re-rooted
all-right machine.  The two stored Moore outputs are intentionally
existential: only the post-transition outputs enter the physical word. -/
theorem profiledRawJointUnitFreshMatchedRight_controls
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₂ × In₁) : ∀ n : Nat,
    ∃ outputOne outputTwo,
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        (profiledRawJointUnitFreshMatchedRightState A strategy initial policy
          bank adapter source row oldOutputOne oldOutputTwo)).globalStateTrace
          (profiledRawJointUnitStrictRightEnvironment env) n =
        (((.rightOwner () ⟨source,
            (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy
              initial policy bank source (omegaPrefix env n)).1⟩), outputOne),
          ((.rightReceiver () ⟨source, row,
            (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy
              initial policy bank source (omegaPrefix env n)).2,
            profiledRawJointUnitRightStagedAfter A strategy initial policy bank
              source row env n⟩), outputTwo)) := by
  intro n
  induction n with
  | zero =>
      exact ⟨oldOutputOne, oldOutputTwo, rfl⟩
  | succ n ih =>
      obtain ⟨outputOne, outputTwo, ih⟩ := ih
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ, ih]
      let current := profiledRawJointUnitRightPolicyFiniteStateAfter A strategy
        initial policy bank source (omegaPrefix env n)
      let owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy
          initial policy bank := ⟨source, current.1⟩
      let receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
          initial policy := ⟨source, row, current.2,
        profiledRawJointUnitRightStagedAfter A strategy initial policy bank
          source row env n⟩
      let oneNext := stepProfiledRawJointUnitRightPolicyOwner A strategy
        initial policy bank owner (env n).2
      let twoNext := continueProfiledRawJointUnitRightPolicyReceiver A strategy
        initial policy bank receiver owner (env n)
      refine ⟨oneNext.1, twoNext.1, ?_⟩
      rw [omegaPrefix_succ]
      simp [ProfiledRawJointLeaderFreeKernel.globalMachine,
        FiniteGlobalRoundMachine.reroot,
        profiledRawJointUnitStrictRightEnvironment,
        ProfiledRawJointLeaderFreeKernel.physicalController,
        ProfiledRawJointLeaderFreeKernel.noRecvOne,
        ProfiledRawJointLeaderFreeKernel.recvTwo,
        profiledRawJointUnitPolicyLeaderFreeKernel,
        profiledRawJointUnitRightPolicyFiniteStateAfter,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        stepProfiledRawJointUnitRightPolicyFiniteState,
        stepProfiledRawJointUnitRightPolicyOwner,
        continueProfiledRawJointUnitRightPolicyReceiver,
        profiledRawJointUnitRightPolicyOwnerControlFor,
        profiledRawJointUnitRightStagedAfter,
        current, owner, receiver, oneNext, twoNext]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The finite-prefix presentation used by a one-round carrier lemma and the
literal omega play have the same round at the end of that prefix. -/
theorem profiledRawJointUnitRightPolicyPlay_prefix_eq_omegaPlay
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (env : Nat → In₂ × In₁) (n : Nat) :
    profiledRawJointUnitRightPolicyPlay A strategy initial policy bank source
        (omegaPrefix env n) (env n) n =
      profiledRawJointUnitRightPolicyOmegaPlay A bank source env n := by
  let finiteWord := omegaPrefix env n ++ [env n]
  let finiteEnv : Nat → In₂ × In₁ := omegaOfList finiteWord
  have hpast : omegaPrefix finiteEnv n = omegaPrefix env n := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro k hkLeft hkRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hkN : k < n := by
        simpa [omegaPrefix] using hkRight
      have hkFinite : k < finiteWord.length := by
        simp [finiteWord, omegaPrefix]
        exact Nat.le_of_lt hkN
      change omegaOfList finiteWord k = env k
      rw [omegaOfList_eq_getElem finiteWord k hkFinite]
      change (omegaPrefix env n ++ [env n])[k] = env k
      rw [List.getElem_append_left hkRight]
      simp [omegaPrefix]
  have hmove : finiteEnv n = env n := by
    have hnFinite : n < finiteWord.length := by
      simp [finiteWord, omegaPrefix]
    change omegaOfList finiteWord n = env n
    rw [omegaOfList_eq_getElem finiteWord n hnFinite]
    change (omegaPrefix env n ++ [env n])[n] = env n
    rw [List.getElem_append_right (by simp [omegaPrefix])]
    simp [omegaPrefix]
  simp [profiledRawJointUnitRightPolicyPlay,
    profiledRawJointUnitRightPolicyOmegaPlay, treePlay,
    narrowedInducedTree, blockLabelApply,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    finiteWord, finiteEnv, hpast, hmove]

/-- One physical right round computed from the finite state at `past`.  This
local definition deliberately does not depend on the recurrent-switching
trace layer. -/
noncomputable def profiledRawJointUnitFreshRightCarrierRecordAt
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁))
    (pending : Option (ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)) (move : In₂ × In₁) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  let state := profiledRawJointUnitRightPolicyFiniteStateAfter A strategy
    initial policy bank source past
  let owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank := ⟨source, state.1⟩
  let receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy := ⟨source, row, state.2, pending⟩
  let one := stepProfiledRawJointUnitRightPolicyOwner A strategy initial policy
    bank owner move.2
  let two := continueProfiledRawJointUnitRightPolicyReceiver A strategy initial
    policy bank receiver owner move
  rightRoundRecord move one.1 two.1

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The local carrier record is the certificate record of the same narrowed
controller play. -/
theorem profiledRawJointUnitFreshRightCarrierRecordAt_eq_playRecord
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁))
    (pending : Option (ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)) (move : In₂ × In₁) :
    profiledRawJointUnitFreshRightCarrierRecordAt A strategy initial policy
        bank source row past pending move =
      pairedRightRecordForRow row
        (profiledRawJointUnitRightPhysicalLetter A
          (profiledRawJointUnitRightPolicyPlay A strategy initial policy bank
            source past move past.length)) := by
  have hat := profiledRawJointUnitRightPolicy_treePlay_at_prefix A strategy
    initial policy bank source past move
  change profiledRawJointUnitRightPolicyPlay A strategy initial policy bank
    source past move past.length = _ at hat
  rw [hat]
  cases row <;>
    simp [profiledRawJointUnitFreshRightCarrierRecordAt,
      profiledRawJointUnitRightPolicyFiniteStateAfter_eq,
      stepProfiledRawJointUnitRightPolicyOwner,
      continueProfiledRawJointUnitRightPolicyReceiver,
      profiledRawJointUnitRightPolicyOwnerControlFor,
      profiledRawJointUnitRightPhysicalLetter, indexedTargetPhysicalLetter,
      narrowedRecord, pairedRightRecordForRow, pairedRightInformedForRow]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A freshly matched right controller emits exactly the physical omega word
used by `right_physical_acceptsFrom`.  The arbitrary outputs stored at the
re-root disappear because the global word has post-transition Moore timing. -/
theorem profiledRawJointUnitFreshMatchedRight_traceWord
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₂ × In₁) :
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      (profiledRawJointUnitFreshMatchedRightState A strategy initial policy
        bank adapter source row oldOutputOne oldOutputTwo)).globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        (profiledRawJointUnitStrictRightEnvironment env) =
      fun n ↦ pairedRightRecordForRow row
        (profiledRawJointUnitRightPhysicalLetter A
          (profiledRawJointUnitRightPolicyOmegaPlay A bank source env n)) := by
  funext n
  obtain ⟨outputOne, outputTwo, hcontrols⟩ :=
    profiledRawJointUnitFreshMatchedRight_controls A strategy initial policy
      bank adapter source row oldOutputOne oldOutputTwo env n
  rw [FiniteGlobalRoundMachine.globalMachineTraceWord,
    FiniteGlobalRoundMachine.globalStateTrace_succ, hcontrols]
  change profiledRawJointUnitFreshRightCarrierRecordAt A strategy initial
      policy bank source row
        (omegaPrefix env n)
        (profiledRawJointUnitRightStagedAfter A strategy initial policy bank
          source row env n) (env n) = _
  rw [profiledRawJointUnitFreshRightCarrierRecordAt_eq_playRecord,
    show (omegaPrefix env n).length = n by simp [omegaPrefix],
    profiledRawJointUnitRightPolicyPlay_prefix_eq_omegaPlay]

/-! ## Fresh matched-left re-root -/

/-- The joint Moore state at a fresh matched-left policy root. -/
noncomputable def profiledRawJointUnitFreshMatchedLeftState
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) :
    (UnitKernel A strategy initial policy bank adapter).globalMachine.State :=
  (((.leftReceiver ()
        (initialProfiledRawJointUnitLeftPolicyReceiver A strategy initial
          policy source row)), oldOutputOne),
    ((.leftOwner ()
        (initialProfiledRawJointUnitLeftPolicyOwner A strategy initial policy
          bank source)), oldOutputTwo))

/-- The opposite macro staged by the latest left-controller round. -/
noncomputable def profiledRawJointUnitLeftStagedAfter
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (env : Nat → In₁ × In₂) : Nat →
      Option (ProfiledRawJointUnitRightPolicyMacro A strategy
        (initial.code A) policy)
  | 0 => none
  | n + 1 =>
      let state := profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy
        initial policy bank source (omegaPrefix env n)
      (stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy initial policy
        bank source state.1 row state.2 (env n)).2.2

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact ordinary controls reached after `n` all-left rounds. -/
theorem profiledRawJointUnitFreshMatchedLeft_controls
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₁ × In₂) : ∀ n : Nat,
    ∃ outputOne outputTwo,
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        (profiledRawJointUnitFreshMatchedLeftState A strategy initial policy
          bank adapter source row oldOutputOne oldOutputTwo)).globalStateTrace
          (profiledRawJointUnitStrictLeftEnvironment env) n =
        (((.leftReceiver () ⟨source, row,
            (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
              policy bank source (omegaPrefix env n)).2,
            profiledRawJointUnitLeftStagedAfter A strategy initial policy bank
              source row env n⟩), outputOne),
          ((.leftOwner () ⟨source,
            (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
              policy bank source (omegaPrefix env n)).1⟩), outputTwo)) := by
  intro n
  induction n with
  | zero =>
      exact ⟨oldOutputOne, oldOutputTwo, rfl⟩
  | succ n ih =>
      obtain ⟨outputOne, outputTwo, ih⟩ := ih
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ, ih]
      let current := profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy
        initial policy bank source (omegaPrefix env n)
      let receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
          initial policy := ⟨source, row, current.2,
        profiledRawJointUnitLeftStagedAfter A strategy initial policy bank
          source row env n⟩
      let owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
          policy bank := ⟨source, current.1⟩
      let oneNext := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
        initial policy bank receiver owner (env n)
      let twoNext := stepProfiledRawJointUnitLeftPolicyOwner A strategy initial
        policy bank owner (env n).2
      refine ⟨oneNext.1, twoNext.1, ?_⟩
      rw [omegaPrefix_succ]
      simp [ProfiledRawJointLeaderFreeKernel.globalMachine,
        FiniteGlobalRoundMachine.reroot,
        profiledRawJointUnitStrictLeftEnvironment,
        ProfiledRawJointLeaderFreeKernel.physicalController,
        ProfiledRawJointLeaderFreeKernel.recvOne,
        ProfiledRawJointLeaderFreeKernel.noRecvTwo,
        profiledRawJointUnitPolicyLeaderFreeKernel,
        profiledRawJointUnitLeftPolicyFiniteStateAfter,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        stepProfiledRawJointUnitLeftPolicyFiniteState,
        stepProfiledRawJointUnitLeftPolicyOwner,
        continueProfiledRawJointUnitLeftPolicyReceiver,
        profiledRawJointUnitLeftPolicyOwnerControlFor,
        profiledRawJointUnitLeftStagedAfter,
        current, receiver, owner, oneNext, twoNext]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Finite-prefix and omega presentations agree at the selected left round. -/
theorem profiledRawJointUnitLeftPolicyPlay_prefix_eq_omegaPlay
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (env : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointUnitLeftPolicyPlay A strategy initial policy bank source
        (omegaPrefix env n) (env n) n =
      profiledRawJointUnitLeftPolicyOmegaPlay A bank source env n := by
  let finiteWord := omegaPrefix env n ++ [env n]
  let finiteEnv : Nat → In₁ × In₂ := omegaOfList finiteWord
  have hpast : omegaPrefix finiteEnv n = omegaPrefix env n := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro k hkLeft hkRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hkN : k < n := by
        simpa [omegaPrefix] using hkRight
      have hkFinite : k < finiteWord.length := by
        simp [finiteWord, omegaPrefix]
        exact Nat.le_of_lt hkN
      change omegaOfList finiteWord k = env k
      rw [omegaOfList_eq_getElem finiteWord k hkFinite]
      change (omegaPrefix env n ++ [env n])[k] = env k
      rw [List.getElem_append_left hkRight]
      simp [omegaPrefix]
  have hmove : finiteEnv n = env n := by
    have hnFinite : n < finiteWord.length := by
      simp [finiteWord, omegaPrefix]
    change omegaOfList finiteWord n = env n
    rw [omegaOfList_eq_getElem finiteWord n hnFinite]
    change (omegaPrefix env n ++ [env n])[n] = env n
    rw [List.getElem_append_right (by simp [omegaPrefix])]
    simp [omegaPrefix]
  simp [profiledRawJointUnitLeftPolicyPlay,
    profiledRawJointUnitLeftPolicyOmegaPlay, treePlay,
    narrowedInducedTree, blockLabelApply,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    finiteWord, finiteEnv, hpast, hmove]

/-- One physical left round computed from its finite controller state. -/
noncomputable def profiledRawJointUnitFreshLeftCarrierRecordAt
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂))
    (pending : Option (ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)) (move : In₁ × In₂) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  let state := profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy
    initial policy bank source past
  let receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy := ⟨source, row, state.2, pending⟩
  let owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank := ⟨source, state.1⟩
  let one := continueProfiledRawJointUnitLeftPolicyReceiver A strategy initial
    policy bank receiver owner move
  let two := stepProfiledRawJointUnitLeftPolicyOwner A strategy initial policy
    bank owner move.2
  leftRoundRecord move one.1 two.1

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left carrier record equals its certificate play record. -/
theorem profiledRawJointUnitFreshLeftCarrierRecordAt_eq_playRecord
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂))
    (pending : Option (ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)) (move : In₁ × In₂) :
    profiledRawJointUnitFreshLeftCarrierRecordAt A strategy initial policy bank
        source row past pending move =
      pairedLeftRecordForRow row
        (profiledRawJointUnitLeftPhysicalLetter A
          (profiledRawJointUnitLeftPolicyPlay A strategy initial policy bank
            source past move past.length)) := by
  have hat := profiledRawJointUnitLeftPolicy_treePlay_at_prefix A strategy
    initial policy bank source past move
  change profiledRawJointUnitLeftPolicyPlay A strategy initial policy bank
    source past move past.length = _ at hat
  rw [hat]
  cases row <;>
    simp [profiledRawJointUnitFreshLeftCarrierRecordAt,
      profiledRawJointUnitLeftPolicyFiniteStateAfter_eq,
      stepProfiledRawJointUnitLeftPolicyOwner,
      continueProfiledRawJointUnitLeftPolicyReceiver,
      profiledRawJointUnitLeftPolicyOwnerControlFor,
      profiledRawJointUnitLeftPhysicalLetter, indexedTargetPhysicalLetter,
      narrowedRecord, pairedLeftRecordForRow, pairedLeftInformedForRow]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Fresh matched-left trace-word identification. -/
theorem profiledRawJointUnitFreshMatchedLeft_traceWord
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₁ × In₂) :
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      (profiledRawJointUnitFreshMatchedLeftState A strategy initial policy bank
        adapter source row oldOutputOne oldOutputTwo)).globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        (profiledRawJointUnitStrictLeftEnvironment env) =
      fun n ↦ pairedLeftRecordForRow row
        (profiledRawJointUnitLeftPhysicalLetter A
          (profiledRawJointUnitLeftPolicyOmegaPlay A bank source env n)) := by
  funext n
  obtain ⟨outputOne, outputTwo, hcontrols⟩ :=
    profiledRawJointUnitFreshMatchedLeft_controls A strategy initial policy bank
      adapter source row oldOutputOne oldOutputTwo env n
  rw [FiniteGlobalRoundMachine.globalMachineTraceWord,
    FiniteGlobalRoundMachine.globalStateTrace_succ, hcontrols]
  change profiledRawJointUnitFreshLeftCarrierRecordAt A strategy initial policy
      bank source row (omegaPrefix env n)
        (profiledRawJointUnitLeftStagedAfter A strategy initial policy bank
          source row env n) (env n) = _
  rw [profiledRawJointUnitFreshLeftCarrierRecordAt_eq_playRecord,
    show (omegaPrefix env n).length = n by simp [omegaPrefix],
    profiledRawJointUnitLeftPolicyPlay_prefix_eq_omegaPlay]

/-! ## Acceptance from an actual physical suffix -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- `AcceptsFrom` is exactly min-even parity of the explicit run-from-state
priority sequence. -/
theorem acceptsFrom_iff_natSeqMinEvenParity_runFrom
    (state : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)) :
    A.AcceptsFrom state word ↔
      NatSeqMinEvenParity (fun n ↦ A.priority (A.runFrom state word n)) := by
  rfl

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- A fresh matched-right reroot is accepted from the row-selected source
state. -/
theorem profiledRawJointUnitFreshMatchedRight_acceptsFrom
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₂ × In₁) :
    A.AcceptsFrom (pairedCodeStateForRow A row source.slot.1.1)
      (((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        (profiledRawJointUnitFreshMatchedRightState A strategy initial policy
          bank adapter source row oldOutputOne oldOutputTwo)).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          (profiledRawJointUnitStrictRightEnvironment env)) := by
  rw [profiledRawJointUnitFreshMatchedRight_traceWord]
  cases row with
  | first =>
      simpa [pairedCodeStateForRow] using
        (bank.right_physical_acceptsFrom A source .first env)
  | both =>
      simpa [pairedCodeStateForRow] using
        (bank.right_physical_acceptsFrom A source .both env)

/-- Fresh matched-left acceptance mirror. -/
theorem profiledRawJointUnitFreshMatchedLeft_acceptsFrom
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₁ × In₂) :
    A.AcceptsFrom (pairedCodeStateForRow A row source.slot.1.1)
      (((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        (profiledRawJointUnitFreshMatchedLeftState A strategy initial policy
          bank adapter source row oldOutputOne oldOutputTwo)).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          (profiledRawJointUnitStrictLeftEnvironment env)) := by
  rw [profiledRawJointUnitFreshMatchedLeft_traceWord]
  cases row with
  | first =>
      simpa [pairedCodeStateForRow] using
        (bank.left_physical_acceptsFrom A source .first env)
  | both =>
      simpa [pairedCodeStateForRow] using
        (bank.left_physical_acceptsFrom A source .both env)

/-- If an actual execution reaches a fresh matched-right control and its
environment suffix is all-right, then the dropped physical word is literally
the certified right omega word. -/
theorem profiledRawJointUnitMatchedRight_suffixWord
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (env : Nat → In₂ × In₁)
    (hcontrol :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
          physicalEnv start =
        profiledRawJointUnitFreshMatchedRightState A strategy initial policy
          bank adapter source row oldOutputOne oldOutputTwo)
    (henv : OmegaWord.drop physicalEnv start =
      profiledRawJointUnitStrictRightEnvironment env) :
    OmegaWord.drop
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv) start =
      fun n ↦ pairedRightRecordForRow row
        (profiledRawJointUnitRightPhysicalLetter A
          (profiledRawJointUnitRightPolicyOmegaPlay A bank source env n)) := by
  let G := (UnitKernel A strategy initial policy bank adapter).globalMachine
  have hreroot := G.reroot_globalMachineTraceWord_drop
    (UnitKernel A strategy initial policy bank adapter).globalOutputOne
    (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
    physicalEnv start
  rw [hcontrol, henv,
    profiledRawJointUnitFreshMatchedRight_traceWord] at hreroot
  exact hreroot.symm

/-- The right suffix is accepted from the *actual* post-prefix checker state.
The state/source equality is the sole semantic seam and is kept as an
explicit premise. -/
theorem profiledRawJointUnitMatchedRight_acceptsFrom_actual
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (env : Nat → In₂ × In₁)
    (hcontrol :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
          physicalEnv start =
        profiledRawJointUnitFreshMatchedRightState A strategy initial policy
          bank adapter source row oldOutputOne oldOutputTwo)
    (henv : OmegaWord.drop physicalEnv start =
      profiledRawJointUnitStrictRightEnvironment env)
    (hstate :
      A.run ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv) start =
        pairedCodeStateForRow A row source.slot.1.1) :
    A.AcceptsFrom
      (A.run ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv) start)
      (OmegaWord.drop
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv) start) := by
  rw [hstate,
    profiledRawJointUnitMatchedRight_suffixWord A strategy initial policy bank
      adapter source row oldOutputOne oldOutputTwo physicalEnv start env
        hcontrol henv]
  cases row with
  | first =>
      simpa [pairedCodeStateForRow] using
        (bank.right_physical_acceptsFrom A source .first env)
  | both =>
      simpa [pairedCodeStateForRow] using
        (bank.right_physical_acceptsFrom A source .both env)

/-- Exact eventual strict-right tail parity, indexed in the original physical
run.  The checker is not restarted: its state at `start` is used above. -/
theorem profiledRawJointUnitMatchedRight_tailParity
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (env : Nat → In₂ × In₁)
    (hcontrol :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
          physicalEnv start =
        profiledRawJointUnitFreshMatchedRightState A strategy initial policy
          bank adapter source row oldOutputOne oldOutputTwo)
    (henv : OmegaWord.drop physicalEnv start =
      profiledRawJointUnitStrictRightEnvironment env)
    (hstate :
      A.run ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv) start =
        pairedCodeStateForRow A row source.slot.1.1) :
    NatSeqMinEvenParity (fun n ↦ A.priority
      (A.run ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv) (start + n))) := by
  let word := (UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
      (UnitKernel A strategy initial policy bank adapter).globalOutputOne
      (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
      physicalEnv
  have haccepts := profiledRawJointUnitMatchedRight_acceptsFrom_actual A
    strategy initial policy bank adapter source row oldOutputOne oldOutputTwo
      physicalEnv start env hcontrol henv hstate
  have hparity :=
    (acceptsFrom_iff_natSeqMinEvenParity_runFrom A (A.run word start)
      (OmegaWord.drop word start)).mp haccepts
  have heq :
      (fun n ↦ A.priority
        (A.runFrom (A.run word start) (OmegaWord.drop word start) n)) =
      (fun n ↦ A.priority (A.run word (start + n))) := by
    funext n
    exact congrArg A.priority (A.runFrom_drop A.initial word start n)
  rw [heq] at hparity
  exact hparity

/-- Actual matched-left suffix word, obtained by the generic machine-reroot
identity and the operational left trace equality. -/
theorem profiledRawJointUnitMatchedLeft_suffixWord
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (env : Nat → In₁ × In₂)
    (hcontrol :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
          physicalEnv start =
        profiledRawJointUnitFreshMatchedLeftState A strategy initial policy bank
          adapter source row oldOutputOne oldOutputTwo)
    (henv : OmegaWord.drop physicalEnv start =
      profiledRawJointUnitStrictLeftEnvironment env) :
    OmegaWord.drop
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv) start =
      fun n ↦ pairedLeftRecordForRow row
        (profiledRawJointUnitLeftPhysicalLetter A
          (profiledRawJointUnitLeftPolicyOmegaPlay A bank source env n)) := by
  let G := (UnitKernel A strategy initial policy bank adapter).globalMachine
  have hreroot := G.reroot_globalMachineTraceWord_drop
    (UnitKernel A strategy initial policy bank adapter).globalOutputOne
    (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
    physicalEnv start
  rw [hcontrol, henv,
    profiledRawJointUnitFreshMatchedLeft_traceWord] at hreroot
  exact hreroot.symm

/-- Left strict-tail acceptance from the actual post-prefix DPA state. -/
theorem profiledRawJointUnitMatchedLeft_acceptsFrom_actual
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (env : Nat → In₁ × In₂)
    (hcontrol :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
          physicalEnv start =
        profiledRawJointUnitFreshMatchedLeftState A strategy initial policy bank
          adapter source row oldOutputOne oldOutputTwo)
    (henv : OmegaWord.drop physicalEnv start =
      profiledRawJointUnitStrictLeftEnvironment env)
    (hstate :
      A.run ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv) start =
        pairedCodeStateForRow A row source.slot.1.1) :
    A.AcceptsFrom
      (A.run ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv) start)
      (OmegaWord.drop
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv) start) := by
  rw [hstate,
    profiledRawJointUnitMatchedLeft_suffixWord A strategy initial policy bank
      adapter source row oldOutputOne oldOutputTwo physicalEnv start env
        hcontrol henv]
  cases row with
  | first =>
      simpa [pairedCodeStateForRow] using
        (bank.left_physical_acceptsFrom A source .first env)
  | both =>
      simpa [pairedCodeStateForRow] using
        (bank.left_physical_acceptsFrom A source .both env)

/-- Exact eventual strict-left tail parity in the original physical run. -/
theorem profiledRawJointUnitMatchedLeft_tailParity
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (env : Nat → In₁ × In₂)
    (hcontrol :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
          physicalEnv start =
        profiledRawJointUnitFreshMatchedLeftState A strategy initial policy bank
          adapter source row oldOutputOne oldOutputTwo)
    (henv : OmegaWord.drop physicalEnv start =
      profiledRawJointUnitStrictLeftEnvironment env)
    (hstate :
      A.run ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv) start =
        pairedCodeStateForRow A row source.slot.1.1) :
    NatSeqMinEvenParity (fun n ↦ A.priority
      (A.run ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv) (start + n))) := by
  let word := (UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
      (UnitKernel A strategy initial policy bank adapter).globalOutputOne
      (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
      physicalEnv
  have haccepts := profiledRawJointUnitMatchedLeft_acceptsFrom_actual A strategy
    initial policy bank adapter source row oldOutputOne oldOutputTwo physicalEnv
      start env hcontrol henv hstate
  have hparity :=
    (acceptsFrom_iff_natSeqMinEvenParity_runFrom A (A.run word start)
      (OmegaWord.drop word start)).mp haccepts
  have heq :
      (fun n ↦ A.priority
        (A.runFrom (A.run word start) (OmegaWord.drop word start) n)) =
      (fun n ↦ A.priority (A.run word (start + n))) := by
    funext n
    exact congrArg A.priority (A.runFrom_drop A.initial word start n)
  rw [heq] at hparity
  exact hparity

end

end

end DetParityAutomaton

end DistributedSynthesis
