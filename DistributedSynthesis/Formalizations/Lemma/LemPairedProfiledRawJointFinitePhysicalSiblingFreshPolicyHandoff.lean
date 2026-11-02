/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSiblingHiddenThreadContinuation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitRootOrientedCloseCuts

/-!
# Installing one fresh fixed policy after a finite sibling move

The canonical finite sibling move emits a finite incidence code.  Its checked
target law says simultaneously that this code is the literal physical close
and that it belongs to the common semantic target relation.  The latter fact
selects one recursively exact semantic root and hence one finite rational
policy.  This file installs that policy **once** at the emitted target.

The root macro is recovered from the physical-close shape: a right close has
one live left slot, and a left close has one live right slot.  Thereafter the
existing scheduled-close construction follows only `AllowedTarget` edges of
this unchanged policy.  Its policy-image theorem therefore supplies parity
without requiring semantic source alignment at successive rational states.

All sides, semantic roots, and schedules below are proof data.  The canonical
finite move contains no graph, orientation, or strict-leader observation, and
neither local process is told which sibling member is the strict one.
-/

namespace DistributedSynthesis

universe u v w x y s i₁ i₂ e₁ e₂

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

/-- Everything needed to enter the already proved recurrent fixed-policy
construction after one sibling close.  In particular, `policy` is selected
once, while `seed` is its literal root macro. -/
structure ProfiledRawJointSiblingFreshPolicyPackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) where
  initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)
  initial_code : initial.code A = target
  policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (initial.code A)
  seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
    policy
  seed_state : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
    policy.run []

/-- Orientation-refined fresh package produced by a right-block close.  The
root is explicitly a left macro; retaining this fact prevents a later global
bank from choosing a package of the wrong root orientation merely because it
has the same public incidence code. -/
structure ProfiledRawJointRightCloseFreshPolicyPackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) where
  initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)
  initial_code : initial.code A = target
  policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (initial.code A)
  seed : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
    policy
  seed_state : seed.state = policy.run []

/-- Orientation-refined fresh package produced by a left-block close. -/
structure ProfiledRawJointLeftCloseFreshPolicyPackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) where
  initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)
  initial_code : initial.code A = target
  policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (initial.code A)
  seed : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
    policy
  seed_state : seed.state = policy.run []

namespace ProfiledRawJointRightCloseFreshPolicyPackage

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {target : ProfiledRawJointIncidenceCode A (I := Unit)}

/-- Forget only the already-recorded right-close orientation. -/
def toFreshPolicyPackage
    (package : ProfiledRawJointRightCloseFreshPolicyPackage A strategy target) :
    ProfiledRawJointSiblingFreshPolicyPackage A strategy target :=
  ⟨package.initial, package.initial_code, package.policy, .inr package.seed,
    package.seed_state⟩

end ProfiledRawJointRightCloseFreshPolicyPackage

namespace ProfiledRawJointLeftCloseFreshPolicyPackage

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {target : ProfiledRawJointIncidenceCode A (I := Unit)}

/-- Forget only the already-recorded left-close orientation. -/
def toFreshPolicyPackage
    (package : ProfiledRawJointLeftCloseFreshPolicyPackage A strategy target) :
    ProfiledRawJointSiblingFreshPolicyPackage A strategy target :=
  ⟨package.initial, package.initial_code, package.policy, .inl package.seed,
    package.seed_state⟩

end ProfiledRawJointLeftCloseFreshPolicyPackage

namespace ProfiledRawJointSiblingFreshPolicyPackage

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {target : ProfiledRawJointIncidenceCode A (I := Unit)}

/-- The unconditional finite controller bank belonging to the one selected
policy. -/
noncomputable def bank
    (package : ProfiledRawJointSiblingFreshPolicyPackage A strategy target) :
    ProfiledRawJointUnitPolicyControllerBank A strategy package.initial
      package.policy :=
  profiledRawJointUnitPolicyControllerBank A strategy package.initial
    package.policy

/-- Any proof-side close schedule now produces one genuine infinite thread
of the unchanged policy.  No semantic witness is reselected between epochs. -/
noncomputable def scheduledThread
    (package : ProfiledRawJointSiblingFreshPolicyPackage A strategy target)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy
      package.initial package.policy) :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingThread A package.policy :=
  profiledRawJointUnitPolicyScheduledAlternatingThread A strategy
    package.initial package.policy (package.bank A) package.seed schedule
      package.seed_state

/-- The positive-time code word of every scheduled continuation is accepted.
This is the fixed-policy anti-mosaic theorem at the canonical sibling seam. -/
theorem scheduledThread_codeWord_accepts
    (package : ProfiledRawJointSiblingFreshPolicyPackage A strategy target)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy
      package.initial package.policy) :
    (profiledRawJointOneSidedCodeParityDPA A (package.initial.code A)).Accepts
      (fun n ↦
        ((package.scheduledThread A schedule).states A package.policy
          (n + 1)).1) :=
  (package.scheduledThread A schedule).codeWord_accepts A package.policy

/-- Once the actual recurrent trace supplies the already named physical-slice
invariant, the fresh policy proves acceptance of the physical trace. -/
theorem physicalTrace_accepts_of_recurrentSlices
    (package : ProfiledRawJointSiblingFreshPolicyPackage A strategy target)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph))
    (lower : Nat)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy
      package.initial package.policy)
    (slices :
      let extraction :=
        recurrentEnvironmentEpochCutExtractionAfter env hboth lower
      ProfiledRawJointUnitPolicyScheduledPhysicalSlices A strategy
        package.initial package.policy (package.bank A) G outputOne outputTwo
          env package.seed schedule extraction.start extraction.cuts) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  let extraction := recurrentEnvironmentEpochCutExtractionAfter env hboth lower
  exact profiledRawJointUnitPolicyScheduledTrace_accepts_of_recurrent A
    strategy package.initial package.policy (package.bank A) G outputOne
      outputTwo env hboth lower package.seed schedule package.seed_state
        (fun k ↦ by
          exact slices.blockMin_eq A strategy package.initial package.policy
            (package.bank A) k)

/-- Persistent strict reversals use the same one-policy path and the same
physical-slice adapter. -/
theorem physicalTrace_accepts_of_persistentReversalSlices
    (package : ProfiledRawJointSiblingFreshPolicyPackage A strategy target)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hpersistent : PersistentStrictReversalTail (fun n ↦ (env n).graph))
    (lower : Nat)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy
      package.initial package.policy)
    (slices :
      let extraction :=
        persistentStrictReversalEpochCutExtractionAfter env hpersistent lower
      ProfiledRawJointUnitPolicyScheduledPhysicalSlices A strategy
        package.initial package.policy (package.bank A) G outputOne outputTwo
          env package.seed schedule extraction.start extraction.cuts) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  let extraction :=
    persistentStrictReversalEpochCutExtractionAfter env hpersistent lower
  exact
    profiledRawJointUnitPolicyScheduledTrace_accepts_of_persistentReversal A
      strategy package.initial package.policy (package.bank A) G outputOne
        outputTwo env hpersistent lower package.seed schedule package.seed_state
          (fun k ↦ by
            exact slices.blockMin_eq A strategy package.initial package.policy
              (package.bank A) k)

/-- Strongest operational endpoint currently available in the repository.
The root-oriented clock already handles graph/root mismatches, makes them
zero-open singleton blocks, builds every physical slice, and transfers parity.
Accordingly the actual leader-free carrier owes only the three fields of
`ProfiledRawJointUnitPolicyFixedRerootInvariant`: entry DPA state, query-list
length, and matched/cross trace alignment at graph/root matches. -/
theorem physicalTrace_accepts_of_fixedRerootInvariant
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (package : ProfiledRawJointSiblingFreshPolicyPackage A strategy target)
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy
      package.initial package.policy (package.bank A) InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy
      package.initial package.policy)
    (invariant : ProfiledRawJointUnitPolicyFixedRerootInvariant A strategy
      package.initial package.policy (package.bank A) adapter physicalEnv base
        hterm package.seed schedule) :
    A.Accepts
      ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy package.initial
        package.policy (package.bank A) adapter).globalMachine.globalMachineTraceWord
          (profiledRawJointUnitPolicyLeaderFreeKernel A strategy
            package.initial package.policy
              (package.bank A) adapter).globalOutputOne
          (profiledRawJointUnitPolicyLeaderFreeKernel A strategy
            package.initial package.policy
              (package.bank A) adapter).globalOutputTwo
          physicalEnv) :=
  profiledRawJointUnitPolicy_accepts_of_fixedRerootInvariant A strategy
    package.initial package.policy (package.bank A) adapter physicalEnv base
      hterm package.seed schedule package.seed_state invariant

end ProfiledRawJointSiblingFreshPolicyPackage

/-! ## Building the fresh package at a checked sibling close -/

section
omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂]

/-- A checked right sibling close starts a fresh policy at a left macro.  This
is the orientation-refined form needed by a target-indexed recurrent bank. -/
theorem nonempty_profiledRawJointRightCloseFreshPolicyPackage_of_close
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : ProfiledRawJointRightSiblingSharedAllowedTarget A family
      direction target)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A target) =
      pairedRightCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointRightCloseFreshPolicyPackage A strategy target) := by
  classical
  let continuation := profiledRawJointRightSiblingContinuationRoot A family
    direction target htarget
  let initial := continuation.state
  let policy := Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin
      initial)
  have hinitial : initial.code A = target := continuation.code_eq
  have hrootCode : (policy.run []).1 = initial.code A :=
    congrArg Prod.fst policy.accepts.1.1
  cases hslot : target.family.left () with
  | none =>
      simp [profiledRawJointUnitRightTargetProjection, hslot,
        erasePairedProfiledState, pairedRightCloseTarget] at hclose
  | some slot =>
      let seed : ProfiledRawJointUnitLeftPolicyMacro A strategy
          (initial.code A) policy := {
        state := policy.run []
        reachable := ⟨[], rfl⟩
        slot := slot
        active_slot := by
          rw [hrootCode, hinitial, hslot] }
      exact ⟨⟨initial, hinitial, policy, seed, rfl⟩⟩

/-- A checked left sibling close starts a fresh policy at a right macro. -/
theorem nonempty_profiledRawJointLeftCloseFreshPolicyPackage_of_close
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : ProfiledRawJointLeftSiblingSharedAllowedTarget A family
      direction target)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A target) =
      pairedLeftCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointLeftCloseFreshPolicyPackage A strategy target) := by
  classical
  let continuation := profiledRawJointLeftSiblingContinuationRoot A family
    direction target htarget
  let initial := continuation.state
  let policy := Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin
      initial)
  have hinitial : initial.code A = target := continuation.code_eq
  have hrootCode : (policy.run []).1 = initial.code A :=
    congrArg Prod.fst policy.accepts.1.1
  cases hslot : target.family.right () with
  | none =>
      simp [profiledRawJointUnitLeftTargetProjection, hslot,
        erasePairedProfiledState, pairedLeftCloseTarget] at hclose
  | some slot =>
      let seed : ProfiledRawJointUnitRightPolicyMacro A strategy
          (initial.code A) policy := {
        state := policy.run []
        reachable := ⟨[], rfl⟩
        slot := slot
        active_slot := by
          rw [hrootCode, hinitial, hslot] }
      exact ⟨⟨initial, hinitial, policy, seed, rfl⟩⟩

/-- A checked right sibling close starts one fresh policy at a literal left
root macro. -/
theorem nonempty_profiledRawJointRightSiblingFreshPolicyPackage_of_close
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : ProfiledRawJointRightSiblingSharedAllowedTarget A family
      direction target)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A target) =
      pairedRightCloseTarget A scan row physical) :
    Nonempty (ProfiledRawJointSiblingFreshPolicyPackage A strategy target) := by
  classical
  let continuation := profiledRawJointRightSiblingContinuationRoot A family
    direction target htarget
  let initial := continuation.state
  let policy := Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin
      initial)
  have hinitial : initial.code A = target := continuation.code_eq
  have hrootCode : (policy.run []).1 = initial.code A :=
    congrArg Prod.fst policy.accepts.1.1
  cases hslot : target.family.left () with
  | none =>
      simp [profiledRawJointUnitRightTargetProjection, hslot,
        erasePairedProfiledState, pairedRightCloseTarget] at hclose
  | some slot =>
      let seed : ProfiledRawJointUnitLeftPolicyMacro A strategy
          (initial.code A) policy := {
        state := policy.run []
        reachable := ⟨[], rfl⟩
        slot := slot
        active_slot := by
          rw [hrootCode, hinitial, hslot] }
      exact ⟨⟨initial, hinitial, policy, .inr seed, rfl⟩⟩

/-- Left-close mirror: the fresh policy starts at a literal right macro. -/
theorem nonempty_profiledRawJointLeftSiblingFreshPolicyPackage_of_close
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : ProfiledRawJointLeftSiblingSharedAllowedTarget A family
      direction target)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A target) =
      pairedLeftCloseTarget A scan row physical) :
    Nonempty (ProfiledRawJointSiblingFreshPolicyPackage A strategy target) := by
  classical
  let continuation := profiledRawJointLeftSiblingContinuationRoot A family
    direction target htarget
  let initial := continuation.state
  let policy := Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin
      initial)
  have hinitial : initial.code A = target := continuation.code_eq
  have hrootCode : (policy.run []).1 = initial.code A :=
    congrArg Prod.fst policy.accepts.1.1
  cases hslot : target.family.right () with
  | none =>
      simp [profiledRawJointUnitLeftTargetProjection, hslot,
        erasePairedProfiledState, pairedLeftCloseTarget] at hclose
  | some slot =>
      let seed : ProfiledRawJointUnitRightPolicyMacro A strategy
          (initial.code A) policy := {
        state := policy.run []
        reachable := ⟨[], rfl⟩
        slot := slot
        active_slot := by
          rw [hrootCode, hinitial, hslot] }
      exact ⟨⟨initial, hinitial, policy, .inl seed, rfl⟩⟩

end

/-! ## Canonical finite-move handoff -/

/-- Every target actually emitted by the canonical finite right sibling move
is a literal physical close and installs one fresh fixed-policy package. -/
theorem profiledRawJointRightPhysicalSiblingMoveOf_targetFreshPolicy
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let move := profiledRawJointRightPhysicalSiblingMoveOf A hwin family
      direction semanticMember hmember
    let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    let target := (play n).2.1.target row
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A target) =
        pairedRightCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      Nonempty
        (ProfiledRawJointSiblingFreshPolicyPackage A strategy target) := by
  dsimp only
  obtain ⟨hclose, htarget⟩ :=
    profiledRawJointRightPhysicalSiblingMoveOf_targetSafe_shared A hwin family
      direction semanticMember hmember member env n row
  exact ⟨hclose,
    nonempty_profiledRawJointRightSiblingFreshPolicyPackage_of_close A hwin
      family direction _ htarget _ row _ hclose⟩

/-- Canonical left finite-move mirror. -/
theorem profiledRawJointLeftPhysicalSiblingMoveOf_targetFreshPolicy
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let move := profiledRawJointLeftPhysicalSiblingMoveOf A hwin family
      direction semanticMember hmember
    let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    let target := (play n).2.1.target row
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A target) =
        pairedLeftCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      Nonempty
        (ProfiledRawJointSiblingFreshPolicyPackage A strategy target) := by
  dsimp only
  obtain ⟨hclose, htarget⟩ :=
    profiledRawJointLeftPhysicalSiblingMoveOf_targetSafe_shared A hwin family
      direction semanticMember hmember member env n row
  exact ⟨hclose,
    nonempty_profiledRawJointLeftSiblingFreshPolicyPackage_of_close A hwin
      family direction _ htarget _ row _ hclose⟩

end

end DetParityAutomaton

end DistributedSynthesis
