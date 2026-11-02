/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRootForest
import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialDelayedRegularization

/-!
# Streaming the initial block into the one global rational policy

The outer transition of the input-free forest is indexed by a complete finite
block and therefore is not itself a streaming implementation.  This file
performs the required finite-branching regularization without choosing new
recurrent policies.  At each possible boundary the controller stages a finite
state in the image of the *same* global rational policy.  The monitor checks
the delayed DPA target and the one-round overlap carried by that state.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory

/-- Finite state staged by a streaming initial controller. -/
abbrev PairedInitialProfiledBankState :=
  ((pairedProfiledForestBase A).stateIndexedGuarded
    (pairedInitialProfiledGuardAllowed A)).State

/-! ## Initial-left block -/

/-- Physical initial-left output plus a state of the one global policy. -/
abbrev EndToEndInitialLeftReceiverOutput :=
  InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂) ×
    PairedInitialProfiledBankState A

def endToEndInitialLeftPhysicalLetter
    (letter : RealizedBlockRound In₁ In₂
      (EndToEndInitialLeftReceiverOutput A) Out₂) :
    InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  (letter.1, letter.2.1.1, letter.2.2)

/-- A staged state is admissible exactly when it occurs below the common
outer root, carries a process-one guard, and erases to the current delayed
target.  Membership in the image is proof-side and decidable classically; the
run-time value itself is finite. -/
def endToEndInitialLeftSourceOK
    (package : PairedInitialProfiledRationalPackage A)
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (source : PairedInitialProfiledBankState A) : Prop :=
  (∃ profile : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁),
      source.1 = some (Sum.inl profile)) ∧
    erasePairedProfiledState A source.2 =
      initialLeftDelayedTarget A scan letter ∧
    ∃ direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂),
      package.next direction = source

/-- The guard staged on the preceding boundary must agree with the current
physical informed output. -/
def endToEndInitialLeftOverlapOK
    (pending : Option (PairedInitialProfiledBankState A))
    (letter : RealizedBlockRound In₁ In₂
      (EndToEndInitialLeftReceiverOutput A) Out₂) : Prop :=
  match pending with
  | none => True
  | some source =>
      match source.1 with
      | some (.inl profile) =>
          profile (letter.1.2, letter.1.1) = letter.2.1.1.informedOne
      | _ => False

/-- Finite monitor for the initial-left streaming seam. -/
noncomputable def endToEndInitialLeftBlockMonitor
    (package : PairedInitialProfiledRationalPackage A) :
    BlockRecordMonitor In₁ In₂ (EndToEndInitialLeftReceiverOutput A) Out₂ := by
  classical
  exact {
    State := (InitialBlockScan A ×
      Option (PairedInitialProfiledBankState A)) × Bool
    stateFinite := inferInstance
    initial := (((A.initial, A.initial), none), true)
    step := fun state letter =>
      let physical := endToEndInitialLeftPhysicalLetter A letter
      let source := letter.2.1.2
      let sourceOK := endToEndInitialLeftSourceOK A package
        state.1.1 physical source
      let overlapOK := endToEndInitialLeftOverlapOK A state.1.2 letter
      ((initialLeftScanStep A state.1.1 physical, some source),
        state.2 && decide sourceOK && decide overlapOK)
    priority := fun state => if state.2 then A.priority state.1.1.1 + 2 else 1
  }

namespace PairedStrategyMemory.PairedInitialProfiledRationalPackage

/-- Raw boundary state selected from the package image.  The row is fixed
proof-side; both rows stage the same target and guard. -/
def initialLeftBankState
    (package : PairedInitialProfiledRationalPackage A)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    PairedInitialProfiledBankState A :=
  package.next (.fromTwo .first past move)

def endToEndInitialLeftReceiverStrategy
    (package : PairedInitialProfiledRationalPackage A) :
    ReceiverBlockStrategy In₁ In₂ (EndToEndInitialLeftReceiverOutput A) :=
  fun past move =>
    (⟨package.left.informedOne past move,
      package.left.reversingOne past move,
      package.left.reversingTwo past move⟩,
      package.initialLeftBankState A past move)

def endToEndInitialLeftPending
    (package : PairedInitialProfiledRationalPackage A)
    (env : Nat → In₁ × In₂) : Nat →
      Option (PairedInitialProfiledBankState A)
  | 0 => none
  | n + 1 => some
      (package.initialLeftBankState A (omegaPrefix env n) (env n))

section
omit [Inhabited In₁] [Inhabited In₂]

theorem endToEndInitialLeft_pairPlay_physical
    (package : PairedInitialProfiledRationalPackage A)
    (env : Nat → In₁ × In₂) (n : Nat) :
    endToEndInitialLeftPhysicalLetter A
      (pairPlay (package.endToEndInitialLeftReceiverStrategy A)
        (initialLeftSenderStrategy package.left) env n) =
      initialLeftLetterAt package.left (omegaPrefix env n) (env n) := by
  simp [endToEndInitialLeftPhysicalLetter, pairPlay, treePlay, treeOfPair,
    blockLabelApply, branchNode_eq_omegaPrefix,
    endToEndInitialLeftReceiverStrategy, initialLeftSenderStrategy,
    initialLeftLetterAt]

theorem endToEndInitialLeft_pairPlay_source
    (package : PairedInitialProfiledRationalPackage A)
    (env : Nat → In₁ × In₂) (n : Nat) :
    (pairPlay (package.endToEndInitialLeftReceiverStrategy A)
      (initialLeftSenderStrategy package.left) env n).2.1.2 =
      package.initialLeftBankState A (omegaPrefix env n) (env n) := by
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    branchNode_eq_omegaPrefix, endToEndInitialLeftReceiverStrategy]

theorem initialLeftBankState_sourceOK
    (package : PairedInitialProfiledRationalPackage A)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    endToEndInitialLeftSourceOK A package
      (initialLeftScanAfter A package.left past)
      (initialLeftLetterAt package.left past move)
      (package.initialLeftBankState A past move) := by
  refine ⟨?_, (package.leftBoundary .first past move).2, ?_⟩
  · exact ⟨initialLeftPendingProfile package.left past move,
      (package.leftBoundary .first past move).1⟩
  · exact ⟨.fromTwo .first past move, rfl⟩

end

section
omit [Inhabited In₁] [Inhabited In₂]

theorem endToEndInitialLeft_overlapOK
    (package : PairedInitialProfiledRationalPackage A)
    (env : Nat → In₁ × In₂) (n : Nat) :
    endToEndInitialLeftOverlapOK A
      (package.endToEndInitialLeftPending A env n)
      (pairPlay (package.endToEndInitialLeftReceiverStrategy A)
        (initialLeftSenderStrategy package.left) env n) := by
  cases n with
  | zero => trivial
  | succ n =>
      have hphysical := package.endToEndInitialLeft_pairPlay_physical A env (n + 1)
      have hmove := congrArg (fun letter => letter.1) hphysical
      have hout := congrArg (fun letter => letter.2.1.informedOne) hphysical
      simp only [endToEndInitialLeftPending, initialLeftBankState,
        endToEndInitialLeftOverlapOK]
      rw [(package.leftBoundary .first (omegaPrefix env n) (env n)).1]
      change initialLeftPendingProfile package.left (omegaPrefix env n) (env n)
          ((pairPlay (package.endToEndInitialLeftReceiverStrategy A)
            (initialLeftSenderStrategy package.left) env (n + 1)).1.2,
           (pairPlay (package.endToEndInitialLeftReceiverStrategy A)
            (initialLeftSenderStrategy package.left) env (n + 1)).1.1) = _
      have hmove' :
          (pairPlay (package.endToEndInitialLeftReceiverStrategy A)
            (initialLeftSenderStrategy package.left) env (n + 1)).1 =
              env (n + 1) := by
        simpa [endToEndInitialLeftPhysicalLetter,
          initialLeftLetterAt] using hmove
      have hout' :
          (pairPlay (package.endToEndInitialLeftReceiverStrategy A)
            (initialLeftSenderStrategy package.left) env (n + 1)).2.1.1.informedOne =
              package.left.informedOne
                (omegaPrefix env (n + 1)) (env (n + 1)) := by
        simpa [endToEndInitialLeftPhysicalLetter,
          initialLeftLetterAt] using hout
      rw [hmove', hout', omegaPrefix_succ]
      rfl

theorem endToEndInitialLeftBlockMonitor_run_eq
    (package : PairedInitialProfiledRationalPackage A)
    (env : Nat → In₁ × In₂) : ∀ n,
    (endToEndInitialLeftBlockMonitor A package).run
      (pairPlay (package.endToEndInitialLeftReceiverStrategy A)
        (initialLeftSenderStrategy package.left) env) n =
      ((initialLeftScanAfter A package.left (omegaPrefix env n),
        package.endToEndInitialLeftPending A env n), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih]
      simp only [endToEndInitialLeftBlockMonitor]
      rw [package.endToEndInitialLeft_pairPlay_physical A env n,
        package.endToEndInitialLeft_pairPlay_source A env n]
      have hsource := package.initialLeftBankState_sourceOK A
        (omegaPrefix env n) (env n)
      have hoverlap := package.endToEndInitialLeft_overlapOK A env n
      change
        ((initialLeftScanStep A
            (initialLeftScanAfter A package.left (omegaPrefix env n))
            (initialLeftLetterAt package.left (omegaPrefix env n) (env n)),
          some (package.initialLeftBankState A (omegaPrefix env n) (env n))),
          true && decide _ && decide _) = _
      rw [decide_eq_true hsource, decide_eq_true hoverlap]
      simp only [Bool.true_and]
      rw [omegaPrefix_succ, initialLeftScanAfter_append]
      rfl

theorem endToEndInitialLeftBlockMonitor_wins
    (package : PairedInitialProfiledRationalPackage A)
    (env : Nat → In₁ × In₂) :
    (endToEndInitialLeftBlockMonitor A package).WinsPlay
      (pairPlay (package.endToEndInitialLeftReceiverStrategy A)
        (initialLeftSenderStrategy package.left) env) := by
  unfold BlockRecordMonitor.WinsPlay
  have heq :
      (fun n => (endToEndInitialLeftBlockMonitor A package).priority
        ((endToEndInitialLeftBlockMonitor A package).run
          (pairPlay (package.endToEndInitialLeftReceiverStrategy A)
            (initialLeftSenderStrategy package.left) env) n)) =
        fun n => A.priority
          (A.run (initialLeftOmegaWord package.left env) n) + 2 := by
    funext n
    rw [package.endToEndInitialLeftBlockMonitor_run_eq A env n]
    simp only [endToEndInitialLeftBlockMonitor, if_pos, Bool.true_eq]
    congr 2
    have hscan :
        (initialLeftScanAfter A package.left (omegaPrefix env n)).1 =
          A.run (initialLeftOmegaWord package.left env) n := by
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [omegaPrefix_succ, initialLeftScanAfter_append]
          simp only [initialLeftScanStep, initialBlockScanStep]
          rw [ih]
          rfl
    exact hscan
  rw [heq]
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr
    (package.leftForever env)

end

/-- The arbitrary whole-block root function is replaced by a finite streaming
controller, while every staged continuation remains in the finite image of
the same rational policy. -/
theorem exists_finite_endToEndInitialLeftController
    [Inhabited Out₁] [Inhabited Out₂]
    (package : PairedInitialProfiledRationalPackage A) :
    ∃ controller : TransitionRationalTree.{v, max u v x y s, max u v x y s}
      In₂ (NarrowedBlockLabel In₁ In₂
        (EndToEndInitialLeftReceiverOutput A) Out₂
        (endToEndInitialLeftBlockMonitor A package).State),
      NarrowedAllThreadsWin (endToEndInitialLeftBlockMonitor A package)
        controller.labeledTree := by
  classical
  let rootState := package.initialLeftBankState A [] (default, default)
  letI : Inhabited (PairedInitialProfiledBankState A) := ⟨rootState⟩
  letI : Inhabited (EndToEndInitialLeftReceiverOutput A) := inferInstance
  apply (block_realizable_iff_implementable_controller_unconditional
    (endToEndInitialLeftBlockMonitor A package)).mp
  exact ⟨package.endToEndInitialLeftReceiverStrategy A,
    initialLeftSenderStrategy package.left,
    package.endToEndInitialLeftBlockMonitor_wins A⟩

/-! ## Initial-right mirror -/

abbrev EndToEndInitialRightReceiverOutput :=
  InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂) ×
    PairedInitialProfiledBankState A

def endToEndInitialRightPhysicalLetter
    (letter : RealizedBlockRound In₂ In₁
      (EndToEndInitialRightReceiverOutput A) Out₁) :
    InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  (letter.1, letter.2.1.1, letter.2.2)

def endToEndInitialRightSourceOK
    (package : PairedInitialProfiledRationalPackage A)
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (source : PairedInitialProfiledBankState A) : Prop :=
  (∃ profile : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂),
      source.1 = some (Sum.inr profile)) ∧
    erasePairedProfiledState A source.2 =
      initialRightDelayedTarget A scan letter ∧
    ∃ direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂),
      package.next direction = source

def endToEndInitialRightOverlapOK
    (pending : Option (PairedInitialProfiledBankState A))
    (letter : RealizedBlockRound In₂ In₁
      (EndToEndInitialRightReceiverOutput A) Out₁) : Prop :=
  match pending with
  | none => True
  | some source =>
      match source.1 with
      | some (.inr profile) =>
          profile (letter.1.2, letter.1.1) = letter.2.1.1.informedTwo
      | _ => False

noncomputable def endToEndInitialRightBlockMonitor
    (package : PairedInitialProfiledRationalPackage A) :
    BlockRecordMonitor In₂ In₁ (EndToEndInitialRightReceiverOutput A) Out₁ := by
  classical
  exact {
    State := (InitialBlockScan A ×
      Option (PairedInitialProfiledBankState A)) × Bool
    stateFinite := inferInstance
    initial := (((A.initial, A.initial), none), true)
    step := fun state letter =>
      let physical := endToEndInitialRightPhysicalLetter A letter
      let source := letter.2.1.2
      let sourceOK := endToEndInitialRightSourceOK A package
        state.1.1 physical source
      let overlapOK := endToEndInitialRightOverlapOK A state.1.2 letter
      ((initialRightScanStep A state.1.1 physical, some source),
        state.2 && decide sourceOK && decide overlapOK)
    priority := fun state => if state.2 then A.priority state.1.1.1 + 2 else 1
  }

def initialRightBankState
    (package : PairedInitialProfiledRationalPackage A)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    PairedInitialProfiledBankState A :=
  package.next (.fromOne .first past move)

def endToEndInitialRightReceiverStrategy
    (package : PairedInitialProfiledRationalPackage A) :
    ReceiverBlockStrategy In₂ In₁ (EndToEndInitialRightReceiverOutput A) :=
  fun past move =>
    (⟨package.right.informedTwo past move,
      package.right.reversingOne past move,
      package.right.reversingTwo past move⟩,
      package.initialRightBankState A past move)

def endToEndInitialRightPending
    (package : PairedInitialProfiledRationalPackage A)
    (env : Nat → In₂ × In₁) : Nat →
      Option (PairedInitialProfiledBankState A)
  | 0 => none
  | n + 1 => some
      (package.initialRightBankState A (omegaPrefix env n) (env n))

section
omit [Inhabited In₁] [Inhabited In₂]

theorem endToEndInitialRight_pairPlay_physical
    (package : PairedInitialProfiledRationalPackage A)
    (env : Nat → In₂ × In₁) (n : Nat) :
    endToEndInitialRightPhysicalLetter A
      (pairPlay (package.endToEndInitialRightReceiverStrategy A)
        (initialRightSenderStrategy package.right) env n) =
      initialRightLetterAt package.right (omegaPrefix env n) (env n) := by
  simp [endToEndInitialRightPhysicalLetter, pairPlay, treePlay, treeOfPair,
    blockLabelApply, branchNode_eq_omegaPrefix,
    endToEndInitialRightReceiverStrategy, initialRightSenderStrategy,
    initialRightLetterAt]

theorem endToEndInitialRight_pairPlay_source
    (package : PairedInitialProfiledRationalPackage A)
    (env : Nat → In₂ × In₁) (n : Nat) :
    (pairPlay (package.endToEndInitialRightReceiverStrategy A)
      (initialRightSenderStrategy package.right) env n).2.1.2 =
      package.initialRightBankState A (omegaPrefix env n) (env n) := by
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    branchNode_eq_omegaPrefix, endToEndInitialRightReceiverStrategy]

theorem initialRightBankState_sourceOK
    (package : PairedInitialProfiledRationalPackage A)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    endToEndInitialRightSourceOK A package
      (initialRightScanAfter A package.right past)
      (initialRightLetterAt package.right past move)
      (package.initialRightBankState A past move) := by
  refine ⟨?_, (package.rightBoundary .first past move).2, ?_⟩
  · exact ⟨initialRightPendingProfile package.right past move,
      (package.rightBoundary .first past move).1⟩
  · exact ⟨.fromOne .first past move, rfl⟩

end

section
omit [Inhabited In₁] [Inhabited In₂]

theorem endToEndInitialRight_overlapOK
    (package : PairedInitialProfiledRationalPackage A)
    (env : Nat → In₂ × In₁) (n : Nat) :
    endToEndInitialRightOverlapOK A
      (package.endToEndInitialRightPending A env n)
      (pairPlay (package.endToEndInitialRightReceiverStrategy A)
        (initialRightSenderStrategy package.right) env n) := by
  cases n with
  | zero => trivial
  | succ n =>
      have hphysical := package.endToEndInitialRight_pairPlay_physical A env (n + 1)
      have hmove := congrArg (fun letter => letter.1) hphysical
      have hout := congrArg (fun letter => letter.2.1.informedTwo) hphysical
      simp only [endToEndInitialRightPending, initialRightBankState,
        endToEndInitialRightOverlapOK]
      rw [(package.rightBoundary .first (omegaPrefix env n) (env n)).1]
      change initialRightPendingProfile package.right (omegaPrefix env n) (env n)
          ((pairPlay (package.endToEndInitialRightReceiverStrategy A)
            (initialRightSenderStrategy package.right) env (n + 1)).1.2,
           (pairPlay (package.endToEndInitialRightReceiverStrategy A)
            (initialRightSenderStrategy package.right) env (n + 1)).1.1) = _
      have hmove' :
          (pairPlay (package.endToEndInitialRightReceiverStrategy A)
            (initialRightSenderStrategy package.right) env (n + 1)).1 =
              env (n + 1) := by
        simpa [endToEndInitialRightPhysicalLetter,
          initialRightLetterAt] using hmove
      have hout' :
          (pairPlay (package.endToEndInitialRightReceiverStrategy A)
            (initialRightSenderStrategy package.right) env (n + 1)).2.1.1.informedTwo =
              package.right.informedTwo
                (omegaPrefix env (n + 1)) (env (n + 1)) := by
        simpa [endToEndInitialRightPhysicalLetter,
          initialRightLetterAt] using hout
      rw [hmove', hout', omegaPrefix_succ]
      rfl

theorem endToEndInitialRightBlockMonitor_run_eq
    (package : PairedInitialProfiledRationalPackage A)
    (env : Nat → In₂ × In₁) : ∀ n,
    (endToEndInitialRightBlockMonitor A package).run
      (pairPlay (package.endToEndInitialRightReceiverStrategy A)
        (initialRightSenderStrategy package.right) env) n =
      ((initialRightScanAfter A package.right (omegaPrefix env n),
        package.endToEndInitialRightPending A env n), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih]
      simp only [endToEndInitialRightBlockMonitor]
      rw [package.endToEndInitialRight_pairPlay_physical A env n,
        package.endToEndInitialRight_pairPlay_source A env n]
      have hsource := package.initialRightBankState_sourceOK A
        (omegaPrefix env n) (env n)
      have hoverlap := package.endToEndInitialRight_overlapOK A env n
      change
        ((initialRightScanStep A
            (initialRightScanAfter A package.right (omegaPrefix env n))
            (initialRightLetterAt package.right (omegaPrefix env n) (env n)),
          some (package.initialRightBankState A (omegaPrefix env n) (env n))),
          true && decide _ && decide _) = _
      rw [decide_eq_true hsource, decide_eq_true hoverlap]
      simp only [Bool.true_and]
      rw [omegaPrefix_succ, initialRightScanAfter_append]
      rfl

theorem endToEndInitialRightBlockMonitor_wins
    (package : PairedInitialProfiledRationalPackage A)
    (env : Nat → In₂ × In₁) :
    (endToEndInitialRightBlockMonitor A package).WinsPlay
      (pairPlay (package.endToEndInitialRightReceiverStrategy A)
        (initialRightSenderStrategy package.right) env) := by
  unfold BlockRecordMonitor.WinsPlay
  have heq :
      (fun n => (endToEndInitialRightBlockMonitor A package).priority
        ((endToEndInitialRightBlockMonitor A package).run
          (pairPlay (package.endToEndInitialRightReceiverStrategy A)
            (initialRightSenderStrategy package.right) env) n)) =
        fun n => A.priority
          (A.run (initialRightOmegaWord package.right env) n) + 2 := by
    funext n
    rw [package.endToEndInitialRightBlockMonitor_run_eq A env n]
    simp only [endToEndInitialRightBlockMonitor, if_pos, Bool.true_eq]
    congr 2
    have hscan :
        (initialRightScanAfter A package.right (omegaPrefix env n)).1 =
          A.run (initialRightOmegaWord package.right env) n := by
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [omegaPrefix_succ, initialRightScanAfter_append]
          simp only [initialRightScanStep, initialBlockScanStep]
          rw [ih]
          rfl
    exact hscan
  rw [heq]
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr
    (package.rightForever env)

end

theorem exists_finite_endToEndInitialRightController
    [Inhabited Out₁] [Inhabited Out₂]
    (package : PairedInitialProfiledRationalPackage A) :
    ∃ controller : TransitionRationalTree.{u, max u v x y s, max u v x y s}
      In₁ (NarrowedBlockLabel In₂ In₁
        (EndToEndInitialRightReceiverOutput A) Out₁
        (endToEndInitialRightBlockMonitor A package).State),
      NarrowedAllThreadsWin (endToEndInitialRightBlockMonitor A package)
        controller.labeledTree := by
  classical
  let rootState := package.initialRightBankState A [] (default, default)
  letI : Inhabited (PairedInitialProfiledBankState A) := ⟨rootState⟩
  letI : Inhabited (EndToEndInitialRightReceiverOutput A) := inferInstance
  apply (block_realizable_iff_implementable_controller_unconditional
    (endToEndInitialRightBlockMonitor A package)).mp
  exact ⟨package.endToEndInitialRightReceiverStrategy A,
    initialRightSenderStrategy package.right,
    package.endToEndInitialRightBlockMonitor_wins A⟩

end PairedStrategyMemory.PairedInitialProfiledRationalPackage

/-- End-to-end initial extraction: one application of the arbitrary-direction
input-free basis produces the common policy package; both finite streaming
controllers are then extracted against the finite image of that same package.
No per-boundary rational-run basis is invoked. -/
theorem exists_endToEndInitialControllers_of_winning
    [Inhabited Out₁] [Inhabited Out₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : (pairedInitialProfiledForestAutomaton A).RationalRunBasis) :
    ∃ package : PairedStrategyMemory.PairedInitialProfiledRationalPackage A,
      (∃ leftController :
          TransitionRationalTree.{v, max u v x y s, max u v x y s}
            In₂ (NarrowedBlockLabel In₁ In₂
              (EndToEndInitialLeftReceiverOutput A) Out₂
              (endToEndInitialLeftBlockMonitor A package).State),
        NarrowedAllThreadsWin (endToEndInitialLeftBlockMonitor A package)
          leftController.labeledTree) ∧
      (∃ rightController :
          TransitionRationalTree.{u, max u v x y s, max u v x y s}
            In₁ (NarrowedBlockLabel In₂ In₁
              (PairedStrategyMemory.PairedInitialProfiledRationalPackage.EndToEndInitialRightReceiverOutput A) Out₁
              (PairedStrategyMemory.PairedInitialProfiledRationalPackage.endToEndInitialRightBlockMonitor A package).State),
        NarrowedAllThreadsWin
          (PairedStrategyMemory.PairedInitialProfiledRationalPackage.endToEndInitialRightBlockMonitor A package)
          rightController.labeledTree) := by
  have hrun := PairedStrategyMemory.pairedInitialProfiledForest_hasRationalRun_of_winning
      A strategy hwin basis
  rcases PairedStrategyMemory.nonempty_initialProfiledRationalPackage_of_hasRationalRun A hrun with
    ⟨package⟩
  refine ⟨package, ?_, ?_⟩
  · exact package.exists_finite_endToEndInitialLeftController A
  · exact package.exists_finite_endToEndInitialRightController A

end

end DetParityAutomaton

end DistributedSynthesis
