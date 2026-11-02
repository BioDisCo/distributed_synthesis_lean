/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRationalPolicy
import DistributedSynthesis.Formalizations.Lemma.LemSendernarrowing

/-!
# Certificate-output monitors for profiled recurrent blocks

The informed output carries, in addition to the physical paired output, one
profiled successor certificate for each latent old row.  The finite monitor
checks three facts:

1. each certificate is an allowed policy successor with the correct erased
   DPA state;
2. the first physical action matches the profile stored at the source; and
3. on the following round, the old block's `both` prediction matches the
   profile carried by the preceding certificate.

The third check is delayed by one round and made sticky.  Consequently the
ordinary unconditional sender-narrowing theorem can fold the receiver while
preserving the boundary law; no whole-table edge coupling is required.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

/-- Physical right-block output plus the two finite successor certificates. -/
structure ProfiledRightReceiverOutput where
  physical : PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)
  target : PairedEntryRow → PairedProfiledTreeState A
deriving Fintype

/-- Physical left-block output plus its successor certificates. -/
structure ProfiledLeftReceiverOutput where
  physical : PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)
  target : PairedEntryRow → PairedProfiledTreeState A
deriving Fintype

noncomputable instance : Inhabited (ProfiledRightReceiverOutput A) :=
  ⟨{ physical := default, target := fun _ => .inl PUnit.unit }⟩

noncomputable instance : Inhabited (ProfiledLeftReceiverOutput A) :=
  ⟨{ physical := default, target := fun _ => .inl PUnit.unit }⟩

/-- Recover the stored left-block initial profile from a profiled state. -/
def leftProfileOfProfiledState (state : PairedProfiledTreeState A) :
    Option (LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)) :=
  match state with
  | .inr (.inr live) => some live.2
  | _ => none

/-- Recover the stored right-block initial profile. -/
def rightProfileOfProfiledState (state : PairedProfiledTreeState A) :
    Option (RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) :=
  match state with
  | .inr (.inl live) => some live.2
  | _ => none

/-- Strip certificate data from a right-block letter. -/
def profiledRightPhysicalLetter
    (letter : RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁) :
    PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  (letter.1, letter.2.1.physical, letter.2.2)

/-- Strip certificate data from a left-block letter. -/
def profiledLeftPhysicalLetter
    (letter : RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂) :
    PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  (letter.1, letter.2.1.physical, letter.2.2)

/-- State of the right certificate monitor. -/
abbrev ProfiledRightBlockMonitorState (Universal : Type*) :=
  Universal × PairedRightScanState A ×
    (PairedEntryRow → Option (LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))) × Bool × Bool

/-- State of the left certificate monitor. -/
abbrev ProfiledLeftBlockMonitorState (Universal : Type*) :=
  Universal × PairedLeftScanState A ×
    (PairedEntryRow → Option (RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))) × Bool × Bool

/-- Right recurrent monitor with certificate-output checking. -/
noncomputable def profiledRightBlockMonitor
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) :
    BlockRecordMonitor In₂ In₁ (ProfiledRightReceiverOutput A) Out₁ := by
  classical
  let U := (pairedRightThreadSystem A code).universalRunDPA
  let source : PairedProfiledTreeState A :=
    .inr (.inl ((code, minimum), profile))
  exact {
    State := ProfiledRightBlockMonitorState A U.State
    stateFinite := inferInstance
    initial := (U.initial, pairedRightScanInitial A code, fun _ => none,
      true, true)
    step := fun state letter =>
      let physical := profiledRightPhysicalLetter A letter
      let rootMatches := !state.2.2.2.1 ||
        decide (pairedRightInformedForRow .first letter.2.1.physical =
          profile letter.1)
      let overlaps := ∀ row expected,
        state.2.2.1 row = some expected →
          pairedRightClosingForRow row letter.2.1.physical =
            expected (letter.1.2, letter.1.1)
      let targetsSafe := ∀ row,
        erasePairedProfiledState A (letter.2.1.target row) =
            pairedRightCloseTarget A state.2.1 row physical ∧
          PairedProfiledRationalPolicy.Allowed A policy source
            (letter.2.1.target row)
      (U.step state.1 physical,
        pairedRightScanStep A state.2.1 physical,
        fun row => leftProfileOfProfiledState A (letter.2.1.target row),
        false,
        state.2.2.2.2 && rootMatches && decide overlaps && decide targetsSafe)
    priority := fun state =>
      if state.2.2.2.2 then U.priority state.1 + 2 else 1
  }

/-- Left mirror. -/
noncomputable def profiledLeftBlockMonitor
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)) :
    BlockRecordMonitor In₁ In₂ (ProfiledLeftReceiverOutput A) Out₂ := by
  classical
  let U := (pairedLeftThreadSystem A code).universalRunDPA
  let source : PairedProfiledTreeState A :=
    .inr (.inr ((code, minimum), profile))
  exact {
    State := ProfiledLeftBlockMonitorState A U.State
    stateFinite := inferInstance
    initial := (U.initial, pairedLeftScanInitial A code, fun _ => none,
      true, true)
    step := fun state letter =>
      let physical := profiledLeftPhysicalLetter A letter
      let rootMatches := !state.2.2.2.1 ||
        decide (pairedLeftInformedForRow .first letter.2.1.physical =
          profile letter.1)
      let overlaps := ∀ row expected,
        state.2.2.1 row = some expected →
          pairedLeftClosingForRow row letter.2.1.physical =
            expected (letter.1.2, letter.1.1)
      let targetsSafe := ∀ row,
        erasePairedProfiledState A (letter.2.1.target row) =
            pairedLeftCloseTarget A state.2.1 row physical ∧
          PairedProfiledRationalPolicy.Allowed A policy source
            (letter.2.1.target row)
      (U.step state.1 physical,
        pairedLeftScanStep A state.2.1 physical,
        fun row => rightProfileOfProfiledState A (letter.2.1.target row),
        false,
        state.2.2.2.2 && rootMatches && decide overlaps && decide targetsSafe)
    priority := fun state =>
      if state.2.2.2.2 then U.priority state.1 + 2 else 1
  }

/-! ## Semantic certificate outputs -/

/-- Enrich a semantic right-block receiver by its exact profiled children. -/
def profiledRightReceiverStrategy
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    ReceiverBlockStrategy In₂ In₁ (ProfiledRightReceiverOutput A) :=
  fun past move => {
    physical := pairedRightReceiverStrategy lambda past move
    target := fun row => pairedProfiledOneChild A code lambda row past move
  }

/-- Left mirror. -/
def profiledLeftReceiverStrategy
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    ReceiverBlockStrategy In₁ In₂ (ProfiledLeftReceiverOutput A) :=
  fun past move => {
    physical := pairedLeftReceiverStrategy lambda past move
    target := fun row => pairedProfiledTwoChild A code lambda row past move
  }

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

@[simp] theorem profiledRightReceiverStrategy_physical
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    (profiledRightReceiverStrategy A code lambda past move).physical =
      pairedRightReceiverStrategy lambda past move := rfl

@[simp] theorem profiledLeftReceiverStrategy_physical
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    (profiledLeftReceiverStrategy A code lambda past move).physical =
      pairedLeftReceiverStrategy lambda past move := rfl

@[simp] theorem profiledRightTarget_profile
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    leftProfileOfProfiledState A
        ((profiledRightReceiverStrategy A code lambda past move).target row) =
      some (rightClosingProfile lambda row past move) := by
  cases row <;> rfl

@[simp] theorem profiledLeftTarget_profile
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    rightProfileOfProfiledState A
        ((profiledLeftReceiverStrategy A code lambda past move).target row) =
      some (leftClosingProfile lambda row past move) := by
  cases row <;> rfl

/-- The delayed right overlap check is definitionally true on the semantic
certificate stream. -/
theorem profiledRightReceiverStrategy_overlap
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move nextMove : In₂ × In₁) :
    pairedRightClosingForRow row
        (profiledRightReceiverStrategy A code lambda (past ++ [move])
          nextMove).physical =
      rightClosingProfile lambda row past move (nextMove.2, nextMove.1) := by
  cases row <;> rfl

/-- Left mirror. -/
theorem profiledLeftReceiverStrategy_overlap
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move nextMove : In₁ × In₂) :
    pairedLeftClosingForRow row
        (profiledLeftReceiverStrategy A code lambda (past ++ [move])
          nextMove).physical =
      leftClosingProfile lambda row past move (nextMove.2, nextMove.1) := by
  cases row <;> rfl

@[simp] theorem profiledRightReceiverStrategy_root
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (move : In₂ × In₁) :
    pairedRightInformedForRow .first
        (profiledRightReceiverStrategy A code lambda [] move).physical =
      rightInitialFirstProfile lambda move := rfl

@[simp] theorem profiledLeftReceiverStrategy_root
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (move : In₁ × In₂) :
    pairedLeftInformedForRow .first
        (profiledLeftReceiverStrategy A code lambda [] move).physical =
      leftInitialFirstProfile lambda move := rfl

end

/-- Pending profile after a finite right-block prefix. -/
def profiledRightPendingAfter
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) :
    PairedEntryRow → Option (LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)) :=
  fun row =>
    match past.reverse with
    | [] => none
    | move :: reversePrefix =>
        some (rightClosingProfile lambda row reversePrefix.reverse move)

/-- Pending profile after a finite left-block prefix. -/
def profiledLeftPendingAfter
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) :
    PairedEntryRow → Option (RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) :=
  fun row =>
    match past.reverse with
    | [] => none
    | move :: reversePrefix =>
        some (leftClosingProfile lambda row reversePrefix.reverse move)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

@[simp] theorem profiledRightPendingAfter_nil
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    profiledRightPendingAfter lambda [] = fun _ => none := rfl

@[simp] theorem profiledLeftPendingAfter_nil
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    profiledLeftPendingAfter lambda [] = fun _ => none := rfl

@[simp] theorem profiledRightPendingAfter_append
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    profiledRightPendingAfter lambda (past ++ [move]) =
      fun row => some (rightClosingProfile lambda row past move) := by
  funext row
  simp [profiledRightPendingAfter]

@[simp] theorem profiledLeftPendingAfter_append
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    profiledLeftPendingAfter lambda (past ++ [move]) =
      fun row => some (leftClosingProfile lambda row past move) := by
  funext row
  simp [profiledLeftPendingAfter]

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRightPendingAfter_realizes
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ∀ row expected,
      profiledRightPendingAfter lambda past row = some expected →
        pairedRightClosingForRow row
            (profiledRightReceiverStrategy A code lambda past move).physical =
          expected (move.2, move.1) := by
  intro row expected hpending
  unfold profiledRightPendingAfter at hpending
  cases hrev : past.reverse with
  | nil => simp [hrev] at hpending
  | cons previous reversePrefix =>
      simp only [hrev, Option.some.injEq] at hpending
      subst expected
      have hpast : past = reversePrefix.reverse ++ [previous] := by
        have := congrArg List.reverse hrev
        simpa using this
      subst past
      exact profiledRightReceiverStrategy_overlap A code lambda row
        reversePrefix.reverse previous move

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledLeftPendingAfter_realizes
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ∀ row expected,
      profiledLeftPendingAfter lambda past row = some expected →
        pairedLeftClosingForRow row
            (profiledLeftReceiverStrategy A code lambda past move).physical =
          expected (move.2, move.1) := by
  intro row expected hpending
  unfold profiledLeftPendingAfter at hpending
  cases hrev : past.reverse with
  | nil => simp [hrev] at hpending
  | cons previous reversePrefix =>
      simp only [hrev, Option.some.injEq] at hpending
      subst expected
      have hpast : past = reversePrefix.reverse ++ [previous] := by
        have := congrArg List.reverse hrev
        simpa using this
      subst past
      exact profiledLeftReceiverStrategy_overlap A code lambda row
        reversePrefix.reverse previous move

/-! ## Exact semantic monitor runs -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

/-- The exact enriched letter produced at a right-block node. -/
theorem profiledRight_pairPlay_eq_letterAt
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat → In₂ × In₁) (n : Nat) :
    pairPlay (profiledRightReceiverStrategy A code lambda)
        (pairedRightSenderStrategy lambda) env n =
      (env n,
        profiledRightReceiverStrategy A code lambda (omegaPrefix env n) (env n),
        lambda.blind (senderWord (omegaPrefix env n)) (env n).2) := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, pairedRightSenderStrategy, senderWord, omegaPrefix]

/-- The exact enriched letter produced at a left-block node. -/
theorem profiledLeft_pairPlay_eq_letterAt
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat → In₁ × In₂) (n : Nat) :
    pairPlay (profiledLeftReceiverStrategy A code lambda)
        (pairedLeftSenderStrategy lambda) env n =
      (env n,
        profiledLeftReceiverStrategy A code lambda (omegaPrefix env n) (env n),
        lambda.blind (senderWord (omegaPrefix env n)) (env n).2) := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, pairedLeftSenderStrategy, senderWord, omegaPrefix]

/-- Erasing the certificates from the semantic right play gives the ordinary
paired block word pointwise. -/
theorem profiledRight_pairPlay_physical
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat → In₂ × In₁) (n : Nat) :
    profiledRightPhysicalLetter A
        (pairPlay (profiledRightReceiverStrategy A code lambda)
          (pairedRightSenderStrategy lambda) env n) =
      pairedRightBlockWord lambda env n := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, profiledRightPhysicalLetter,
    profiledRightReceiverStrategy, pairedRightReceiverStrategy,
    pairedRightSenderStrategy, pairedRightBlockWord, senderWord, omegaPrefix]

/-- Left mirror of `profiledRight_pairPlay_physical`. -/
theorem profiledLeft_pairPlay_physical
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat → In₁ × In₂) (n : Nat) :
    profiledLeftPhysicalLetter A
        (pairPlay (profiledLeftReceiverStrategy A code lambda)
          (pairedLeftSenderStrategy lambda) env n) =
      pairedLeftBlockWord lambda env n := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, profiledLeftPhysicalLetter,
    profiledLeftReceiverStrategy, pairedLeftReceiverStrategy,
    pairedLeftSenderStrategy, pairedLeftBlockWord, pairedLeftBlockLetterAt,
    senderWord, omegaPrefix]

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The certificate monitor is safe at every finite prefix of the semantic
right-block play, and its remaining components have their expected scans. -/
theorem profiledRightBlockMonitor_run_eq
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hprofile : rightInitialFirstProfile lambda = profile)
    (hclose : PairedProfiledRationalPolicy.ProcessOneCloseSafe
      A policy code minimum profile lambda)
    (env : Nat → In₂ × In₁) :
    ∀ n,
      (profiledRightBlockMonitor A policy code minimum profile).run
          (pairPlay (profiledRightReceiverStrategy A code lambda)
            (pairedRightSenderStrategy lambda) env) n =
        ((pairedRightThreadSystem A code).universalRunDPA.run
            (pairedRightBlockWord lambda env) n,
          pairedRightScanAfter A code lambda (omegaPrefix env n),
          profiledRightPendingAfter lambda (omegaPrefix env n),
          decide (n = 0), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih,
        profiledRight_pairPlay_eq_letterAt A code lambda env n,
        omegaPrefix_succ, pairedRightScanAfter_append,
        profiledRightPendingAfter_append]
      have hoverlaps : ∀ row expected,
          profiledRightPendingAfter lambda (omegaPrefix env n) row =
              some expected →
            pairedRightClosingForRow row
                (profiledRightReceiverStrategy A code lambda
                  (omegaPrefix env n) (env n)).physical =
              expected ((env n).2, (env n).1) :=
        profiledRightPendingAfter_realizes A code lambda
          (omegaPrefix env n) (env n)
      have htargets : ∀ row,
          erasePairedProfiledState A
              ((profiledRightReceiverStrategy A code lambda
                (omegaPrefix env n) (env n)).target row) =
              pairedRightCloseTarget A
                (pairedRightScanAfter A code lambda (omegaPrefix env n)) row
                (pairedRightBlockLetterAt lambda (omegaPrefix env n) (env n)) ∧
            PairedProfiledRationalPolicy.Allowed A policy
              (.inr (.inl ((code, minimum), profile)))
              ((profiledRightReceiverStrategy A code lambda
                (omegaPrefix env n) (env n)).target row) := by
        intro row
        constructor
        · rw [profiledRightReceiverStrategy, erase_pairedProfiledOneChild,
            pairedRightCloseTarget_scanAfter]
        · exact hclose row (omegaPrefix env n) (env n)
      have hphysicalAt :
          profiledRightPhysicalLetter A
              (env n,
                profiledRightReceiverStrategy A code lambda
                  (omegaPrefix env n) (env n),
                lambda.blind (senderWord (omegaPrefix env n)) (env n).2) =
            pairedRightBlockLetterAt lambda (omegaPrefix env n) (env n) := rfl
      simp only [profiledRightBlockMonitor]
      rw [hphysicalAt]
      rw [decide_eq_true hoverlaps, decide_eq_true htargets]
      rw [← pairedRightBlockWord_eq_letterAt lambda env n]
      by_cases hn : n = 0
      · subst n
        have hroot :
            pairedRightInformedForRow .first
                (pairedRightReceiverStrategy lambda [] (env 0)) =
              profile (env 0) := by
          simpa [rightInitialFirstProfile] using congrFun hprofile (env 0)
        simp [omegaPrefix, hroot, profiledRightTarget_profile]
      · simp [hn, profiledRightTarget_profile]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror of `profiledRightBlockMonitor_run_eq`. -/
theorem profiledLeftBlockMonitor_run_eq
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hprofile : leftInitialFirstProfile lambda = profile)
    (hclose : PairedProfiledRationalPolicy.ProcessTwoCloseSafe
      A policy code minimum profile lambda)
    (env : Nat → In₁ × In₂) :
    ∀ n,
      (profiledLeftBlockMonitor A policy code minimum profile).run
          (pairPlay (profiledLeftReceiverStrategy A code lambda)
            (pairedLeftSenderStrategy lambda) env) n =
        ((pairedLeftThreadSystem A code).universalRunDPA.run
            (pairedLeftBlockWord lambda env) n,
          pairedLeftScanAfter A code lambda (omegaPrefix env n),
          profiledLeftPendingAfter lambda (omegaPrefix env n),
          decide (n = 0), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih,
        profiledLeft_pairPlay_eq_letterAt A code lambda env n,
        omegaPrefix_succ, pairedLeftScanAfter_append,
        profiledLeftPendingAfter_append]
      have hoverlaps : ∀ row expected,
          profiledLeftPendingAfter lambda (omegaPrefix env n) row =
              some expected →
            pairedLeftClosingForRow row
                (profiledLeftReceiverStrategy A code lambda
                  (omegaPrefix env n) (env n)).physical =
              expected ((env n).2, (env n).1) :=
        profiledLeftPendingAfter_realizes A code lambda
          (omegaPrefix env n) (env n)
      have htargets : ∀ row,
          erasePairedProfiledState A
              ((profiledLeftReceiverStrategy A code lambda
                (omegaPrefix env n) (env n)).target row) =
              pairedLeftCloseTarget A
                (pairedLeftScanAfter A code lambda (omegaPrefix env n)) row
                (pairedLeftBlockLetterAt lambda (omegaPrefix env n) (env n)) ∧
            PairedProfiledRationalPolicy.Allowed A policy
              (.inr (.inr ((code, minimum), profile)))
              ((profiledLeftReceiverStrategy A code lambda
                (omegaPrefix env n) (env n)).target row) := by
        intro row
        constructor
        · rw [profiledLeftReceiverStrategy, erase_pairedProfiledTwoChild,
            pairedLeftCloseTarget_scanAfter]
        · exact hclose row (omegaPrefix env n) (env n)
      have hphysicalAt :
          profiledLeftPhysicalLetter A
              (env n,
                profiledLeftReceiverStrategy A code lambda
                  (omegaPrefix env n) (env n),
                lambda.blind (senderWord (omegaPrefix env n)) (env n).2) =
            pairedLeftBlockLetterAt lambda (omegaPrefix env n) (env n) := rfl
      simp only [profiledLeftBlockMonitor]
      rw [hphysicalAt]
      rw [decide_eq_true hoverlaps, decide_eq_true htargets]
      change
        ((pairedLeftThreadSystem A code).universalRunDPA.step
            ((pairedLeftThreadSystem A code).universalRunDPA.run
              (pairedLeftBlockWord lambda env) n)
            (pairedLeftBlockWord lambda env n), _, _, _, _) = _
      by_cases hn : n = 0
      · subst n
        have hroot :
            pairedLeftInformedForRow .first
                (pairedLeftReceiverStrategy lambda [] (env 0)) =
              profile (env 0) := by
          simpa [leftInitialFirstProfile] using congrFun hprofile (env 0)
        simp [omegaPrefix, hroot, profiledLeftTarget_profile]
      · simp [hn, profiledLeftTarget_profile]

/-! ## Unconditional finite recurrent controllers -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The semantic profiled right-block strategies win the certificate
monitor against every environment. -/
theorem profiledRightBlockMonitor_realizable
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hforever : PairedRightForeverAccepts A code lambda)
    (hprofile : rightInitialFirstProfile lambda = profile)
    (hclose : PairedProfiledRationalPolicy.ProcessOneCloseSafe
      A policy code minimum profile lambda) :
    ∀ env : Nat → In₂ × In₁,
      (profiledRightBlockMonitor A policy code minimum profile).WinsPlay
        (pairPlay (profiledRightReceiverStrategy A code lambda)
          (pairedRightSenderStrategy lambda) env) := by
  intro env
  have huniversal := pairedRightUniversalDPA_accepts_of_forever
    A code lambda hforever env
  have hparity : NatSeqMinEvenParity
      (fun n =>
        (pairedRightThreadSystem A code).universalRunDPA.priority
          ((pairedRightThreadSystem A code).universalRunDPA.run
            (pairedRightBlockWord lambda env) n)) := huniversal
  have hshifted : NatSeqMinEvenParity
      (fun n =>
        (pairedRightThreadSystem A code).universalRunDPA.priority
          ((pairedRightThreadSystem A code).universalRunDPA.run
            (pairedRightBlockWord lambda env) n) + 2) :=
    (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hparity
  unfold BlockRecordMonitor.WinsPlay
  convert hshifted using 1
  funext n
  rw [profiledRightBlockMonitor_run_eq A policy code minimum profile lambda
    hprofile hclose env n]
  simp [profiledRightBlockMonitor]
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror of `profiledRightBlockMonitor_realizable`. -/
theorem profiledLeftBlockMonitor_realizable
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hforever : PairedLeftForeverAccepts A code lambda)
    (hprofile : leftInitialFirstProfile lambda = profile)
    (hclose : PairedProfiledRationalPolicy.ProcessTwoCloseSafe
      A policy code minimum profile lambda) :
    ∀ env : Nat → In₁ × In₂,
      (profiledLeftBlockMonitor A policy code minimum profile).WinsPlay
        (pairPlay (profiledLeftReceiverStrategy A code lambda)
          (pairedLeftSenderStrategy lambda) env) := by
  intro env
  have huniversal := pairedLeftUniversalDPA_accepts_of_forever
    A code lambda hforever env
  have hparity : NatSeqMinEvenParity
      (fun n =>
        (pairedLeftThreadSystem A code).universalRunDPA.priority
          ((pairedLeftThreadSystem A code).universalRunDPA.run
            (pairedLeftBlockWord lambda env) n)) := huniversal
  have hshifted : NatSeqMinEvenParity
      (fun n =>
        (pairedLeftThreadSystem A code).universalRunDPA.priority
          ((pairedLeftThreadSystem A code).universalRunDPA.run
            (pairedLeftBlockWord lambda env) n) + 2) :=
    (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hparity
  unfold BlockRecordMonitor.WinsPlay
  convert hshifted using 1
  funext n
  rw [profiledLeftBlockMonitor_run_eq A policy code minimum profile lambda
    hprofile hclose env n]
  simp [profiledLeftBlockMonitor]
  rfl

/-- Every reachable profiled process-one state has an unconditional finite
controller whose receiver outputs retain certified profiled successors. -/
theorem exists_finite_profiledProcessOneBlockController
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hreachable : PairedProfiledRationalPolicy.Reachable A policy
      (.inr (.inl ((code, minimum), profile)))) :
    ∃ controller : TransitionRationalTree.{u, max 1 u v x y s, max 1 s u v x} In₁
        (NarrowedBlockLabel In₂ In₁ (ProfiledRightReceiverOutput A) Out₁
          (profiledRightBlockMonitor.{u, v, x, y, s, 1}
            A policy code minimum profile).State),
      NarrowedAllThreadsWin
        (profiledRightBlockMonitor.{u, v, x, y, s, 1}
          A policy code minimum profile)
        controller.labeledTree := by
  rcases PairedProfiledRationalPolicy.exists_processOneLambda_closeSafe
      A policy code minimum profile hreachable with
    ⟨lambda, hforever, hprofile, hclose⟩
  refine (block_realizable_iff_implementable_controller_unconditional
    (profiledRightBlockMonitor.{u, v, x, y, s, 1}
      A policy code minimum profile)).mp ?_
  exact ⟨profiledRightReceiverStrategy A code lambda,
    pairedRightSenderStrategy lambda,
    profiledRightBlockMonitor_realizable A policy code minimum profile lambda
      hforever hprofile hclose⟩

/-- Process-two mirror. -/
theorem exists_finite_profiledProcessTwoBlockController
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hreachable : PairedProfiledRationalPolicy.Reachable A policy
      (.inr (.inr ((code, minimum), profile)))) :
    ∃ controller : TransitionRationalTree.{v, max 1 u v x y s, max 1 s u v y} In₂
        (NarrowedBlockLabel In₁ In₂ (ProfiledLeftReceiverOutput A) Out₂
          (profiledLeftBlockMonitor.{u, v, x, y, s, 1}
            A policy code minimum profile).State),
      NarrowedAllThreadsWin
        (profiledLeftBlockMonitor.{u, v, x, y, s, 1}
          A policy code minimum profile)
        controller.labeledTree := by
  rcases PairedProfiledRationalPolicy.exists_processTwoLambda_closeSafe
      A policy code minimum profile hreachable with
    ⟨lambda, hforever, hprofile, hclose⟩
  refine (block_realizable_iff_implementable_controller_unconditional
    (profiledLeftBlockMonitor.{u, v, x, y, s, 1}
      A policy code minimum profile)).mp ?_
  exact ⟨profiledLeftReceiverStrategy A code lambda,
    pairedLeftSenderStrategy lambda,
    profiledLeftBlockMonitor_realizable A policy code minimum profile lambda
      hforever hprofile hclose⟩

end

end


end DetParityAutomaton

end DistributedSynthesis
