/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartFirstThenBothCombinedMonitor

/-!
# Exact profiled-state targets for the first-then-both lane

The mixed restart scan need not be encoded by one of the old constant-row
successor keys.  The profiled paired state is itself finite, so it can be
used directly as the target alphabet.  This module retargets any existing
semantic block activation to that alphabet and supplies the exact mixed
finite-safety extension definitionally.
-/

namespace DistributedSynthesis

universe u v x y s t

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

local instance : Inhabited (PairedProfiledTreeState A) :=
  ⟨.inl PUnit.unit⟩

/-! ## Causal finite block-letter lists -/

private def pairedRightBlockLettersFrom
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    List (In₂ × In₁) → List (In₂ × In₁) →
      List (PairedRightBlockLetter
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
  | _, [] => []
  | prior, move :: moves =>
      pairedRightBlockLetterAt lambda prior move ::
        pairedRightBlockLettersFrom lambda (prior ++ [move]) moves

/-- The physical right block letters determined by one finite input past. -/
def profiledRawJointRightBlockLetters
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) :
    List (PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :=
  pairedRightBlockLettersFrom lambda [] past

private theorem pairedRightBlockLettersFrom_append
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (prior moves : List (In₂ × In₁)) (move : In₂ × In₁) :
    pairedRightBlockLettersFrom lambda prior (moves ++ [move]) =
      pairedRightBlockLettersFrom lambda prior moves ++
        [pairedRightBlockLetterAt lambda (prior ++ moves) move] := by
  induction moves generalizing prior with
  | nil => simp [pairedRightBlockLettersFrom]
  | cons first rest ih =>
      simp only [List.cons_append, pairedRightBlockLettersFrom]
      rw [ih]
      simp [List.append_assoc]

theorem profiledRawJointRightBlockLetters_append
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    profiledRawJointRightBlockLetters lambda (past ++ [move]) =
      profiledRawJointRightBlockLetters lambda past ++
        [pairedRightBlockLetterAt lambda past move] := by
  simpa [profiledRawJointRightBlockLetters] using
    pairedRightBlockLettersFrom_append lambda [] past move

theorem profiledRawJointRightBlockLetters_omegaPrefix
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat → In₂ × In₁) : ∀ n,
    profiledRawJointRightBlockLetters lambda (omegaPrefix env n) =
      omegaPrefix (pairedRightBlockWord lambda env) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [omegaPrefix_succ, profiledRawJointRightBlockLetters_append, ih,
        omegaPrefix_succ, pairedRightBlockWord_eq_letterAt]

private def pairedLeftBlockLettersFrom
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    List (In₁ × In₂) → List (In₁ × In₂) →
      List (PairedLeftBlockLetter
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
  | _, [] => []
  | prior, move :: moves =>
      pairedLeftBlockLetterAt lambda prior move ::
        pairedLeftBlockLettersFrom lambda (prior ++ [move]) moves

/-- Left mirror of the causal physical-letter list. -/
def profiledRawJointLeftBlockLetters
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) :
    List (PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :=
  pairedLeftBlockLettersFrom lambda [] past

private theorem pairedLeftBlockLettersFrom_append
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (prior moves : List (In₁ × In₂)) (move : In₁ × In₂) :
    pairedLeftBlockLettersFrom lambda prior (moves ++ [move]) =
      pairedLeftBlockLettersFrom lambda prior moves ++
        [pairedLeftBlockLetterAt lambda (prior ++ moves) move] := by
  induction moves generalizing prior with
  | nil => simp [pairedLeftBlockLettersFrom]
  | cons first rest ih =>
      simp only [List.cons_append, pairedLeftBlockLettersFrom]
      rw [ih]
      simp [List.append_assoc]

theorem profiledRawJointLeftBlockLetters_append
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    profiledRawJointLeftBlockLetters lambda (past ++ [move]) =
      profiledRawJointLeftBlockLetters lambda past ++
        [pairedLeftBlockLetterAt lambda past move] := by
  simpa [profiledRawJointLeftBlockLetters] using
    pairedLeftBlockLettersFrom_append lambda [] past move

theorem profiledRawJointLeftBlockLetters_omegaPrefix
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat → In₁ × In₂) : ∀ n,
    profiledRawJointLeftBlockLetters lambda (omegaPrefix env n) =
      omegaPrefix (pairedLeftBlockWord lambda env) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [omegaPrefix_succ, profiledRawJointLeftBlockLetters_append, ih,
        omegaPrefix_succ]
      rfl

/-! ## Literal mixed record prefixes -/

private theorem rightFirstThenBothRecords_append_of_ne_nil
    (letters : List (PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (hne : letters ≠ [])
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    profiledRawJointRightFirstThenBothRecords (letters ++ [letter]) =
      profiledRawJointRightFirstThenBothRecords letters ++
        [pairedRightRecordForRow .both letter] := by
  cases letters with
  | nil => exact False.elim (hne rfl)
  | cons first rest =>
      simp [profiledRawJointRightFirstThenBothRecords]

/-- A finite mixed right record prefix is the pointwise row schedule used by
the operational restart: `.first` at zero and `.both` afterwards. -/
theorem profiledRawJointRightFirstThenBothRecords_omegaPrefix
    (letters : Nat → PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : ∀ n,
    profiledRawJointRightFirstThenBothRecords (omegaPrefix letters n) =
      omegaPrefix
        (fun j ↦ pairedRightRecordForRow (if j = 0 then .first else .both)
          (letters j)) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [omegaPrefix_succ]
      cases n with
      | zero => rfl
      | succ n =>
          rw [rightFirstThenBothRecords_append_of_ne_nil _
            (by simp [omegaPrefix])]
          rw [ih, omegaPrefix_succ]
          simp

private theorem leftFirstThenBothRecords_append_of_ne_nil
    (letters : List (PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (hne : letters ≠ [])
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    profiledRawJointLeftFirstThenBothRecords (letters ++ [letter]) =
      profiledRawJointLeftFirstThenBothRecords letters ++
        [pairedLeftRecordForRow .both letter] := by
  cases letters with
  | nil => exact False.elim (hne rfl)
  | cons first rest =>
      simp [profiledRawJointLeftFirstThenBothRecords]

/-- Left pointwise mixed record schedule. -/
theorem profiledRawJointLeftFirstThenBothRecords_omegaPrefix
    (letters : Nat → PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : ∀ n,
    profiledRawJointLeftFirstThenBothRecords (omegaPrefix letters n) =
      omegaPrefix
        (fun j ↦ pairedLeftRecordForRow (if j = 0 then .first else .both)
          (letters j)) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [omegaPrefix_succ]
      cases n with
      | zero => rfl
      | succ n =>
          rw [leftFirstThenBothRecords_append_of_ne_nil _
            (by simp [omegaPrefix])]
          rw [ih, omegaPrefix_succ]
          simp

/-! ## Retargeting the existing accepting activation -/

/-- Forget the old target representation and expose every right close as its
full finite profiled state. -/
def profiledRawJointRightProfiledStateActivation
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source) :
    ProfiledRawJointTargetRightBlockActivation A (PairedProfiledTreeState A)
      id (fun _ ↦ True) source where
  lambda := activation.lambda
  initial_profile := activation.initial_profile
  forever := activation.forever
  target := fun row past input ↦
    .inr (.inr (profiledRawRightChildSlot A source activation.lambda row past
      input))
  target_allowed := by simp
  target_state := by intro row past input; rfl

/-- Left profiled-state retargeting. -/
def profiledRawJointLeftProfiledStateActivation
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source) :
    ProfiledRawJointTargetLeftBlockActivation A (PairedProfiledTreeState A)
      id (fun _ ↦ True) source where
  lambda := activation.lambda
  initial_profile := activation.initial_profile
  forever := activation.forever
  target := fun row past input ↦
    .inr (.inl (profiledRawLeftChildSlot A source activation.lambda row past
      input))
  target_allowed := by simp
  target_state := by intro row past input; rfl

/-! ## Definitionally exact mixed targets -/

/-- Exact mixed right target over the finite profiled-state alphabet. -/
def profiledRawJointRightFirstThenBothProfiledStateExtension
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source) :
    ProfiledRawJointTargetRightFirstThenBothActivationExtension A
      (profiledRawJointRightProfiledStateActivation A activation) where
  target := fun past input ↦
    let letters := profiledRawJointRightBlockLetters activation.lambda past
    let scan := profiledRawJointRightFirstThenBothScan A source.1.1 letters
    let row := profiledRawJointFirstThenBothScanRow A scan
    profiledRawJointRightFirstThenBothProfiledCloseTarget A scan
      (pairedRightBlockLetterAt activation.lambda past input)
      (rightClosingProfile activation.lambda row past input)
  target_allowed := by simp
  target_state := by
    intro env n
    simp only [profiledRawJointRightProfiledStateActivation, id_eq]
    rw [profiledRawJointRightBlockLetters_omegaPrefix]
    rfl

/-- Exact mixed left target. -/
def profiledRawJointLeftFirstThenBothProfiledStateExtension
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source) :
    ProfiledRawJointTargetLeftFirstThenBothActivationExtension A
      (profiledRawJointLeftProfiledStateActivation A activation) where
  target := fun past input ↦
    let letters := profiledRawJointLeftBlockLetters activation.lambda past
    let scan := profiledRawJointLeftFirstThenBothScan A source.1.1 letters
    let row := profiledRawJointFirstThenBothScanRow A scan
    profiledRawJointLeftFirstThenBothProfiledCloseTarget A scan
      (pairedLeftBlockLetterAt activation.lambda past input)
      (leftClosingProfile activation.lambda row past input)
  target_allowed := by simp
  target_state := by
    intro env n
    simp only [profiledRawJointLeftProfiledStateActivation, id_eq]
    rw [profiledRawJointLeftBlockLetters_omegaPrefix]
    rfl

/-! ## Exact finite-prefix priorities -/

/-- The concrete right extension exposes the accumulated mixed-lane
minimum definitionally. -/
theorem profiledRawJointRightFirstThenBothProfiledStateExtension_priority
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    let letters := profiledRawJointRightBlockLetters activation.lambda past
    let scan := profiledRawJointRightFirstThenBothScan A source.1.1 letters
    pairedProfiledEntryPriority A
        ((profiledRawJointRightFirstThenBothProfiledStateExtension A
          activation).target past input) =
      A.priority scan.2.2 := by
  dsimp only [profiledRawJointRightFirstThenBothProfiledStateExtension]
  exact
    pairedProfiledEntryPriority_eq_rightFirstThenBoth_min_of_erase_eq A _ _ _
      (by rfl)

/-- The same right priority stated as the original DPA minimum of the
literal `.first, .both, ...` finite record prefix. -/
theorem
    profiledRawJointRightFirstThenBothProfiledStateExtension_priority_eq_blockMin
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    pairedProfiledEntryPriority A
        ((profiledRawJointRightFirstThenBothProfiledStateExtension A
          activation).target past input) =
      A.priority
        (blockMinState A source.1.1.1
          (profiledRawJointRightFirstThenBothRecords
            (profiledRawJointRightBlockLetters activation.lambda past))) := by
  rw [profiledRawJointRightFirstThenBothProfiledStateExtension_priority A]
  rw [profiledRawJointRightFirstThenBothScan_eq_blockEndAndMin]
  rfl

/-- Left mixed-lane target priority. -/
theorem profiledRawJointLeftFirstThenBothProfiledStateExtension_priority
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let letters := profiledRawJointLeftBlockLetters activation.lambda past
    let scan := profiledRawJointLeftFirstThenBothScan A source.1.1 letters
    pairedProfiledEntryPriority A
        ((profiledRawJointLeftFirstThenBothProfiledStateExtension A
          activation).target past input) =
      A.priority scan.2.2 := by
  dsimp only [profiledRawJointLeftFirstThenBothProfiledStateExtension]
  exact
    pairedProfiledEntryPriority_eq_leftFirstThenBoth_min_of_erase_eq A _ _ _
      (by rfl)

/-- Left priority as the original DPA minimum of the literal mixed prefix. -/
theorem
    profiledRawJointLeftFirstThenBothProfiledStateExtension_priority_eq_blockMin
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    pairedProfiledEntryPriority A
        ((profiledRawJointLeftFirstThenBothProfiledStateExtension A
          activation).target past input) =
      A.priority
        (blockMinState A source.1.1.1
          (profiledRawJointLeftFirstThenBothRecords
            (profiledRawJointLeftBlockLetters activation.lambda past))) := by
  rw [profiledRawJointLeftFirstThenBothProfiledStateExtension_priority A]
  rw [profiledRawJointLeftFirstThenBothScan_eq_blockEndAndMin]
  rfl

/-! ## Direct finite controllers -/

/-- Every existing accepting right activation has a finite controller whose
extra certificate is the exact first-then-both close state. -/
theorem exists_profiledRawJointRightFirstThenBothProfiledStateController
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source) :
    ∃ controller :
        TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
          (NarrowedBlockLabel In₂ In₁
            (ProfiledRawJointRightFirstThenBothReceiverOutput
              (Out₁ := Out₁) (Out₂ := Out₂) (PairedProfiledTreeState A))
            Out₁
            (profiledRawJointTargetRightFirstThenBothCombinedMonitor A
              (PairedProfiledTreeState A) id (fun _ ↦ True) source).State),
      NarrowedAllThreadsWin
        (profiledRawJointTargetRightFirstThenBothCombinedMonitor A
          (PairedProfiledTreeState A) id (fun _ ↦ True) source)
        controller.labeledTree := by
  exact exists_profiledRawJointTargetRightFirstThenBothController A id
    (fun _ ↦ True) source
      (profiledRawJointRightProfiledStateActivation A activation)
      (profiledRawJointRightFirstThenBothProfiledStateExtension A activation)

/-- Left mirror. -/
theorem exists_profiledRawJointLeftFirstThenBothProfiledStateController
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source) :
    ∃ controller :
        TransitionRationalTree.{v, max u v x y s, max u v y s} In₂
          (NarrowedBlockLabel In₁ In₂
            (ProfiledRawJointLeftFirstThenBothReceiverOutput
              (Out₁ := Out₁) (Out₂ := Out₂) (PairedProfiledTreeState A))
            Out₂
            (profiledRawJointTargetLeftFirstThenBothCombinedMonitor A
              (PairedProfiledTreeState A) id (fun _ ↦ True) source).State),
      NarrowedAllThreadsWin
        (profiledRawJointTargetLeftFirstThenBothCombinedMonitor A
          (PairedProfiledTreeState A) id (fun _ ↦ True) source)
        controller.labeledTree := by
  exact exists_profiledRawJointTargetLeftFirstThenBothController A id
    (fun _ ↦ True) source
      (profiledRawJointLeftProfiledStateActivation A activation)
      (profiledRawJointLeftFirstThenBothProfiledStateExtension A activation)

end

end DetParityAutomaton

end DistributedSynthesis
