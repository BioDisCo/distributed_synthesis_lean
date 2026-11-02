/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartFirstThenBothScanAudit

/-!
# A finite first-then-both scan lane

The literal full-restart block does not follow either constant row of the
old paired scan: its first record uses `.first`, and every later record uses
`.both`.  This file adds exactly that finite lane.  Its state consists of one
phase bit and the current/minimum DPA pair, initialized at `code.1`.

The fold theorem below is unconditional: the lane is exactly
`blockEndAndMin` of the literal first-then-both record list.  The last section
then names, but does not assume or manufacture, the two extra fields needed
to install the lane in the target monitor: a third checked target and
acceptance of the mixed omega word.  This keeps the finite bookkeeping
separate from the remaining semantic obligation exposed by the audit.
-/

namespace DistributedSynthesis

universe u v x y s t

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-! ## The finite mixed lane -/

/-- `false` means that no letter has yet been consumed.  The second
coordinate is the current DPA state together with its minimum-priority
representative, including the initial state. -/
abbrev ProfiledRawJointFirstThenBothScanState :=
  Bool × (A.State × A.State)

/-- Canonical start of the mixed lane.  Unlike the old constant-`.both`
lane, it starts at `code.1`, because its literal first record uses `.first`. -/
def profiledRawJointFirstThenBothScanInitial
    (code : A.State × A.State) :
    ProfiledRawJointFirstThenBothScanState A :=
  (false, (code.1, code.1))

/-- The row physically selected by the mixed lane in its current phase. -/
def profiledRawJointFirstThenBothScanRow
    (scan : ProfiledRawJointFirstThenBothScanState A) : PairedEntryRow :=
  if scan.1 then .both else .first

/-- One ordinary current/minimum update. -/
def profiledRawJointStateMinStep
    (currentMin : A.State × A.State)
    (record : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    A.State × A.State :=
  let next := A.step currentMin.1 record
  (next, A.minPriorityState currentMin.2 next)

/-- Right mixed-lane transition: `.first` once and `.both` thereafter. -/
def profiledRawJointRightFirstThenBothScanStep
    (scan : ProfiledRawJointFirstThenBothScanState A)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    ProfiledRawJointFirstThenBothScanState A :=
  (true, profiledRawJointStateMinStep A scan.2
    (pairedRightRecordForRow
      (profiledRawJointFirstThenBothScanRow A scan) letter))

/-- Left mixed-lane transition. -/
def profiledRawJointLeftFirstThenBothScanStep
    (scan : ProfiledRawJointFirstThenBothScanState A)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    ProfiledRawJointFirstThenBothScanState A :=
  (true, profiledRawJointStateMinStep A scan.2
    (pairedLeftRecordForRow
      (profiledRawJointFirstThenBothScanRow A scan) letter))

/-- Finite right scan from the paired entry code. -/
def profiledRawJointRightFirstThenBothScan
    (code : A.State × A.State)
    (letters : List (PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) :
    ProfiledRawJointFirstThenBothScanState A :=
  letters.foldl (profiledRawJointRightFirstThenBothScanStep A)
    (profiledRawJointFirstThenBothScanInitial A code)

/-- Finite left scan from the paired entry code. -/
def profiledRawJointLeftFirstThenBothScan
    (code : A.State × A.State)
    (letters : List (PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) :
    ProfiledRawJointFirstThenBothScanState A :=
  letters.foldl (profiledRawJointLeftFirstThenBothScanStep A)
    (profiledRawJointFirstThenBothScanInitial A code)

private theorem rightFirstThenBothScanFold_true
    (currentMin : A.State × A.State) :
    ∀ letters : List (PairedRightBlockLetter
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)),
      (letters.foldl (profiledRawJointRightFirstThenBothScanStep A)
          (true, currentMin)).2 =
        (letters.map (pairedRightRecordForRow .both)).foldl
          (profiledRawJointStateMinStep A) currentMin := by
  intro letters
  induction letters generalizing currentMin with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons, List.map_cons]
      change
        (rest.foldl (profiledRawJointRightFirstThenBothScanStep A)
          (true, profiledRawJointStateMinStep A currentMin
            (pairedRightRecordForRow .both letter))).2 = _
      exact ih _

private theorem leftFirstThenBothScanFold_true
    (currentMin : A.State × A.State) :
    ∀ letters : List (PairedLeftBlockLetter
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)),
      (letters.foldl (profiledRawJointLeftFirstThenBothScanStep A)
          (true, currentMin)).2 =
        (letters.map (pairedLeftRecordForRow .both)).foldl
          (profiledRawJointStateMinStep A) currentMin := by
  intro letters
  induction letters generalizing currentMin with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons, List.map_cons]
      change
        (rest.foldl (profiledRawJointLeftFirstThenBothScanStep A)
          (true, profiledRawJointStateMinStep A currentMin
            (pairedLeftRecordForRow .both letter))).2 = _
      exact ih _

/-- The right finite lane is exactly the DPA current/minimum pair of the
literal `.first, .both, .both, ...` record list. -/
theorem profiledRawJointRightFirstThenBothScan_eq_blockEndAndMin
    (code : A.State × A.State)
    (letters : List (PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) :
    (profiledRawJointRightFirstThenBothScan A code letters).2 =
      blockEndAndMin A code.1
        (profiledRawJointRightFirstThenBothRecords letters) := by
  cases letters with
  | nil => rfl
  | cons first rest =>
      unfold profiledRawJointRightFirstThenBothScan
      simp only [List.foldl_cons]
      change
        (rest.foldl (profiledRawJointRightFirstThenBothScanStep A)
          (true, profiledRawJointStateMinStep A (code.1, code.1)
            (pairedRightRecordForRow .first first))).2 =
          (rest.map (pairedRightRecordForRow .both)).foldl
            (profiledRawJointStateMinStep A)
            (profiledRawJointStateMinStep A (code.1, code.1)
              (pairedRightRecordForRow .first first))
      exact rightFirstThenBothScanFold_true A _ rest

/-- Left finite-lane mirror. -/
theorem profiledRawJointLeftFirstThenBothScan_eq_blockEndAndMin
    (code : A.State × A.State)
    (letters : List (PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) :
    (profiledRawJointLeftFirstThenBothScan A code letters).2 =
      blockEndAndMin A code.1
        (profiledRawJointLeftFirstThenBothRecords letters) := by
  cases letters with
  | nil => rfl
  | cons first rest =>
      unfold profiledRawJointLeftFirstThenBothScan
      simp only [List.foldl_cons]
      change
        (rest.foldl (profiledRawJointLeftFirstThenBothScanStep A)
          (true, profiledRawJointStateMinStep A (code.1, code.1)
            (pairedLeftRecordForRow .first first))).2 =
          (rest.map (pairedLeftRecordForRow .both)).foldl
            (profiledRawJointStateMinStep A)
            (profiledRawJointStateMinStep A (code.1, code.1)
              (pairedLeftRecordForRow .first first))
      exact leftFirstThenBothScanFold_true A _ rest

/-! ## The exact closing target carried by the third lane -/

/-- Right closing child computed from the actual mixed-lane state. -/
def profiledRawJointRightFirstThenBothCloseTarget
    (scan : ProfiledRawJointFirstThenBothScanState A)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    PairedEntryTreeState A :=
  let row := profiledRawJointFirstThenBothScanRow A scan
  let current := scan.2.1
  let minimum := scan.2.2
  let informed := pairedRightInformedForRow row letter.2.1
  let closing := pairedRightClosingForRow row letter.2.1
  let childCode :=
    (A.step current (rightRoundRecord letter.1 letter.2.2 informed),
      A.step current
        (bothRoundRecord (letter.1.2, letter.1.1) closing informed))
  .inr (.inr (childCode, minimum))

/-- Left closing child computed from the mixed lane. -/
def profiledRawJointLeftFirstThenBothCloseTarget
    (scan : ProfiledRawJointFirstThenBothScanState A)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    PairedEntryTreeState A :=
  let row := profiledRawJointFirstThenBothScanRow A scan
  let current := scan.2.1
  let minimum := scan.2.2
  let informed := pairedLeftInformedForRow row letter.2.1
  let closing := pairedLeftClosingForRow row letter.2.1
  let childCode :=
    (A.step current (leftRoundRecord letter.1 informed letter.2.2),
      A.step current (bothRoundRecord letter.1 informed closing))
  .inr (.inl (childCode, minimum))

/-- Profiled right target for the mixed lane.  The explicit profile is the
one-round overlap datum checked on the following letter. -/
def profiledRawJointRightFirstThenBothProfiledCloseTarget
    (scan : ProfiledRawJointFirstThenBothScanState A)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)) :
    PairedProfiledTreeState A :=
  let row := profiledRawJointFirstThenBothScanRow A scan
  let current := scan.2.1
  let minimum := scan.2.2
  let informed := pairedRightInformedForRow row letter.2.1
  let closing := pairedRightClosingForRow row letter.2.1
  let childCode :=
    (A.step current (rightRoundRecord letter.1 letter.2.2 informed),
      A.step current
        (bothRoundRecord (letter.1.2, letter.1.1) closing informed))
  .inr (.inr (((childCode, minimum), profile)))

/-- Profiled left target for the mixed lane. -/
def profiledRawJointLeftFirstThenBothProfiledCloseTarget
    (scan : ProfiledRawJointFirstThenBothScanState A)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) :
    PairedProfiledTreeState A :=
  let row := profiledRawJointFirstThenBothScanRow A scan
  let current := scan.2.1
  let minimum := scan.2.2
  let informed := pairedLeftInformedForRow row letter.2.1
  let closing := pairedLeftClosingForRow row letter.2.1
  let childCode :=
    (A.step current (leftRoundRecord letter.1 informed letter.2.2),
      A.step current (bothRoundRecord letter.1 informed closing))
  .inr (.inl (((childCode, minimum), profile)))

@[simp] theorem erase_rightFirstThenBothProfiledCloseTarget
    (scan : ProfiledRawJointFirstThenBothScanState A)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)) :
    erasePairedProfiledState A
        (profiledRawJointRightFirstThenBothProfiledCloseTarget A scan letter
          profile) =
      profiledRawJointRightFirstThenBothCloseTarget A scan letter := by
  rfl

@[simp] theorem erase_leftFirstThenBothProfiledCloseTarget
    (scan : ProfiledRawJointFirstThenBothScanState A)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) :
    erasePairedProfiledState A
        (profiledRawJointLeftFirstThenBothProfiledCloseTarget A scan letter
          profile) =
      profiledRawJointLeftFirstThenBothCloseTarget A scan letter := by
  rfl

/-- An exact right mixed-close check exposes exactly the lane's accumulated
minimum as the compressed target priority. -/
theorem pairedProfiledEntryPriority_eq_rightFirstThenBoth_min_of_erase_eq
    (target : PairedProfiledTreeState A)
    (scan : ProfiledRawJointFirstThenBothScanState A)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      profiledRawJointRightFirstThenBothCloseTarget A scan letter) :
    pairedProfiledEntryPriority A target = A.priority scan.2.2 := by
  unfold pairedProfiledEntryPriority
  rw [herase]
  rfl

/-- Left mixed-close priority mirror. -/
theorem pairedProfiledEntryPriority_eq_leftFirstThenBoth_min_of_erase_eq
    (target : PairedProfiledTreeState A)
    (scan : ProfiledRawJointFirstThenBothScanState A)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      profiledRawJointLeftFirstThenBothCloseTarget A scan letter) :
    pairedProfiledEntryPriority A target = A.priority scan.2.2 := by
  unfold pairedProfiledEntryPriority
  rw [herase]
  rfl

/-! ## Named sockets for the monitor extension

These definitions isolate the additional finite-safety obligation.  The
current receiver output carries targets only for the two constant rows, so
the repaired monitor adds one target value for the mixed lane and checks its
exact state at every prefix.  Omega acceptance remains with the transported
two-row monitor: fixed-row acceptance does not imply acceptance of the mixed
omega word, as the preceding audit shows, and no such implication is used.
-/

/-- The smallest output extension: retain the existing two target entries
and add one target for the first-then-both lane. -/
structure ProfiledRawJointRightFirstThenBothReceiverOutput
    (Target : Type t) where
  base : ProfiledRawJointTargetRightReceiverOutput
    (Out₁ := Out₁) (Out₂ := Out₂) Target
  firstThenBothTarget : Target
deriving Inhabited

/-- Left output extension. -/
structure ProfiledRawJointLeftFirstThenBothReceiverOutput
    (Target : Type t) where
  base : ProfiledRawJointTargetLeftReceiverOutput
    (Out₁ := Out₁) (Out₂ := Out₂) Target
  firstThenBothTarget : Target
deriving Inhabited

noncomputable instance {Target : Type t}
    [Fintype Out₁] [Fintype Out₂] [Fintype Target] :
    Fintype (ProfiledRawJointRightFirstThenBothReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) Target) := by
  classical
  exact Fintype.ofEquiv
    (ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) Target × Target) {
      toFun := fun output ↦ ⟨output.1, output.2⟩
      invFun := fun output ↦ (output.base, output.firstThenBothTarget)
      left_inv := by intro output; cases output; rfl
      right_inv := by intro output; cases output; rfl }

noncomputable instance {Target : Type t}
    [Fintype Out₁] [Fintype Out₂] [Fintype Target] :
    Fintype (ProfiledRawJointLeftFirstThenBothReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) Target) := by
  classical
  exact Fintype.ofEquiv
    (ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) Target × Target) {
      toFun := fun output ↦ ⟨output.1, output.2⟩
      invFun := fun output ↦ (output.base, output.firstThenBothTarget)
      left_inv := by intro output; cases output; rfl
      right_inv := by intro output; cases output; rfl }

/-- Exact third-target check consumed by a repaired right monitor at one
prefix. -/
def ProfiledRawJointRightFirstThenBothTargetSafe
    {Target : Type t}
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (scan : ProfiledRawJointFirstThenBothScanState A)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (target : Target) : Prop :=
  erasePairedProfiledState A (targetState target) =
      profiledRawJointRightFirstThenBothCloseTarget A scan letter ∧
    Allowed target

/-- Exact left third-target check. -/
def ProfiledRawJointLeftFirstThenBothTargetSafe
    {Target : Type t}
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (scan : ProfiledRawJointFirstThenBothScanState A)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (target : Target) : Prop :=
  erasePairedProfiledState A (targetState target) =
      profiledRawJointLeftFirstThenBothCloseTarget A scan letter ∧
    Allowed target

/-- Acceptance obligation for one infinite right physical-letter stream. -/
def ProfiledRawJointRightFirstThenBothAccepts
    (code : A.State × A.State)
    (letters : Nat → PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  A.AcceptsFrom code.1 (fun n ↦
    pairedRightRecordForRow (if n = 0 then .first else .both) (letters n))

/-- Acceptance obligation for one infinite left physical-letter stream. -/
def ProfiledRawJointLeftFirstThenBothAccepts
    (code : A.State × A.State)
    (letters : Nat → PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  A.AcceptsFrom code.1 (fun n ↦
    pairedLeftRecordForRow (if n = 0 then .first else .both) (letters n))

/-- The actual mixed right omega word generated by one paired lambda. -/
def pairedRightFirstThenBothOmegaWord
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat → In₂ × In₁) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n ↦ pairedRightRecordForRow (if n = 0 then .first else .both)
    (pairedRightBlockWord lambda env n)

/-- Left mixed omega word. -/
def pairedLeftFirstThenBothOmegaWord
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat → In₁ × In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n ↦ pairedLeftRecordForRow (if n = 0 then .first else .both)
    (pairedLeftBlockWord lambda env n)

/-- Optional source-level mixed acceptance property.  The finite restart
repair below does not require this property: omega acceptance continues to
come from the existing two-row block monitor. -/
def PairedRightFirstThenBothForeverAccepts
    (code : A.State × A.State)
  (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ env, A.AcceptsFrom code.1
    (pairedRightFirstThenBothOmegaWord lambda env)

/-- Left source-level mixed acceptance field. -/
def PairedLeftFirstThenBothForeverAccepts
    (code : A.State × A.State)
  (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ env, A.AcceptsFrom code.1
    (pairedLeftFirstThenBothOmegaWord lambda env)

/-- Minimal source-level right extension.  It wraps an existing activation
and adds only the exact finite mixed-lane target.  The existing activation
already supplies omega acceptance through the transported two-row monitor.
The new target carries the full profiled child (not only its erasure), which
also pins the next-round overlap profile. -/
structure ProfiledRawJointTargetRightFirstThenBothActivationExtension
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source) : Type _ where
  target : List (In₂ × In₁) → In₂ × In₁ → Target
  target_allowed : ∀ past input, Allowed (target past input)
  target_state : ∀ (env : Nat → In₂ × In₁) (n : Nat),
    let letters := pairedRightBlockWord activation.lambda env
    let scan := profiledRawJointRightFirstThenBothScan A source.1.1
      (omegaPrefix letters n)
    let row := profiledRawJointFirstThenBothScanRow A scan
    targetState (target (omegaPrefix env n) (env n)) =
      profiledRawJointRightFirstThenBothProfiledCloseTarget A scan
        (letters n)
        (rightClosingProfile activation.lambda row (omegaPrefix env n)
          (env n))

/-- Minimal source-level left extension. -/
structure ProfiledRawJointTargetLeftFirstThenBothActivationExtension
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source) : Type _ where
  target : List (In₁ × In₂) → In₁ × In₂ → Target
  target_allowed : ∀ past input, Allowed (target past input)
  target_state : ∀ (env : Nat → In₁ × In₂) (n : Nat),
    let letters := pairedLeftBlockWord activation.lambda env
    let scan := profiledRawJointLeftFirstThenBothScan A source.1.1
      (omegaPrefix letters n)
    let row := profiledRawJointFirstThenBothScanRow A scan
    targetState (target (omegaPrefix env n) (env n)) =
      profiledRawJointLeftFirstThenBothProfiledCloseTarget A scan
        (letters n)
        (leftClosingProfile activation.lambda row (omegaPrefix env n)
          (env n))

/-- Exact right-side finite-safety socket for one physical play. -/
structure ProfiledRawJointRightFirstThenBothMonitorLaws
    {Target : Type t}
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (code : A.State × A.State)
    (letters : Nat → PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (targets : Nat → Target) : Prop where
  targetSafe : ∀ n,
    ProfiledRawJointRightFirstThenBothTargetSafe A targetState Allowed
      (profiledRawJointRightFirstThenBothScan A code (omegaPrefix letters n))
      (letters n) (targets n)

/-- Exact left-side proof socket. -/
structure ProfiledRawJointLeftFirstThenBothMonitorLaws
    {Target : Type t}
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (code : A.State × A.State)
    (letters : Nat → PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (targets : Nat → Target) : Prop where
  targetSafe : ∀ n,
    ProfiledRawJointLeftFirstThenBothTargetSafe A targetState Allowed
      (profiledRawJointLeftFirstThenBothScan A code (omegaPrefix letters n))
      (letters n) (targets n)

end DetParityAutomaton

end DistributedSynthesis
