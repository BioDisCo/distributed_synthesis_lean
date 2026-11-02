/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedInitialRegularization
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedFirstControllerBank

/-!
# Inversion and local key handoff for profiled initial controllers

A winning finite initial controller emits raw finite certificate data.  The
sticky monitor retypes it as a profiled guarded source.  Its erased-target
equation then forces the target into the correct live orientation, producing
the exact key of the exceptional first-block controller bank.
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

/-! ## Initial-left inversion -/

variable
  (leftReceiver : ReceiverBlockStrategy In₁ In₂
    (ProfiledGuardedInitialLeftReceiverOutput A))
  (leftSender : SenderBlockStrategy In₂ Out₂)

def initialLeftLambdaOfProfiledGuardedPair : InitialLeftLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) where
  blindTwo := leftSender
  informedOne := fun past move => (leftReceiver past move).1.informedOne
  reversingOne := fun past move => (leftReceiver past move).1.reversingOne
  reversingTwo := fun past move => (leftReceiver past move).1.reversingTwo

noncomputable def profiledGuardedInitialLeftPairPending
    (env : Nat → In₁ × In₂) : Nat →
      Option (ProfiledGuardedRightEntryData A)
  | 0 => none
  | n + 1 => some (leftReceiver (omegaPrefix env n) (env n)).2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledGuardedInitialLeftPair_physical
    (env : Nat → In₁ × In₂) (n : Nat) :
    profiledGuardedInitialLeftPhysicalLetter A
        (pairPlay leftReceiver leftSender env n) =
      initialLeftLetterAt
        (initialLeftLambdaOfProfiledGuardedPair A leftReceiver leftSender)
        (omegaPrefix env n) (env n) := by
  simp [profiledGuardedInitialLeftPhysicalLetter, pairPlay, treePlay,
    treeOfPair, blockLabelApply, branchNode_eq_omegaPrefix,
    initialLeftLambdaOfProfiledGuardedPair, initialLeftLetterAt]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledGuardedInitialLeftPair_source
    (env : Nat → In₁ × In₂) (n : Nat) :
    (pairPlay leftReceiver leftSender env n).2.1.2 =
      (leftReceiver (omegaPrefix env n) (env n)).2 := by
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    branchNode_eq_omegaPrefix]

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂]

theorem profiledGuardedInitialLeftBlockMonitor_run_shape
    (env : Nat → In₁ × In₂) : ∀ n, ∃ safe : Bool,
    (profiledGuardedInitialLeftBlockMonitor A).run
        (pairPlay leftReceiver leftSender env) n =
      ((initialLeftScanAfter A
          (initialLeftLambdaOfProfiledGuardedPair A leftReceiver leftSender)
          (omegaPrefix env n),
        profiledGuardedInitialLeftPairPending A leftReceiver env n), safe) := by
  classical
  intro n
  induction n with
  | zero => exact ⟨true, rfl⟩
  | succ n ih =>
      rcases ih with ⟨safe, ih⟩
      rw [BlockRecordMonitor.run, ih]
      refine ⟨(profiledGuardedInitialLeftBlockMonitor A).step
        ((initialLeftScanAfter A
            (initialLeftLambdaOfProfiledGuardedPair A leftReceiver leftSender)
            (omegaPrefix env n),
          profiledGuardedInitialLeftPairPending A leftReceiver env n), safe)
        (pairPlay leftReceiver leftSender env n) |>.2, ?_⟩
      rw [omegaPrefix_succ, initialLeftScanAfter_append]
      simp only [profiledGuardedInitialLeftBlockMonitor]
      rw [profiledGuardedInitialLeftPair_physical
        A leftReceiver leftSender env n,
        profiledGuardedInitialLeftPair_source
        A leftReceiver leftSender env n]
      rfl

theorem profiledGuardedInitialLeft_safe_false_persists
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledGuardedInitialLeftReceiverOutput A) Out₂)
    {N : Nat}
    (hfalse : ((profiledGuardedInitialLeftBlockMonitor A).run play N).2 = false) :
    ∀ n, N ≤ n →
      ((profiledGuardedInitialLeftBlockMonitor A).run play n).2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [profiledGuardedInitialLeftBlockMonitor]
      change (((profiledGuardedInitialLeftBlockMonitor A).run
        play (N + k)).2 && decide _ && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

theorem profiledGuardedInitialLeft_safe_of_wins
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledGuardedInitialLeftReceiverOutput A) Out₂)
    (hwin : (profiledGuardedInitialLeftBlockMonitor A).WinsPlay play)
    (n : Nat) :
    ((profiledGuardedInitialLeftBlockMonitor A).run play n).2 = true := by
  by_contra hnot
  have hfalse := Bool.eq_false_of_not_eq_true hnot
  have hpersist := profiledGuardedInitialLeft_safe_false_persists
    A play hfalse
  have heventual : ∀ k, n ≤ k →
      (profiledGuardedInitialLeftBlockMonitor A).priority
        ((profiledGuardedInitialLeftBlockMonitor A).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change (if ((profiledGuardedInitialLeftBlockMonitor A).run play k).2
      then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

end

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Target and profiled feasibility checks at one concrete initial-left node. -/
theorem profiledGuardedInitialLeft_stepConditions
    (hmonitor : ∀ env : Nat → In₁ × In₂,
      (profiledGuardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay leftReceiver leftSender env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    let lambda := initialLeftLambdaOfProfiledGuardedPair
      A leftReceiver leftSender
    let source := (leftReceiver past move).2
    erasePairedProfiledState A source.1 = initialLeftDelayedTarget A
        (initialLeftScanAfter A lambda past)
        (initialLeftLetterAt lambda past move) ∧
      (rightProfiledGuardedAutomaton A source.1 source.2).HasRationalRun := by
  classical
  dsimp only
  let finiteWord := past ++ [move]
  let env : Nat → In₁ × In₂ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix, finiteWord]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by simp [finiteWord]; omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = move
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  rcases profiledGuardedInitialLeftBlockMonitor_run_shape
      A leftReceiver leftSender env past.length with ⟨safe, hshape⟩
  have hsafeNext := profiledGuardedInitialLeft_safe_of_wins A
    (pairPlay leftReceiver leftSender env) (hmonitor env) (past.length + 1)
  rw [BlockRecordMonitor.run, hshape] at hsafeNext
  simp only [profiledGuardedInitialLeftBlockMonitor] at hsafeNext
  rw [profiledGuardedInitialLeftPair_physical
      A leftReceiver leftSender env past.length,
    profiledGuardedInitialLeftPair_source
      A leftReceiver leftSender env past.length, hpast, hmove] at hsafeNext
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsafeNext
  exact ⟨hsafeNext.1.1.2, hsafeNext.1.2⟩

noncomputable def profiledGuardedInitialLeftSourceAt
    (hmonitor : ∀ env : Nat → In₁ × In₂,
      (profiledGuardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay leftReceiver leftSender env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ProfiledGuardedRightEntrySource A :=
  ⟨(leftReceiver past move).2,
    (profiledGuardedInitialLeft_stepConditions A leftReceiver leftSender
      hmonitor past move).2⟩

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledGuardedInitialLeftSourceAt_target
    (hmonitor : ∀ env : Nat → In₁ × In₂,
      (profiledGuardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay leftReceiver leftSender env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    erasePairedProfiledState A
        (profiledGuardedInitialLeftSourceAt A leftReceiver leftSender
          hmonitor past move).1.1 =
      initialLeftDelayedTarget A
        (initialLeftScanAfter A
          (initialLeftLambdaOfProfiledGuardedPair A leftReceiver leftSender) past)
        (initialLeftLetterAt
          (initialLeftLambdaOfProfiledGuardedPair A leftReceiver leftSender)
          past move) :=
  (profiledGuardedInitialLeft_stepConditions A leftReceiver leftSender
    hmonitor past move).1

/-- Erasure to an initial-left delayed target forces the profiled target to
be a process-one live state, exposing its stored recurrent profile. -/
noncomputable def profiledGuardedFirstRightMacroOfDelayedTarget
    (source : ProfiledGuardedRightEntrySource A)
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (htarget : erasePairedProfiledState A source.1.1 =
      initialLeftDelayedTarget A scan letter) :
    ProfiledGuardedFirstRightMacro A := by
  classical
  cases hs : source.1.1 with
  | inl sink =>
      rw [hs] at htarget
      simp [erasePairedProfiledState, initialLeftDelayedTarget] at htarget
  | inr live =>
      cases live with
      | inl rightLive => exact ⟨source, ⟨rightLive, hs⟩⟩
      | inr leftLive =>
          rw [hs] at htarget
          simp [erasePairedProfiledState, initialLeftDelayedTarget] at htarget

/-- Exact exceptional right-bank key emitted at an initial-left node. -/
noncomputable def profiledGuardedInitialLeftFirstMacroAt
    (hmonitor : ∀ env : Nat → In₁ × In₂,
      (profiledGuardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay leftReceiver leftSender env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ProfiledGuardedFirstRightMacro A :=
  profiledGuardedFirstRightMacroOfDelayedTarget A
    (profiledGuardedInitialLeftSourceAt A leftReceiver leftSender
      hmonitor past move)
    (initialLeftScanAfter A
      (initialLeftLambdaOfProfiledGuardedPair A leftReceiver leftSender) past)
    (initialLeftLetterAt
      (initialLeftLambdaOfProfiledGuardedPair A leftReceiver leftSender)
      past move)
    (profiledGuardedInitialLeftSourceAt_target A leftReceiver leftSender
      hmonitor past move)

/-! ## Initial-right inversion -/

variable
  (rightReceiver : ReceiverBlockStrategy In₂ In₁
    (ProfiledGuardedInitialRightReceiverOutput A))
  (rightSender : SenderBlockStrategy In₁ Out₁)

def initialRightLambdaOfProfiledGuardedPair : InitialRightLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) where
  blindOne := rightSender
  informedTwo := fun past move => (rightReceiver past move).1.informedTwo
  reversingOne := fun past move => (rightReceiver past move).1.reversingOne
  reversingTwo := fun past move => (rightReceiver past move).1.reversingTwo

noncomputable def profiledGuardedInitialRightPairPending
    (env : Nat → In₂ × In₁) : Nat → Option (ProfiledGuardedLeftEntryData A)
  | 0 => none
  | n + 1 => some (rightReceiver (omegaPrefix env n) (env n)).2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledGuardedInitialRightPair_physical
    (env : Nat → In₂ × In₁) (n : Nat) :
    profiledGuardedInitialRightPhysicalLetter A
        (pairPlay rightReceiver rightSender env n) =
      initialRightLetterAt
        (initialRightLambdaOfProfiledGuardedPair A rightReceiver rightSender)
        (omegaPrefix env n) (env n) := by
  simp [profiledGuardedInitialRightPhysicalLetter, pairPlay, treePlay,
    treeOfPair, blockLabelApply, branchNode_eq_omegaPrefix,
    initialRightLambdaOfProfiledGuardedPair, initialRightLetterAt]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledGuardedInitialRightPair_source
    (env : Nat → In₂ × In₁) (n : Nat) :
    (pairPlay rightReceiver rightSender env n).2.1.2 =
      (rightReceiver (omegaPrefix env n) (env n)).2 := by
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    branchNode_eq_omegaPrefix]

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂]

theorem profiledGuardedInitialRightBlockMonitor_run_shape
    (env : Nat → In₂ × In₁) : ∀ n, ∃ safe : Bool,
    (profiledGuardedInitialRightBlockMonitor A).run
        (pairPlay rightReceiver rightSender env) n =
      ((initialRightScanAfter A
          (initialRightLambdaOfProfiledGuardedPair A rightReceiver rightSender)
          (omegaPrefix env n),
        profiledGuardedInitialRightPairPending A rightReceiver env n), safe) := by
  classical
  intro n
  induction n with
  | zero => exact ⟨true, rfl⟩
  | succ n ih =>
      rcases ih with ⟨safe, ih⟩
      rw [BlockRecordMonitor.run, ih]
      refine ⟨(profiledGuardedInitialRightBlockMonitor A).step
        ((initialRightScanAfter A
            (initialRightLambdaOfProfiledGuardedPair A rightReceiver rightSender)
            (omegaPrefix env n),
          profiledGuardedInitialRightPairPending A rightReceiver env n), safe)
        (pairPlay rightReceiver rightSender env n) |>.2, ?_⟩
      rw [omegaPrefix_succ, initialRightScanAfter_append]
      simp only [profiledGuardedInitialRightBlockMonitor]
      rw [profiledGuardedInitialRightPair_physical
        A rightReceiver rightSender env n,
        profiledGuardedInitialRightPair_source
        A rightReceiver rightSender env n]
      rfl

theorem profiledGuardedInitialRight_safe_false_persists
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledGuardedInitialRightReceiverOutput A) Out₁)
    {N : Nat}
    (hfalse : ((profiledGuardedInitialRightBlockMonitor A).run play N).2 = false) :
    ∀ n, N ≤ n →
      ((profiledGuardedInitialRightBlockMonitor A).run play n).2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [profiledGuardedInitialRightBlockMonitor]
      change (((profiledGuardedInitialRightBlockMonitor A).run
        play (N + k)).2 && decide _ && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

theorem profiledGuardedInitialRight_safe_of_wins
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledGuardedInitialRightReceiverOutput A) Out₁)
    (hwin : (profiledGuardedInitialRightBlockMonitor A).WinsPlay play)
    (n : Nat) :
    ((profiledGuardedInitialRightBlockMonitor A).run play n).2 = true := by
  by_contra hnot
  have hfalse := Bool.eq_false_of_not_eq_true hnot
  have hpersist := profiledGuardedInitialRight_safe_false_persists
    A play hfalse
  have heventual : ∀ k, n ≤ k →
      (profiledGuardedInitialRightBlockMonitor A).priority
        ((profiledGuardedInitialRightBlockMonitor A).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change (if ((profiledGuardedInitialRightBlockMonitor A).run play k).2
      then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

end

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledGuardedInitialRight_stepConditions
    (hmonitor : ∀ env : Nat → In₂ × In₁,
      (profiledGuardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay rightReceiver rightSender env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    let lambda := initialRightLambdaOfProfiledGuardedPair
      A rightReceiver rightSender
    let source := (rightReceiver past move).2
    erasePairedProfiledState A source.1 = initialRightDelayedTarget A
        (initialRightScanAfter A lambda past)
        (initialRightLetterAt lambda past move) ∧
      (leftProfiledGuardedAutomaton A source.1 source.2).HasRationalRun := by
  classical
  dsimp only
  let finiteWord := past ++ [move]
  let env : Nat → In₂ × In₁ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix, finiteWord]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by simp [finiteWord]; omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = move
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  rcases profiledGuardedInitialRightBlockMonitor_run_shape
      A rightReceiver rightSender env past.length with ⟨safe, hshape⟩
  have hsafeNext := profiledGuardedInitialRight_safe_of_wins A
    (pairPlay rightReceiver rightSender env) (hmonitor env) (past.length + 1)
  rw [BlockRecordMonitor.run, hshape] at hsafeNext
  simp only [profiledGuardedInitialRightBlockMonitor] at hsafeNext
  rw [profiledGuardedInitialRightPair_physical
      A rightReceiver rightSender env past.length,
    profiledGuardedInitialRightPair_source
      A rightReceiver rightSender env past.length, hpast, hmove] at hsafeNext
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsafeNext
  exact ⟨hsafeNext.1.1.2, hsafeNext.1.2⟩

noncomputable def profiledGuardedInitialRightSourceAt
    (hmonitor : ∀ env : Nat → In₂ × In₁,
      (profiledGuardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay rightReceiver rightSender env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ProfiledGuardedLeftEntrySource A :=
  ⟨(rightReceiver past move).2,
    (profiledGuardedInitialRight_stepConditions A rightReceiver rightSender
      hmonitor past move).2⟩

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledGuardedInitialRightSourceAt_target
    (hmonitor : ∀ env : Nat → In₂ × In₁,
      (profiledGuardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay rightReceiver rightSender env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    erasePairedProfiledState A
        (profiledGuardedInitialRightSourceAt A rightReceiver rightSender
          hmonitor past move).1.1 =
      initialRightDelayedTarget A
        (initialRightScanAfter A
          (initialRightLambdaOfProfiledGuardedPair A rightReceiver rightSender) past)
        (initialRightLetterAt
          (initialRightLambdaOfProfiledGuardedPair A rightReceiver rightSender)
          past move) :=
  (profiledGuardedInitialRight_stepConditions A rightReceiver rightSender
    hmonitor past move).1

noncomputable def profiledGuardedFirstLeftMacroOfDelayedTarget
    (source : ProfiledGuardedLeftEntrySource A)
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (htarget : erasePairedProfiledState A source.1.1 =
      initialRightDelayedTarget A scan letter) :
    ProfiledGuardedFirstLeftMacro A := by
  classical
  cases hs : source.1.1 with
  | inl sink =>
      rw [hs] at htarget
      simp [erasePairedProfiledState, initialRightDelayedTarget] at htarget
  | inr live =>
      cases live with
      | inl rightLive =>
          rw [hs] at htarget
          simp [erasePairedProfiledState, initialRightDelayedTarget] at htarget
      | inr leftLive => exact ⟨source, ⟨leftLive, hs⟩⟩

noncomputable def profiledGuardedInitialRightFirstMacroAt
    (hmonitor : ∀ env : Nat → In₂ × In₁,
      (profiledGuardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay rightReceiver rightSender env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ProfiledGuardedFirstLeftMacro A :=
  profiledGuardedFirstLeftMacroOfDelayedTarget A
    (profiledGuardedInitialRightSourceAt A rightReceiver rightSender
      hmonitor past move)
    (initialRightScanAfter A
      (initialRightLambdaOfProfiledGuardedPair A rightReceiver rightSender) past)
    (initialRightLetterAt
      (initialRightLambdaOfProfiledGuardedPair A rightReceiver rightSender)
      past move)
    (profiledGuardedInitialRightSourceAt_target A rightReceiver rightSender
      hmonitor past move)

/-! ## Finite local initialization from one common key -/

variable (firstBank : FiniteProfiledGuardedFirstControllerBank A)

abbrev ProfiledGuardedFirstRightOwnerControl :=
  Σ key : ProfiledGuardedFirstRightMacro A,
    (firstBank.rightController key).Control

abbrev ProfiledGuardedFirstLeftOwnerControl :=
  Σ key : ProfiledGuardedFirstLeftMacro A,
    (firstBank.leftController key).Control

abbrev ProfiledGuardedFirstRightReceiverControl :=
  Σ key : ProfiledGuardedFirstRightMacro A,
    PairedEntryRow × (profiledGuardedFirstRightMonitorAt A key).State

abbrev ProfiledGuardedFirstLeftReceiverControl :=
  Σ key : ProfiledGuardedFirstLeftMacro A,
    PairedEntryRow × (profiledGuardedFirstLeftMonitorAt A key).State

noncomputable instance :
    Fintype (ProfiledGuardedFirstRightOwnerControl A firstBank) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledGuardedFirstLeftOwnerControl A firstBank) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledGuardedFirstRightReceiverControl A) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledGuardedFirstLeftReceiverControl A) := by
  classical
  infer_instance

noncomputable def initialProfiledGuardedFirstRightOwner
    (key : ProfiledGuardedFirstRightMacro A) :
    ProfiledGuardedFirstRightOwnerControl A firstBank :=
  ⟨key, (firstBank.rightController key).initial⟩

noncomputable def initialProfiledGuardedFirstLeftOwner
    (key : ProfiledGuardedFirstLeftMacro A) :
    ProfiledGuardedFirstLeftOwnerControl A firstBank :=
  ⟨key, (firstBank.leftController key).initial⟩

noncomputable def initialProfiledGuardedFirstRightReceiver
    (key : ProfiledGuardedFirstRightMacro A) (row : PairedEntryRow) :
    ProfiledGuardedFirstRightReceiverControl A :=
  ⟨key, row, (profiledGuardedFirstRightMonitorAt A key).initial⟩

noncomputable def initialProfiledGuardedFirstLeftReceiver
    (key : ProfiledGuardedFirstLeftMacro A) (row : PairedEntryRow) :
    ProfiledGuardedFirstLeftReceiverControl A :=
  ⟨key, row, (profiledGuardedFirstLeftMonitorAt A key).initial⟩

/-- Initial-left boundary initializes owner and receiver exceptional controls
from literally the same profiled macro. -/
noncomputable def profiledGuardedInitialLeftFirstControlsAt
    (hmonitor : ∀ env : Nat → In₁ × In₂,
      (profiledGuardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay leftReceiver leftSender env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) :
    ProfiledGuardedFirstRightOwnerControl A firstBank ×
      ProfiledGuardedFirstRightReceiverControl A :=
  let key := profiledGuardedInitialLeftFirstMacroAt A leftReceiver leftSender
    hmonitor past move
  (initialProfiledGuardedFirstRightOwner A firstBank key,
    initialProfiledGuardedFirstRightReceiver A key row)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledGuardedInitialLeftFirstControlsAt_keys
    (hmonitor : ∀ env : Nat → In₁ × In₂,
      (profiledGuardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay leftReceiver leftSender env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) :
    (profiledGuardedInitialLeftFirstControlsAt A leftReceiver leftSender
      firstBank hmonitor past move row).1.1 =
    (profiledGuardedInitialLeftFirstControlsAt A leftReceiver leftSender
      firstBank hmonitor past move row).2.1 := rfl

/-- Initial-right mirror. -/
noncomputable def profiledGuardedInitialRightFirstControlsAt
    (hmonitor : ∀ env : Nat → In₂ × In₁,
      (profiledGuardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay rightReceiver rightSender env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) :
    ProfiledGuardedFirstLeftOwnerControl A firstBank ×
      ProfiledGuardedFirstLeftReceiverControl A :=
  let key := profiledGuardedInitialRightFirstMacroAt A rightReceiver rightSender
    hmonitor past move
  (initialProfiledGuardedFirstLeftOwner A firstBank key,
    initialProfiledGuardedFirstLeftReceiver A key row)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledGuardedInitialRightFirstControlsAt_keys
    (hmonitor : ∀ env : Nat → In₂ × In₁,
      (profiledGuardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay rightReceiver rightSender env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) :
    (profiledGuardedInitialRightFirstControlsAt A rightReceiver rightSender
      firstBank hmonitor past move row).1.1 =
    (profiledGuardedInitialRightFirstControlsAt A rightReceiver rightSender
      firstBank hmonitor past move row).2.1 := rfl

end

end


end DetParityAutomaton

end DistributedSynthesis
