/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedInitialRegularization

/-!
# Inverting the guarded initial monitor

Winning the sticky guarded monitor implies that every source emitted by the
informed receiver has the exact delayed target, is genuinely feasible, and
has a profile agreeing with the receiver's complete next-round overlap table.
These statements turn the untyped finite runtime pair back into a typed
`GuardedRightEntrySource` at readback time.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

section Left

variable
  (receiver : ReceiverBlockStrategy In₁ In₂ (GuardedInitialLeftReceiverOutput A))
  (sender : SenderBlockStrategy In₂ Out₂)

/-- Physical initial-left lambda obtained by erasing the guarded source. -/
def initialLeftLambdaOfGuardedPair : InitialLeftLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) where
  blindTwo := sender
  informedOne := fun past move => (receiver past move).1.informedOne
  reversingOne := fun past move => (receiver past move).1.reversingOne
  reversingTwo := fun past move => (receiver past move).1.reversingTwo

noncomputable def guardedInitialLeftPairPending
    (env : Nat -> In₁ × In₂) : Nat -> Option (GuardedRightEntryData A)
  | 0 => none
  | n + 1 => some (receiver (omegaPrefix env n) (env n)).2

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
theorem guardedInitialLeftPair_physical
    (env : Nat -> In₁ × In₂) (n : Nat) :
    guardedInitialLeftPhysicalLetter A (pairPlay receiver sender env n) =
      initialLeftLetterAt (initialLeftLambdaOfGuardedPair A receiver sender)
        (omegaPrefix env n) (env n) := by
  simp [guardedInitialLeftPhysicalLetter, pairPlay, treePlay, treeOfPair,
    blockLabelApply, branchNode_eq_omegaPrefix,
    initialLeftLambdaOfGuardedPair, initialLeftLetterAt]

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
theorem guardedInitialLeftPair_source
    (env : Nat -> In₁ × In₂) (n : Nat) :
    (pairPlay receiver sender env n).2.1.2 =
      (receiver (omegaPrefix env n) (env n)).2 := by
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    branchNode_eq_omegaPrefix]

section
omit [Fintype Out₂]

theorem guardedInitialLeftBlockMonitor_run_shape
    (env : Nat -> In₁ × In₂) : ∀ n, ∃ safe : Bool,
    (guardedInitialLeftBlockMonitor A).run (pairPlay receiver sender env) n =
      ((initialLeftScanAfter A (initialLeftLambdaOfGuardedPair A receiver sender)
          (omegaPrefix env n),
        guardedInitialLeftPairPending A receiver env n), safe) := by
  classical
  intro n
  induction n with
  | zero => exact ⟨true, rfl⟩
  | succ n ih =>
      rcases ih with ⟨safe, ih⟩
      rw [BlockRecordMonitor.run, ih]
      refine ⟨((guardedInitialLeftBlockMonitor A).step
        ((initialLeftScanAfter A (initialLeftLambdaOfGuardedPair A receiver sender)
            (omegaPrefix env n),
          guardedInitialLeftPairPending A receiver env n), safe)
        (pairPlay receiver sender env n)).2, ?_⟩
      rw [omegaPrefix_succ, initialLeftScanAfter_append]
      simp only [guardedInitialLeftBlockMonitor]
      rw [guardedInitialLeftPair_physical A receiver sender env n,
        guardedInitialLeftPair_source A receiver sender env n]
      rfl

theorem guardedInitialLeftBlockMonitor_safe_false_persists
    (play : Nat -> RealizedBlockRound In₁ In₂
      (GuardedInitialLeftReceiverOutput A) Out₂)
    {N : Nat}
    (hfalse : ((guardedInitialLeftBlockMonitor A).run play N).2 = false) :
    ∀ n, N ≤ n ->
      ((guardedInitialLeftBlockMonitor A).run play n).2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [guardedInitialLeftBlockMonitor]
      change (((guardedInitialLeftBlockMonitor A).run play (N + k)).2 &&
        decide _ && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

/-- A winning guarded play can never enter the sticky rejecting state. -/
theorem guardedInitialLeft_safe_of_wins
    (play : Nat -> RealizedBlockRound In₁ In₂
      (GuardedInitialLeftReceiverOutput A) Out₂)
    (hwin : (guardedInitialLeftBlockMonitor A).WinsPlay play) (n : Nat) :
    ((guardedInitialLeftBlockMonitor A).run play n).2 = true := by
  by_contra hnot
  have hfalse : ((guardedInitialLeftBlockMonitor A).run play n).2 = false :=
    Bool.eq_false_of_not_eq_true hnot
  have hpersist := guardedInitialLeftBlockMonitor_safe_false_persists
    A play hfalse
  have heventual : ∀ k, n ≤ k ->
      (guardedInitialLeftBlockMonitor A).priority
        ((guardedInitialLeftBlockMonitor A).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change (if ((guardedInitialLeftBlockMonitor A).run play k).2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

/-- All three checks performed at one reachable initial-left round. -/
theorem guardedInitialLeft_stepConditions
    [Inhabited (In₁ × In₂)]
    (hmonitor : ∀ env : Nat -> In₁ × In₂,
      (guardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay receiver sender env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    let lambda := initialLeftLambdaOfGuardedPair A receiver sender
    let source := (receiver past move).2
    source.1 = initialLeftDelayedTarget A
        (initialLeftScanAfter A lambda past)
        (initialLeftLetterAt lambda past move) ∧
      (rightProfileGuardedAutomaton A source.1 source.2).HasRationalRun := by
  classical
  dsimp only
  let finiteWord := past ++ [move]
  let env : Nat -> In₁ × In₂ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix, finiteWord]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by
        simp [finiteWord]
        omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = move
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  rcases guardedInitialLeftBlockMonitor_run_shape A receiver sender env past.length with
    ⟨safe, hshape⟩
  have hsafeNext := guardedInitialLeft_safe_of_wins A
    (pairPlay receiver sender env) (hmonitor env) (past.length + 1)
  rw [BlockRecordMonitor.run, hshape] at hsafeNext
  simp only [guardedInitialLeftBlockMonitor] at hsafeNext
  rw [guardedInitialLeftPair_physical A receiver sender env past.length,
    guardedInitialLeftPair_source A receiver sender env past.length,
    hpast, hmove] at hsafeNext
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsafeNext
  exact ⟨hsafeNext.1.1.2, hsafeNext.1.2⟩

end

/-- Every emitted data pair can therefore be retyped as a feasible guarded
source at readback time. -/
noncomputable def guardedInitialLeftSourceAt
    [Inhabited (In₁ × In₂)]
    (hmonitor : ∀ env : Nat -> In₁ × In₂,
      (guardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay receiver sender env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    GuardedRightEntrySource A :=
  ⟨(receiver past move).2,
    (guardedInitialLeft_stepConditions A receiver sender hmonitor past move).2⟩

omit [Fintype Out₂] in
theorem guardedInitialLeftSourceAt_target
    [Inhabited (In₁ × In₂)]
    (hmonitor : ∀ env : Nat -> In₁ × In₂,
      (guardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay receiver sender env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    (guardedInitialLeftSourceAt A receiver sender hmonitor past move).1.1 =
      initialLeftDelayedTarget A
        (initialLeftScanAfter A (initialLeftLambdaOfGuardedPair A receiver sender) past)
        (initialLeftLetterAt (initialLeftLambdaOfGuardedPair A receiver sender)
          past move) :=
  (guardedInitialLeft_stepConditions A receiver sender hmonitor past move).1

omit [Fintype Out₂] in
/-- The typed source emitted at a boundary agrees with the complete overlap
table used by the old initial block at the following round. -/
theorem guardedInitialLeftSourceAt_profile
    [Inhabited (In₁ × In₂)]
    (hmonitor : ∀ env : Nat -> In₁ × In₂,
      (guardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay receiver sender env))
    (past : List (In₁ × In₂)) (move nextMove : In₁ × In₂) :
    (guardedInitialLeftSourceAt A receiver sender hmonitor past move).1.2
        (nextMove.2, nextMove.1) =
      (receiver (past ++ [move]) nextMove).1.informedOne := by
  classical
  let finiteWord := past ++ [move, nextMove]
  let env : Nat -> In₁ × In₂ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix, finiteWord]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by
        simp [finiteWord]
        omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = move
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  have hprefix : omegaPrefix env (past.length + 1) = past ++ [move] := by
    rw [omegaPrefix_succ, hpast, hmove]
  have hnext : env (past.length + 1) = nextMove := by
    have hnPrefix : past.length + 1 < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord (past.length + 1) = nextMove
    rw [omegaOfList_eq_getElem finiteWord (past.length + 1) hnPrefix]
    simp [finiteWord]
  let N := past.length + 1
  rcases guardedInitialLeftBlockMonitor_run_shape A receiver sender env N with
    ⟨safe, hshape⟩
  have hsafeNext := guardedInitialLeft_safe_of_wins A
    (pairPlay receiver sender env) (hmonitor env) (N + 1)
  rw [BlockRecordMonitor.run, hshape] at hsafeNext
  simp only [guardedInitialLeftBlockMonitor] at hsafeNext
  rw [guardedInitialLeftPair_physical A receiver sender env N,
    guardedInitialLeftPair_source A receiver sender env N,
    hprefix, hnext] at hsafeNext
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsafeNext
  have hoverlap := hsafeNext.2
  have hphysical := guardedInitialLeftPair_physical A receiver sender env N
  have hcurrentMove := congrArg (fun letter => letter.1) hphysical
  have hcurrentOut := congrArg (fun letter => letter.2.1.informedOne) hphysical
  have hcurrentMove' : (pairPlay receiver sender env N).1 = nextMove := by
    simpa [N, guardedInitialLeftPhysicalLetter, initialLeftLetterAt,
      hprefix, hnext] using hcurrentMove
  have hcurrentOut' :
      (pairPlay receiver sender env N).2.1.1.informedOne =
        (receiver (past ++ [move]) nextMove).1.informedOne := by
    simpa [N, guardedInitialLeftPhysicalLetter, initialLeftLetterAt,
      initialLeftLambdaOfGuardedPair, hpast, hmove, hnext] using hcurrentOut
  simpa [guardedInitialLeftSourceAt, N, guardedInitialLeftPairPending,
    guardedInitialLeftOverlapOK, hpast, hmove, hcurrentMove', hcurrentOut'] using hoverlap

end Left

section Right

variable
  (receiver : ReceiverBlockStrategy In₂ In₁ (GuardedInitialRightReceiverOutput A))
  (sender : SenderBlockStrategy In₁ Out₁)

/-- Physical initial-right lambda obtained by erasing the guarded source. -/
def initialRightLambdaOfGuardedPair : InitialRightLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) where
  blindOne := sender
  informedTwo := fun past move => (receiver past move).1.informedTwo
  reversingOne := fun past move => (receiver past move).1.reversingOne
  reversingTwo := fun past move => (receiver past move).1.reversingTwo

noncomputable def guardedInitialRightPairPending
    (env : Nat -> In₂ × In₁) : Nat -> Option (GuardedLeftEntryData A)
  | 0 => none
  | n + 1 => some (receiver (omegaPrefix env n) (env n)).2

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
theorem guardedInitialRightPair_physical
    (env : Nat -> In₂ × In₁) (n : Nat) :
    guardedInitialRightPhysicalLetter A (pairPlay receiver sender env n) =
      initialRightLetterAt (initialRightLambdaOfGuardedPair A receiver sender)
        (omegaPrefix env n) (env n) := by
  simp [guardedInitialRightPhysicalLetter, pairPlay, treePlay, treeOfPair,
    blockLabelApply, branchNode_eq_omegaPrefix,
    initialRightLambdaOfGuardedPair, initialRightLetterAt]

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
theorem guardedInitialRightPair_source
    (env : Nat -> In₂ × In₁) (n : Nat) :
    (pairPlay receiver sender env n).2.1.2 =
      (receiver (omegaPrefix env n) (env n)).2 := by
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    branchNode_eq_omegaPrefix]

section
omit [Fintype Out₁]

theorem guardedInitialRightBlockMonitor_run_shape
    (env : Nat -> In₂ × In₁) : ∀ n, ∃ safe : Bool,
    (guardedInitialRightBlockMonitor A).run (pairPlay receiver sender env) n =
      ((initialRightScanAfter A (initialRightLambdaOfGuardedPair A receiver sender)
          (omegaPrefix env n),
        guardedInitialRightPairPending A receiver env n), safe) := by
  classical
  intro n
  induction n with
  | zero => exact ⟨true, rfl⟩
  | succ n ih =>
      rcases ih with ⟨safe, ih⟩
      rw [BlockRecordMonitor.run, ih]
      refine ⟨((guardedInitialRightBlockMonitor A).step
        ((initialRightScanAfter A (initialRightLambdaOfGuardedPair A receiver sender)
            (omegaPrefix env n),
          guardedInitialRightPairPending A receiver env n), safe)
        (pairPlay receiver sender env n)).2, ?_⟩
      rw [omegaPrefix_succ, initialRightScanAfter_append]
      simp only [guardedInitialRightBlockMonitor]
      rw [guardedInitialRightPair_physical A receiver sender env n,
        guardedInitialRightPair_source A receiver sender env n]
      rfl

theorem guardedInitialRightBlockMonitor_safe_false_persists
    (play : Nat -> RealizedBlockRound In₂ In₁
      (GuardedInitialRightReceiverOutput A) Out₁)
    {N : Nat}
    (hfalse : ((guardedInitialRightBlockMonitor A).run play N).2 = false) :
    ∀ n, N ≤ n ->
      ((guardedInitialRightBlockMonitor A).run play n).2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [guardedInitialRightBlockMonitor]
      change (((guardedInitialRightBlockMonitor A).run play (N + k)).2 &&
        decide _ && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

/-- A winning right-guarded play can never enter the sticky rejecting state. -/
theorem guardedInitialRight_safe_of_wins
    (play : Nat -> RealizedBlockRound In₂ In₁
      (GuardedInitialRightReceiverOutput A) Out₁)
    (hwin : (guardedInitialRightBlockMonitor A).WinsPlay play) (n : Nat) :
    ((guardedInitialRightBlockMonitor A).run play n).2 = true := by
  by_contra hnot
  have hfalse : ((guardedInitialRightBlockMonitor A).run play n).2 = false :=
    Bool.eq_false_of_not_eq_true hnot
  have hpersist := guardedInitialRightBlockMonitor_safe_false_persists
    A play hfalse
  have heventual : ∀ k, n ≤ k ->
      (guardedInitialRightBlockMonitor A).priority
        ((guardedInitialRightBlockMonitor A).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change (if ((guardedInitialRightBlockMonitor A).run play k).2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

/-- All three checks performed at one reachable initial-right round. -/
theorem guardedInitialRight_stepConditions
    [Inhabited (In₂ × In₁)]
    (hmonitor : ∀ env : Nat -> In₂ × In₁,
      (guardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay receiver sender env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    let lambda := initialRightLambdaOfGuardedPair A receiver sender
    let source := (receiver past move).2
    source.1 = initialRightDelayedTarget A
        (initialRightScanAfter A lambda past)
        (initialRightLetterAt lambda past move) ∧
      (leftProfileGuardedAutomaton A source.1 source.2).HasRationalRun := by
  classical
  dsimp only
  let finiteWord := past ++ [move]
  let env : Nat -> In₂ × In₁ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix, finiteWord]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by
        simp [finiteWord]
        omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = move
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  rcases guardedInitialRightBlockMonitor_run_shape A receiver sender env past.length with
    ⟨safe, hshape⟩
  have hsafeNext := guardedInitialRight_safe_of_wins A
    (pairPlay receiver sender env) (hmonitor env) (past.length + 1)
  rw [BlockRecordMonitor.run, hshape] at hsafeNext
  simp only [guardedInitialRightBlockMonitor] at hsafeNext
  rw [guardedInitialRightPair_physical A receiver sender env past.length,
    guardedInitialRightPair_source A receiver sender env past.length,
    hpast, hmove] at hsafeNext
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsafeNext
  exact ⟨hsafeNext.1.1.2, hsafeNext.1.2⟩

end

/-- Every emitted right-block data pair can be retyped as a feasible guarded
source at readback time. -/
noncomputable def guardedInitialRightSourceAt
    [Inhabited (In₂ × In₁)]
    (hmonitor : ∀ env : Nat -> In₂ × In₁,
      (guardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay receiver sender env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    GuardedLeftEntrySource A :=
  ⟨(receiver past move).2,
    (guardedInitialRight_stepConditions A receiver sender hmonitor past move).2⟩

omit [Fintype Out₁] in
theorem guardedInitialRightSourceAt_target
    [Inhabited (In₂ × In₁)]
    (hmonitor : ∀ env : Nat -> In₂ × In₁,
      (guardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay receiver sender env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    (guardedInitialRightSourceAt A receiver sender hmonitor past move).1.1 =
      initialRightDelayedTarget A
        (initialRightScanAfter A (initialRightLambdaOfGuardedPair A receiver sender) past)
        (initialRightLetterAt (initialRightLambdaOfGuardedPair A receiver sender)
          past move) :=
  (guardedInitialRight_stepConditions A receiver sender hmonitor past move).1

omit [Fintype Out₁] in
/-- The typed source emitted at a right boundary agrees with the complete
overlap table used by the old initial block at the following round. -/
theorem guardedInitialRightSourceAt_profile
    [Inhabited (In₂ × In₁)]
    (hmonitor : ∀ env : Nat -> In₂ × In₁,
      (guardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay receiver sender env))
    (past : List (In₂ × In₁)) (move nextMove : In₂ × In₁) :
    (guardedInitialRightSourceAt A receiver sender hmonitor past move).1.2
        (nextMove.2, nextMove.1) =
      (receiver (past ++ [move]) nextMove).1.informedTwo := by
  classical
  let finiteWord := past ++ [move, nextMove]
  let env : Nat -> In₂ × In₁ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix, finiteWord]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by
        simp [finiteWord]
        omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = move
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  have hprefix : omegaPrefix env (past.length + 1) = past ++ [move] := by
    rw [omegaPrefix_succ, hpast, hmove]
  have hnext : env (past.length + 1) = nextMove := by
    have hnPrefix : past.length + 1 < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord (past.length + 1) = nextMove
    rw [omegaOfList_eq_getElem finiteWord (past.length + 1) hnPrefix]
    simp [finiteWord]
  let N := past.length + 1
  rcases guardedInitialRightBlockMonitor_run_shape A receiver sender env N with
    ⟨safe, hshape⟩
  have hsafeNext := guardedInitialRight_safe_of_wins A
    (pairPlay receiver sender env) (hmonitor env) (N + 1)
  rw [BlockRecordMonitor.run, hshape] at hsafeNext
  simp only [guardedInitialRightBlockMonitor] at hsafeNext
  rw [guardedInitialRightPair_physical A receiver sender env N,
    guardedInitialRightPair_source A receiver sender env N,
    hprefix, hnext] at hsafeNext
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsafeNext
  have hoverlap := hsafeNext.2
  have hphysical := guardedInitialRightPair_physical A receiver sender env N
  have hcurrentMove := congrArg (fun letter => letter.1) hphysical
  have hcurrentOut := congrArg (fun letter => letter.2.1.informedTwo) hphysical
  have hcurrentMove' : (pairPlay receiver sender env N).1 = nextMove := by
    simpa [N, guardedInitialRightPhysicalLetter, initialRightLetterAt,
      hprefix, hnext] using hcurrentMove
  have hcurrentOut' :
      (pairPlay receiver sender env N).2.1.1.informedTwo =
        (receiver (past ++ [move]) nextMove).1.informedTwo := by
    simpa [N, guardedInitialRightPhysicalLetter, initialRightLetterAt,
      initialRightLambdaOfGuardedPair, hpast, hmove, hnext] using hcurrentOut
  simpa [guardedInitialRightSourceAt, N, guardedInitialRightPairPending,
    guardedInitialRightOverlapOK, hpast, hmove, hcurrentMove', hcurrentOut'] using hoverlap

end Right

end DetParityAutomaton

end DistributedSynthesis
