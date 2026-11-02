/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointInitialBlockHandoff
import DistributedSynthesis.Formalizations.Lemma.LemLocallyConsistentSenderNarrowing

/-!
# Finite guarded raw-joint keys at the initial seam

The Unit raw-joint code at an initial boundary does not by itself remember
the other output table needed on an ambiguous immediate `both` close.  The
finite handoff key therefore consists of

* the exact Unit incidence code of one literal initial boundary, and
* the existing process-one/process-two overlap profile at that boundary.

This is finite boundary compatibility, not a strict-leader observation.  An
initial-left controller always carries the right-oriented key and the mirror
controller always carries the left-oriented key; no row or side bit is
revealed to either process.

The monitor is deliberately installed *before* initial-block narrowing.
Post-composing the older end-to-end initial package would be unsound: its
rationalized initial lambda need not be the original strategy lambda from
which semantic raw-joint provenance is obtained.
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

/-! ## Finite guarded boundary keys -/

/-- A finite process-one/right key known to represent one genuine boundary
of the original initial-left block. -/
abbrev ProfiledRawJointInitialLeftGuardedKey
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :=
  { data : ProfiledRawJointIncidenceCode A (I := Unit) ×
      ProcOneEntryOverlapProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) //
    ∃ past : List (In₁ × In₂), ∃ move : In₁ × In₂,
      data =
        ((profiledRawJointInitialLeftBoundaryState A strategy past move).code A,
          initialLeftNextBothProfile strategy past move) }

/-- Process-two/left mirror. -/
abbrev ProfiledRawJointInitialRightGuardedKey
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :=
  { data : ProfiledRawJointIncidenceCode A (I := Unit) ×
      ProcTwoEntryOverlapProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂) //
    ∃ past : List (In₂ × In₁), ∃ move : In₂ × In₁,
      data =
        ((profiledRawJointInitialRightBoundaryState A strategy past move).code A,
          initialRightNextBothProfile strategy past move) }

noncomputable instance
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    Fintype (ProfiledRawJointInitialLeftGuardedKey A strategy) := by
  classical
  infer_instance

noncomputable instance
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    Fintype (ProfiledRawJointInitialRightGuardedKey A strategy) := by
  classical
  infer_instance

/-- Literal key staged by the original strategy after one possible final
initial-left round. -/
def profiledRawJointInitialLeftGuardedKeyAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ProfiledRawJointInitialLeftGuardedKey A strategy :=
  ⟨((profiledRawJointInitialLeftBoundaryState A strategy past move).code A,
      initialLeftNextBothProfile strategy past move),
    past, move, rfl⟩

/-- Literal mirror key. -/
def profiledRawJointInitialRightGuardedKeyAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ProfiledRawJointInitialRightGuardedKey A strategy :=
  ⟨((profiledRawJointInitialRightBoundaryState A strategy past move).code A,
      initialRightNextBothProfile strategy past move),
    past, move, rfl⟩

noncomputable instance
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    Inhabited (ProfiledRawJointInitialLeftGuardedKey A strategy) :=
  ⟨profiledRawJointInitialLeftGuardedKeyAt A strategy [] (default, default)⟩

noncomputable instance
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    Inhabited (ProfiledRawJointInitialRightGuardedKey A strategy) :=
  ⟨profiledRawJointInitialRightGuardedKeyAt A strategy [] (default, default)⟩

/-! ## Exact target and one-round compatibility -/

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

/-- The literal left key projects to the exact delayed source expected by
the old initial scanner. -/
theorem profiledRawJointInitialLeftGuardedKeyAt_target
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A
          (profiledRawJointInitialLeftGuardedKeyAt A strategy past move).1.1) =
      initialLeftDelayedTarget A
        (initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy) past)
        (initialLeftLetterAt (initialLeftLambdaOfStrategy strategy) past move) := by
  rw [show (profiledRawJointInitialLeftGuardedKeyAt A strategy past move).1.1 =
      (profiledRawJointInitialLeftBoundaryState A strategy past move).code A
    from rfl]
  rw [profiledRawJointInitialLeftBoundaryState_projection A strategy past move,
    initialLeftProfiledTarget, PairedStrategyMemory.erase_toProfiledTreeState]
  exact (initialLeftDelayedTarget_lambdaOfStrategy A strategy past move).symm

/-- Mirror exact delayed target. -/
theorem profiledRawJointInitialRightGuardedKeyAt_target
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A
          (profiledRawJointInitialRightGuardedKeyAt A strategy past move).1.1) =
      initialRightDelayedTarget A
        (initialRightScanAfter A (initialRightLambdaOfStrategy strategy) past)
        (initialRightLetterAt (initialRightLambdaOfStrategy strategy) past move) := by
  rw [show (profiledRawJointInitialRightGuardedKeyAt A strategy past move).1.1 =
      (profiledRawJointInitialRightBoundaryState A strategy past move).code A
    from rfl]
  rw [profiledRawJointInitialRightBoundaryState_projection A strategy past move,
    initialRightProfiledTarget, PairedStrategyMemory.erase_toProfiledTreeState]
  exact (initialRightDelayedTarget_lambdaOfStrategy A strategy past move).symm

/-- The two finite tables of a staged initial-left key agree with the next
literal initial-left receiver output. -/
theorem profiledRawJointInitialLeftGuardedKeyAt_next_profile
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₁ × In₂)) (move nextMove : In₁ × In₂) :
    let key := profiledRawJointInitialLeftGuardedKeyAt A strategy past move
    let next := initialLeftLetterAt (initialLeftLambdaOfStrategy strategy)
      (past ++ [move]) nextMove
    ∃ profile,
      rightProfileOfProfiledState A
          (profiledRawJointUnitLeftTargetProjection A key.1.1) = some profile ∧
        profile (nextMove.2, nextMove.1) = next.2.1.reversingTwo := by
  dsimp only
  refine ⟨rightInitialFirstProfile
      (profiledRawJointInitialLeftBoundaryWorld A strategy past move
        |>.procOne A).lambdaOfStrategy, ?_, ?_⟩
  rw [show (profiledRawJointInitialLeftGuardedKeyAt A strategy past move).1.1 =
      (profiledRawJointInitialLeftBoundaryState A strategy past move).code A
    from rfl,
    profiledRawJointInitialLeftBoundaryState_projection A strategy past move]
  · rfl
  · simp [rightInitialFirstProfile, ProcOnePairedEntryRep.lambdaOfStrategy,
      ProfiledRawJointCommonBaseWorld.procOne,
      profiledRawJointInitialLeftBoundaryWorld, procOneFreshPair,
      initialLeftLetterAt, initialLeftLambdaOfStrategy,
      blockReceiverTwo, leftEnvironment, List.map_append, extendPrefix_snoc]

/-- Mirror pair of next-round compatibility laws. -/
theorem profiledRawJointInitialRightGuardedKeyAt_next_compatible
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₂ × In₁)) (move nextMove : In₂ × In₁) :
    let key := profiledRawJointInitialRightGuardedKeyAt A strategy past move
    let next := initialRightLetterAt (initialRightLambdaOfStrategy strategy)
      (past ++ [move]) nextMove
    key.1.2 (nextMove.2, nextMove.1) = next.2.1.informedTwo ∧
      ∃ profile,
        leftProfileOfProfiledState A
            (profiledRawJointUnitRightTargetProjection A key.1.1) = some profile ∧
          profile (nextMove.2, nextMove.1) = next.2.1.reversingOne := by
  dsimp only
  constructor
  · rfl
  · refine ⟨leftInitialFirstProfile
        (profiledRawJointInitialRightBoundaryWorld A strategy past move
          |>.procTwo A).lambdaOfStrategy, ?_, ?_⟩
    rw [show (profiledRawJointInitialRightGuardedKeyAt A strategy past move).1.1 =
        (profiledRawJointInitialRightBoundaryState A strategy past move).code A
      from rfl,
      profiledRawJointInitialRightBoundaryState_projection A strategy past move]
    · rfl
    · simp [leftInitialFirstProfile, ProcTwoPairedEntryRep.lambdaOfStrategy,
        ProfiledRawJointCommonBaseWorld.procTwo,
        profiledRawJointInitialRightBoundaryWorld, procTwoFreshPair,
        initialRightLetterAt, initialRightLambdaOfStrategy,
        blockReceiverOne, rightEnvironment, List.map_append, extendPrefix_snoc]

end

/-! ## Enriched initial receiver outputs and monitors -/

abbrev ProfiledRawJointInitialLeftReceiverOutput
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :=
  InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂) ×
    ProfiledRawJointInitialLeftGuardedKey A strategy

abbrev ProfiledRawJointInitialRightReceiverOutput
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :=
  InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂) ×
    ProfiledRawJointInitialRightGuardedKey A strategy

def profiledRawJointInitialLeftPhysicalLetter
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (letter : RealizedBlockRound In₁ In₂
      (ProfiledRawJointInitialLeftReceiverOutput A strategy) Out₂) :
    InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  (letter.1, letter.2.1.1, letter.2.2)

def profiledRawJointInitialRightPhysicalLetter
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (letter : RealizedBlockRound In₂ In₁
      (ProfiledRawJointInitialRightReceiverOutput A strategy) Out₁) :
    InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  (letter.1, letter.2.1.1, letter.2.2)

def profiledRawJointInitialLeftPendingOK
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (pending : Option (ProfiledRawJointInitialLeftGuardedKey A strategy))
    (letter : RealizedBlockRound In₁ In₂
      (ProfiledRawJointInitialLeftReceiverOutput A strategy) Out₂) : Prop :=
  match pending with
  | none => True
  | some key =>
      key.1.2 (letter.1.2, letter.1.1) = letter.2.1.1.informedOne ∧
        ∃ profile,
          rightProfileOfProfiledState A
              (profiledRawJointUnitLeftTargetProjection A key.1.1) =
            some profile ∧
          profile (letter.1.2, letter.1.1) = letter.2.1.1.reversingTwo

def profiledRawJointInitialRightPendingOK
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (pending : Option (ProfiledRawJointInitialRightGuardedKey A strategy))
    (letter : RealizedBlockRound In₂ In₁
      (ProfiledRawJointInitialRightReceiverOutput A strategy) Out₁) : Prop :=
  match pending with
  | none => True
  | some key =>
      key.1.2 (letter.1.2, letter.1.1) = letter.2.1.1.informedTwo ∧
        ∃ profile,
          leftProfileOfProfiledState A
              (profiledRawJointUnitRightTargetProjection A key.1.1) =
            some profile ∧
          profile (letter.1.2, letter.1.1) = letter.2.1.1.reversingOne

/-- Initial-left monitor with exact finite guarded raw-joint staging. -/
noncomputable def profiledRawJointInitialLeftBlockMonitor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    BlockRecordMonitor In₁ In₂
      (ProfiledRawJointInitialLeftReceiverOutput A strategy) Out₂ := by
  classical
  exact {
    State := (InitialBlockScan A ×
      Option (ProfiledRawJointInitialLeftGuardedKey A strategy)) × Bool
    stateFinite := inferInstance
    initial := (((A.initial, A.initial), none), true)
    step := fun state letter =>
      let physical := profiledRawJointInitialLeftPhysicalLetter A letter
      let key := letter.2.1.2
      let targetOK := erasePairedProfiledState A
          (profiledRawJointUnitLeftTargetProjection A key.1.1) =
        initialLeftDelayedTarget A state.1.1 physical
      let pendingOK := profiledRawJointInitialLeftPendingOK A state.1.2 letter
      ((initialLeftScanStep A state.1.1 physical, some key),
        state.2 && decide targetOK && decide pendingOK)
    priority := fun state => if state.2 then A.priority state.1.1.1 + 2 else 1
  }

/-- Initial-right mirror monitor. -/
noncomputable def profiledRawJointInitialRightBlockMonitor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    BlockRecordMonitor In₂ In₁
      (ProfiledRawJointInitialRightReceiverOutput A strategy) Out₁ := by
  classical
  exact {
    State := (InitialBlockScan A ×
      Option (ProfiledRawJointInitialRightGuardedKey A strategy)) × Bool
    stateFinite := inferInstance
    initial := (((A.initial, A.initial), none), true)
    step := fun state letter =>
      let physical := profiledRawJointInitialRightPhysicalLetter A letter
      let key := letter.2.1.2
      let targetOK := erasePairedProfiledState A
          (profiledRawJointUnitRightTargetProjection A key.1.1) =
        initialRightDelayedTarget A state.1.1 physical
      let pendingOK := profiledRawJointInitialRightPendingOK A state.1.2 letter
      ((initialRightScanStep A state.1.1 physical, some key),
        state.2 && decide targetOK && decide pendingOK)
    priority := fun state => if state.2 then A.priority state.1.1.1 + 2 else 1
  }

/-! ## Literal realization -/

def profiledRawJointInitialLeftReceiverStrategy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    ReceiverBlockStrategy In₁ In₂
      (ProfiledRawJointInitialLeftReceiverOutput A strategy) :=
  fun past move =>
    (initialLeftReceiverStrategy (initialLeftLambdaOfStrategy strategy) past move,
      profiledRawJointInitialLeftGuardedKeyAt A strategy past move)

def profiledRawJointInitialRightReceiverStrategy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    ReceiverBlockStrategy In₂ In₁
      (ProfiledRawJointInitialRightReceiverOutput A strategy) :=
  fun past move =>
    (initialRightReceiverStrategy (initialRightLambdaOfStrategy strategy) past move,
      profiledRawJointInitialRightGuardedKeyAt A strategy past move)

def profiledRawJointInitialLeftPending
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : Nat → In₁ × In₂) : Nat →
      Option (ProfiledRawJointInitialLeftGuardedKey A strategy)
  | 0 => none
  | n + 1 => some (profiledRawJointInitialLeftGuardedKeyAt A strategy
      (omegaPrefix env n) (env n))

def profiledRawJointInitialRightPending
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : Nat → In₂ × In₁) : Nat →
      Option (ProfiledRawJointInitialRightGuardedKey A strategy)
  | 0 => none
  | n + 1 => some (profiledRawJointInitialRightGuardedKeyAt A strategy
      (omegaPrefix env n) (env n))

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

theorem profiledRawJointInitialLeft_pairPlay_physical
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointInitialLeftPhysicalLetter A
        (pairPlay (profiledRawJointInitialLeftReceiverStrategy A strategy)
          (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
          env n) =
      initialLeftLetterAt (initialLeftLambdaOfStrategy strategy)
        (omegaPrefix env n) (env n) := by
  simp [profiledRawJointInitialLeftPhysicalLetter, pairPlay, treePlay,
    treeOfPair, blockLabelApply, branchNode_eq_omegaPrefix,
    profiledRawJointInitialLeftReceiverStrategy,
    initialLeftReceiverStrategy, initialLeftSenderStrategy,
    initialLeftLetterAt, senderWord]

theorem profiledRawJointInitialRight_pairPlay_physical
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : Nat → In₂ × In₁) (n : Nat) :
    profiledRawJointInitialRightPhysicalLetter A
        (pairPlay (profiledRawJointInitialRightReceiverStrategy A strategy)
          (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
          env n) =
      initialRightLetterAt (initialRightLambdaOfStrategy strategy)
        (omegaPrefix env n) (env n) := by
  simp [profiledRawJointInitialRightPhysicalLetter, pairPlay, treePlay,
    treeOfPair, blockLabelApply, branchNode_eq_omegaPrefix,
    profiledRawJointInitialRightReceiverStrategy,
    initialRightReceiverStrategy, initialRightSenderStrategy,
    initialRightLetterAt, senderWord]

theorem profiledRawJointInitialLeft_pairPlay_key
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : Nat → In₁ × In₂) (n : Nat) :
    (pairPlay (profiledRawJointInitialLeftReceiverStrategy A strategy)
      (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
      env n).2.1.2 =
        profiledRawJointInitialLeftGuardedKeyAt A strategy
          (omegaPrefix env n) (env n) := by
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    branchNode_eq_omegaPrefix,
    profiledRawJointInitialLeftReceiverStrategy]

theorem profiledRawJointInitialRight_pairPlay_key
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : Nat → In₂ × In₁) (n : Nat) :
    (pairPlay (profiledRawJointInitialRightReceiverStrategy A strategy)
      (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
      env n).2.1.2 =
        profiledRawJointInitialRightGuardedKeyAt A strategy
          (omegaPrefix env n) (env n) := by
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    branchNode_eq_omegaPrefix,
    profiledRawJointInitialRightReceiverStrategy]

end

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointInitialLeft_pendingOK
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointInitialLeftPendingOK A
      (profiledRawJointInitialLeftPending A strategy env n)
      (pairPlay (profiledRawJointInitialLeftReceiverStrategy A strategy)
        (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
        env n) := by
  cases n with
  | zero => trivial
  | succ n =>
      have hcompat :
        (profiledRawJointInitialLeftGuardedKeyAt A strategy
            (omegaPrefix env n) (env n)).1.2
              ((env (n + 1)).2, (env (n + 1)).1) =
            (initialLeftLetterAt (initialLeftLambdaOfStrategy strategy)
              (omegaPrefix env (n + 1)) (env (n + 1))).2.1.informedOne ∧
          ∃ profile,
            rightProfileOfProfiledState A
                (profiledRawJointUnitLeftTargetProjection A
                  (profiledRawJointInitialLeftGuardedKeyAt A strategy
                    (omegaPrefix env n) (env n)).1.1) = some profile ∧
              profile ((env (n + 1)).2, (env (n + 1)).1) =
                (initialLeftLetterAt (initialLeftLambdaOfStrategy strategy)
                  (omegaPrefix env (n + 1))
                  (env (n + 1))).2.1.reversingTwo := by
        rw [omegaPrefix_succ]
        exact ⟨rfl,
        profiledRawJointInitialLeftGuardedKeyAt_next_profile A strategy
            (omegaPrefix env n) (env n) (env (n + 1))⟩
      simpa [profiledRawJointInitialLeftPending,
        profiledRawJointInitialLeftPendingOK, pairPlay, treePlay, treeOfPair,
        blockLabelApply, branchNode_eq_omegaPrefix,
        profiledRawJointInitialLeftReceiverStrategy] using hcompat

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointInitialRight_pendingOK
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : Nat → In₂ × In₁) (n : Nat) :
    profiledRawJointInitialRightPendingOK A
      (profiledRawJointInitialRightPending A strategy env n)
      (pairPlay (profiledRawJointInitialRightReceiverStrategy A strategy)
        (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
        env n) := by
  cases n with
  | zero => trivial
  | succ n =>
      have hcompat :
        (profiledRawJointInitialRightGuardedKeyAt A strategy
            (omegaPrefix env n) (env n)).1.2
              ((env (n + 1)).2, (env (n + 1)).1) =
            (initialRightLetterAt (initialRightLambdaOfStrategy strategy)
              (omegaPrefix env (n + 1)) (env (n + 1))).2.1.informedTwo ∧
          ∃ profile,
            leftProfileOfProfiledState A
                (profiledRawJointUnitRightTargetProjection A
                  (profiledRawJointInitialRightGuardedKeyAt A strategy
                    (omegaPrefix env n) (env n)).1.1) = some profile ∧
              profile ((env (n + 1)).2, (env (n + 1)).1) =
                (initialRightLetterAt (initialRightLambdaOfStrategy strategy)
                  (omegaPrefix env (n + 1))
                  (env (n + 1))).2.1.reversingOne := by
        rw [omegaPrefix_succ]
        exact profiledRawJointInitialRightGuardedKeyAt_next_compatible A strategy
          (omegaPrefix env n) (env n) (env (n + 1))
      simpa [profiledRawJointInitialRightPending,
        profiledRawJointInitialRightPendingOK, pairPlay, treePlay, treeOfPair,
        blockLabelApply, branchNode_eq_omegaPrefix,
        profiledRawJointInitialRightReceiverStrategy] using hcompat

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Along the original initial-left strategy, the enriched monitor retains
the exact scan, the preceding literal guarded key, and a true sticky bit. -/
theorem profiledRawJointInitialLeftBlockMonitor_run_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : Nat → In₁ × In₂) : ∀ n,
    (profiledRawJointInitialLeftBlockMonitor A strategy).run
        (pairPlay (profiledRawJointInitialLeftReceiverStrategy A strategy)
          (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
          env) n =
      ((initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy)
          (omegaPrefix env n),
        profiledRawJointInitialLeftPending A strategy env n), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih]
      simp only [profiledRawJointInitialLeftBlockMonitor]
      rw [profiledRawJointInitialLeft_pairPlay_physical A strategy env n,
        profiledRawJointInitialLeft_pairPlay_key A strategy env n]
      have htarget := profiledRawJointInitialLeftGuardedKeyAt_target A strategy
        (omegaPrefix env n) (env n)
      have hpending := profiledRawJointInitialLeft_pendingOK A strategy env n
      change
        ((initialLeftScanStep A
            (initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy)
              (omegaPrefix env n))
            (initialLeftLetterAt (initialLeftLambdaOfStrategy strategy)
              (omegaPrefix env n) (env n)),
          some (profiledRawJointInitialLeftGuardedKeyAt A strategy
            (omegaPrefix env n) (env n))),
          true && decide _ && decide _) = _
      rw [decide_eq_true htarget, decide_eq_true hpending]
      simp only [Bool.true_and]
      rw [omegaPrefix_succ, initialLeftScanAfter_append]
      rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Initial-right run mirror. -/
theorem profiledRawJointInitialRightBlockMonitor_run_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : Nat → In₂ × In₁) : ∀ n,
    (profiledRawJointInitialRightBlockMonitor A strategy).run
        (pairPlay (profiledRawJointInitialRightReceiverStrategy A strategy)
          (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
          env) n =
      ((initialRightScanAfter A (initialRightLambdaOfStrategy strategy)
          (omegaPrefix env n),
        profiledRawJointInitialRightPending A strategy env n), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih]
      simp only [profiledRawJointInitialRightBlockMonitor]
      rw [profiledRawJointInitialRight_pairPlay_physical A strategy env n,
        profiledRawJointInitialRight_pairPlay_key A strategy env n]
      have htarget := profiledRawJointInitialRightGuardedKeyAt_target A strategy
        (omegaPrefix env n) (env n)
      have hpending := profiledRawJointInitialRight_pendingOK A strategy env n
      change
        ((initialRightScanStep A
            (initialRightScanAfter A (initialRightLambdaOfStrategy strategy)
              (omegaPrefix env n))
            (initialRightLetterAt (initialRightLambdaOfStrategy strategy)
              (omegaPrefix env n) (env n)),
          some (profiledRawJointInitialRightGuardedKeyAt A strategy
            (omegaPrefix env n) (env n))),
          true && decide _ && decide _) = _
      rw [decide_eq_true htarget, decide_eq_true hpending]
      simp only [Bool.true_and]
      rw [omegaPrefix_succ, initialRightScanAfter_append]
      rfl

/-! ## Parity realizability and unconditional finite narrowing -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointInitialLeftBlockMonitor_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (env : Nat → In₁ × In₂) :
    (profiledRawJointInitialLeftBlockMonitor A strategy).WinsPlay
      (pairPlay (profiledRawJointInitialLeftReceiverStrategy A strategy)
        (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
        env) := by
  unfold BlockRecordMonitor.WinsPlay
  have hforever := initialLeftForeverAccepts_lambdaOfStrategy A strategy hwin env
  have hparity : NatSeqMinEvenParity
      (fun n => A.priority
        (A.run (initialLeftOmegaWord
          (initialLeftLambdaOfStrategy strategy) env) n) + 2) :=
    (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hforever
  convert hparity using 1
  funext n
  rw [profiledRawJointInitialLeftBlockMonitor_run_eq A strategy env n]
  simp only [profiledRawJointInitialLeftBlockMonitor, if_pos, Bool.true_eq]
  congr 2
  have hscan :
      (initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy)
        (omegaPrefix env n)).1 =
        A.run (initialLeftOmegaWord (initialLeftLambdaOfStrategy strategy) env)
          n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [omegaPrefix_succ, initialLeftScanAfter_append]
        simp only [initialLeftScanStep, initialBlockScanStep]
        rw [ih]
        rfl
  exact hscan

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointInitialRightBlockMonitor_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (env : Nat → In₂ × In₁) :
    (profiledRawJointInitialRightBlockMonitor A strategy).WinsPlay
      (pairPlay (profiledRawJointInitialRightReceiverStrategy A strategy)
        (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
        env) := by
  unfold BlockRecordMonitor.WinsPlay
  have hforever := initialRightForeverAccepts_lambdaOfStrategy A strategy hwin env
  have hparity : NatSeqMinEvenParity
      (fun n => A.priority
        (A.run (initialRightOmegaWord
          (initialRightLambdaOfStrategy strategy) env) n) + 2) :=
    (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hforever
  convert hparity using 1
  funext n
  rw [profiledRawJointInitialRightBlockMonitor_run_eq A strategy env n]
  simp only [profiledRawJointInitialRightBlockMonitor, if_pos, Bool.true_eq]
  congr 2
  have hscan :
      (initialRightScanAfter A (initialRightLambdaOfStrategy strategy)
        (omegaPrefix env n)).1 =
        A.run (initialRightOmegaWord (initialRightLambdaOfStrategy strategy) env)
          n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [omegaPrefix_succ, initialRightScanAfter_append]
        simp only [initialRightScanStep, initialBlockScanStep]
        rw [ih]
        rfl
  exact hscan

/-- The exact guarded initial-left seam admits a finite controller directly
from the original winner; no recurrent-policy basis is assumed. -/
theorem exists_finite_profiledRawJointInitialLeftController_of_winning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    ∃ controller : TransitionRationalTree.{v, max u v x y s, max u v x y s}
      In₂ (NarrowedBlockLabel In₁ In₂
        (ProfiledRawJointInitialLeftReceiverOutput A strategy) Out₂
        (profiledRawJointInitialLeftBlockMonitor A strategy).State),
      NarrowedAllThreadsWin (profiledRawJointInitialLeftBlockMonitor A strategy)
        controller.labeledTree := by
  classical
  apply (block_realizable_iff_implementable_controller_unconditional
    (profiledRawJointInitialLeftBlockMonitor A strategy)).mp
  exact ⟨profiledRawJointInitialLeftReceiverStrategy A strategy,
    initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy),
    profiledRawJointInitialLeftBlockMonitor_wins A strategy hwin⟩

/-- Symmetric unconditional finite initial-right controller. -/
theorem exists_finite_profiledRawJointInitialRightController_of_winning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    ∃ controller : TransitionRationalTree.{u, max u v x y s, max u v x y s}
      In₁ (NarrowedBlockLabel In₂ In₁
        (ProfiledRawJointInitialRightReceiverOutput A strategy) Out₁
        (profiledRawJointInitialRightBlockMonitor A strategy).State),
      NarrowedAllThreadsWin (profiledRawJointInitialRightBlockMonitor A strategy)
        controller.labeledTree := by
  classical
  apply (block_realizable_iff_implementable_controller_unconditional
    (profiledRawJointInitialRightBlockMonitor A strategy)).mp
  exact ⟨profiledRawJointInitialRightReceiverStrategy A strategy,
    initialRightSenderStrategy (initialRightLambdaOfStrategy strategy),
    profiledRawJointInitialRightBlockMonitor_wins A strategy hwin⟩

/-! ## Certified-close inversion for arbitrary narrowed plays -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem profiledRawJointInitialLeft_safe_false_persists
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointInitialLeftReceiverOutput A strategy) Out₂)
    {N : Nat}
    (hfalse : ((profiledRawJointInitialLeftBlockMonitor A strategy).run
      play N).2 = false) :
    ∀ n, N ≤ n →
      ((profiledRawJointInitialLeftBlockMonitor A strategy).run play n).2 =
        false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [profiledRawJointInitialLeftBlockMonitor]
      change (((profiledRawJointInitialLeftBlockMonitor A strategy).run
        play (N + k)).2 && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

theorem profiledRawJointInitialRight_safe_false_persists
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointInitialRightReceiverOutput A strategy) Out₁)
    {N : Nat}
    (hfalse : ((profiledRawJointInitialRightBlockMonitor A strategy).run
      play N).2 = false) :
    ∀ n, N ≤ n →
      ((profiledRawJointInitialRightBlockMonitor A strategy).run play n).2 =
        false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [profiledRawJointInitialRightBlockMonitor]
      change (((profiledRawJointInitialRightBlockMonitor A strategy).run
        play (N + k)).2 && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

theorem profiledRawJointInitialLeft_safe_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointInitialLeftReceiverOutput A strategy) Out₂)
    (hwin : (profiledRawJointInitialLeftBlockMonitor A strategy).WinsPlay play)
    (n : Nat) :
    ((profiledRawJointInitialLeftBlockMonitor A strategy).run play n).2 =
      true := by
  by_contra hnot
  have hfalse := Bool.eq_false_of_not_eq_true hnot
  have hpersist := profiledRawJointInitialLeft_safe_false_persists A strategy
    play hfalse
  have heventual : ∀ k, n ≤ k →
      (profiledRawJointInitialLeftBlockMonitor A strategy).priority
        ((profiledRawJointInitialLeftBlockMonitor A strategy).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change (if ((profiledRawJointInitialLeftBlockMonitor A strategy).run
      play k).2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

theorem profiledRawJointInitialRight_safe_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointInitialRightReceiverOutput A strategy) Out₁)
    (hwin : (profiledRawJointInitialRightBlockMonitor A strategy).WinsPlay play)
    (n : Nat) :
    ((profiledRawJointInitialRightBlockMonitor A strategy).run play n).2 =
      true := by
  by_contra hnot
  have hfalse := Bool.eq_false_of_not_eq_true hnot
  have hpersist := profiledRawJointInitialRight_safe_false_persists A strategy
    play hfalse
  have heventual : ∀ k, n ≤ k →
      (profiledRawJointInitialRightBlockMonitor A strategy).priority
        ((profiledRawJointInitialRightBlockMonitor A strategy).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change (if ((profiledRawJointInitialRightBlockMonitor A strategy).run
      play k).2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

/-- Every key emitted by a winning left initial-controller play has the
checked delayed target, while the preceding key satisfies both finite
one-round overlap checks.  Genuine-boundary provenance is already carried by
the key subtype itself. -/
theorem profiledRawJointInitialLeft_stepConditions_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointInitialLeftReceiverOutput A strategy) Out₂)
    (hwin : (profiledRawJointInitialLeftBlockMonitor A strategy).WinsPlay play)
    (n : Nat) :
    let state := (profiledRawJointInitialLeftBlockMonitor A strategy).run play n
    let physical := profiledRawJointInitialLeftPhysicalLetter A (play n)
    let key := (play n).2.1.2
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A key.1.1) =
      initialLeftDelayedTarget A state.1.1 physical ∧
    profiledRawJointInitialLeftPendingOK A state.1.2 (play n) := by
  classical
  dsimp only
  have hsafeNext := profiledRawJointInitialLeft_safe_of_wins A strategy play
    hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledRawJointInitialLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact ⟨hsafeNext.1.2, hsafeNext.2⟩

/-- Symmetric certified-close inversion. -/
theorem profiledRawJointInitialRight_stepConditions_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointInitialRightReceiverOutput A strategy) Out₁)
    (hwin : (profiledRawJointInitialRightBlockMonitor A strategy).WinsPlay play)
    (n : Nat) :
    let state := (profiledRawJointInitialRightBlockMonitor A strategy).run play n
    let physical := profiledRawJointInitialRightPhysicalLetter A (play n)
    let key := (play n).2.1.2
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A key.1.1) =
      initialRightDelayedTarget A state.1.1 physical ∧
    profiledRawJointInitialRightPendingOK A state.1.2 (play n) := by
  classical
  dsimp only
  have hsafeNext := profiledRawJointInitialRight_safe_of_wins A strategy play
    hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledRawJointInitialRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact ⟨hsafeNext.1.2, hsafeNext.2⟩

end

end


end DetParityAutomaton

end DistributedSynthesis
