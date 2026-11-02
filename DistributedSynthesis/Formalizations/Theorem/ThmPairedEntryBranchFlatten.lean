/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntrySwitchingPasting

/-!
# Flattening a paired-entry branch

This is the concrete stream construction needed by
`SwitchingPastingWitness`.  A compressed direction contains the homogeneous
part of its block and its final reversing inputs.  The graph of that reversing
round is selected by the *next* direction's row; this is exactly the one-round
delay represented by the paired child.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

/-- Number of real rounds contributed by one compressed direction. -/
def pairedDirectionBlockLength
    {In₁ : Type u} {In₂ : Type v}
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) : Nat :=
  match direction with
  | .fromOne _ past _ => past.length + 1
  | .fromTwo _ past _ => past.length + 1

/-- Homogeneous rounds before the reversing close. -/
def pairedDirectionOpenEnvs
    {In₁ : Type u} {In₂ : Type v}
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    List (EnvironmentRound In₁ In₂) :=
  match direction with
  | .fromOne _ past _ => past.map rightEnvironment
  | .fromTwo _ past _ => past.map leftEnvironment

/-- The next row resolves which graph was used at the current reversing
round.  The fallback cases are irrelevant on `Alternates` branches. -/
def pairedClosingGraph
    {In₁ : Type u} {In₂ : Type v}
    (current next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) : Graph :=
  match current, next with
  | .fromOne _ _ _, .fromTwo .first _ _ => .right
  | .fromOne _ _ _, .fromTwo .both _ _ => .both
  | .fromTwo _ _ _, .fromOne .first _ _ => .left
  | .fromTwo _ _ _, .fromOne .both _ _ => .both
  | _, _ => .both

/-- The finite environment chunk represented by a direction. -/
def pairedDirectionChunk
    {In₁ : Type u} {In₂ : Type v}
    (current next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    List (EnvironmentRound In₁ In₂) :=
  match current with
  | .fromOne _ past move =>
      past.map rightEnvironment ++
        [⟨move.2, move.1, pairedClosingGraph current next⟩]
  | .fromTwo _ past move =>
      past.map leftEnvironment ++
        [⟨move.1, move.2, pairedClosingGraph current next⟩]

@[simp]
theorem pairedDirectionChunk_length
    {In₁ : Type u} {In₂ : Type v}
    (current next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    (pairedDirectionChunk current next).length =
      pairedDirectionBlockLength current := by
  cases current <;> simp [pairedDirectionChunk, pairedDirectionBlockLength]

@[simp]
theorem pairedDirectionOpenEnvs_length
    {In₁ : Type u} {In₂ : Type v}
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    (pairedDirectionOpenEnvs direction).length + 1 =
      pairedDirectionBlockLength direction := by
  cases direction <;> simp [pairedDirectionOpenEnvs, pairedDirectionBlockLength]

theorem pairedDirectionChunk_eq_openEnvs_append
    {In₁ : Type u} {In₂ : Type v}
    (current next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    ∃ closing : EnvironmentRound In₁ In₂,
      pairedDirectionChunk current next =
        pairedDirectionOpenEnvs current ++ [closing] := by
  cases current with
  | fromOne row past move =>
      exact ⟨⟨move.2, move.1, pairedClosingGraph (.fromOne row past move) next⟩,
        rfl⟩
  | fromTwo row past move =>
      exact ⟨⟨move.1, move.2, pairedClosingGraph (.fromTwo row past move) next⟩,
        rfl⟩

/-- Cumulative real-round cuts of a compressed branch. -/
def pairedBranchCuts
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    Nat -> Nat
  | 0 => 0
  | n + 1 => pairedBranchCuts branch n +
      pairedDirectionBlockLength (branch n)

@[simp]
theorem pairedBranchCuts_zero
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    pairedBranchCuts branch 0 = 0 := rfl

@[simp]
theorem pairedBranchCuts_succ
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (n : Nat) :
    pairedBranchCuts branch (n + 1) = pairedBranchCuts branch n +
      pairedDirectionBlockLength (branch n) := rfl

theorem pairedDirectionBlockLength_pos
    {In₁ : Type u} {In₂ : Type v}
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    0 < pairedDirectionBlockLength direction := by
  cases direction <;> simp [pairedDirectionBlockLength]

theorem pairedBranchCuts_strictMono
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    StrictMono (pairedBranchCuts branch) := by
  exact strictMono_nat_of_lt_succ fun n => by
    rw [pairedBranchCuts_succ]
    exact Nat.lt_add_of_pos_right (pairedDirectionBlockLength_pos (branch n))

/-- `cutBlock` selects `k` exactly for indices in the half-open `k`-th cut
interval. -/
theorem cutBlock_eq_of_mem_interval
    (cuts : Nat -> Nat) (hmono : StrictMono cuts) (hzero : cuts 0 = 0)
    (k n : Nat) (hlower : cuts k ≤ n) (hupper : n < cuts (k + 1)) :
    cutBlock cuts n = k := by
  apply Nat.le_antisymm
  · by_contra hnot
    have hkOne : k + 1 ≤ cutBlock cuts n := by omega
    have hcutsLe : cuts (k + 1) ≤ cuts (cutBlock cuts n) :=
      hmono.monotone hkOne
    have hselected : cuts (cutBlock cuts n) ≤ n :=
      cuts_cutBlock_le hzero n
    omega
  · apply le_cutBlock n
    · exact Nat.le_trans (le_cuts hmono k) hlower
    · exact hlower

/-- The chunk at compressed index `k`. -/
def pairedBranchChunk
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (k : Nat) : List (EnvironmentRound In₁ In₂) :=
  pairedDirectionChunk (branch k) (branch (k + 1))

@[simp]
theorem pairedBranchChunk_length
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (k : Nat) :
    (pairedBranchChunk branch k).length =
      pairedDirectionBlockLength (branch k) :=
  pairedDirectionChunk_length _ _

/-- Flatten all finite branch chunks into one infinite environment sequence.
Strict growth of the cuts proves that the selected chunk index is in range. -/
def pairedBranchEnvironment
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    EnvironmentSequence In₁ In₂ :=
  fun n =>
    let cuts := pairedBranchCuts branch
    let k := cutBlock cuts n
    have hlower : cuts k ≤ n := cuts_cutBlock_le (cuts := cuts) rfl n
    have hupper : n < cuts (k + 1) :=
      lt_cuts_succ_cutBlock (pairedBranchCuts_strictMono branch) n
    have hindex : n - cuts k < (pairedBranchChunk branch k).length := by
      rw [pairedBranchChunk_length]
      change pairedBranchCuts branch k ≤ n at hlower
      change n < pairedBranchCuts branch (k + 1) at hupper
      change n - pairedBranchCuts branch k <
        pairedDirectionBlockLength (branch k)
      rw [pairedBranchCuts_succ] at hupper
      omega
    (pairedBranchChunk branch k).get ⟨n - cuts k, hindex⟩

/-- Reading the flattened stream inside block `k` returns the corresponding
element of the finite chunk. -/
theorem pairedBranchEnvironment_at
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (k j : Nat) (hj : j < (pairedBranchChunk branch k).length) :
    pairedBranchEnvironment branch (pairedBranchCuts branch k + j) =
      (pairedBranchChunk branch k).get ⟨j, hj⟩ := by
  have hupper :
      pairedBranchCuts branch k + j < pairedBranchCuts branch (k + 1) := by
    rw [pairedBranchCuts_succ, ← pairedBranchChunk_length]
    omega
  have hblock :
      cutBlock (pairedBranchCuts branch)
          (pairedBranchCuts branch k + j) = k :=
    cutBlock_eq_of_mem_interval _ (pairedBranchCuts_strictMono branch) rfl k _
      (Nat.le_add_right _ _) hupper
  dsimp only [pairedBranchEnvironment]
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp only [hblock, Nat.add_sub_cancel_left]

/-- At each cut, the flattened environment begins with exactly the
homogeneous part stored in that direction. -/
theorem omegaPrefix_drop_pairedBranchEnvironment
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (k : Nat) :
    omegaPrefix
        (OmegaWord.drop (pairedBranchEnvironment branch)
          (pairedBranchCuts branch k))
        (pairedDirectionOpenEnvs (branch k)).length =
      pairedDirectionOpenEnvs (branch k) := by
  apply List.ext_get
  · simp [omegaPrefix]
  · intro i hiLeft hiRight
    unfold omegaPrefix
    rw [List.get_eq_getElem, List.getElem_ofFn, List.get_eq_getElem]
    change pairedBranchEnvironment branch (pairedBranchCuts branch k + i) = _
    have hiChunk : i < (pairedBranchChunk branch k).length := by
      rw [pairedBranchChunk_length, ← pairedDirectionOpenEnvs_length]
      omega
    rw [pairedBranchEnvironment_at branch k i hiChunk]
    rw [List.get_eq_getElem]
    rcases pairedDirectionChunk_eq_openEnvs_append (branch k) (branch (k + 1))
      with ⟨closing, hchunk⟩
    have hbranchChunk :
        pairedBranchChunk branch k =
          pairedDirectionOpenEnvs (branch k) ++ [closing] := hchunk
    have hget :
        (pairedBranchChunk branch k)[i]? =
          (pairedDirectionOpenEnvs (branch k))[i]? := by
      rw [hbranchChunk]
      rw [List.getElem?_append_left hiRight,
        List.getElem?_eq_getElem hiRight]
    rw [List.getElem?_eq_getElem hiChunk,
      List.getElem?_eq_getElem hiRight] at hget
    exact Option.some.inj hget

/-- Split a finite omega prefix after `n` entries. -/
theorem omegaPrefix_add {Move : Type*} (env : Nat -> Move) (n m : Nat) :
    omegaPrefix env (n + m) = omegaPrefix env n ++
      List.ofFn (fun i : Fin m => env (n + i)) := by
  unfold omegaPrefix
  rw [List.ofFn_add]
  congr 1

/-- The length-`k` slice of the flattened environment is exactly branch chunk
`k`. -/
theorem pairedBranchEnvironment_blockOfFn
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (k : Nat) :
    List.ofFn (fun i : Fin (pairedBranchChunk branch k).length =>
      pairedBranchEnvironment branch (pairedBranchCuts branch k + i)) =
      pairedBranchChunk branch k := by
  apply List.ext_get
  · simp
  · intro i hiLeft hiRight
    rw [List.get_eq_getElem, List.getElem_ofFn, List.get_eq_getElem]
    exact pairedBranchEnvironment_at branch k i hiRight

/-- Successive cut prefixes differ by exactly one branch chunk. -/
theorem omegaPrefix_pairedBranchCuts_succ
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (k : Nat) :
    omegaPrefix (pairedBranchEnvironment branch)
        (pairedBranchCuts branch (k + 1)) =
      omegaPrefix (pairedBranchEnvironment branch)
          (pairedBranchCuts branch k) ++
        pairedBranchChunk branch k := by
  rw [pairedBranchCuts_succ, ← pairedBranchChunk_length,
    omegaPrefix_add, pairedBranchEnvironment_blockOfFn]

/-! ## Exact finite-block priority minima -/

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

theorem priority_minPriorityState_eq_min
    (incumbent next : A.State) :
    A.priority (A.minPriorityState incumbent next) =
      min (A.priority incumbent) (A.priority next) := by
  simp only [minPriorityState]
  split <;> omega

theorem blockEndAndMin_snoc
    (state : A.State)
    (word : List (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (record : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    blockEndAndMin A state (word ++ [record]) =
      let old := blockEndAndMin A state word
      let next := A.step old.1 record
      (next, A.minPriorityState old.2 next) := by
  simp [blockEndAndMin, List.foldl_append]

/-- The first component of the finite block scan is the ordinary DPA run
state after that prefix. -/
theorem blockEndAndMin_omegaPrefix_fst
    (state : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)) :
    ∀ n : Nat,
      (blockEndAndMin A state (omegaPrefix word n)).1 =
        A.runFrom state word n := by
  intro n
  induction n with
  | zero =>
      change state = state
      rfl
  | succ n ih =>
      rw [omegaPrefix_succ]
      rw [blockEndAndMin_snoc]
      dsimp only
      rw [ih]
      rfl

/-- `blockMinState` is exactly the priority minimum over the starting state
and all states reached while reading the finite prefix. -/
theorem priority_blockMinState_omegaPrefix_eq_rangeMin
    (state : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)) :
    ∀ n : Nat,
      A.priority (blockMinState A state (omegaPrefix word n)) =
        rangeMin (fun j => A.priority (A.runFrom state word j)) 0 n := by
  intro n
  induction n with
  | zero =>
      change A.priority state = A.priority state
      rfl
  | succ n ih =>
      rw [omegaPrefix_succ]
      simp only [blockMinState]
      rw [blockEndAndMin_snoc]
      dsimp only
      rw [priority_minPriorityState_eq_min A]
      change min
        (A.priority (blockMinState A state (omegaPrefix word n)))
        (A.priority
          (A.step (blockEndAndMin A state (omegaPrefix word n)).1 (word n))) = _
      rw [ih,
        blockEndAndMin_omegaPrefix_fst A]
      rw [rangeMin]
      simp only [Nat.zero_add]
      rw [show A.runFrom state word (n + 1) =
        A.step (A.runFrom state word n) (word n) by rfl]

theorem rangeMin_shift_origin (priority : Nat -> Nat) (start : Nat) :
    ∀ length : Nat,
      rangeMin priority start length =
        rangeMin (fun j => priority (start + j)) 0 length := by
  intro length
  induction length with
  | zero => rfl
  | succ length ih =>
      rw [rangeMin, rangeMin, ih]
      simp only [Nat.zero_add]

namespace PairedStrategyMemory

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}

/-- The concrete old-row history selected by a compatible direction.  The
fallback is irrelevant under `DirectionCompatible`. -/
def selectedHistory
    (memory : PairedStrategyMemory A strategy)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  match memory, direction with
  | .processOne entry _, .fromOne .first _ _ => entry.leftHistory
  | .processOne entry _, .fromOne .both _ _ => entry.bothHistory
  | .processTwo entry _, .fromTwo .first _ _ => entry.rightHistory
  | .processTwo entry _, .fromTwo .both _ _ => entry.bothHistory
  | _, _ => []

/-- Finite DPA record word of the selected homogeneous block. -/
def selectedBlockWord
    [Inhabited In₁] [Inhabited In₂]
    (memory : PairedStrategyMemory A strategy)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  match memory, direction with
  | .processOne entry _, .fromOne .first past _ =>
      entry.lambdaOfStrategy.leftWord past
  | .processOne entry _, .fromOne .both past _ =>
      entry.lambdaOfStrategy.bothWord past
  | .processTwo entry _, .fromTwo .first past _ =>
      entry.lambdaOfStrategy.rightWord past
  | .processTwo entry _, .fromTwo .both past _ =>
      entry.lambdaOfStrategy.bothWord past
  | _, _ => []

theorem pairedRightWordFrom_length
    (blind : SenderBlockStrategy In₁ Out₁)
    (informed : ReceiverBlockStrategy In₂ In₁ Out₂)
    (past moves : List (In₂ × In₁)) :
    (pairedRightWordFrom blind informed past moves).length = moves.length := by
  induction moves generalizing past with
  | nil => rfl
  | cons move rest ih =>
      simp [pairedRightWordFrom, ih]

theorem pairedLeftWordFrom_length
    (blind : SenderBlockStrategy In₂ Out₂)
    (informed : ReceiverBlockStrategy In₁ In₂ Out₁)
    (past moves : List (In₁ × In₂)) :
    (pairedLeftWordFrom blind informed past moves).length = moves.length := by
  induction moves generalizing past with
  | nil => rfl
  | cons move rest ih =>
      simp [pairedLeftWordFrom, ih]

/-- The selected block word has exactly the length of the homogeneous
environment prefix. -/
theorem selectedBlockWord_length
    [Inhabited In₁] [Inhabited In₂]
    (memory : PairedStrategyMemory A strategy)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hcompatible : DirectionCompatible memory direction) :
    (selectedBlockWord memory direction).length =
      (pairedDirectionOpenEnvs direction).length := by
  cases memory with
  | sink => simp [DirectionCompatible] at hcompatible
  | processOne entry minimum =>
      cases direction with
      | fromTwo row past move => simp [DirectionCompatible] at hcompatible
      | fromOne row past move =>
          cases row <;>
            simp [selectedBlockWord, pairedDirectionOpenEnvs,
              ProcOnePairedRightLambda.leftWord,
              ProcOnePairedRightLambda.bothWord, pairedRightWordFrom_length]
  | processTwo entry minimum =>
      cases direction with
      | fromOne row past move => simp [DirectionCompatible] at hcompatible
      | fromTwo row past move =>
          cases row <;>
            simp [selectedBlockWord, pairedDirectionOpenEnvs,
              ProcTwoPairedLeftLambda.rightWord,
              ProcTwoPairedLeftLambda.bothWord, pairedLeftWordFrom_length]

/-- Every selected row of a compatible live node is a genuine strategy
prefix. -/
theorem selectedHistory_generated
    [Inhabited In₁] [Inhabited In₂]
    (memory : PairedStrategyMemory A strategy)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hcompatible : DirectionCompatible memory direction) :
    StrategyGeneratedPrefix strategy (selectedHistory memory direction) := by
  cases memory with
  | sink => simp [DirectionCompatible] at hcompatible
  | processOne entry minimum =>
      cases direction with
      | fromTwo row past move => simp [DirectionCompatible] at hcompatible
      | fromOne row past move =>
          cases row with
          | first => exact entry.leftGenerated
          | both => exact entry.bothGenerated
  | processTwo entry minimum =>
      cases direction with
      | fromOne row past move => simp [DirectionCompatible] at hcompatible
      | fromTwo row past move =>
          cases row with
          | first => exact entry.rightGenerated
          | both => exact entry.bothGenerated

/-- Playing the selected homogeneous inputs appends exactly the selected
lambda word. -/
theorem extend_selectedHistory_openEnvs
    [Inhabited In₁] [Inhabited In₂]
    (memory : PairedStrategyMemory A strategy)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hcompatible : DirectionCompatible memory direction) :
    extendPrefix strategy (selectedHistory memory direction)
        (pairedDirectionOpenEnvs direction) =
      selectedHistory memory direction ++ selectedBlockWord memory direction := by
  cases memory with
  | sink => simp [DirectionCompatible] at hcompatible
  | processOne entry minimum =>
      cases direction with
      | fromTwo row past move => simp [DirectionCompatible] at hcompatible
      | fromOne row past move =>
          cases row with
          | first =>
              simpa [selectedHistory, selectedBlockWord,
                pairedDirectionOpenEnvs,
                ProcOnePairedRightLambda.leftWord,
                ProcOnePairedEntryRep.lambdaOfStrategy] using
                (extendPrefix_eq_append_pairedRightWordFrom
                  strategy entry.leftHistory [] past)
          | both =>
              have h := extendPrefix_eq_append_pairedRightWordFrom
                strategy entry.bothHistory [] past
              rw [← entry.lambdaOfStrategy_blind_eq_both] at h
              simpa [selectedHistory, selectedBlockWord,
                pairedDirectionOpenEnvs,
                ProcOnePairedRightLambda.bothWord,
                ProcOnePairedEntryRep.lambdaOfStrategy] using h
  | processTwo entry minimum =>
      cases direction with
      | fromOne row past move => simp [DirectionCompatible] at hcompatible
      | fromTwo row past move =>
          cases row with
          | first =>
              simpa [selectedHistory, selectedBlockWord,
                pairedDirectionOpenEnvs,
                ProcTwoPairedLeftLambda.rightWord,
                ProcTwoPairedEntryRep.lambdaOfStrategy] using
                (extendPrefix_eq_append_pairedLeftWordFrom
                  strategy entry.rightHistory [] past)
          | both =>
              have h := extendPrefix_eq_append_pairedLeftWordFrom
                strategy entry.bothHistory [] past
              rw [← entry.lambdaOfStrategy_blind_eq_both] at h
              simpa [selectedHistory, selectedBlockWord,
                pairedDirectionOpenEnvs,
                ProcTwoPairedLeftLambda.bothWord,
                ProcTwoPairedEntryRep.lambdaOfStrategy] using h

/-- One compressed step is exactly extension by its flattened finite chunk.
The next direction supplies the delayed choice between the fresh one-way and
`both` histories. -/
theorem extend_selectedHistory_chunk
    [Inhabited In₁] [Inhabited In₂]
    (memory : PairedStrategyMemory A strategy)
    (current next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hcurrent : DirectionCompatible memory current)
    (hnext : DirectionCompatible (memory.step (A := A) current) next) :
    extendPrefix strategy (selectedHistory memory current)
        (pairedDirectionChunk current next) =
      selectedHistory (memory.step (A := A) current) next := by
  cases memory with
  | sink => simp [DirectionCompatible] at hcurrent
  | processOne entry minimum =>
      cases current with
      | fromTwo row past move => simp [DirectionCompatible] at hcurrent
      | fromOne row past move =>
          cases row <;> cases next <;>
            try simp [DirectionCompatible, step] at hnext
          all_goals
            cases ‹PairedEntryRow› <;>
              simp [selectedHistory, step, pairedDirectionChunk,
                pairedClosingGraph, extendPrefix_snoc, procTwoFreshPair]
  | processTwo entry minimum =>
      cases current with
      | fromOne row past move => simp [DirectionCompatible] at hcurrent
      | fromTwo row past move =>
          cases row <;> cases next <;>
            try simp [DirectionCompatible, step] at hnext
          all_goals
            cases ‹PairedEntryRow› <;>
              simp [selectedHistory, step, pairedDirectionChunk,
                pairedClosingGraph, extendPrefix_snoc, procOneFreshPair]

/-- Continuing for `n` rounds is finite extension by the first `n`
environment moves. -/
theorem continueExec_eq_extendPrefix_omegaPrefix
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n : Nat,
      continueExec strategy base env n =
        extendPrefix strategy base (omegaPrefix env n) := by
  intro n
  induction n with
  | zero => simp [continueExec, omegaPrefix, extendPrefix]
  | succ n ih =>
      simp only [continueExec, omegaPrefix_succ, extendPrefix_snoc]
      rw [ih]

/-- The records emitted by a finite continuation are exactly the appended
suffix of its extended history. -/
theorem extendPrefix_eq_append_omegaPrefix_contWord
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n : Nat,
      extendPrefix strategy base (omegaPrefix env n) =
        base ++ omegaPrefix (contWord strategy base env) n := by
  intro n
  induction n with
  | zero => simp [omegaPrefix, extendPrefix]
  | succ n ih =>
      have hcont :
          continueExec strategy base env n =
            base ++ omegaPrefix (contWord strategy base env) n := by
        rw [continueExec_eq_extendPrefix_omegaPrefix, ih]
      rw [omegaPrefix_succ, omegaPrefix_succ, extendPrefix_snoc, ih]
      change History.append
          (base ++ omegaPrefix (contWord strategy base env) n)
          (nextRound strategy
            (base ++ omegaPrefix (contWord strategy base env) n) (env n)) =
        base ++ (omegaPrefix (contWord strategy base env) n ++
          [nextRound strategy (continueExec strategy base env n) (env n)])
      rw [hcont]
      simp [History.append, List.append_assoc]

/-- DPA execution on a continuation word agrees with the entry state of its
concrete continued history. -/
theorem runFrom_contWord_eq_entryState_continueExec
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n : Nat,
      A.runFrom (entryState (A := A) base) (contWord strategy base env) n =
        entryState (A := A) (continueExec strategy base env n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change A.step
          (A.runFrom (entryState (A := A) base) (contWord strategy base env) n)
          (contWord strategy base env n) = _
      rw [ih]
      simp [continueExec, contWord, entryState, History.append,
        List.foldl_append]

theorem continueExec_drop
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (n : Nat) :
    ∀ m : Nat,
      continueExec strategy (continueExec strategy base env n)
          (OmegaWord.drop env n) m =
        continueExec strategy base env (n + m) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      change History.append _
          (nextRound strategy _ (env (n + m))) = _
      rw [ih]
      rfl

/-- Dropping a continuation word restarts it from the concrete history at the
cut. -/
theorem drop_contWord
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (n : Nat) :
    OmegaWord.drop (contWord strategy base env) n =
      contWord strategy (continueExec strategy base env n)
        (OmegaWord.drop env n) := by
  funext m
  change nextRound strategy (continueExec strategy base env (n + m))
      (env (n + m)) =
    nextRound strategy
      (continueExec strategy (continueExec strategy base env n)
        (OmegaWord.drop env n) m)
      (env (n + m))
  rw [continueExec_drop]

/-- Extension composes over concatenated finite environment words. -/
theorem extendPrefix_append
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (left right : List (EnvironmentRound In₁ In₂)) :
    extendPrefix strategy base (left ++ right) =
      extendPrefix strategy (extendPrefix strategy base left) right := by
  simp [extendPrefix, List.foldl_append]

/-- The finite selected lambda word is exactly the record prefix seen after
the corresponding flattened cut. -/
theorem omegaPrefix_contWord_at_cut_eq_selectedBlockWord
    [Inhabited In₁] [Inhabited In₂]
    (memory : PairedStrategyMemory A strategy)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hcompatible : DirectionCompatible memory direction)
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (k : Nat) (hdirection : branch k = direction) :
    omegaPrefix
        (contWord strategy (selectedHistory memory direction)
          (OmegaWord.drop (pairedBranchEnvironment branch)
            (pairedBranchCuts branch k)))
        (pairedDirectionOpenEnvs direction).length =
      selectedBlockWord memory direction := by
  have hext := extendPrefix_eq_append_omegaPrefix_contWord strategy
    (selectedHistory memory direction)
    (OmegaWord.drop (pairedBranchEnvironment branch)
      (pairedBranchCuts branch k))
    (pairedDirectionOpenEnvs direction).length
  have henv := omegaPrefix_drop_pairedBranchEnvironment branch k
  rw [hdirection] at henv
  rw [henv, extend_selectedHistory_openEnvs memory direction hcompatible] at hext
  exact (List.append_cancel_left hext).symm

/-- **Cut-alignment invariant.**  At every compressed cut, the concrete
continuation through the flattened environment is exactly the old-row history
selected at that paired node. -/
theorem selectedHistory_at_pairedBranchCut
    [Inhabited In₁] [Inhabited In₂]
    (initial : PairedStrategyMemory A strategy)
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (halternates : Alternates (A := A) initial branch) :
    ∀ k : Nat,
      continueExec strategy (selectedHistory initial (branch 0))
          (pairedBranchEnvironment branch) (pairedBranchCuts branch k) =
        selectedHistory
          (atNode (A := A) initial (branchNode branch k)) (branch k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      let memory := atNode (A := A) initial (branchNode branch k)
      have hcurrent : DirectionCompatible memory (branch k) :=
        halternates k
      have hnext :
          DirectionCompatible (memory.step (A := A) (branch k))
            (branch (k + 1)) := by
        simpa [memory, branchNode, atNode_append] using halternates (k + 1)
      calc
        continueExec strategy (selectedHistory initial (branch 0))
            (pairedBranchEnvironment branch)
            (pairedBranchCuts branch (k + 1)) =
          extendPrefix strategy (selectedHistory initial (branch 0))
            (omegaPrefix (pairedBranchEnvironment branch)
              (pairedBranchCuts branch (k + 1))) :=
                continueExec_eq_extendPrefix_omegaPrefix _ _ _ _
        _ = extendPrefix strategy (selectedHistory initial (branch 0))
            (omegaPrefix (pairedBranchEnvironment branch)
                (pairedBranchCuts branch k) ++
              pairedBranchChunk branch k) := by
                rw [omegaPrefix_pairedBranchCuts_succ]
        _ = extendPrefix strategy
            (extendPrefix strategy (selectedHistory initial (branch 0))
              (omegaPrefix (pairedBranchEnvironment branch)
                (pairedBranchCuts branch k)))
            (pairedBranchChunk branch k) :=
              extendPrefix_append _ _ _ _
        _ = extendPrefix strategy
            (continueExec strategy (selectedHistory initial (branch 0))
              (pairedBranchEnvironment branch) (pairedBranchCuts branch k))
            (pairedBranchChunk branch k) := by
              rw [continueExec_eq_extendPrefix_omegaPrefix]
        _ = extendPrefix strategy (selectedHistory memory (branch k))
            (pairedBranchChunk branch k) := by rw [ih]
        _ = selectedHistory (memory.step (A := A) (branch k))
            (branch (k + 1)) := by
              exact extend_selectedHistory_chunk memory (branch k)
                (branch (k + 1)) hcurrent hnext
        _ = selectedHistory
            (atNode (A := A) initial (branchNode branch (k + 1)))
            (branch (k + 1)) := by
              rw [branchNode, atNode_append]

/-- The priority stored at the successor tree node is precisely the minimum
state of the selected homogeneous block. -/
theorem pairedEntryPriority_succ_eq_selectedBlockMin
    [Inhabited In₁] [Inhabited In₂]
    (initial : PairedStrategyMemory A strategy)
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (halternates : Alternates (A := A) initial branch)
    (k : Nat) :
    let memory := atNode (A := A) initial (branchNode branch k)
    pairedEntryPriority A
        (run (A := A) initial (branchNode branch (k + 1))) =
      A.priority
        (blockMinState A
          (entryState (A := A) (selectedHistory memory (branch k)))
          (selectedBlockWord memory (branch k))) := by
  let memory := atNode (A := A) initial (branchNode branch k)
  have hcompatible : DirectionCompatible memory (branch k) := halternates k
  change pairedEntryPriority A
      ((atNode (A := A) initial (branchNode branch (k + 1))).toTreeState) = _
  rw [branchNode, atNode_append]
  change pairedEntryPriority A (toTreeState (memory.step (A := A) (branch k))) = _
  rw [show atNode (A := A) initial (branchNode branch k) = memory by rfl]
  cases hmemory : memory with
  | sink => simp [DirectionCompatible, hmemory] at hcompatible
  | processOne entry minimum =>
      cases hdirection : branch k with
      | fromTwo row past move =>
          simp [DirectionCompatible, hmemory, hdirection] at hcompatible
      | fromOne row past move =>
          cases row <;>
            simp [step, toTreeState, pairedEntryPriority,
              selectedHistory, selectedBlockWord, ProcOnePairedEntryRep.code]
  | processTwo entry minimum =>
      cases hdirection : branch k with
      | fromOne row past move =>
          simp [DirectionCompatible, hmemory, hdirection] at hcompatible
      | fromTwo row past move =>
          cases row <;>
            simp [step, toTreeState, pairedEntryPriority,
              selectedHistory, selectedBlockWord, ProcTwoPairedEntryRep.code]

/-- The stored compressed priority is exactly `cutBlockMin` on the genuine
flattened continuation word. -/
theorem pairedEntryPriority_eq_cutBlockMin
    [Inhabited In₁] [Inhabited In₂]
    (initial : PairedStrategyMemory A strategy)
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (halternates : Alternates (A := A) initial branch)
    (k : Nat) :
    let base := selectedHistory initial (branch 0)
    let env := pairedBranchEnvironment branch
    let word := contWord strategy base env
    let start := entryState (A := A) base
    pairedEntryPriority A
        (run (A := A) initial (branchNode branch (k + 1))) =
      cutBlockMin (fun n => A.priority (A.runFrom start word n))
        (pairedBranchCuts branch) k := by
  let base := selectedHistory initial (branch 0)
  let env := pairedBranchEnvironment branch
  let word := contWord strategy base env
  let start := entryState (A := A) base
  let memory := atNode (A := A) initial (branchNode branch k)
  let direction := branch k
  let selected := selectedHistory memory direction
  let localWord := OmegaWord.drop word (pairedBranchCuts branch k)
  let length := (pairedDirectionOpenEnvs direction).length
  have hcompatible : DirectionCompatible memory direction := halternates k
  have halign :
      continueExec strategy base env (pairedBranchCuts branch k) = selected := by
    exact selectedHistory_at_pairedBranchCut initial branch halternates k
  have hstate :
      A.runFrom start word (pairedBranchCuts branch k) =
        entryState (A := A) selected := by
    dsimp only [start, word]
    rw [runFrom_contWord_eq_entryState_continueExec, halign]
  have hdrop :
      localWord =
        contWord strategy selected
          (OmegaWord.drop env (pairedBranchCuts branch k)) := by
    dsimp only [localWord, word]
    rw [drop_contWord, halign]
  have hprefix :
      omegaPrefix localWord length = selectedBlockWord memory direction := by
    rw [hdrop]
    exact omegaPrefix_contWord_at_cut_eq_selectedBlockWord
      memory direction hcompatible branch k rfl
  have hminimum :
      A.priority
          (blockMinState A (entryState (A := A) selected)
            (selectedBlockWord memory direction)) =
        rangeMin
          (fun j => A.priority
            (A.runFrom (entryState (A := A) selected) localWord j)) 0 length := by
    rw [← hprefix]
    exact priority_blockMinState_omegaPrefix_eq_rangeMin A _ _ length
  have hrun :
      (fun j => A.priority
          (A.runFrom (entryState (A := A) selected) localWord j)) =
        (fun j => A.priority
          (A.runFrom start word (pairedBranchCuts branch k + j))) := by
    funext j
    rw [← hstate]
    exact congrArg A.priority
      (A.runFrom_drop start word (pairedBranchCuts branch k) j)
  have hwidth :
      pairedBranchCuts branch (k + 1) - pairedBranchCuts branch k - 1 =
        length := by
    dsimp only [length, direction]
    rw [pairedBranchCuts_succ, ← pairedDirectionOpenEnvs_length]
    omega
  calc
    pairedEntryPriority A
        (run (A := A) initial (branchNode branch (k + 1))) =
      A.priority
        (blockMinState A (entryState (A := A) selected)
          (selectedBlockWord memory direction)) := by
            exact pairedEntryPriority_succ_eq_selectedBlockMin
              initial branch halternates k
    _ = rangeMin
        (fun j => A.priority
          (A.runFrom (entryState (A := A) selected) localWord j)) 0 length :=
      hminimum
    _ = rangeMin
        (fun j => A.priority
          (A.runFrom start word (pairedBranchCuts branch k + j))) 0 length := by
      rw [hrun]
    _ = rangeMin (fun n => A.priority (A.runFrom start word n))
        (pairedBranchCuts branch k) length := by
      exact (rangeMin_shift_origin
        (fun n => A.priority (A.runFrom start word n))
        (pairedBranchCuts branch k) length).symm
    _ = cutBlockMin (fun n => A.priority (A.runFrom start word n))
        (pairedBranchCuts branch) k := by
      unfold cutBlockMin
      rw [hwidth]

/-- A winning distributed strategy supplies the concrete pasting witness for
every correctly alternating paired-entry branch.  The witness is the genuine
strategy continuation obtained by flattening the compressed directions. -/
theorem switchingPastingWitness_of_winning
    [Inhabited In₁] [Inhabited In₂]
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : PairedStrategyMemory A strategy)
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (halternates : Alternates (A := A) initial branch) :
    Nonempty (SwitchingPastingWitness (A := A) initial branch) := by
  let base := selectedHistory initial (branch 0)
  let env := pairedBranchEnvironment branch
  let word := contWord strategy base env
  let start := entryState (A := A) base
  refine ⟨{
    start := start
    word := word
    cuts := pairedBranchCuts branch
    cutsStrictMono := pairedBranchCuts_strictMono branch
    cutsZero := pairedBranchCuts_zero branch
    accepts := ?_
    priority_eq_blockMin := ?_
  }⟩
  · dsimp only [start, word, base, env]
    exact acceptsFrom_contWord_of_winning A strategy hwin
      (selectedHistory_generated initial (branch 0) (by
        simpa [branchNode] using halternates 0))
      (pairedBranchEnvironment branch)
  · intro k
    dsimp only [start, word, base, env]
    exact pairedEntryPriority_eq_cutBlockMin initial branch halternates k

/-- End-to-end switching closure: no branch-pasting hypothesis remains. -/
theorem switchingAccepts_of_winning
    [Inhabited In₁] [Inhabited In₂]
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : PairedStrategyMemory A strategy) :
    initial.SwitchingAccepts (A := A) := by
  apply switchingAccepts_of_alternating_pasting initial
  intro branch halternates
  exact switchingPastingWitness_of_winning hwin initial branch halternates

/-- The Bérard rational-run handoff for the paired-entry automaton, with the
model-specific infinite-branch proof now completely discharged. -/
theorem hasRationalRun_of_winning_flattened
    [Inhabited In₁] [Inhabited In₂]
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : PairedStrategyMemory A strategy)
    (basis :
      (pairedEntryRunAutomaton A initial.toTreeState).RationalRunBasis) :
    (pairedEntryRunAutomaton A initial.toTreeState).HasRationalRun := by
  exact initial.hasRationalRun_of_winning (A := A) hwin basis
    (switchingAccepts_of_winning hwin initial)

end PairedStrategyMemory

end DetParityAutomaton

end DistributedSynthesis
