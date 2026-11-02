/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryRootGuard
import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialDelayedHandoff
import DistributedSynthesis.Formalizations.Lemma.LemCommittedSenderNarrowing

/-!
# Finite guarded sources at a delayed initial handoff

This file turns the one-shot root guard into a finite handoff key.  A key is a
paired entry state, one finite overlap profile, and the proposition that the
corresponding guarded input-free automaton has a rational run.  Proof fields
do not add run-time information, so the key type is finite.

The only rationality premise is the classical input-free rational-run basis,
instantiated at the guarded finite-state automaton itself.  The overlap guard
is proved from the original distributed strategy.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

def rightProfileGuardedAutomaton
    (target : PairedEntryTreeState A)
    (profile : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)) :=
  (pairedEntryRunAutomaton A target).rootGuarded
    (pairedEntryRootGuard A target profile.Matches (fun _ => True))

def leftProfileGuardedAutomaton
    (target : PairedEntryTreeState A)
    (profile : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) :=
  (pairedEntryRunAutomaton A target).rootGuarded
    (pairedEntryRootGuard A target (fun _ => True) profile.Matches)

/-- Runtime data of a guarded right-block source. -/
abbrev GuardedRightEntryData := PairedEntryTreeState A ×
  ProcOneEntryOverlapProfile
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)

/-- A finite source for a right block whose first process-one overlap table
has already been fixed. -/
abbrev GuardedRightEntrySource :=
  { data : GuardedRightEntryData A //
    (rightProfileGuardedAutomaton A data.1 data.2).HasRationalRun }

/-- Process-two/left-block mirror. -/
abbrev GuardedLeftEntryData := PairedEntryTreeState A ×
  ProcTwoEntryOverlapProfile
    (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)

abbrev GuardedLeftEntrySource :=
  { data : GuardedLeftEntryData A //
    (leftProfileGuardedAutomaton A data.1 data.2).HasRationalRun }

noncomputable instance guardedRightEntrySourceFintype
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] :
    Fintype (GuardedRightEntrySource A) := by
  classical
  exact Fintype.ofFinite _

noncomputable instance guardedLeftEntrySourceFintype
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] :
    Fintype (GuardedLeftEntrySource A) := by
  classical
  exact Fintype.ofFinite _

section Generated

variable [Inhabited In₁] [Inhabited In₂]

/-- The actual strategy supplies a guarded rational right-block source at
every delayed initial-left boundary. -/
theorem initialLeft_guardedHasRationalRun
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (basis :
      (rightProfileGuardedAutomaton A
        (initialLeftDelayedTarget A
          (initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy) past)
          (initialLeftLetterAt (initialLeftLambdaOfStrategy strategy) past move))
        (initialLeftNextBothProfile strategy past move)).RationalRunBasis) :
    (rightProfileGuardedAutomaton A
      (initialLeftDelayedTarget A
        (initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy) past)
        (initialLeftLetterAt (initialLeftLambdaOfStrategy strategy) past move))
      (initialLeftNextBothProfile strategy past move)).HasRationalRun := by
  let base := extendPrefix strategy [] (past.map leftEnvironment)
  let entry := procOneFreshPair strategy base
    (strategyGenerated_extendPrefix_basic strategy
      StrategyGeneratedPrefix.empty _) move.1 move.2
  let memory : PairedStrategyMemory A strategy :=
    .processOne entry
      (blockMinState A A.initial
        (extendPrefix strategy [] (past.map leftEnvironment)))
  have htarget :
      initialLeftDelayedTarget A
          (initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy) past)
          (initialLeftLetterAt (initialLeftLambdaOfStrategy strategy) past move) =
        memory.toTreeState := by
    simpa [memory, entry, base] using
      initialLeftDelayedTarget_lambdaOfStrategy A strategy past move
  have hmatches :
      (initialLeftNextBothProfile strategy past move).Matches
        entry.lambdaOfStrategy := by
    simpa [entry, base] using
      initialLeftNextBothProfile_matches_generated strategy past move
  have hallowed : PairedStrategyMemory.RootLambdaAllowed
      (A := A) memory
      (initialLeftNextBothProfile strategy past move).Matches
      (fun _ => True) := by
    simpa [memory, PairedStrategyMemory.RootLambdaAllowed] using hmatches
  have hbasis :
      ((pairedEntryRunAutomaton A memory.toTreeState).rootGuarded
        (pairedEntryRootGuard A memory.toTreeState
          (initialLeftNextBothProfile strategy past move).Matches
          (fun _ => True))).RationalRunBasis := by
    rw [htarget] at basis
    simpa [rightProfileGuardedAutomaton] using basis
  have hr := PairedStrategyMemory.rootGuarded_hasRationalRun
    A memory
    (initialLeftNextBothProfile strategy past move).Matches
    (fun _ => True)
    (memory.foreverAccepts_of_winning (A := A) hwin)
    (PairedStrategyMemory.switchingAccepts_of_winning hwin memory)
    hallowed hbasis
  rw [htarget]
  simpa [rightProfileGuardedAutomaton] using hr

/-- The corresponding finite source key. -/
noncomputable def initialLeftGuardedSource
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (basis :
      (rightProfileGuardedAutomaton A
        (initialLeftDelayedTarget A
          (initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy) past)
          (initialLeftLetterAt (initialLeftLambdaOfStrategy strategy) past move))
        (initialLeftNextBothProfile strategy past move)).RationalRunBasis) :
    GuardedRightEntrySource A :=
  ⟨(_, initialLeftNextBothProfile strategy past move),
    initialLeft_guardedHasRationalRun A strategy hwin past move basis⟩

theorem initialRight_guardedHasRationalRun
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (basis :
      (leftProfileGuardedAutomaton A
        (initialRightDelayedTarget A
          (initialRightScanAfter A (initialRightLambdaOfStrategy strategy) past)
          (initialRightLetterAt (initialRightLambdaOfStrategy strategy) past move))
        (initialRightNextBothProfile strategy past move)).RationalRunBasis) :
    (leftProfileGuardedAutomaton A
      (initialRightDelayedTarget A
        (initialRightScanAfter A (initialRightLambdaOfStrategy strategy) past)
        (initialRightLetterAt (initialRightLambdaOfStrategy strategy) past move))
      (initialRightNextBothProfile strategy past move)).HasRationalRun := by
  let base := extendPrefix strategy [] (past.map rightEnvironment)
  let entry := procTwoFreshPair strategy base
    (strategyGenerated_extendPrefix_basic strategy
      StrategyGeneratedPrefix.empty _) move.2 move.1
  let memory : PairedStrategyMemory A strategy :=
    .processTwo entry
      (blockMinState A A.initial
        (extendPrefix strategy [] (past.map rightEnvironment)))
  have htarget :
      initialRightDelayedTarget A
          (initialRightScanAfter A (initialRightLambdaOfStrategy strategy) past)
          (initialRightLetterAt (initialRightLambdaOfStrategy strategy) past move) =
        memory.toTreeState := by
    simpa [memory, entry, base] using
      initialRightDelayedTarget_lambdaOfStrategy A strategy past move
  have hmatches :
      (initialRightNextBothProfile strategy past move).Matches
        entry.lambdaOfStrategy := by
    simpa [entry, base] using
      initialRightNextBothProfile_matches_generated strategy past move
  have hallowed : PairedStrategyMemory.RootLambdaAllowed
      (A := A) memory (fun _ => True)
      (initialRightNextBothProfile strategy past move).Matches := by
    simpa [memory, PairedStrategyMemory.RootLambdaAllowed] using hmatches
  have hbasis :
      ((pairedEntryRunAutomaton A memory.toTreeState).rootGuarded
        (pairedEntryRootGuard A memory.toTreeState (fun _ => True)
          (initialRightNextBothProfile strategy past move).Matches)).RationalRunBasis := by
    rw [htarget] at basis
    simpa [leftProfileGuardedAutomaton] using basis
  have hr := PairedStrategyMemory.rootGuarded_hasRationalRun
    A memory (fun _ => True)
    (initialRightNextBothProfile strategy past move).Matches
    (memory.foreverAccepts_of_winning (A := A) hwin)
    (PairedStrategyMemory.switchingAccepts_of_winning hwin memory)
    hallowed hbasis
  rw [htarget]
  simpa [leftProfileGuardedAutomaton] using hr

noncomputable def initialRightGuardedSource
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (basis :
      (leftProfileGuardedAutomaton A
        (initialRightDelayedTarget A
          (initialRightScanAfter A (initialRightLambdaOfStrategy strategy) past)
          (initialRightLetterAt (initialRightLambdaOfStrategy strategy) past move))
        (initialRightNextBothProfile strategy past move)).RationalRunBasis) :
    GuardedLeftEntrySource A :=
  ⟨(_, initialRightNextBothProfile strategy past move),
    initialRight_guardedHasRationalRun A strategy hwin past move basis⟩

end Generated

end DetParityAutomaton

end DistributedSynthesis
