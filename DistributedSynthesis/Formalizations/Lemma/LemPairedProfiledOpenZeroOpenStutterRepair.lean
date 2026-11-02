/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageStutterAudit
import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryBranchFlatten

/-!
# A real zero-open transition repairs repeated physical sides

An abstract same-side stutter is parity-unsound.  The paired-entry semantics
nevertheless contains a different, honest repair.  When two consecutive
physical epochs have the same strict side, the synchronizing `.both` round
between them can be represented by a zero-open direction of the opposite
paired orientation:

* the preceding direction closes on its last strict round (row `first`);
* the opposite direction has empty homogeneous past and closes on the actual
  `.both` round (the following row is `both`);
* the next nonempty direction is back on the original side.

The lemmas below prove that this is an exact partition of the real physical
round word, not an inserted dummy letter.  They also prove that the priority
of the zero-open direction is the DPA priority immediately before its real
`.both` round.  Hence this repair is eligible for ordinary block-minimum
pasting and does not require any neutral-priority assumption.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

/-! ## Exact two-chunk word identities -/

/-- Repeated right closing sides are represented by a right chunk ending in
the last strict-right round, followed by a zero-open left chunk containing
the actual synchronizing round. -/
theorem pairedDirectionChunks_repeatedRight_zeroOpen
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow)
    (strictPrefix : List (In₂ × In₁)) (lastStrict : In₂ × In₁)
    (closing : In₁ × In₂)
    (nextPast : List (In₂ × In₁)) (nextMove : In₂ × In₁) :
    pairedDirectionChunk
          (.fromOne row strictPrefix lastStrict)
          (.fromTwo .first [] closing) ++
        pairedDirectionChunk
          (.fromTwo .first [] closing)
          (.fromOne .both nextPast nextMove) =
      strictPrefix.map rightEnvironment ++
        [rightEnvironment lastStrict,
          { inputOne := closing.1, inputTwo := closing.2,
            graph := .both }] := by
  simp [pairedDirectionChunk, pairedClosingGraph, rightEnvironment]

/-- Mirror identity for two consecutive left-closing physical epochs. -/
theorem pairedDirectionChunks_repeatedLeft_zeroOpen
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow)
    (strictPrefix : List (In₁ × In₂)) (lastStrict : In₁ × In₂)
    (closing : In₂ × In₁)
    (nextPast : List (In₁ × In₂)) (nextMove : In₁ × In₂) :
    pairedDirectionChunk
          (.fromTwo row strictPrefix lastStrict)
          (.fromOne .first [] closing) ++
        pairedDirectionChunk
          (.fromOne .first [] closing)
          (.fromTwo .both nextPast nextMove) =
      strictPrefix.map leftEnvironment ++
        [leftEnvironment lastStrict,
          { inputOne := closing.2, inputTwo := closing.1,
            graph := .both }] := by
  simp [pairedDirectionChunk, pairedClosingGraph, leftEnvironment]

/-! ## The extra step is a real one-round, zero-open block -/

@[simp] theorem pairedDirectionOpenEnvs_zeroOpen_fromOne
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (move : In₂ × In₁) :
    pairedDirectionOpenEnvs
      (PairedEntryDirection.fromOne row [] move) =
        ([] : List (EnvironmentRound In₁ In₂)) := by
  rfl

@[simp] theorem pairedDirectionOpenEnvs_zeroOpen_fromTwo
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (move : In₁ × In₂) :
    pairedDirectionOpenEnvs
      (PairedEntryDirection.fromTwo row [] move) =
        ([] : List (EnvironmentRound In₁ In₂)) := by
  rfl

@[simp] theorem pairedDirectionBlockLength_zeroOpen_fromOne
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (move : In₂ × In₁) :
    pairedDirectionBlockLength
      (PairedEntryDirection.fromOne row [] move) = 1 := by
  rfl

@[simp] theorem pairedDirectionBlockLength_zeroOpen_fromTwo
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (move : In₁ × In₂) :
    pairedDirectionBlockLength
      (PairedEntryDirection.fromTwo row [] move) = 1 := by
  rfl

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

variable [Inhabited In₁] [Inhabited In₂]

/-- A zero-open direction out of a process-one pending entry carries exactly
the priority of the selected pre-`.both` DPA state. -/
theorem pairedEntryPriority_step_zeroOpen_fromOne
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcOnePairedEntryRep strategy) (minimum : A.State)
    (row : PairedEntryRow) (move : In₂ × In₁) :
    pairedEntryPriority A
        (((PairedStrategyMemory.processOne entry minimum).step (A := A)
          (.fromOne row [] move)).toTreeState) =
      A.priority (match row with
        | .first => entry.code.1
        | .both => entry.code.2) := by
  cases row <;>
    simp [PairedStrategyMemory.step, PairedStrategyMemory.toTreeState,
      pairedEntryPriority, blockMinState, blockEndAndMin,
      ProcOnePairedRightLambda.leftWord,
      ProcOnePairedRightLambda.bothWord, pairedRightWordFrom]

/-- Mirror priority identity for a zero-open direction out of a process-two
pending entry. -/
theorem pairedEntryPriority_step_zeroOpen_fromTwo
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcTwoPairedEntryRep strategy) (minimum : A.State)
    (row : PairedEntryRow) (move : In₁ × In₂) :
    pairedEntryPriority A
        (((PairedStrategyMemory.processTwo entry minimum).step (A := A)
          (.fromTwo row [] move)).toTreeState) =
      A.priority (match row with
        | .first => entry.code.1
        | .both => entry.code.2) := by
  cases row <;>
    simp [PairedStrategyMemory.step, PairedStrategyMemory.toTreeState,
      pairedEntryPriority, blockMinState, blockEndAndMin,
      ProcTwoPairedLeftLambda.rightWord,
      ProcTwoPairedLeftLambda.bothWord, pairedLeftWordFrom]

end DetParityAutomaton

end DistributedSynthesis
