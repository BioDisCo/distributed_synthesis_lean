/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenPolicyAlignedEpochPriority

/-!
# A literal boundary bounce costs a real round

The paired-entry automaton flips orientation at every compatible memory step.
It is tempting to repair two consecutive physical epochs with the same closing
side by inserting an extra `.both`-row step.  This file checks that proposal
against the already proved branch flattener.

An empty-open-part step is perfectly meaningful: it represents exactly one
closing round, and its stored priority is the priority at the entry of that
one-round block.  But it is not an administrative zero-time transition.
Every paired direction contributes `past.length + 1` literal physical rounds.
Consequently inserting any extra compatible direction strictly lengthens the
flattened word.  In particular one physical `.both` round cannot realize two
successive paired-memory/code flips.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-! ## Exact physical-word obstruction -/

/-- In the process-one orientation, choosing `.both` for the intermediate
row and again for the following row makes both closes literal simultaneous
rounds.  With the same move used for the bounce, the physical closing round
is duplicated, not shared by the two code steps. -/
theorem pairedFromOne_bothBounce_duplicatesClosingRound
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) (afterPast : List (In₂ × In₁))
    (afterMove : In₂ × In₁) :
    pairedDirectionChunk (.fromOne row past move)
          (.fromTwo .both [] (move.2, move.1)) ++
        pairedDirectionChunk (.fromTwo .both [] (move.2, move.1))
          (.fromOne .both afterPast afterMove) =
      past.map rightEnvironment ++
        [{ inputOne := move.2, inputTwo := move.1, graph := .both },
          { inputOne := move.2, inputTwo := move.1, graph := .both }] := by
  simp [pairedDirectionChunk, pairedClosingGraph]

/-- Mirror of `pairedFromOne_bothBounce_duplicatesClosingRound`. -/
theorem pairedFromTwo_bothBounce_duplicatesClosingRound
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) (afterPast : List (In₁ × In₂))
    (afterMove : In₁ × In₂) :
    pairedDirectionChunk (.fromTwo row past move)
          (.fromOne .both [] (move.2, move.1)) ++
        pairedDirectionChunk (.fromOne .both [] (move.2, move.1))
          (.fromTwo .both afterPast afterMove) =
      past.map leftEnvironment ++
        [{ inputOne := move.1, inputTwo := move.2, graph := .both },
          { inputOne := move.1, inputTwo := move.2, graph := .both }] := by
  simp [pairedDirectionChunk, pairedClosingGraph]

/-- Inserting one additional paired direction cannot preserve the literal
flattened physical chunk.  The result is independent of rows and graphs:
the extra direction always contributes at least one real round. -/
theorem pairedDirectionChunk_append_extra_ne_chunk
    (current extra next originalNext :
      PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    pairedDirectionChunk current extra ++ pairedDirectionChunk extra next ≠
      pairedDirectionChunk current originalNext := by
  intro heq
  have hlength := congrArg List.length heq
  simp only [List.length_append, pairedDirectionChunk_length] at hlength
  have hpositive := pairedDirectionBlockLength_pos extra
  omega

/-- Two paired steps cannot be hosted by one literal physical round.  This is
the special shape needed by the proposed boundary bounce. -/
theorem pairedDirectionChunk_pair_ne_singleton
    (first second third :
      PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (round : EnvironmentRound In₁ In₂) :
    pairedDirectionChunk first second ++ pairedDirectionChunk second third ≠
      [round] := by
  intro heq
  have hlength := congrArg List.length heq
  simp only [List.length_append, pairedDirectionChunk_length,
    List.length_singleton] at hlength
  have hfirst := pairedDirectionBlockLength_pos first
  have hsecond := pairedDirectionBlockLength_pos second
  omega

/-- An empty homogeneous prefix still leaves the compulsory closing round. -/
theorem pairedDirectionBlockLength_eq_one_of_openEnvs_nil
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hopen : pairedDirectionOpenEnvs direction = []) :
    pairedDirectionBlockLength direction = 1 := by
  have hlength := pairedDirectionOpenEnvs_length direction
  rw [hopen] at hlength
  simpa using hlength.symm

/-! ## Exact priority of the one-round step -/

namespace PairedStrategyMemory

variable {A}
variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable [Inhabited In₁] [Inhabited In₂]
variable [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- For an empty-open-part (hence one-round) paired step, the stored block
minimum is exactly the priority of the selected entry state.  The closing
round itself is the delayed fresh state and belongs to the following cut. -/
theorem pairedEntryPriority_emptyStep_eq_selectedEntryPriority
    (memory : PairedStrategyMemory A strategy)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hcompatible : DirectionCompatible (A := A) memory direction)
    (hopen : pairedDirectionOpenEnvs direction = []) :
    pairedEntryPriority A ((memory.step (A := A) direction).toTreeState) =
      A.priority
        (entryState (A := A) (selectedHistory memory direction)) := by
  have hwordLength := selectedBlockWord_length memory direction hcompatible
  rw [hopen] at hwordLength
  have hwordLengthZero : (selectedBlockWord memory direction).length = 0 := by
    simpa using hwordLength
  have hword : selectedBlockWord memory direction = [] :=
    List.eq_nil_of_length_eq_zero hwordLengthZero
  rw [pairedEntryPriority_step_eq_selectedBlockMin A strategy memory direction
    hcompatible, hword]
  rfl

/-- The preceding identity is exactly the `cutBlockMin` of a literal
one-round cut.  Thus the priority bookkeeping itself works; the obstruction
is that a second flip would require a second physical letter. -/
theorem pairedEntryPriority_emptyStep_eq_oneRoundCutBlockMin
    (memory : PairedStrategyMemory A strategy)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hcompatible : DirectionCompatible (A := A) memory direction)
    (hopen : pairedDirectionOpenEnvs direction = [])
    (continuation : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)) :
    pairedEntryPriority A ((memory.step (A := A) direction).toTreeState) =
      cutBlockMin
        (fun n => A.priority
          (A.runFrom
            (entryState (A := A) (selectedHistory memory direction))
            continuation n))
        (fun n => n) 0 := by
  rw [pairedEntryPriority_emptyStep_eq_selectedEntryPriority (A := A) memory
    direction hcompatible hopen]
  change A.priority
      (entryState (A := A) (selectedHistory memory direction)) =
    A.priority
      (A.runFrom
        (entryState (A := A) (selectedHistory memory direction))
        continuation 0)
  rfl

end PairedStrategyMemory

end DetParityAutomaton

end DistributedSynthesis
