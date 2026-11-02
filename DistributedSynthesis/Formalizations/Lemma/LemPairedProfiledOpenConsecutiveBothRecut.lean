/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenDelayedBoundarySplit

/-!
# Arbitrary consecutive simultaneous rounds in the delayed recut clock

The one-`.both` pair test is not enough: Nature may produce an arbitrarily
long finite run of simultaneous rounds between two strict runs.  This file
builds the exact finite recut for such a run.

There are two candidate segmentations.  The current nonempty strict
direction either closes on its last strict round, leaving every `.both` to a
zero-open direction, or it consumes the first `.both`, leaving the remaining
ones zero-open.  Both candidates flatten to the same physical word.  Their
endpoint orientations differ by one flip, so exactly one has the orientation
of the next strict run.  Only the parity of the finite `.both` run is needed.

This is proof-side recutting.  The two candidates may be retained together
until the next strict round; no process is told a side, leader, row, or bit.
-/

namespace DistributedSynthesis

universe u v

namespace DetParityAutomaton

/-- Proof-side orientation of a compressed paired direction. -/
def pairedEntryDirectionSide
    {In₁ : Type u} {In₂ : Type v} :
    PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
      IndexedLineageSide
  | .fromOne _ _ _ => .right
  | .fromTwo _ _ _ => .left

/-- Replace only the graph of a physical environment round by `.both`. -/
def forceBothRound
    {In₁ : Type u} {In₂ : Type v}
    (round : EnvironmentRound In₁ In₂) : EnvironmentRound In₁ In₂ :=
  { inputOne := round.inputOne
    inputTwo := round.inputTwo
    graph := .both }

/-- On an actual simultaneous round, forcing the graph is the identity. -/
theorem forceBothRound_eq_self
    {In₁ : Type u} {In₂ : Type v}
    (round : EnvironmentRound In₁ In₂) (hboth : round.graph = .both) :
    forceBothRound round = round := by
  cases round with
  | mk inputOne inputTwo graph =>
      cases graph <;> simp [forceBothRound] at hboth ⊢

/-- List form of the literal-physical-round identity. -/
theorem map_forceBothRound_eq_self
    {In₁ : Type u} {In₂ : Type v}
    (rounds : List (EnvironmentRound In₁ In₂))
    (hboth : ∀ round ∈ rounds, round.graph = .both) :
    rounds.map forceBothRound = rounds := by
  induction rounds with
  | nil => rfl
  | cons round rest ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨forceBothRound_eq_self round (hboth round (by simp)),
        ih (fun next hnext ↦ hboth next (by simp [hnext]))⟩

/-- A zero-open compressed direction on the requested proof-side
orientation, carrying the real inputs of one physical round. -/
def pairedZeroOpenRoundDirection
    {In₁ : Type u} {In₂ : Type v}
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (round : EnvironmentRound In₁ In₂) :
    PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
  match side with
  | .right => .fromOne row [] (round.inputTwo, round.inputOne)
  | .left => .fromTwo row [] (round.inputOne, round.inputTwo)

@[simp] theorem pairedEntryDirectionSide_zeroOpenRound
    {In₁ : Type u} {In₂ : Type v}
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (round : EnvironmentRound In₁ In₂) :
    pairedEntryDirectionSide
      (pairedZeroOpenRoundDirection side row round) = side := by
  cases side <;> rfl

/-- Flatten all adjacent chunks of a finite direction path.  The last
direction is lookahead only and contributes no round yet. -/
def pairedFiniteDirectionPathWord
    {In₁ : Type u} {In₂ : Type v} :
    List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) →
      List (EnvironmentRound In₁ In₂)
  | [] => []
  | [_] => []
  | first :: second :: rest =>
      pairedDirectionChunk first second ++
        pairedFiniteDirectionPathWord (second :: rest)

/-- A chain of zero-open directions for all supplied rounds, followed by one
lookahead direction.  The first row is supplied by the preceding strict
direction; every later row is `both`, forcing the preceding zero-open chunk
to have graph `.both`. -/
def pairedZeroOpenPath
    {In₁ : Type u} {In₂ : Type v} :
    IndexedLineageSide → PairedEntryRow →
      List (EnvironmentRound In₁ In₂) →
        EnvironmentRound In₁ In₂ →
          List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
  | side, row, [], lookahead =>
      [pairedZeroOpenRoundDirection side row lookahead]
  | side, row, round :: rest, lookahead =>
      pairedZeroOpenRoundDirection side row round ::
        pairedZeroOpenPath side.other .both rest lookahead

@[simp] theorem pairedZeroOpenPath_ne_nil
    {In₁ : Type u} {In₂ : Type v}
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (rounds : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    pairedZeroOpenPath side row rounds lookahead ≠ [] := by
  cases rounds <;> simp [pairedZeroOpenPath]

@[simp] theorem pairedZeroOpenPath_length
    {In₁ : Type u} {In₂ : Type v}
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (rounds : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    (pairedZeroOpenPath side row rounds lookahead).length =
      rounds.length + 1 := by
  induction rounds generalizing side row with
  | nil => rfl
  | cons round rest ih =>
      simp [pairedZeroOpenPath, ih]

/-- One zero-open direction followed by an opposite `both`-row direction
contributes exactly the real simultaneous round. -/
theorem pairedDirectionChunk_zeroOpen_other_both
    {In₁ : Type u} {In₂ : Type v}
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (round nextRound : EnvironmentRound In₁ In₂) :
    pairedDirectionChunk
        (pairedZeroOpenRoundDirection side row round)
        (pairedZeroOpenRoundDirection side.other .both nextRound) =
      [forceBothRound round] := by
  cases side <;>
    simp [pairedZeroOpenRoundDirection, pairedDirectionChunk,
      pairedClosingGraph, forceBothRound, IndexedLineageSide.other]

/-- Arbitrarily many zero-open flips flatten to exactly the corresponding
physical `.both` rounds. -/
theorem pairedFiniteDirectionPathWord_zeroOpenPath
    {In₁ : Type u} {In₂ : Type v}
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (rounds : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    pairedFiniteDirectionPathWord
        (pairedZeroOpenPath side row rounds lookahead) =
      rounds.map forceBothRound := by
  induction rounds generalizing side row with
  | nil => rfl
  | cons round rest ih =>
      cases rest with
      | nil =>
          simp [pairedZeroOpenPath, pairedFiniteDirectionPathWord,
            pairedDirectionChunk_zeroOpen_other_both]
      | cons next rest =>
          simp only [pairedZeroOpenPath, pairedFiniteDirectionPathWord,
            List.map_cons]
          rw [pairedDirectionChunk_zeroOpen_other_both]
          change
            [forceBothRound round] ++
                pairedFiniteDirectionPathWord
                  (pairedZeroOpenPath side.other .both (next :: rest)
                    lookahead) =
              forceBothRound round :: forceBothRound next ::
                rest.map forceBothRound
          rw [ih]
          rfl

/-- Exact literal version for a genuine finite run of physical simultaneous
rounds. -/
theorem pairedFiniteDirectionPathWord_zeroOpenPath_eq_rounds
    {In₁ : Type u} {In₂ : Type v}
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (rounds : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂)
    (hboth : ∀ round ∈ rounds, round.graph = .both) :
    pairedFiniteDirectionPathWord
        (pairedZeroOpenPath side row rounds lookahead) = rounds := by
  rw [pairedFiniteDirectionPathWord_zeroOpenPath,
    map_forceBothRound_eq_self rounds hboth]

/-- With no preceding strict group, either proof-side initial orientation
parses the same finite simultaneous prefix.  This is the leading/all-`.both`
finite-prefix interface; the paths have `rounds.length` real chunks and one
lookahead direction, so they are productive for arbitrarily long prefixes. -/
theorem pairedLeadingBoth_twoInitialOrientations
    {In₁ : Type u} {In₂ : Type v}
    (rounds : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂)
    (hboth : ∀ round ∈ rounds, round.graph = .both) :
    pairedFiniteDirectionPathWord
          (pairedZeroOpenPath .right .both rounds lookahead) = rounds ∧
      pairedFiniteDirectionPathWord
          (pairedZeroOpenPath .left .both rounds lookahead) = rounds := by
  exact ⟨pairedFiniteDirectionPathWord_zeroOpenPath_eq_rounds .right .both
      rounds lookahead hboth,
    pairedFiniteDirectionPathWord_zeroOpenPath_eq_rounds .left .both rounds
      lookahead hboth⟩

/-- Cons form of the zero-open path theorem, convenient after exposing the
first adjacent chunk of a surrounding strict direction. -/
theorem pairedFiniteDirectionPathWord_zeroOpenCons
    {In₁ : Type u} {In₂ : Type v}
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (first : EnvironmentRound In₁ In₂)
    (rest : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    pairedFiniteDirectionPathWord
        (pairedZeroOpenRoundDirection side row first ::
          pairedZeroOpenPath side.other .both rest lookahead) =
      (first :: rest).map forceBothRound := by
  change pairedFiniteDirectionPathWord
      (pairedZeroOpenPath side row (first :: rest) lookahead) = _
  exact pairedFiniteDirectionPathWord_zeroOpenPath side row (first :: rest)
    lookahead

/-! ## Endpoint parity -/

/-- Side obtained after `n` genuine compressed flips. -/
def pairedRoundSideAfter : IndexedLineageSide → Nat → IndexedLineageSide
  | side, 0 => side
  | side, n + 1 => pairedRoundSideAfter side.other n

@[simp] theorem pairedRoundSideAfter_zero (side : IndexedLineageSide) :
    pairedRoundSideAfter side 0 = side :=
  rfl

@[simp] theorem pairedRoundSideAfter_succ
    (side : IndexedLineageSide) (n : Nat) :
    pairedRoundSideAfter side (n + 1) = pairedRoundSideAfter side.other n :=
  rfl

@[simp] theorem pairedRoundSideAfter_add_two
    (side : IndexedLineageSide) (n : Nat) :
    pairedRoundSideAfter side (n + 2) = pairedRoundSideAfter side n := by
  simp [pairedRoundSideAfter, IndexedLineageSide.other_other]

@[simp] theorem pairedRoundSideAfter_two_mul
    (side : IndexedLineageSide) (k : Nat) :
    pairedRoundSideAfter side (2 * k) = side := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega]
      rw [pairedRoundSideAfter_add_two, ih]

@[simp] theorem pairedRoundSideAfter_two_mul_add_one
    (side : IndexedLineageSide) (k : Nat) :
    pairedRoundSideAfter side (2 * k + 1) = side.other := by
  change pairedRoundSideAfter side.other (2 * k) = side.other
  exact pairedRoundSideAfter_two_mul side.other k

/-- Flipping the initial side flips the endpoint side. -/
theorem pairedRoundSideAfter_other
    (side : IndexedLineageSide) (n : Nat) :
    pairedRoundSideAfter side.other n =
      (pairedRoundSideAfter side n).other := by
  induction n generalizing side with
  | zero => rfl
  | succ n ih =>
      rw [pairedRoundSideAfter_succ, pairedRoundSideAfter_succ,
        IndexedLineageSide.other_other, ih]
      exact (IndexedLineageSide.other_other _).symm

/-- One additional real direction produces the opposite endpoint. -/
theorem pairedRoundSideAfter_succ_eq_other
    (side : IndexedLineageSide) (n : Nat) :
    pairedRoundSideAfter side (n + 1) =
      (pairedRoundSideAfter side n).other := by
  rw [pairedRoundSideAfter_succ, pairedRoundSideAfter_other]

theorem pairedRoundSideAfter_ne_succ
    (side : IndexedLineageSide) (n : Nat) :
    pairedRoundSideAfter side n ≠ pairedRoundSideAfter side (n + 1) := by
  rw [pairedRoundSideAfter_succ_eq_other]
  cases hside : pairedRoundSideAfter side n <;>
    simp [IndexedLineageSide.other]

/-- **Finite resolution law.**  For `m` simultaneous rounds, the
close-on-`.both` candidate ends at `sideAfter side m`; the close-on-strict
candidate has one extra direction and ends at `sideAfter side (m+1)`.
These are the two sides, so exactly one equals the requested next strict
side.  The first disjunct selects close-on-`.both`; the second selects
close-on-strict. -/
theorem pairedBothGapEndpoint_exactlyOne
    (current next : IndexedLineageSide) (m : Nat) :
    (next = pairedRoundSideAfter current m ∧
        next ≠ pairedRoundSideAfter current (m + 1)) ∨
      (next = pairedRoundSideAfter current (m + 1) ∧
        next ≠ pairedRoundSideAfter current m) := by
  have hne := pairedRoundSideAfter_ne_succ current m
  have hchoice : next = pairedRoundSideAfter current m ∨
      next = pairedRoundSideAfter current (m + 1) := by
    rw [pairedRoundSideAfter_succ_eq_other]
    cases hcurrent : pairedRoundSideAfter current m <;>
      cases next <;> simp [IndexedLineageSide.other]
  rcases hchoice with hfirst | hsecond
  · left
    refine ⟨hfirst, ?_⟩
    intro hnext
    exact hne (hfirst.symm.trans hnext)
  · right
    refine ⟨hsecond, ?_⟩
    intro hnext
    exact hne (hnext.symm.trans hsecond)

/-- The lookahead direction after a zero-open path has flipped once for each
consumed simultaneous round. -/
theorem pairedZeroOpenPath_lastSide
    {In₁ : Type u} {In₂ : Type v}
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (rounds : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    (pairedZeroOpenPath side row rounds lookahead).getLast?.map
        pairedEntryDirectionSide =
      some (pairedRoundSideAfter side rounds.length) := by
  induction rounds generalizing side row with
  | nil => simp [pairedZeroOpenPath]
  | cons round rest ih =>
      cases rest with
      | nil =>
          simp [pairedZeroOpenPath, pairedRoundSideAfter]
      | cons next rest =>
          simpa [pairedZeroOpenPath, pairedRoundSideAfter] using
            ih (side := side.other) (row := .both)

/-- Prefixing a zero-open path by its preceding strict direction does not
change the path's lookahead endpoint. -/
theorem pairedConsZeroOpenPath_lastSide
    {In₁ : Type u} {In₂ : Type v}
    (current : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (rounds : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    (current :: pairedZeroOpenPath side row rounds lookahead).getLast?.map
        pairedEntryDirectionSide =
      some (pairedRoundSideAfter side rounds.length) := by
  cases rounds with
  | nil =>
      simp [pairedZeroOpenPath, pairedRoundSideAfter]
  | cons round rest =>
      simpa [pairedZeroOpenPath] using
        pairedZeroOpenPath_lastSide side row (round :: rest) lookahead

/-! ## The two exact finite segmentation candidates -/

/-- Close a right strict group on its last strict round, then give every
simultaneous round to an alternating zero-open direction. -/
def pairedRightGapCloseOnStrictPath
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₂ × In₁))
    (lastStrict : In₂ × In₁)
    (boths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :=
  .fromOne row strictPrefix lastStrict ::
    pairedZeroOpenPath .left .first boths lookahead

/-- Let the right strict group consume the first simultaneous round, then
represent only the remaining simultaneous rounds as zero-open. -/
def pairedRightGapCloseOnBothPath
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₂ × In₁))
    (lastStrict : In₂ × In₁)
    (firstBoth : EnvironmentRound In₁ In₂)
    (restBoths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :=
  .fromOne row (strictPrefix ++ [lastStrict])
      (firstBoth.inputTwo, firstBoth.inputOne) ::
    pairedZeroOpenPath .left .both restBoths lookahead

/-- Endpoint of the close-on-strict candidate: one flip for the strict
direction and one for every simultaneous zero-open direction. -/
theorem pairedRightGapCloseOnStrictPath_lastSide
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₂ × In₁))
    (lastStrict : In₂ × In₁)
    (boths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    (pairedRightGapCloseOnStrictPath row strictPrefix lastStrict boths
        lookahead).getLast?.map pairedEntryDirectionSide =
      some (pairedRoundSideAfter .right (boths.length + 1)) := by
  simpa [pairedRightGapCloseOnStrictPath, pairedRoundSideAfter_succ] using
    pairedConsZeroOpenPath_lastSide
      (PairedEntryDirection.fromOne row strictPrefix lastStrict)
      .left .first boths lookahead

/-- Endpoint of the close-on-first-`.both` candidate.  The first simultaneous
round is already the closing letter of the nonempty strict direction, so the
total number of flips is the total number of simultaneous rounds. -/
theorem pairedRightGapCloseOnBothPath_lastSide
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₂ × In₁))
    (lastStrict : In₂ × In₁)
    (firstBoth : EnvironmentRound In₁ In₂)
    (restBoths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    (pairedRightGapCloseOnBothPath row strictPrefix lastStrict firstBoth
        restBoths lookahead).getLast?.map pairedEntryDirectionSide =
      some (pairedRoundSideAfter .right (restBoths.length + 1)) := by
  simpa [pairedRightGapCloseOnBothPath, pairedRoundSideAfter_succ] using
    pairedConsZeroOpenPath_lastSide
      (PairedEntryDirection.fromOne row (strictPrefix ++ [lastStrict])
        (firstBoth.inputTwo, firstBoth.inputOne))
      .left .both restBoths lookahead

/-- Both right-gap segmentations flatten to the same real strict prefix and
the requested (forced) simultaneous suffix. -/
theorem pairedFiniteDirectionPathWord_right_closeOnStrict
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₂ × In₁))
    (lastStrict : In₂ × In₁)
    (boths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    pairedFiniteDirectionPathWord
        (pairedRightGapCloseOnStrictPath row strictPrefix lastStrict boths
          lookahead) =
      strictPrefix.map rightEnvironment ++ [rightEnvironment lastStrict] ++
        boths.map forceBothRound := by
  cases boths with
  | nil =>
      simp [pairedRightGapCloseOnStrictPath, pairedZeroOpenPath,
        pairedFiniteDirectionPathWord, pairedDirectionChunk,
        pairedZeroOpenRoundDirection, pairedClosingGraph, rightEnvironment]
  | cons first rest =>
      simp only [pairedRightGapCloseOnStrictPath, pairedZeroOpenPath,
        pairedFiniteDirectionPathWord]
      rw [show pairedDirectionChunk
          (.fromOne row strictPrefix lastStrict)
          (pairedZeroOpenRoundDirection .left .first first) =
            strictPrefix.map rightEnvironment ++ [rightEnvironment lastStrict]
        by simp [pairedZeroOpenRoundDirection, pairedDirectionChunk,
          pairedClosingGraph, rightEnvironment]]
      rw [pairedFiniteDirectionPathWord_zeroOpenCons]

theorem pairedFiniteDirectionPathWord_right_closeOnBoth
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₂ × In₁))
    (lastStrict : In₂ × In₁)
    (firstBoth : EnvironmentRound In₁ In₂)
    (restBoths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    pairedFiniteDirectionPathWord
        (pairedRightGapCloseOnBothPath row strictPrefix lastStrict firstBoth
          restBoths lookahead) =
      strictPrefix.map rightEnvironment ++ [rightEnvironment lastStrict] ++
        (firstBoth :: restBoths).map forceBothRound := by
  cases restBoths with
  | nil =>
      simp [pairedRightGapCloseOnBothPath, pairedZeroOpenPath,
        pairedFiniteDirectionPathWord, pairedDirectionChunk,
        pairedZeroOpenRoundDirection, pairedClosingGraph, rightEnvironment,
        forceBothRound, List.map_append, List.append_assoc]
  | cons next rest =>
      simp only [pairedRightGapCloseOnBothPath, pairedZeroOpenPath,
        pairedFiniteDirectionPathWord]
      rw [show pairedDirectionChunk
          (.fromOne row (strictPrefix ++ [lastStrict])
            (firstBoth.inputTwo, firstBoth.inputOne))
          (pairedZeroOpenRoundDirection .left .both next) =
            strictPrefix.map rightEnvironment ++ [rightEnvironment lastStrict,
              forceBothRound firstBoth]
        by simp [pairedZeroOpenRoundDirection, pairedDirectionChunk,
          pairedClosingGraph, rightEnvironment, forceBothRound,
          List.map_append, List.append_assoc]]
      rw [pairedFiniteDirectionPathWord_zeroOpenCons]
      simp [List.append_assoc]

/-! The left mirror is stated separately so downstream recut code needs no
casts or side-dependent input transports. -/

def pairedLeftGapCloseOnStrictPath
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₁ × In₂))
    (lastStrict : In₁ × In₂)
    (boths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :=
  .fromTwo row strictPrefix lastStrict ::
    pairedZeroOpenPath .right .first boths lookahead

def pairedLeftGapCloseOnBothPath
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₁ × In₂))
    (lastStrict : In₁ × In₂)
    (firstBoth : EnvironmentRound In₁ In₂)
    (restBoths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :=
  .fromTwo row (strictPrefix ++ [lastStrict])
      (firstBoth.inputOne, firstBoth.inputTwo) ::
    pairedZeroOpenPath .right .both restBoths lookahead

theorem pairedLeftGapCloseOnStrictPath_lastSide
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₁ × In₂))
    (lastStrict : In₁ × In₂)
    (boths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    (pairedLeftGapCloseOnStrictPath row strictPrefix lastStrict boths
        lookahead).getLast?.map pairedEntryDirectionSide =
      some (pairedRoundSideAfter .left (boths.length + 1)) := by
  simpa [pairedLeftGapCloseOnStrictPath, pairedRoundSideAfter_succ] using
    pairedConsZeroOpenPath_lastSide
      (PairedEntryDirection.fromTwo row strictPrefix lastStrict)
      .right .first boths lookahead

theorem pairedLeftGapCloseOnBothPath_lastSide
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₁ × In₂))
    (lastStrict : In₁ × In₂)
    (firstBoth : EnvironmentRound In₁ In₂)
    (restBoths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    (pairedLeftGapCloseOnBothPath row strictPrefix lastStrict firstBoth
        restBoths lookahead).getLast?.map pairedEntryDirectionSide =
      some (pairedRoundSideAfter .left (restBoths.length + 1)) := by
  simpa [pairedLeftGapCloseOnBothPath, pairedRoundSideAfter_succ] using
    pairedConsZeroOpenPath_lastSide
      (PairedEntryDirection.fromTwo row (strictPrefix ++ [lastStrict])
        (firstBoth.inputOne, firstBoth.inputTwo))
      .right .both restBoths lookahead

theorem pairedFiniteDirectionPathWord_left_closeOnStrict
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₁ × In₂))
    (lastStrict : In₁ × In₂)
    (boths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    pairedFiniteDirectionPathWord
        (pairedLeftGapCloseOnStrictPath row strictPrefix lastStrict boths
          lookahead) =
      strictPrefix.map leftEnvironment ++ [leftEnvironment lastStrict] ++
        boths.map forceBothRound := by
  cases boths with
  | nil =>
      simp [pairedLeftGapCloseOnStrictPath, pairedZeroOpenPath,
        pairedFiniteDirectionPathWord, pairedDirectionChunk,
        pairedZeroOpenRoundDirection, pairedClosingGraph, leftEnvironment]
  | cons first rest =>
      simp only [pairedLeftGapCloseOnStrictPath, pairedZeroOpenPath,
        pairedFiniteDirectionPathWord]
      rw [show pairedDirectionChunk
          (.fromTwo row strictPrefix lastStrict)
          (pairedZeroOpenRoundDirection .right .first first) =
            strictPrefix.map leftEnvironment ++ [leftEnvironment lastStrict]
        by simp [pairedZeroOpenRoundDirection, pairedDirectionChunk,
          pairedClosingGraph, leftEnvironment]]
      rw [pairedFiniteDirectionPathWord_zeroOpenCons]

theorem pairedFiniteDirectionPathWord_left_closeOnBoth
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₁ × In₂))
    (lastStrict : In₁ × In₂)
    (firstBoth : EnvironmentRound In₁ In₂)
    (restBoths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    pairedFiniteDirectionPathWord
        (pairedLeftGapCloseOnBothPath row strictPrefix lastStrict firstBoth
          restBoths lookahead) =
      strictPrefix.map leftEnvironment ++ [leftEnvironment lastStrict] ++
        (firstBoth :: restBoths).map forceBothRound := by
  cases restBoths with
  | nil =>
      simp [pairedLeftGapCloseOnBothPath, pairedZeroOpenPath,
        pairedFiniteDirectionPathWord, pairedDirectionChunk,
        pairedZeroOpenRoundDirection, pairedClosingGraph, leftEnvironment,
        forceBothRound, List.map_append, List.append_assoc]
  | cons next rest =>
      simp only [pairedLeftGapCloseOnBothPath, pairedZeroOpenPath,
        pairedFiniteDirectionPathWord]
      rw [show pairedDirectionChunk
          (.fromTwo row (strictPrefix ++ [lastStrict])
            (firstBoth.inputOne, firstBoth.inputTwo))
          (pairedZeroOpenRoundDirection .right .both next) =
            strictPrefix.map leftEnvironment ++ [leftEnvironment lastStrict,
              forceBothRound firstBoth]
        by simp [pairedZeroOpenRoundDirection, pairedDirectionChunk,
          pairedClosingGraph, leftEnvironment, forceBothRound,
          List.map_append, List.append_assoc]]
      rw [pairedFiniteDirectionPathWord_zeroOpenCons]
      simp [List.append_assoc]

/-! ## One-step global recut resolution -/

/-- A nonempty right strict group, the complete finite simultaneous gap, and
the side of the next strict group determine one exact finite direction path.
When the gap is empty the next strict side must be left; equal adjacent right
groups are then one larger strict group, not a cut. -/
theorem exists_pairedRightGapRecutPath
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₂ × In₁))
    (lastStrict : In₂ × In₁)
    (boths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂)
    (nextSide : IndexedLineageSide)
    (hempty : boths = [] → nextSide = .left)
    (hboth : ∀ round ∈ boths, round.graph = .both) :
    ∃ path : List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)),
      pairedFiniteDirectionPathWord path =
          strictPrefix.map rightEnvironment ++ [rightEnvironment lastStrict] ++
            boths ∧
        path.getLast?.map pairedEntryDirectionSide = some nextSide := by
  cases boths with
  | nil =>
      refine ⟨pairedRightGapCloseOnStrictPath row strictPrefix lastStrict []
          lookahead, ?_, ?_⟩
      · simpa using pairedFiniteDirectionPathWord_right_closeOnStrict row
          strictPrefix lastStrict [] lookahead
      · have hend := pairedRightGapCloseOnStrictPath_lastSide row
          strictPrefix lastStrict [] lookahead
        rw [hempty rfl]
        simpa [pairedRoundSideAfter, IndexedLineageSide.other] using hend
  | cons first rest =>
      rcases pairedBothGapEndpoint_exactlyOne .right nextSide
          (rest.length + 1) with hcloseBoth | hcloseStrict
      · refine ⟨pairedRightGapCloseOnBothPath row strictPrefix lastStrict
            first rest lookahead, ?_, ?_⟩
        · rw [pairedFiniteDirectionPathWord_right_closeOnBoth,
            map_forceBothRound_eq_self (first :: rest) hboth]
        · have hend := pairedRightGapCloseOnBothPath_lastSide row
            strictPrefix lastStrict first rest lookahead
          simpa [hcloseBoth.1] using hend
      · refine ⟨pairedRightGapCloseOnStrictPath row strictPrefix lastStrict
            (first :: rest) lookahead, ?_, ?_⟩
        · rw [pairedFiniteDirectionPathWord_right_closeOnStrict,
            map_forceBothRound_eq_self (first :: rest) hboth]
        · have hend := pairedRightGapCloseOnStrictPath_lastSide row
            strictPrefix lastStrict (first :: rest) lookahead
          simpa [hcloseStrict.1, Nat.add_assoc] using hend

/-- Mirror one-step recut resolution for a left strict group. -/
theorem exists_pairedLeftGapRecutPath
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₁ × In₂))
    (lastStrict : In₁ × In₂)
    (boths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂)
    (nextSide : IndexedLineageSide)
    (hempty : boths = [] → nextSide = .right)
    (hboth : ∀ round ∈ boths, round.graph = .both) :
    ∃ path : List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)),
      pairedFiniteDirectionPathWord path =
          strictPrefix.map leftEnvironment ++ [leftEnvironment lastStrict] ++
            boths ∧
        path.getLast?.map pairedEntryDirectionSide = some nextSide := by
  cases boths with
  | nil =>
      refine ⟨pairedLeftGapCloseOnStrictPath row strictPrefix lastStrict []
          lookahead, ?_, ?_⟩
      · simpa using pairedFiniteDirectionPathWord_left_closeOnStrict row
          strictPrefix lastStrict [] lookahead
      · have hend := pairedLeftGapCloseOnStrictPath_lastSide row
          strictPrefix lastStrict [] lookahead
        rw [hempty rfl]
        simpa [pairedRoundSideAfter, IndexedLineageSide.other] using hend
  | cons first rest =>
      rcases pairedBothGapEndpoint_exactlyOne .left nextSide
          (rest.length + 1) with hcloseBoth | hcloseStrict
      · refine ⟨pairedLeftGapCloseOnBothPath row strictPrefix lastStrict
            first rest lookahead, ?_, ?_⟩
        · rw [pairedFiniteDirectionPathWord_left_closeOnBoth,
            map_forceBothRound_eq_self (first :: rest) hboth]
        · have hend := pairedLeftGapCloseOnBothPath_lastSide row
            strictPrefix lastStrict first rest lookahead
          simpa [hcloseBoth.1] using hend
      · refine ⟨pairedLeftGapCloseOnStrictPath row strictPrefix lastStrict
            (first :: rest) lookahead, ?_, ?_⟩
        · rw [pairedFiniteDirectionPathWord_left_closeOnStrict,
            map_forceBothRound_eq_self (first :: rest) hboth]
        · have hend := pairedLeftGapCloseOnStrictPath_lastSide row
            strictPrefix lastStrict (first :: rest) lookahead
          simpa [hcloseStrict.1, Nat.add_assoc] using hend

end DetParityAutomaton

end DistributedSynthesis
