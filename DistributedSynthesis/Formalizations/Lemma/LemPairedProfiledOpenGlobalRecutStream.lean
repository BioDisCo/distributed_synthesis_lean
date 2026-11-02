/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenConsecutiveBothRecut

/-!
# Global concatenation of finite paired-direction recuts

The finite gap lemmas produce paths with one lookahead direction.  This file
contains the purely mathematical gluing layer: a productive stream of such
paths, whose lookahead agrees with the first direction of the next path,
determines one infinite paired branch.  At the segment cuts the branch reads
the original finite paths literally, so its flattened environment is the
concatenation of their exact physical words.

The construction is proof-side only.  In particular it neither exposes nor
assumes a runtime strict-leader/orientation signal.  Eventual one-sided tails
are deliberately outside the `body_ne_nil` productivity interface and are
handled by the separate trapped-tail case.

This module proves only the physical recut and proof-side orientation clock.
It does **not** choose a code lineage or identify target slots across root
deduplication.  The fixed-lineage/priority coupling is a separate downstream
obligation; per-segment existence of some target slot is not used here.
-/

namespace DistributedSynthesis

universe u v

namespace DetParityAutomaton

/-! ## Generic finite windows of an infinite paired branch -/

/-- Chunks `start, ..., start + count - 1`, concatenated in order. -/
def pairedBranchChunkRange
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat → PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (start : Nat) : Nat → List (EnvironmentRound In₁ In₂)
  | 0 => []
  | count + 1 => pairedBranchChunkRange branch start count ++
      pairedBranchChunk branch (start + count)

@[simp] theorem pairedBranchChunkRange_zero
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat → PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (start : Nat) :
    pairedBranchChunkRange branch start 0 = [] :=
  rfl

@[simp] theorem pairedBranchChunkRange_succ
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat → PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (start count : Nat) :
    pairedBranchChunkRange branch start (count + 1) =
      pairedBranchChunkRange branch start count ++
        pairedBranchChunk branch (start + count) :=
  rfl

/-- Adding a final lookahead node appends exactly the last adjacent chunk. -/
theorem pairedFiniteDirectionPathWord_append_singleton_of_getLast?
    {In₁ : Type u} {In₂ : Type v}
    (path : List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)))
    (last next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hlast : path.getLast? = some last) :
    pairedFiniteDirectionPathWord (path ++ [next]) =
      pairedFiniteDirectionPathWord path ++ pairedDirectionChunk last next := by
  induction path with
  | nil => simp at hlast
  | cons first rest ih =>
      cases rest with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          subst last
          simp [pairedFiniteDirectionPathWord]
      | cons second tail =>
          have htail : (second :: tail).getLast? = some last := by
            simpa using hlast
          change pairedDirectionChunk first second ++
              pairedFiniteDirectionPathWord ((second :: tail) ++ [next]) =
            pairedDirectionChunk first second ++
                pairedFiniteDirectionPathWord (second :: tail) ++
              pairedDirectionChunk last next
          rw [ih htail]
          simp [List.append_assoc]

/-- The finite word of `count + 1` consecutive branch nodes is precisely the
concatenation of the corresponding `count` chunks. -/
theorem pairedFiniteDirectionPathWord_ofFn_eq_chunkRange
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat → PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (start count : Nat) :
    pairedFiniteDirectionPathWord
        (List.ofFn (fun i : Fin (count + 1) ↦ branch (start + i))) =
      pairedBranchChunkRange branch start count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega]
      rw [List.ofFn_succ']
      have hprefix :
          List.ofFn
              (fun i : Fin (count + 1) ↦
                branch (start + (Fin.castSucc i : Nat))) =
            List.ofFn
              (fun i : Fin (count + 1) ↦ branch (start + i)) := by
        apply List.ofFn_congr rfl
      rw [hprefix]
      simp only [List.concat_eq_append]
      change pairedFiniteDirectionPathWord
          (List.ofFn (fun i : Fin (count + 1) ↦ branch (start + i)) ++
            [branch (start + (count + 1))]) = _
      have hlast :
          (List.ofFn (fun i : Fin (count + 1) ↦ branch (start + i))).getLast? =
            some (branch (start + count)) := by
        rw [List.ofFn_succ']
        simp
      rw [pairedFiniteDirectionPathWord_append_singleton_of_getLast?
        _ _ _ hlast]
      rw [ih]
      change pairedBranchChunkRange branch start count ++
          pairedDirectionChunk (branch (start + count))
            (branch (start + (count + 1))) = _
      simp only [pairedBranchChunkRange_succ, pairedBranchChunk]
      congr 2

/-- Successive global branch cuts over a finite range differ by exactly the
corresponding chunk range. -/
theorem omegaPrefix_pairedBranchCuts_add
    {In₁ : Type u} {In₂ : Type v}
    (branch : Nat → PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (start count : Nat) :
    omegaPrefix (pairedBranchEnvironment branch)
        (pairedBranchCuts branch (start + count)) =
      omegaPrefix (pairedBranchEnvironment branch)
          (pairedBranchCuts branch start) ++
        pairedBranchChunkRange branch start count := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [show start + (count + 1) = (start + count) + 1 by omega]
      rw [omegaPrefix_pairedBranchCuts_succ, ih]
      simp [pairedBranchChunkRange, List.append_assoc]

/-- Equality of prefixes along any strictly increasing sequence of cuts
determines an infinite word pointwise. -/
theorem omegaWord_eq_of_prefix_eq_at_strictCuts
    {Move : Type*} (left right : Nat → Move) (cuts : Nat → Nat)
    (hcuts : StrictMono cuts)
    (hprefix : ∀ k, omegaPrefix left (cuts k) =
      omegaPrefix right (cuts k)) :
    left = right := by
  funext n
  have hn : n < cuts (n + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (le_cuts hcuts (n + 1))
  have hget := congrArg (fun word ↦ word[n]?) (hprefix (n + 1))
  simpa [omegaPrefix, hn] using hget

/-- One finite recut segment.  `body` contains precisely the directions whose
chunks are contributed by this segment; `endpoint` is the lookahead direction
shared with the following segment. -/
structure PairedFiniteRecutSegment (In₁ : Type u) (In₂ : Type v) where
  body : List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
  endpoint : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)
  body_ne_nil : body ≠ []
  physicalWord : List (EnvironmentRound In₁ In₂)
  exact_word : pairedFiniteDirectionPathWord (body ++ [endpoint]) = physicalWord

/-- A productive sequence of finite recuts.  The only coherence law is the
literal overlap of the current lookahead with the head of the next body. -/
structure PairedFiniteRecutStream (In₁ : Type u) (In₂ : Type v) where
  segment : Nat → PairedFiniteRecutSegment In₁ In₂
  overlap : ∀ n,
    (segment (n + 1)).body.head? = some (segment n).endpoint

/-- Adjacent directions in a finite path have opposite proof-side
orientations. -/
def PairedDirectionPathSideAlternates
    {In₁ : Type u} {In₂ : Type v}
    (path : List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂))) : Prop :=
  path.IsChain (fun current next ↦
    pairedEntryDirectionSide next =
      (pairedEntryDirectionSide current).other)

@[simp] theorem pairedZeroOpenPath_headSide
    {In₁ : Type u} {In₂ : Type v}
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (rounds : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    (pairedZeroOpenPath side row rounds lookahead).head?.map
        pairedEntryDirectionSide = some side := by
  cases rounds <;> cases side <;>
    simp [pairedZeroOpenPath, pairedZeroOpenRoundDirection,
      pairedEntryDirectionSide]

/-- Zero-open paths alternate their proof-side orientation by construction. -/
theorem pairedZeroOpenPath_sideAlternates
    {In₁ : Type u} {In₂ : Type v}
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (rounds : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    PairedDirectionPathSideAlternates
      (pairedZeroOpenPath side row rounds lookahead) := by
  induction rounds generalizing side row with
  | nil =>
      simp [pairedZeroOpenPath, PairedDirectionPathSideAlternates]
  | cons round rest ih =>
      simp only [pairedZeroOpenPath]
      apply List.IsChain.cons
      · exact ih (side := side.other) (row := .both)
      · intro next hnext
        have hhead := pairedZeroOpenPath_headSide side.other .both rest
          lookahead
        rw [hnext] at hhead
        cases side <;>
          simpa [pairedZeroOpenRoundDirection, pairedEntryDirectionSide,
            IndexedLineageSide.other] using hhead

/-- Prefix a zero-open path by the opposite-side strict direction. -/
theorem pairedConsZeroOpenPath_sideAlternates
    {In₁ : Type u} {In₂ : Type v}
    (current : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (rounds : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂)
    (hcurrent : pairedEntryDirectionSide current = side.other) :
    PairedDirectionPathSideAlternates
      (current :: pairedZeroOpenPath side row rounds lookahead) := by
  apply List.IsChain.cons
  · exact pairedZeroOpenPath_sideAlternates side row rounds lookahead
  · intro next hnext
    have hhead := pairedZeroOpenPath_headSide side row rounds lookahead
    rw [hnext] at hhead
    have hnextSide : pairedEntryDirectionSide next = side := by
      simpa using hhead
    calc
      pairedEntryDirectionSide next = side := hnextSide
      _ = (pairedEntryDirectionSide current).other := by
        rw [hcurrent, IndexedLineageSide.other_other]

/-- Row component of a paired direction. -/
def pairedEntryDirectionRow
    {In₁ : Type u} {In₂ : Type v} :
    PairedEntryDirection (In₁ := In₁) (In₂ := In₂) → PairedEntryRow
  | .fromOne row _ _ => row
  | .fromTwo row _ _ => row

/-- The part of a lookahead direction visible to the preceding chunk. -/
def pairedEntryDirectionSignature
    {In₁ : Type u} {In₂ : Type v}
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    IndexedLineageSide × PairedEntryRow :=
  (pairedEntryDirectionSide direction, pairedEntryDirectionRow direction)

/-- A nonempty simultaneous gap makes the following strict direction a
`both`-row child; an empty gap makes it a `first`-row child. -/
def pairedGapNextRow
    {In₁ : Type u} {In₂ : Type v} :
    List (EnvironmentRound In₁ In₂) → PairedEntryRow
  | [] => .first
  | _ :: _ => .both

/-- Endpoint row of a zero-open path.  Once at least one simultaneous round
is consumed, every later lookahead carries row `both`. -/
theorem pairedZeroOpenPath_lastRow
    {In₁ : Type u} {In₂ : Type v}
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (rounds : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    (pairedZeroOpenPath side row rounds lookahead).getLast?.map
        pairedEntryDirectionRow =
      some (match rounds with
        | [] => row
        | _ :: _ => .both) := by
  induction rounds generalizing side row with
  | nil =>
      cases side <;>
        simp [pairedZeroOpenPath, pairedZeroOpenRoundDirection,
          pairedEntryDirectionRow]
  | cons round rest ih =>
      cases rest with
      | nil =>
          cases side <;>
            simp [pairedZeroOpenPath, pairedZeroOpenRoundDirection,
              pairedEntryDirectionRow, IndexedLineageSide.other]
      | cons next tail =>
          simpa [pairedZeroOpenPath] using
            ih (side := side.other) (row := .both)

/-- Prefixing the zero-open path by the preceding nonempty strict direction
does not change its endpoint row. -/
theorem pairedConsZeroOpenPath_lastRow
    {In₁ : Type u} {In₂ : Type v}
    (current : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (rounds : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂) :
    (current :: pairedZeroOpenPath side row rounds lookahead).getLast?.map
        pairedEntryDirectionRow =
      some (match rounds with
        | [] => row
        | _ :: _ => .both) := by
  cases rounds with
  | nil =>
      cases side <;>
        simp [pairedZeroOpenPath, pairedZeroOpenRoundDirection,
          pairedEntryDirectionRow]
  | cons first rest =>
      have htail := pairedZeroOpenPath_lastRow side row (first :: rest)
        lookahead
      have hne := pairedZeroOpenPath_ne_nil side row (first :: rest) lookahead
      have hlast :
          (current :: pairedZeroOpenPath side row (first :: rest)
              lookahead).getLast? =
            (pairedZeroOpenPath side row (first :: rest) lookahead).getLast? := by
        simpa using List.getLast?_append_of_ne_nil [current] hne
      rw [hlast]
      exact htail

/-- Pair two separately established endpoint components into the combined
side/row signature. -/
theorem Option.map_pairedEntryDirectionSignature_eq_some
    {In₁ : Type u} {In₂ : Type v}
    (direction : Option
      (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)))
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (hside : direction.map pairedEntryDirectionSide = some side)
    (hrow : direction.map pairedEntryDirectionRow = some row) :
    direction.map pairedEntryDirectionSignature = some (side, row) := by
  cases direction <;>
    simp_all [pairedEntryDirectionSignature]

/-- A chunk observes only the side and row of its lookahead direction; the
lookahead's past and move belong to the following chunk. -/
theorem pairedDirectionChunk_eq_of_nextSignature_eq
    {In₁ : Type u} {In₂ : Type v}
    (current oldNext newNext :
      PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hsignature : pairedEntryDirectionSignature oldNext =
      pairedEntryDirectionSignature newNext) :
    pairedDirectionChunk current oldNext =
      pairedDirectionChunk current newNext := by
  cases current <;> cases oldNext <;> cases newNext <;>
    simp_all [pairedEntryDirectionSignature, pairedEntryDirectionSide,
      pairedEntryDirectionRow, pairedDirectionChunk, pairedClosingGraph] <;>
    subst_vars <;> cases_type PairedEntryRow <;>
      cases_type PairedEntryRow <;> rfl

/-- A nonempty finite path may replace its lookahead by any direction with
the same side and row, without changing its physical word. -/
theorem pairedFiniteDirectionPathWord_replace_endpoint
    {In₁ : Type u} {In₂ : Type v}
    (body : List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)))
    (oldEndpoint newEndpoint :
      PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hbody : body ≠ [])
    (hsignature : pairedEntryDirectionSignature oldEndpoint =
      pairedEntryDirectionSignature newEndpoint) :
    pairedFiniteDirectionPathWord (body ++ [newEndpoint]) =
      pairedFiniteDirectionPathWord (body ++ [oldEndpoint]) := by
  let last := body.getLast hbody
  have hlast : body.getLast? = some last :=
    List.getLast?_eq_getLast_of_ne_nil hbody
  rw [pairedFiniteDirectionPathWord_append_singleton_of_getLast?
    body last newEndpoint hlast]
  rw [pairedFiniteDirectionPathWord_append_singleton_of_getLast?
    body last oldEndpoint hlast]
  rw [pairedDirectionChunk_eq_of_nextSignature_eq last oldEndpoint newEndpoint
    hsignature]

/-- Replacing the endpoint by a direction with the same proof-side preserves
side alternation along a nonempty body. -/
theorem pairedDirectionPathSideAlternates_replace_endpoint
    {In₁ : Type u} {In₂ : Type v}
    (body : List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)))
    (oldEndpoint newEndpoint :
      PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hbody : body ≠ [])
    (hside : pairedEntryDirectionSide oldEndpoint =
      pairedEntryDirectionSide newEndpoint)
    (halternates : PairedDirectionPathSideAlternates
      (body ++ [oldEndpoint])) :
    PairedDirectionPathSideAlternates (body ++ [newEndpoint]) := by
  induction body with
  | nil => exact (hbody rfl).elim
  | cons first rest ih =>
      cases rest with
      | nil =>
          simp only [List.cons_append, List.nil_append,
            PairedDirectionPathSideAlternates] at halternates ⊢
          have hrel := (List.isChain_cons.mp halternates).1 oldEndpoint (by simp)
          apply List.IsChain.cons
          · simp
          · intro next hnext
            have hnextEq : next = newEndpoint := by
              symm
              simpa using hnext
            subst next
            rw [← hside]
            exact hrel
      | cons second tail =>
          simp only [List.cons_append]
          apply List.IsChain.cons
          · exact ih (List.cons_ne_nil _ _) halternates.tail
          · exact (List.isChain_cons.mp halternates).1

/-- Signature equality is enough for endpoint replacement to preserve side
alternation. -/
theorem pairedDirectionPathSideAlternates_replace_endpoint_of_signature
    {In₁ : Type u} {In₂ : Type v}
    (body : List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)))
    (oldEndpoint newEndpoint :
      PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hbody : body ≠ [])
    (hsignature : pairedEntryDirectionSignature oldEndpoint =
      pairedEntryDirectionSignature newEndpoint)
    (halternates : PairedDirectionPathSideAlternates
      (body ++ [oldEndpoint])) :
    PairedDirectionPathSideAlternates (body ++ [newEndpoint]) := by
  apply pairedDirectionPathSideAlternates_replace_endpoint body oldEndpoint
    newEndpoint hbody
  · have hside := congrArg Prod.fst hsignature
    simpa [pairedEntryDirectionSignature] using hside
  · exact halternates

/-! ## Gluing a supplied productive signed-gap decomposition -/

/-- A concrete finite witness for one signed recut gap. -/
structure PairedSignedRecutWitness
    (In₁ : Type u) (In₂ : Type v)
    (currentSignature nextSignature : IndexedLineageSide × PairedEntryRow)
    (physicalWord : List (EnvironmentRound In₁ In₂)) where
  first : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)
  rest : List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
  oldEndpoint : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)
  first_signature : pairedEntryDirectionSignature first = currentSignature
  endpoint_signature : pairedEntryDirectionSignature oldEndpoint = nextSignature
  side_alternates : PairedDirectionPathSideAlternates
    ((first :: rest) ++ [oldEndpoint])
  exact_word : pairedFiniteDirectionPathWord
      ((first :: rest) ++ [oldEndpoint]) = physicalWord

/-- Any exact finite path with at least one contributed chunk can be put in
`PairedSignedRecutWitness` form by separating its final lookahead. -/
theorem nonempty_pairedSignedRecutWitness_of_path
    {In₁ : Type u} {In₂ : Type v}
    (currentSignature nextSignature : IndexedLineageSide × PairedEntryRow)
    (physicalWord : List (EnvironmentRound In₁ In₂))
    (path : List (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)))
    (hlength : 2 ≤ path.length)
    (hfirst : path.head?.map pairedEntryDirectionSignature =
      some currentSignature)
    (hlast : path.getLast?.map pairedEntryDirectionSignature =
      some nextSignature)
    (halternates : PairedDirectionPathSideAlternates path)
    (hexact : pairedFiniteDirectionPathWord path = physicalWord) :
    Nonempty (PairedSignedRecutWitness In₁ In₂ currentSignature
      nextSignature physicalWord) := by
  cases path with
  | nil => simp at hlength
  | cons first rest =>
      cases rest with
      | nil => simp at hlength
      | cons second tail =>
          let path : List
              (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :=
            first :: second :: tail
          have hpath : path ≠ [] := by simp [path]
          let oldEndpoint := path.getLast hpath
          have hold : path.getLast? = some oldEndpoint :=
            List.getLast?_eq_getLast_of_ne_nil hpath
          have hfirstSignature : pairedEntryDirectionSignature first =
              currentSignature := by
            simpa [path] using hfirst
          have holdSignature : pairedEntryDirectionSignature oldEndpoint =
              nextSignature := by
            rw [hold] at hlast
            simpa using hlast
          have hdrop : first :: path.dropLast.tail = path.dropLast := by
            cases tail <;> simp [path]
          have holdMem : oldEndpoint ∈ path.getLast? := by
            rw [hold]
            simp
          have hdecomp : path.dropLast ++ [oldEndpoint] = path :=
            List.dropLast_append_getLast? oldEndpoint holdMem
          refine ⟨{
            first := first
            rest := path.dropLast.tail
            oldEndpoint := oldEndpoint
            first_signature := hfirstSignature
            endpoint_signature := holdSignature
            side_alternates := by
              rw [hdrop, hdecomp]
              exact halternates
            exact_word := ?_ }⟩
          calc
            pairedFiniteDirectionPathWord
                ((first :: path.dropLast.tail) ++ [oldEndpoint]) =
              pairedFiniteDirectionPathWord
                (path.dropLast ++ [oldEndpoint]) := by rw [hdrop]
            _ = pairedFiniteDirectionPathWord path := by rw [hdecomp]
            _ = physicalWord := hexact

/-- One gap of a productive strict-gap decomposition, retaining only the two
boundary signatures and its literal physical word. -/
structure PairedSignedFiniteRecut (In₁ : Type u) (In₂ : Type v) where
  currentSignature : IndexedLineageSide × PairedEntryRow
  nextSignature : IndexedLineageSide × PairedEntryRow
  physicalWord : List (EnvironmentRound In₁ In₂)
  realization : Nonempty
    (PairedSignedRecutWitness In₁ In₂ currentSignature nextSignature
      physicalWord)

/-- Concrete signed recut for a nonempty right-strict group followed by its
complete finite simultaneous gap.  This is the signature-strengthened form
of `exists_pairedRightGapRecutPath`. -/
theorem nonempty_pairedSignedRightGapRecutWitness
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₂ × In₁))
    (lastStrict : In₂ × In₁)
    (boths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂)
    (nextSide : IndexedLineageSide)
    (hempty : boths = [] → nextSide = .left)
    (hboth : ∀ round ∈ boths, round.graph = .both) :
    Nonempty (PairedSignedRecutWitness In₁ In₂ (.right, row)
      (nextSide, pairedGapNextRow boths)
      (strictPrefix.map rightEnvironment ++ [rightEnvironment lastStrict] ++
        boths)) := by
    cases boths with
    | nil =>
        let path := pairedRightGapCloseOnStrictPath row strictPrefix
          lastStrict [] lookahead
        apply nonempty_pairedSignedRecutWitness_of_path
          (.right, row) (nextSide, pairedGapNextRow [])
          (strictPrefix.map rightEnvironment ++ [rightEnvironment lastStrict] ++ [])
          path
        · simp [path, pairedRightGapCloseOnStrictPath,
            pairedZeroOpenPath]
        · simp [path, pairedRightGapCloseOnStrictPath,
            pairedEntryDirectionSignature, pairedEntryDirectionSide,
            pairedEntryDirectionRow]
        · have hside := pairedRightGapCloseOnStrictPath_lastSide row
            strictPrefix lastStrict [] lookahead
          have hrow := pairedConsZeroOpenPath_lastRow
            (PairedEntryDirection.fromOne row strictPrefix lastStrict)
            .left .first [] lookahead
          apply Option.map_pairedEntryDirectionSignature_eq_some
            path.getLast? nextSide (pairedGapNextRow [])
          · rw [hempty rfl]
            simpa [path, pairedRoundSideAfter,
              IndexedLineageSide.other] using hside
          · simpa [path, pairedRightGapCloseOnStrictPath,
              pairedGapNextRow] using hrow
        · simpa [path, pairedRightGapCloseOnStrictPath] using
            pairedConsZeroOpenPath_sideAlternates
              (PairedEntryDirection.fromOne row strictPrefix lastStrict)
              .left .first [] lookahead rfl
        · simpa [path] using
            pairedFiniteDirectionPathWord_right_closeOnStrict row
              strictPrefix lastStrict [] lookahead
    | cons first rest =>
        rcases pairedBothGapEndpoint_exactlyOne .right nextSide
            (rest.length + 1) with hcloseBoth | hcloseStrict
        · let path := pairedRightGapCloseOnBothPath row strictPrefix
            lastStrict first rest lookahead
          apply nonempty_pairedSignedRecutWitness_of_path
            (.right, row) (nextSide, pairedGapNextRow (first :: rest))
            (strictPrefix.map rightEnvironment ++
              [rightEnvironment lastStrict] ++ (first :: rest)) path
          · simp [path, pairedRightGapCloseOnBothPath,
              pairedZeroOpenPath_length]
          · simp [path, pairedRightGapCloseOnBothPath,
              pairedEntryDirectionSignature, pairedEntryDirectionSide,
              pairedEntryDirectionRow]
          · have hside := pairedRightGapCloseOnBothPath_lastSide row
              strictPrefix lastStrict first rest lookahead
            have hrow := pairedConsZeroOpenPath_lastRow
              (PairedEntryDirection.fromOne row
                (strictPrefix ++ [lastStrict])
                (first.inputTwo, first.inputOne))
              .left .both rest lookahead
            apply Option.map_pairedEntryDirectionSignature_eq_some
              path.getLast? nextSide (pairedGapNextRow (first :: rest))
            · simpa [path, hcloseBoth.1] using hside
            · cases rest <;>
                simpa [path, pairedRightGapCloseOnBothPath,
                  pairedGapNextRow] using hrow
          · simpa [path, pairedRightGapCloseOnBothPath] using
              pairedConsZeroOpenPath_sideAlternates
                (PairedEntryDirection.fromOne row
                  (strictPrefix ++ [lastStrict])
                  (first.inputTwo, first.inputOne))
                .left .both rest lookahead rfl
          · rw [show pairedFiniteDirectionPathWord path =
                strictPrefix.map rightEnvironment ++
                  [rightEnvironment lastStrict] ++
                    (first :: rest).map forceBothRound by
                exact pairedFiniteDirectionPathWord_right_closeOnBoth row
                  strictPrefix lastStrict first rest lookahead]
            rw [map_forceBothRound_eq_self (first :: rest) hboth]
        · let path := pairedRightGapCloseOnStrictPath row strictPrefix
            lastStrict (first :: rest) lookahead
          apply nonempty_pairedSignedRecutWitness_of_path
            (.right, row) (nextSide, pairedGapNextRow (first :: rest))
            (strictPrefix.map rightEnvironment ++
              [rightEnvironment lastStrict] ++ (first :: rest)) path
          · simp [path, pairedRightGapCloseOnStrictPath,
              pairedZeroOpenPath_length]
          · simp [path, pairedRightGapCloseOnStrictPath,
              pairedEntryDirectionSignature, pairedEntryDirectionSide,
              pairedEntryDirectionRow]
          · have hside := pairedRightGapCloseOnStrictPath_lastSide row
              strictPrefix lastStrict (first :: rest) lookahead
            have hrow := pairedConsZeroOpenPath_lastRow
              (PairedEntryDirection.fromOne row strictPrefix lastStrict)
              .left .first (first :: rest) lookahead
            apply Option.map_pairedEntryDirectionSignature_eq_some
              path.getLast? nextSide (pairedGapNextRow (first :: rest))
            · simpa [path, hcloseStrict.1, Nat.add_assoc] using hside
            · simpa [path, pairedRightGapCloseOnStrictPath,
                pairedGapNextRow] using hrow
          · simpa [path, pairedRightGapCloseOnStrictPath] using
              pairedConsZeroOpenPath_sideAlternates
                (PairedEntryDirection.fromOne row strictPrefix lastStrict)
                .left .first (first :: rest) lookahead rfl
          · rw [show pairedFiniteDirectionPathWord path =
                strictPrefix.map rightEnvironment ++
                  [rightEnvironment lastStrict] ++
                    (first :: rest).map forceBothRound by
                exact pairedFiniteDirectionPathWord_right_closeOnStrict row
                  strictPrefix lastStrict (first :: rest) lookahead]
            rw [map_forceBothRound_eq_self (first :: rest) hboth]

/-- Pack the concrete right-gap witness as one supplied signed recut. -/
def pairedSignedRightGapRecut
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₂ × In₁))
    (lastStrict : In₂ × In₁)
    (boths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂)
    (nextSide : IndexedLineageSide)
    (hempty : boths = [] → nextSide = .left)
    (hboth : ∀ round ∈ boths, round.graph = .both) :
    PairedSignedFiniteRecut In₁ In₂ where
  currentSignature := (.right, row)
  nextSignature := (nextSide, pairedGapNextRow boths)
  physicalWord := strictPrefix.map rightEnvironment ++
    [rightEnvironment lastStrict] ++ boths
  realization := nonempty_pairedSignedRightGapRecutWitness row strictPrefix
    lastStrict boths lookahead nextSide hempty hboth

/-- Left mirror of the concrete signed right-gap witness. -/
theorem nonempty_pairedSignedLeftGapRecutWitness
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₁ × In₂))
    (lastStrict : In₁ × In₂)
    (boths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂)
    (nextSide : IndexedLineageSide)
    (hempty : boths = [] → nextSide = .right)
    (hboth : ∀ round ∈ boths, round.graph = .both) :
    Nonempty (PairedSignedRecutWitness In₁ In₂ (.left, row)
      (nextSide, pairedGapNextRow boths)
      (strictPrefix.map leftEnvironment ++ [leftEnvironment lastStrict] ++
        boths)) := by
  cases boths with
  | nil =>
      let path := pairedLeftGapCloseOnStrictPath row strictPrefix
        lastStrict [] lookahead
      apply nonempty_pairedSignedRecutWitness_of_path
        (.left, row) (nextSide, pairedGapNextRow [])
        (strictPrefix.map leftEnvironment ++ [leftEnvironment lastStrict] ++ [])
        path
      · simp [path, pairedLeftGapCloseOnStrictPath,
          pairedZeroOpenPath]
      · simp [path, pairedLeftGapCloseOnStrictPath,
          pairedEntryDirectionSignature, pairedEntryDirectionSide,
          pairedEntryDirectionRow]
      · have hside := pairedLeftGapCloseOnStrictPath_lastSide row
          strictPrefix lastStrict [] lookahead
        have hrow := pairedConsZeroOpenPath_lastRow
          (PairedEntryDirection.fromTwo row strictPrefix lastStrict)
          .right .first [] lookahead
        apply Option.map_pairedEntryDirectionSignature_eq_some
          path.getLast? nextSide (pairedGapNextRow [])
        · rw [hempty rfl]
          simpa [path, pairedRoundSideAfter,
            IndexedLineageSide.other] using hside
        · simpa [path, pairedLeftGapCloseOnStrictPath,
            pairedGapNextRow] using hrow
      · simpa [path, pairedLeftGapCloseOnStrictPath] using
          pairedConsZeroOpenPath_sideAlternates
            (PairedEntryDirection.fromTwo row strictPrefix lastStrict)
            .right .first [] lookahead rfl
      · simpa [path] using
          pairedFiniteDirectionPathWord_left_closeOnStrict row
            strictPrefix lastStrict [] lookahead
  | cons first rest =>
      rcases pairedBothGapEndpoint_exactlyOne .left nextSide
          (rest.length + 1) with hcloseBoth | hcloseStrict
      · let path := pairedLeftGapCloseOnBothPath row strictPrefix
          lastStrict first rest lookahead
        apply nonempty_pairedSignedRecutWitness_of_path
          (.left, row) (nextSide, pairedGapNextRow (first :: rest))
          (strictPrefix.map leftEnvironment ++
            [leftEnvironment lastStrict] ++ (first :: rest)) path
        · simp [path, pairedLeftGapCloseOnBothPath,
            pairedZeroOpenPath_length]
        · simp [path, pairedLeftGapCloseOnBothPath,
            pairedEntryDirectionSignature, pairedEntryDirectionSide,
            pairedEntryDirectionRow]
        · have hside := pairedLeftGapCloseOnBothPath_lastSide row
            strictPrefix lastStrict first rest lookahead
          have hrow := pairedConsZeroOpenPath_lastRow
            (PairedEntryDirection.fromTwo row
              (strictPrefix ++ [lastStrict])
              (first.inputOne, first.inputTwo))
            .right .both rest lookahead
          apply Option.map_pairedEntryDirectionSignature_eq_some
            path.getLast? nextSide (pairedGapNextRow (first :: rest))
          · simpa [path, hcloseBoth.1] using hside
          · cases rest <;>
              simpa [path, pairedLeftGapCloseOnBothPath,
                pairedGapNextRow] using hrow
        · simpa [path, pairedLeftGapCloseOnBothPath] using
            pairedConsZeroOpenPath_sideAlternates
              (PairedEntryDirection.fromTwo row
                (strictPrefix ++ [lastStrict])
                (first.inputOne, first.inputTwo))
              .right .both rest lookahead rfl
        · rw [show pairedFiniteDirectionPathWord path =
              strictPrefix.map leftEnvironment ++
                [leftEnvironment lastStrict] ++
                  (first :: rest).map forceBothRound by
              exact pairedFiniteDirectionPathWord_left_closeOnBoth row
                strictPrefix lastStrict first rest lookahead]
          rw [map_forceBothRound_eq_self (first :: rest) hboth]
      · let path := pairedLeftGapCloseOnStrictPath row strictPrefix
          lastStrict (first :: rest) lookahead
        apply nonempty_pairedSignedRecutWitness_of_path
          (.left, row) (nextSide, pairedGapNextRow (first :: rest))
          (strictPrefix.map leftEnvironment ++
            [leftEnvironment lastStrict] ++ (first :: rest)) path
        · simp [path, pairedLeftGapCloseOnStrictPath,
            pairedZeroOpenPath_length]
        · simp [path, pairedLeftGapCloseOnStrictPath,
            pairedEntryDirectionSignature, pairedEntryDirectionSide,
            pairedEntryDirectionRow]
        · have hside := pairedLeftGapCloseOnStrictPath_lastSide row
            strictPrefix lastStrict (first :: rest) lookahead
          have hrow := pairedConsZeroOpenPath_lastRow
            (PairedEntryDirection.fromTwo row strictPrefix lastStrict)
            .right .first (first :: rest) lookahead
          apply Option.map_pairedEntryDirectionSignature_eq_some
            path.getLast? nextSide (pairedGapNextRow (first :: rest))
          · simpa [path, hcloseStrict.1, Nat.add_assoc] using hside
          · simpa [path, pairedLeftGapCloseOnStrictPath,
              pairedGapNextRow] using hrow
        · simpa [path, pairedLeftGapCloseOnStrictPath] using
            pairedConsZeroOpenPath_sideAlternates
              (PairedEntryDirection.fromTwo row strictPrefix lastStrict)
              .right .first (first :: rest) lookahead rfl
        · rw [show pairedFiniteDirectionPathWord path =
              strictPrefix.map leftEnvironment ++
                [leftEnvironment lastStrict] ++
                  (first :: rest).map forceBothRound by
              exact pairedFiniteDirectionPathWord_left_closeOnStrict row
                strictPrefix lastStrict (first :: rest) lookahead]
          rw [map_forceBothRound_eq_self (first :: rest) hboth]

/-- Pack the concrete left-gap witness as one supplied signed recut. -/
def pairedSignedLeftGapRecut
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow) (strictPrefix : List (In₁ × In₂))
    (lastStrict : In₁ × In₂)
    (boths : List (EnvironmentRound In₁ In₂))
    (lookahead : EnvironmentRound In₁ In₂)
    (nextSide : IndexedLineageSide)
    (hempty : boths = [] → nextSide = .right)
    (hboth : ∀ round ∈ boths, round.graph = .both) :
    PairedSignedFiniteRecut In₁ In₂ where
  currentSignature := (.left, row)
  nextSignature := (nextSide, pairedGapNextRow boths)
  physicalWord := strictPrefix.map leftEnvironment ++
    [leftEnvironment lastStrict] ++ boths
  realization := nonempty_pairedSignedLeftGapRecutWitness row strictPrefix
    lastStrict boths lookahead nextSide hempty hboth

/-- A supplied productive gap decomposition.  The endpoint signature of each
gap is exactly the starting signature of the next; no local process observes
this proof-side coherence datum. -/
structure PairedSignedRecutStream (In₁ : Type u) (In₂ : Type v) where
  gap : Nat → PairedSignedFiniteRecut In₁ In₂
  signature_overlap : ∀ n,
    (gap n).nextSignature = (gap (n + 1)).currentSignature

namespace PairedFiniteRecutStream

variable {In₁ : Type u} {In₂ : Type v}

/-- Number of global directions contributed before segment `n`. -/
def directionCuts (stream : PairedFiniteRecutStream In₁ In₂) : Nat → Nat
  | 0 => 0
  | n + 1 => directionCuts stream n + (stream.segment n).body.length

@[simp] theorem directionCuts_zero
    (stream : PairedFiniteRecutStream In₁ In₂) :
    stream.directionCuts 0 = 0 :=
  rfl

@[simp] theorem directionCuts_succ
    (stream : PairedFiniteRecutStream In₁ In₂) (n : Nat) :
    stream.directionCuts (n + 1) = stream.directionCuts n +
      (stream.segment n).body.length :=
  rfl

theorem body_length_pos
    (stream : PairedFiniteRecutStream In₁ In₂) (n : Nat) :
    0 < (stream.segment n).body.length := by
  cases hbody : (stream.segment n).body with
  | nil => exact ((stream.segment n).body_ne_nil hbody).elim
  | cons first rest => simp

/-- Productivity makes the segment-direction cuts strictly increasing. -/
theorem directionCuts_strictMono
    (stream : PairedFiniteRecutStream In₁ In₂) :
    StrictMono stream.directionCuts := by
  exact strictMono_nat_of_lt_succ fun n ↦ by
    rw [directionCuts_succ]
    exact Nat.lt_add_of_pos_right (stream.body_length_pos n)

/-- Concatenate all nonempty segment bodies into an infinite branch. -/
def branch (stream : PairedFiniteRecutStream In₁ In₂) :
    Nat → PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
  fun n ↦
    let cuts := stream.directionCuts
    let k := cutBlock cuts n
    have hlower : cuts k ≤ n := cuts_cutBlock_le (cuts := cuts) rfl n
    have hupper : n < cuts (k + 1) :=
      lt_cuts_succ_cutBlock stream.directionCuts_strictMono n
    have hindex : n - cuts k < (stream.segment k).body.length := by
      change n < stream.directionCuts (k + 1) at hupper
      change stream.directionCuts k ≤ n at hlower
      change n - stream.directionCuts k < (stream.segment k).body.length
      rw [directionCuts_succ] at hupper
      omega
    (stream.segment k).body.get ⟨n - cuts k, hindex⟩

/-- Inside a segment body, the global branch is the corresponding literal
direction. -/
theorem branch_at
    (stream : PairedFiniteRecutStream In₁ In₂)
    (k j : Nat) (hj : j < (stream.segment k).body.length) :
    stream.branch (stream.directionCuts k + j) =
      (stream.segment k).body.get ⟨j, hj⟩ := by
  have hupper :
      stream.directionCuts k + j < stream.directionCuts (k + 1) := by
    rw [directionCuts_succ]
    omega
  have hblock :
      cutBlock stream.directionCuts (stream.directionCuts k + j) = k :=
    cutBlock_eq_of_mem_interval _ stream.directionCuts_strictMono rfl k _
      (Nat.le_add_right _ _) hupper
  dsimp only [branch]
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp only [hblock, Nat.add_sub_cancel_left]

/-- At the next segment cut the global branch is the previous segment's
lookahead endpoint. -/
theorem branch_at_next_cut
    (stream : PairedFiniteRecutStream In₁ In₂) (k : Nat) :
    stream.branch (stream.directionCuts (k + 1)) =
      (stream.segment k).endpoint := by
  have hnext := (stream.segment (k + 1)).body_ne_nil
  cases hbody : (stream.segment (k + 1)).body with
  | nil => exact (hnext hbody).elim
  | cons first rest =>
      have hhead : first = (stream.segment k).endpoint := by
        have hoverlap := stream.overlap k
        simpa [hbody] using hoverlap
      have hat := stream.branch_at (k + 1) 0 (by simp [hbody])
      simpa [hbody, hhead] using hat

/-- Version of `branch_at` including the shared endpoint. -/
theorem branch_at_segmentPath
    (stream : PairedFiniteRecutStream In₁ In₂)
    (k j : Nat) (hj : j < (stream.segment k).body.length + 1) :
    stream.branch (stream.directionCuts k + j) =
      ((stream.segment k).body ++ [(stream.segment k).endpoint]).get
        ⟨j, by simpa using hj⟩ := by
  by_cases hbody : j < (stream.segment k).body.length
  · rw [stream.branch_at k j hbody]
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [List.getElem_append_left hbody]
  · have hjlast : j = (stream.segment k).body.length := by omega
    subst j
    rw [← directionCuts_succ, stream.branch_at_next_cut]
    simp

/-- If every certified finite segment alternates proof-side orientations, so
does the globally concatenated branch. -/
theorem branch_side_alternates
    (stream : PairedFiniteRecutStream In₁ In₂)
    (halternates : ∀ k,
      PairedDirectionPathSideAlternates
        ((stream.segment k).body ++ [(stream.segment k).endpoint]))
    (n : Nat) :
    pairedEntryDirectionSide (stream.branch (n + 1)) =
      (pairedEntryDirectionSide (stream.branch n)).other := by
  let k := cutBlock stream.directionCuts n
  have hlower : stream.directionCuts k ≤ n :=
    cuts_cutBlock_le (cuts := stream.directionCuts) rfl n
  have hupper : n < stream.directionCuts (k + 1) :=
    lt_cuts_succ_cutBlock stream.directionCuts_strictMono n
  let j := n - stream.directionCuts k
  have hj : j < (stream.segment k).body.length := by
    rw [directionCuts_succ] at hupper
    dsimp only [j]
    omega
  have hn : stream.directionCuts k + j = n := by
    dsimp only [j]
    omega
  have hnnext : stream.directionCuts k + (j + 1) = n + 1 := by omega
  have hlocal := (List.isChain_iff_getElem.mp (halternates k)) j (by
      simp only [List.length_append, List.length_singleton]
      omega)
  have hcurrent := stream.branch_at_segmentPath k j (by omega)
  have hnext := stream.branch_at_segmentPath k (j + 1) (by omega)
  rw [hn] at hcurrent
  rw [hnnext] at hnext
  rw [List.get_eq_getElem] at hcurrent hnext
  rw [← hcurrent, ← hnext] at hlocal
  exact hlocal

/-- The complete finite direction window at a segment cut is exactly its
stored body followed by its shared lookahead endpoint. -/
theorem branch_segment_window
    (stream : PairedFiniteRecutStream In₁ In₂) (k : Nat) :
    List.ofFn (fun i : Fin ((stream.segment k).body.length + 1) ↦
        stream.branch (stream.directionCuts k + i)) =
      (stream.segment k).body ++ [(stream.segment k).endpoint] := by
  apply List.ext_get
  · simp
  · intro i hiLeft hiRight
    rw [List.get_eq_getElem, List.getElem_ofFn, List.get_eq_getElem]
    by_cases hi : i < (stream.segment k).body.length
    · rw [stream.branch_at k i hi]
      rw [List.getElem_append_left hi]
      rfl
    · have hilast : i = (stream.segment k).body.length := by
        simp only [List.length_ofFn] at hiLeft
        omega
      subst i
      rw [← directionCuts_succ, stream.branch_at_next_cut]
      simp

/-- Consequently the finite path read from the global branch contributes the
literal physical word certified by the segment. -/
theorem pairedFiniteDirectionPathWord_branch_segment
    (stream : PairedFiniteRecutStream In₁ In₂) (k : Nat) :
    pairedFiniteDirectionPathWord
        (List.ofFn (fun i : Fin ((stream.segment k).body.length + 1) ↦
          stream.branch (stream.directionCuts k + i))) =
      (stream.segment k).physicalWord := by
  rw [stream.branch_segment_window k]
  exact (stream.segment k).exact_word

/-- Real-round cut at the beginning of a finite recut segment. -/
def physicalCuts (stream : PairedFiniteRecutStream In₁ In₂) (k : Nat) : Nat :=
  pairedBranchCuts stream.branch (stream.directionCuts k)

@[simp] theorem physicalCuts_zero
    (stream : PairedFiniteRecutStream In₁ In₂) :
    stream.physicalCuts 0 = 0 :=
  rfl

/-- The exact global gluing equation: between two consecutive segment cuts,
the flattened infinite branch contributes precisely the certified physical
word of that segment. -/
theorem omegaPrefix_physicalCuts_succ
    (stream : PairedFiniteRecutStream In₁ In₂) (k : Nat) :
    omegaPrefix (pairedBranchEnvironment stream.branch)
        (stream.physicalCuts (k + 1)) =
      omegaPrefix (pairedBranchEnvironment stream.branch)
          (stream.physicalCuts k) ++
        (stream.segment k).physicalWord := by
  rw [physicalCuts, physicalCuts, directionCuts_succ]
  rw [omegaPrefix_pairedBranchCuts_add]
  rw [← pairedFiniteDirectionPathWord_ofFn_eq_chunkRange]
  rw [stream.pairedFiniteDirectionPathWord_branch_segment k]

/-- The physical cuts advance by the literal length of the certified segment
word. -/
theorem physicalCuts_succ
    (stream : PairedFiniteRecutStream In₁ In₂) (k : Nat) :
    stream.physicalCuts (k + 1) = stream.physicalCuts k +
      (stream.segment k).physicalWord.length := by
  have h := congrArg List.length (stream.omegaPrefix_physicalCuts_succ k)
  simpa [omegaPrefix] using h

/-- Productivity of directions implies productivity of physical rounds: each
contributed direction has a nonempty chunk. -/
theorem physicalWord_length_pos
    (stream : PairedFiniteRecutStream In₁ In₂) (k : Nat) :
    0 < (stream.segment k).physicalWord.length := by
  have hcutsDir : stream.directionCuts k < stream.directionCuts (k + 1) :=
    stream.directionCuts_strictMono (Nat.lt_succ_self k)
  have hcutsPhysical : stream.physicalCuts k < stream.physicalCuts (k + 1) := by
    exact (pairedBranchCuts_strictMono stream.branch) hcutsDir
  rw [stream.physicalCuts_succ k] at hcutsPhysical
  omega

/-- Segment physical cuts are strictly increasing, hence every finite
physical time lies before some completed segment. -/
theorem physicalCuts_strictMono
    (stream : PairedFiniteRecutStream In₁ In₂) :
    StrictMono stream.physicalCuts := by
  exact strictMono_nat_of_lt_succ fun k ↦ by
    rw [stream.physicalCuts_succ k]
    exact Nat.lt_add_of_pos_right (stream.physicalWord_length_pos k)

/-- Finite concatenation of the first `k` certified physical segment words. -/
def physicalWordsPrefix
    (stream : PairedFiniteRecutStream In₁ In₂) : Nat →
      List (EnvironmentRound In₁ In₂)
  | 0 => []
  | k + 1 => physicalWordsPrefix stream k ++
      (stream.segment k).physicalWord

@[simp] theorem physicalWordsPrefix_zero
    (stream : PairedFiniteRecutStream In₁ In₂) :
    stream.physicalWordsPrefix 0 = [] :=
  rfl

@[simp] theorem physicalWordsPrefix_succ
    (stream : PairedFiniteRecutStream In₁ In₂) (k : Nat) :
    stream.physicalWordsPrefix (k + 1) = stream.physicalWordsPrefix k ++
      (stream.segment k).physicalWord :=
  rfl

/-- Every completed-segment prefix of the flattened branch is the literal
concatenation of the certified physical words. -/
theorem omegaPrefix_physicalCuts_eq_physicalWordsPrefix
    (stream : PairedFiniteRecutStream In₁ In₂) : ∀ k : Nat,
    omegaPrefix (pairedBranchEnvironment stream.branch)
        (stream.physicalCuts k) = stream.physicalWordsPrefix k
  | 0 => rfl
  | k + 1 => by
      rw [stream.omegaPrefix_physicalCuts_succ k]
      rw [stream.omegaPrefix_physicalCuts_eq_physicalWordsPrefix k]
      rfl

/-- The finite slice of the flattened environment between two segment cuts
is the corresponding certified word. -/
theorem physicalSegment_blockOfFn
    (stream : PairedFiniteRecutStream In₁ In₂) (k : Nat) :
    List.ofFn
        (fun i : Fin (stream.segment k).physicalWord.length ↦
          pairedBranchEnvironment stream.branch (stream.physicalCuts k + i)) =
      (stream.segment k).physicalWord := by
  have hsplit := omegaPrefix_add
    (pairedBranchEnvironment stream.branch) (stream.physicalCuts k)
      (stream.segment k).physicalWord.length
  rw [← stream.physicalCuts_succ k] at hsplit
  rw [stream.omegaPrefix_physicalCuts_succ k] at hsplit
  exact (List.append_cancel_left hsplit).symm

/-- Pointwise form of the exact segment-slice equation. -/
theorem pairedBranchEnvironment_at_physicalSegment
    (stream : PairedFiniteRecutStream In₁ In₂)
    (k j : Nat) (hj : j < (stream.segment k).physicalWord.length) :
    pairedBranchEnvironment stream.branch (stream.physicalCuts k + j) =
      (stream.segment k).physicalWord.get ⟨j, hj⟩ := by
  have h := congrArg (fun word ↦ word[j]?)
    (stream.physicalSegment_blockOfFn k)
  have h' : j < (stream.segment k).physicalWord.length ∧
      pairedBranchEnvironment stream.branch (stream.physicalCuts k + j) =
        (stream.segment k).physicalWord[j] := by
    simpa [List.getElem?_eq_getElem hj] using h
  exact h'.2

/-- The direct infinite concatenation of the certified physical words. -/
def concatenatedPhysicalEnvironment
    (stream : PairedFiniteRecutStream In₁ In₂) :
    EnvironmentSequence In₁ In₂ :=
  fun n ↦
    let cuts := stream.physicalCuts
    let k := cutBlock cuts n
    have hlower : cuts k ≤ n := cuts_cutBlock_le (cuts := cuts) rfl n
    have hupper : n < cuts (k + 1) :=
      lt_cuts_succ_cutBlock stream.physicalCuts_strictMono n
    have hindex : n - cuts k < (stream.segment k).physicalWord.length := by
      change n < stream.physicalCuts (k + 1) at hupper
      change stream.physicalCuts k ≤ n at hlower
      change n - stream.physicalCuts k <
        (stream.segment k).physicalWord.length
      rw [stream.physicalCuts_succ k] at hupper
      omega
    (stream.segment k).physicalWord.get ⟨n - cuts k, hindex⟩

/-- Main global recut identity: flattening the coherent infinite paired branch
is pointwise equal to direct concatenation of the certified physical segment
words. -/
theorem pairedBranchEnvironment_eq_concatenatedPhysicalEnvironment
    (stream : PairedFiniteRecutStream In₁ In₂) :
    pairedBranchEnvironment stream.branch =
      stream.concatenatedPhysicalEnvironment := by
  funext n
  let k := cutBlock stream.physicalCuts n
  have hlower : stream.physicalCuts k ≤ n :=
    cuts_cutBlock_le (cuts := stream.physicalCuts) rfl n
  have hupper : n < stream.physicalCuts (k + 1) :=
    lt_cuts_succ_cutBlock stream.physicalCuts_strictMono n
  have hindex : n - stream.physicalCuts k <
      (stream.segment k).physicalWord.length := by
    rw [stream.physicalCuts_succ k] at hupper
    omega
  have hat := stream.pairedBranchEnvironment_at_physicalSegment k
    (n - stream.physicalCuts k) hindex
  have hn : stream.physicalCuts k + (n - stream.physicalCuts k) = n := by
    omega
  rw [hn] at hat
  rw [hat]
  dsimp only [concatenatedPhysicalEnvironment]

end PairedFiniteRecutStream

namespace PairedSignedRecutStream

variable {In₁ : Type u} {In₂ : Type v}

/-- A fixed proof-side witness for each supplied gap. -/
noncomputable def chosenWitness
    (stream : PairedSignedRecutStream In₁ In₂) (n : Nat) :
    PairedSignedRecutWitness In₁ In₂
      (stream.gap n).currentSignature (stream.gap n).nextSignature
        (stream.gap n).physicalWord :=
  (stream.gap n).realization.some

/-- Glue the supplied signed gaps into the generic global recut stream by
replacing each old lookahead with the literal first direction of the next
chosen gap.  Signature coherence makes this replacement physically inert. -/
noncomputable def toFiniteRecutStream
    (stream : PairedSignedRecutStream In₁ In₂) :
    PairedFiniteRecutStream In₁ In₂ where
  segment n :=
    { body := (stream.chosenWitness n).first ::
        (stream.chosenWitness n).rest
      endpoint := (stream.chosenWitness (n + 1)).first
      body_ne_nil := List.cons_ne_nil _ _
      physicalWord := (stream.gap n).physicalWord
      exact_word := by
        have hsignature :
            pairedEntryDirectionSignature
                (stream.chosenWitness n).oldEndpoint =
              pairedEntryDirectionSignature
                (stream.chosenWitness (n + 1)).first := by
          rw [(stream.chosenWitness n).endpoint_signature]
          rw [stream.signature_overlap n]
          exact (stream.chosenWitness (n + 1)).first_signature.symm
        exact (pairedFiniteDirectionPathWord_replace_endpoint
          ((stream.chosenWitness n).first :: (stream.chosenWitness n).rest)
          (stream.chosenWitness n).oldEndpoint
          (stream.chosenWitness (n + 1)).first (List.cons_ne_nil _ _)
          hsignature).trans (stream.chosenWitness n).exact_word }
  overlap n := by
    simp

/-- Every glued segment retains the side-alternation certificate of its signed
witness after replacing the old endpoint by the next segment's first
direction. -/
theorem toFiniteRecutStream_segment_sideAlternates
    (stream : PairedSignedRecutStream In₁ In₂) (k : Nat) :
    PairedDirectionPathSideAlternates
      ((stream.toFiniteRecutStream.segment k).body ++
        [(stream.toFiniteRecutStream.segment k).endpoint]) := by
  have hsignature :
      pairedEntryDirectionSignature (stream.chosenWitness k).oldEndpoint =
        pairedEntryDirectionSignature (stream.chosenWitness (k + 1)).first := by
    rw [(stream.chosenWitness k).endpoint_signature]
    rw [stream.signature_overlap k]
    exact (stream.chosenWitness (k + 1)).first_signature.symm
  exact pairedDirectionPathSideAlternates_replace_endpoint_of_signature
    ((stream.chosenWitness k).first :: (stream.chosenWitness k).rest)
    (stream.chosenWitness k).oldEndpoint
    (stream.chosenWitness (k + 1)).first (List.cons_ne_nil _ _)
    hsignature (stream.chosenWitness k).side_alternates

/-- Hence the proof-side query orientation of the glued global branch flips at
every adjacent direction. -/
theorem toFiniteRecutStream_branch_side_alternates
    (stream : PairedSignedRecutStream In₁ In₂) (n : Nat) :
    pairedEntryDirectionSide
        (stream.toFiniteRecutStream.branch (n + 1)) =
      (pairedEntryDirectionSide
        (stream.toFiniteRecutStream.branch n)).other :=
  stream.toFiniteRecutStream.branch_side_alternates
    stream.toFiniteRecutStream_segment_sideAlternates n

/-- The signature seen by the global branch at a segment cut is exactly the
current signed-gap signature. -/
theorem toFiniteRecutStream_branch_signature_at_cut
    (stream : PairedSignedRecutStream In₁ In₂) (k : Nat) :
    pairedEntryDirectionSignature
        (stream.toFiniteRecutStream.branch
          (stream.toFiniteRecutStream.directionCuts k)) =
      (stream.gap k).currentSignature := by
  have hat := stream.toFiniteRecutStream.branch_at k 0
    (stream.toFiniteRecutStream.body_length_pos k)
  rw [Nat.add_zero] at hat
  rw [hat]
  exact (stream.chosenWitness k).first_signature

/-- At the following cut the same branch carries the current gap's endpoint
signature, equivalently the next gap's current signature. -/
theorem toFiniteRecutStream_branch_signature_at_next_cut
    (stream : PairedSignedRecutStream In₁ In₂) (k : Nat) :
    pairedEntryDirectionSignature
        (stream.toFiniteRecutStream.branch
          (stream.toFiniteRecutStream.directionCuts (k + 1))) =
      (stream.gap k).nextSignature := by
  rw [stream.toFiniteRecutStream.branch_at_next_cut k]
  change pairedEntryDirectionSignature
      (stream.chosenWitness (k + 1)).first = (stream.gap k).nextSignature
  rw [(stream.chosenWitness (k + 1)).first_signature]
  exact (stream.signature_overlap k).symm

/-- Side and row projections of the exact cut signature. -/
theorem toFiniteRecutStream_branch_side_at_cut
    (stream : PairedSignedRecutStream In₁ In₂) (k : Nat) :
    pairedEntryDirectionSide
        (stream.toFiniteRecutStream.branch
          (stream.toFiniteRecutStream.directionCuts k)) =
      (stream.gap k).currentSignature.1 := by
  have h := congrArg Prod.fst
    (stream.toFiniteRecutStream_branch_signature_at_cut k)
  simpa [pairedEntryDirectionSignature] using h

theorem toFiniteRecutStream_branch_row_at_cut
    (stream : PairedSignedRecutStream In₁ In₂) (k : Nat) :
    pairedEntryDirectionRow
        (stream.toFiniteRecutStream.branch
          (stream.toFiniteRecutStream.directionCuts k)) =
      (stream.gap k).currentSignature.2 := by
  have h := congrArg Prod.snd
    (stream.toFiniteRecutStream_branch_signature_at_cut k)
  simpa [pairedEntryDirectionSignature] using h

/-- The glued branch's physical environment is exactly the direct
concatenation of the supplied gap words. -/
theorem pairedBranchEnvironment_eq_suppliedGapConcatenation
    (stream : PairedSignedRecutStream In₁ In₂) :
    pairedBranchEnvironment stream.toFiniteRecutStream.branch =
      stream.toFiniteRecutStream.concatenatedPhysicalEnvironment :=
  PairedFiniteRecutStream.pairedBranchEnvironment_eq_concatenatedPhysicalEnvironment
    stream.toFiniteRecutStream

/-- A productive strict-gap decomposition of a concrete environment.  The
`recuts.gap` entries are intended to be the concrete values constructed by
`pairedSignedRightGapRecut` and `pairedSignedLeftGapRecut`; `exact_prefix`
states that their physical words partition the supplied environment. -/
structure ProductiveStrictGapDecomposition (In₁ : Type u) (In₂ : Type v) where
  recuts : PairedSignedRecutStream In₁ In₂
  environment : EnvironmentSequence In₁ In₂
  exact_prefix : ∀ k,
    omegaPrefix environment (recuts.toFiniteRecutStream.physicalCuts k) =
      recuts.toFiniteRecutStream.physicalWordsPrefix k

namespace ProductiveStrictGapDecomposition

/-- A supplied productive decomposition gives the desired global exact
recut of the original environment. -/
theorem pairedBranchEnvironment_eq_original
    (decomposition : ProductiveStrictGapDecomposition In₁ In₂) :
    pairedBranchEnvironment
        decomposition.recuts.toFiniteRecutStream.branch =
      decomposition.environment := by
  apply omegaWord_eq_of_prefix_eq_at_strictCuts _ _
    decomposition.recuts.toFiniteRecutStream.physicalCuts
    decomposition.recuts.toFiniteRecutStream.physicalCuts_strictMono
  intro k
  rw [PairedFiniteRecutStream.omegaPrefix_physicalCuts_eq_physicalWordsPrefix
    decomposition.recuts.toFiniteRecutStream k]
  exact (decomposition.exact_prefix k).symm

/-- Direct concatenation of the concrete strict-gap words is likewise the
original environment. -/
theorem concatenatedPhysicalEnvironment_eq_original
    (decomposition : ProductiveStrictGapDecomposition In₁ In₂) :
    decomposition.recuts.toFiniteRecutStream.concatenatedPhysicalEnvironment =
      decomposition.environment := by
  rw [← pairedBranchEnvironment_eq_suppliedGapConcatenation
    decomposition.recuts]
  exact decomposition.pairedBranchEnvironment_eq_original

end ProductiveStrictGapDecomposition

end PairedSignedRecutStream

end DetParityAutomaton

end DistributedSynthesis
