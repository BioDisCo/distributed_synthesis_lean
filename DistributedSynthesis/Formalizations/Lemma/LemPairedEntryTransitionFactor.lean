/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPendingBitResolution
import DistributedSynthesis.Formalizations.Theorem.ThmBlockRestriction
import DistributedSynthesis.Formalizations.Theorem.ThmBoundaryGame

/-!
# Fail-fast test for the paired-entry Bérard route

This file deliberately stops before constructing a Rabin tree automaton.  It
tests the local claim on which that construction depends: one strategy-tree
node may represent the two `b_old` variants, use one shared blind lambda on
both, and update the objective automaton using only the finite pair of entry
states and the chosen lambda transition.

The first orientation is treated here.  A process-one pending pair is an
opening `left`/`both` ambiguity followed by a `right` block.  Process one is the
blind sender in that block.  Its complete Bérard lambda fragment is therefore
`SenderBlockStrategy In₁ Out₁`, not a finite plan.

The decisive distinction is explicit:

* the raw realizing strategy need not choose the same lambda at two unrelated
  entry representatives with equal automaton code (that would resurrect the
  false `InformedPostEntryAgreement`);
* inside one paired representative, however, the two variants have literally
  equal blind views, so the one raw strategy supplies one shared lambda;
* once a lambda transition has been chosen, its automaton successor depends
  only on the finite entry-state pair.  It does not inspect either history.

The remaining global test, after this local factor, is successor-class
stitching: the children produced at the next reversal must again be packaged
as paired representatives.  `LemPendingBitResolution` supplies the raw
replace-not-accumulate fact needed there.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- One process-one pending entry class, represented by its ordered
`left`/`both` histories.  Both histories are genuine prefixes of the same
distributed strategy. -/
structure ProcOnePairedEntryRep
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) where
  leftHistory : History In₁ In₂ Graph Out₁ Out₂
  bothHistory : History In₁ In₂ Graph Out₁ Out₂
  leftGenerated : StrategyGeneratedPrefix strategy leftHistory
  bothGenerated : StrategyGeneratedPrefix strategy bothHistory
  pending : ProcOnePendingOverlap leftHistory bothHistory

/-- Orientation mirror: an ordered `right`/`both` entry pair sharing the
process-two blind view before a following left block. -/
structure ProcTwoPairedEntryRep
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) where
  rightHistory : History In₁ In₂ Graph Out₁ Out₂
  bothHistory : History In₁ In₂ Graph Out₁ Out₂
  rightGenerated : StrategyGeneratedPrefix strategy rightHistory
  bothGenerated : StrategyGeneratedPrefix strategy bothHistory
  pending : ProcTwoPendingOverlap rightHistory bothHistory

namespace ProcOnePairedEntryRep

variable {A}

/-- The finite objective code of a paired entry.  Ordering records which
coordinate is the one-way and which is the `both` variant. -/
def code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcOnePairedEntryRep strategy) : A.State × A.State :=
  (entryState (A := A) entry.leftHistory,
    entryState (A := A) entry.bothHistory)

/-- The blind view shared by the two variants. -/
theorem view_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcOnePairedEntryRep strategy) :
    currentView Proc.one entry.leftHistory =
      currentView Proc.one entry.bothHistory :=
  entry.pending.view_eq

end ProcOnePairedEntryRep

namespace ProcTwoPairedEntryRep

variable {A}

/-- The finite objective code of the mirror paired entry. -/
def code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcTwoPairedEntryRep strategy) : A.State × A.State :=
  (entryState (A := A) entry.rightHistory,
    entryState (A := A) entry.bothHistory)

theorem view_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcTwoPairedEntryRep strategy) :
    currentView Proc.two entry.rightHistory =
      currentView Proc.two entry.bothHistory :=
  entry.pending.view_eq

end ProcTwoPairedEntryRep

/-- A paired right-block lambda transition.  The blind sender component is
shared.  The informed receiver may use a different full-information fragment
for the two actual entry variants; it knows which entry thread is real. -/
structure ProcOnePairedRightLambda where
  blind : SenderBlockStrategy In₁ Out₁
  informedLeft : ReceiverBlockStrategy In₂ In₁ Out₂
  informedBoth : ReceiverBlockStrategy In₂ In₁ Out₂
  bothOneLeft : ReceiverBlockStrategy In₂ In₁ Out₁
  bothOneBoth : ReceiverBlockStrategy In₂ In₁ Out₁

/-- Equality of process-one base views gives equality of their complete
right-block sender lambdas, for every own-input word. -/
theorem blockSenderOne_eq_of_view_eq
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    {h h' : History In₁ In₂ Graph Out₁ Out₂}
    (hview : currentView Proc.one h = currentView Proc.one h') :
    blockSenderOne strategy h = blockSenderOne strategy h' := by
  funext word input
  unfold blockSenderOne
  rw [nextView_one_of_graph_right _ _ rfl,
    nextView_one_of_graph_right _ _ rfl]
  have hright :
      ∀ env ∈ word.map
          (fun sIn => rightEnvironment ((default : In₂), sIn)),
        env.graph = Graph.right := by
    intro env henv
    rcases List.mem_map.mp henv with ⟨sIn, _, rfl⟩
    rfl
  rw [currentView_one_extendPrefix_right strategy h _ hright,
    currentView_one_extendPrefix_right strategy h' _ hright, hview]

namespace ProcOnePairedEntryRep

/-- The possibly infinite paired lambda label supplied by the original
strategy at one paired node. -/
def lambdaOfStrategy
    [Inhabited In₂]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcOnePairedEntryRep strategy) :
    ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) where
  blind := blockSenderOne strategy entry.leftHistory
  informedLeft := blockReceiverTwo strategy entry.leftHistory
  informedBoth := blockReceiverTwo strategy entry.bothHistory
  bothOneLeft := fun node move =>
    strategy.one
      (nextView Proc.one
        (extendPrefix strategy entry.leftHistory (node.map rightEnvironment))
        ⟨move.2, move.1, Graph.both⟩)
  bothOneBoth := fun node move =>
    strategy.one
      (nextView Proc.one
        (extendPrefix strategy entry.bothHistory (node.map rightEnvironment))
        ⟨move.2, move.1, Graph.both⟩)

/-- The label chosen above is genuinely shared: reading its blind component
from the `both` representative gives the same whole lambda function. -/
theorem lambdaOfStrategy_blind_eq_both
    [Inhabited In₂]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcOnePairedEntryRep strategy) :
    entry.lambdaOfStrategy.blind =
      blockSenderOne strategy entry.bothHistory :=
  blockSenderOne_eq_of_view_eq strategy entry.view_eq

end ProcOnePairedEntryRep

/-- Play a finite right-block lambda from a given full-move prefix. -/
def pairedRightWordFrom
    (blind : SenderBlockStrategy In₁ Out₁)
    (informed : ReceiverBlockStrategy In₂ In₁ Out₂) :
    List (In₂ × In₁) -> List (In₂ × In₁) ->
      List (RoundRecord In₁ In₂ Graph Out₁ Out₂)
  | _, [] => []
  | past, move :: rest =>
      rightRoundRecord move (blind (senderWord past) move.2)
          (informed past move) ::
        pairedRightWordFrom blind informed (past ++ [move]) rest

/-- The finite word emitted by a paired lambda on its left entry variant. -/
def ProcOnePairedRightLambda.leftWord
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (moves : List (In₂ × In₁)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  pairedRightWordFrom lambda.blind lambda.informedLeft [] moves

/-- The finite word emitted on the `both` entry variant. -/
def ProcOnePairedRightLambda.bothWord
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (moves : List (In₂ × In₁)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  pairedRightWordFrom lambda.blind lambda.informedBoth [] moves

/-- The successor entry-state pair computed by a paired lambda transition.
This definition mentions no history: it is the proposed finite RTA transition
semantics. -/
def pairedRightSuccessorCode
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (moves : List (In₂ × In₁)) : A.State × A.State :=
  ((lambda.leftWord moves).foldl A.step code.1,
    (lambda.bothWord moves).foldl A.step code.2)

/-- The fresh process-two `right`/`both` child reached after resolving the old
pair to its left-entry row.  Its code is computed solely from the parent code,
the paired lambda, and the finite direction prefix/current move. -/
def pairedRightFreshChildCodeLeft
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    A.State × A.State :=
  let state := (pairedRightSuccessorCode A code lambda past).1
  let outOneRight := lambda.blind (senderWord past) move.2
  let outTwo := lambda.informedLeft past move
  let outOneBoth := lambda.bothOneLeft past move
  (A.step state (rightRoundRecord move outOneRight outTwo),
    A.step state (bothRoundRecord (move.2, move.1) outOneBoth outTwo))

/-- The corresponding child after resolving to the old `both` row. -/
def pairedRightFreshChildCodeBoth
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    A.State × A.State :=
  let state := (pairedRightSuccessorCode A code lambda past).2
  let outOneRight := lambda.blind (senderWord past) move.2
  let outTwo := lambda.informedBoth past move
  let outOneBoth := lambda.bothOneBoth past move
  (A.step state (rightRoundRecord move outOneRight outTwo),
    A.step state (bothRoundRecord (move.2, move.1) outOneBoth outTwo))

theorem pairedRightFreshChildCodeLeft_congr
    {code code' : A.State × A.State} (hcode : code = code')
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    pairedRightFreshChildCodeLeft A code lambda past move =
      pairedRightFreshChildCodeLeft A code' lambda past move := by
  rw [hcode]

theorem pairedRightFreshChildCodeBoth_congr
    {code code' : A.State × A.State} (hcode : code = code')
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    pairedRightFreshChildCodeBoth A code lambda past move =
      pairedRightFreshChildCodeBoth A code' lambda past move := by
  rw [hcode]

/-- The abstract lambda word extracted from a strategy is exactly the list of
records appended by the concrete execution extension.  The statement is
generalized over an already-read block prefix because this is the induction
invariant needed for an infinite lambda fragment. -/
theorem extendPrefix_eq_append_pairedRightWordFrom
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (past moves : List (In₂ × In₁)) :
    extendPrefix strategy base ((past ++ moves).map rightEnvironment) =
      extendPrefix strategy base (past.map rightEnvironment) ++
        pairedRightWordFrom (blockSenderOne strategy base)
          (blockReceiverTwo strategy base) past moves := by
  induction moves generalizing past with
  | nil => simp [pairedRightWordFrom]
  | cons move rest ih =>
      have hrecord :
          rightRoundRecord move
              (blockSenderOne strategy base (senderWord past) move.2)
              (blockReceiverTwo strategy base past move) =
            nextRound strategy
              (extendPrefix strategy base (past.map rightEnvironment))
              (rightEnvironment move) := by
        rw [blockSenderOne_eq strategy base past move]
        rfl
      calc
        extendPrefix strategy base
              ((past ++ move :: rest).map rightEnvironment) =
            extendPrefix strategy base
              (((past ++ [move]) ++ rest).map rightEnvironment) := by
                simp [List.append_assoc]
        _ = extendPrefix strategy base
                ((past ++ [move]).map rightEnvironment) ++
              pairedRightWordFrom (blockSenderOne strategy base)
                (blockReceiverTwo strategy base) (past ++ [move]) rest := by
              exact ih (past ++ [move])
        _ = History.append
                (extendPrefix strategy base (past.map rightEnvironment))
                (nextRound strategy
                  (extendPrefix strategy base (past.map rightEnvironment))
                  (rightEnvironment move)) ++
              pairedRightWordFrom (blockSenderOne strategy base)
                (blockReceiverTwo strategy base) (past ++ [move]) rest := by
              simp only [List.map_append, List.map_singleton]
              rw [extendPrefix_snoc]
        _ = extendPrefix strategy base (past.map rightEnvironment) ++
              rightRoundRecord move
                  (blockSenderOne strategy base (senderWord past) move.2)
                  (blockReceiverTwo strategy base past move) ::
                pairedRightWordFrom (blockSenderOne strategy base)
                  (blockReceiverTwo strategy base) (past ++ [move]) rest := by
              rw [hrecord]
              simp [History.append, List.append_assoc]
        _ = extendPrefix strategy base (past.map rightEnvironment) ++
              pairedRightWordFrom (blockSenderOne strategy base)
                (blockReceiverTwo strategy base) past (move :: rest) := by
              rw [pairedRightWordFrom]

/-- At a paired node, the proposed finite transition semantics reproduces the
actual objective states reached by the raw strategy on both representatives.
This is the nontrivial half of the local factor test: the history is needed to
obtain the lambda, but disappears completely from its transition update. -/
theorem pairedRightSuccessorCode_lambdaOfStrategy
    [Inhabited In₂]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcOnePairedEntryRep strategy)
    (moves : List (In₂ × In₁)) :
    pairedRightSuccessorCode A entry.code entry.lambdaOfStrategy moves =
      (entryState (A := A)
          (extendPrefix strategy entry.leftHistory
            (moves.map rightEnvironment)),
        entryState (A := A)
          (extendPrefix strategy entry.bothHistory
            (moves.map rightEnvironment))) := by
  have hleft :=
    extendPrefix_eq_append_pairedRightWordFrom
      strategy entry.leftHistory [] moves
  have hboth :=
    extendPrefix_eq_append_pairedRightWordFrom
      strategy entry.bothHistory [] moves
  simp only [List.nil_append, List.map_nil, extendPrefix_nil,
    ProcOnePairedEntryRep.lambdaOfStrategy] at hleft ⊢
  rw [← entry.lambdaOfStrategy_blind_eq_both] at hboth
  simp only [List.nil_append, List.map_nil, extendPrefix_nil,
    ProcOnePairedEntryRep.lambdaOfStrategy] at hboth
  apply Prod.ext
  · change
      (pairedRightWordFrom (blockSenderOne strategy entry.leftHistory)
          (blockReceiverTwo strategy entry.leftHistory) [] moves).foldl A.step
          (entryState (A := A) entry.leftHistory) =
        entryState (A := A)
          (extendPrefix strategy entry.leftHistory
            (moves.map rightEnvironment))
    rw [hleft]
    simp [entryState, List.foldl_append]
  · change
      (pairedRightWordFrom (blockSenderOne strategy entry.leftHistory)
          (blockReceiverTwo strategy entry.bothHistory) [] moves).foldl A.step
          (entryState (A := A) entry.bothHistory) =
        entryState (A := A)
          (extendPrefix strategy entry.bothHistory
            (moves.map rightEnvironment))
    rw [hboth]
    simp [entryState, List.foldl_append]

/-- **The local paired-entry transition factor.**  Once the shared lambda is
fixed, equal finite entry codes have equal successor codes for every finite
right-block direction.  This is the history-erasure check required before an
input-free rational-run construction is even meaningful. -/
theorem pairedRightSuccessorCode_congr
    {code code' : A.State × A.State}
    (hcode : code = code')
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (moves : List (In₂ × In₁)) :
    pairedRightSuccessorCode A code lambda moves =
      pairedRightSuccessorCode A code' lambda moves := by
  rw [hcode]

/-! ## Successor-class stitching: the four-corner test -/

/-- Strategy generation is closed under a finite environment extension.  This
small unrestricted form avoids importing the later uniformization game. -/
theorem strategyGenerated_extendPrefix_basic
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix strategy h)
    (envs : List (EnvironmentRound In₁ In₂)) :
    StrategyGeneratedPrefix strategy (extendPrefix strategy h envs) := by
  induction envs using List.reverseRecOn with
  | nil => exact hgen
  | append_singleton envs env ih =>
      rw [extendPrefix_snoc]
      exact StrategyGeneratedPrefix.append ih env

/-- Different process-two views remain different when both executions are
extended through the same right-block environment word.  Outputs may differ;
the receiver keeps its old own view as the first component of every new
receive view. -/
theorem procTwo_ne_preserved_by_right_extension
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (hne : currentView Proc.two h ≠ currentView Proc.two h')
    (moves : List (In₂ × In₁)) :
    currentView Proc.two
        (extendPrefix strategy h (moves.map rightEnvironment)) ≠
      currentView Proc.two
        (extendPrefix strategy h' (moves.map rightEnvironment)) := by
  induction moves using List.reverseRecOn with
  | nil => simpa using hne
  | append_singleton moves move ih =>
      simp only [List.map_append, List.map_singleton]
      rw [extendPrefix_snoc, extendPrefix_snoc]
      simp only [currentView_two_append, nextRound]
      intro heq
      exact ih (View.recv.inj heq).1

/-- The other process distinguishes the two histories of a process-one
pending pair. -/
theorem ProcOnePairedEntryRep.other_view_ne
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcOnePairedEntryRep strategy) :
    currentView Proc.two entry.leftHistory ≠
      currentView Proc.two entry.bothHistory := by
  obtain ⟨base, rLeft, rBoth, suffix, _hinOne, _hinTwo, hleft, hboth,
    hsuffix, hentryLeft, hentryBoth⟩ := entry.pending
  rw [hentryLeft, hentryBoth]
  apply procTwo_ne_preserved_by_right_suffix
  · simp [currentView_two_append, hleft, hboth]
  · exact hsuffix

/-- Create the fresh process-two `right`/`both` pair at one generated base.
The two graph choices have equal process-two receive views and are therefore
one legitimate paired node. -/
def procTwoFreshPair
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (hgen : StrategyGeneratedPrefix strategy base)
    (inputOne : In₁) (inputTwo : In₂) :
    ProcTwoPairedEntryRep strategy where
  rightHistory :=
    History.append base
      (nextRound strategy base ⟨inputOne, inputTwo, Graph.right⟩)
  bothHistory :=
    History.append base
      (nextRound strategy base ⟨inputOne, inputTwo, Graph.both⟩)
  rightGenerated := StrategyGeneratedPrefix.append hgen _
  bothGenerated := StrategyGeneratedPrefix.append hgen _
  pending := ⟨base,
    nextRound strategy base ⟨inputOne, inputTwo, Graph.right⟩,
    nextRound strategy base ⟨inputOne, inputTwo, Graph.both⟩,
    [], by simp [nextRound]⟩

/-- The process-two receiver output used by a right-block lambda is also its
output on the indistinguishable `both` alternative. -/
theorem blockReceiverTwo_eq_both
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    blockReceiverTwo strategy base past move =
      strategy.two
        (nextView Proc.two
          (extendPrefix strategy base (past.map rightEnvironment))
          ⟨move.2, move.1, Graph.both⟩) := by
  rfl

/-- The finite left-row child-code calculation agrees with the actual fresh
pair generated from the raw strategy. -/
theorem pairedRightFreshChildCodeLeft_lambdaOfStrategy
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    pairedRightFreshChildCodeLeft A entry.code entry.lambdaOfStrategy past move =
      (procTwoFreshPair strategy
        (extendPrefix strategy entry.leftHistory (past.map rightEnvironment))
        (strategyGenerated_extendPrefix_basic strategy entry.leftGenerated _)
        move.2 move.1).code (A := A) := by
  have hstate := congrArg Prod.fst
    (pairedRightSuccessorCode_lambdaOfStrategy A entry past)
  simp only at hstate
  rw [pairedRightFreshChildCodeLeft, hstate]
  apply Prod.ext
  · change
      A.step (entryState (A := A)
          (extendPrefix strategy entry.leftHistory
            (past.map rightEnvironment)))
          (rightRoundRecord move
            (blockSenderOne strategy entry.leftHistory (senderWord past) move.2)
            (blockReceiverTwo strategy entry.leftHistory past move)) =
        entryState (A := A)
          (History.append
            (extendPrefix strategy entry.leftHistory
              (past.map rightEnvironment))
            (nextRound strategy
              (extendPrefix strategy entry.leftHistory
                (past.map rightEnvironment))
              ⟨move.2, move.1, Graph.right⟩))
    rw [blockSenderOne_eq strategy entry.leftHistory past move]
    simp [entryState, History.append, List.foldl_append, nextRound,
      rightRoundRecord, blockReceiverTwo, rightEnvironment]
  · change
      A.step (entryState (A := A)
          (extendPrefix strategy entry.leftHistory
            (past.map rightEnvironment)))
          (bothRoundRecord (move.2, move.1)
            (strategy.one
              (nextView Proc.one
                (extendPrefix strategy entry.leftHistory
                  (past.map rightEnvironment))
                ⟨move.2, move.1, Graph.both⟩))
            (blockReceiverTwo strategy entry.leftHistory past move)) =
        entryState (A := A)
          (History.append
            (extendPrefix strategy entry.leftHistory
              (past.map rightEnvironment))
            (nextRound strategy
              (extendPrefix strategy entry.leftHistory
                (past.map rightEnvironment))
              ⟨move.2, move.1, Graph.both⟩))
    rw [blockReceiverTwo_eq_both]
    simp [entryState, History.append, List.foldl_append, nextRound,
      bothRoundRecord]

/-- Mirror row of the same raw-to-finite child calculation. -/
theorem pairedRightFreshChildCodeBoth_lambdaOfStrategy
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    pairedRightFreshChildCodeBoth A entry.code entry.lambdaOfStrategy past move =
      (procTwoFreshPair strategy
        (extendPrefix strategy entry.bothHistory (past.map rightEnvironment))
        (strategyGenerated_extendPrefix_basic strategy entry.bothGenerated _)
        move.2 move.1).code (A := A) := by
  have hstate := congrArg Prod.snd
    (pairedRightSuccessorCode_lambdaOfStrategy A entry past)
  simp only at hstate
  rw [pairedRightFreshChildCodeBoth, hstate]
  apply Prod.ext
  · change
      A.step (entryState (A := A)
          (extendPrefix strategy entry.bothHistory
            (past.map rightEnvironment)))
          (rightRoundRecord move
            (blockSenderOne strategy entry.leftHistory (senderWord past) move.2)
            (blockReceiverTwo strategy entry.bothHistory past move)) =
        entryState (A := A)
          (History.append
            (extendPrefix strategy entry.bothHistory
              (past.map rightEnvironment))
            (nextRound strategy
              (extendPrefix strategy entry.bothHistory
                (past.map rightEnvironment))
              ⟨move.2, move.1, Graph.right⟩))
    have hblind := congrArg
      (fun sender : SenderBlockStrategy In₁ Out₁ =>
        sender (senderWord past) move.2)
      entry.lambdaOfStrategy_blind_eq_both
    change blockSenderOne strategy entry.leftHistory (senderWord past) move.2 =
      blockSenderOne strategy entry.bothHistory (senderWord past) move.2 at hblind
    rw [hblind, blockSenderOne_eq strategy entry.bothHistory past move]
    simp [entryState, History.append, List.foldl_append, nextRound,
      rightRoundRecord, blockReceiverTwo, rightEnvironment]
  · change
      A.step (entryState (A := A)
          (extendPrefix strategy entry.bothHistory
            (past.map rightEnvironment)))
          (bothRoundRecord (move.2, move.1)
            (strategy.one
              (nextView Proc.one
                (extendPrefix strategy entry.bothHistory
                  (past.map rightEnvironment))
                ⟨move.2, move.1, Graph.both⟩))
            (blockReceiverTwo strategy entry.bothHistory past move)) =
        entryState (A := A)
          (History.append
            (extendPrefix strategy entry.bothHistory
              (past.map rightEnvironment))
            (nextRound strategy
              (extendPrefix strategy entry.bothHistory
                (past.map rightEnvironment))
              ⟨move.2, move.1, Graph.both⟩))
    rw [blockReceiverTwo_eq_both]
    simp [entryState, History.append, List.foldl_append, nextRound,
      bothRoundRecord]

/-- Appending process-two receive rounds to two bases with different
process-two views cannot make the resulting views equal, independently of
whether either receive graph is `right` or `both`. -/
theorem procTwo_receive_preserves_base_ne
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (hne : currentView Proc.two h ≠ currentView Proc.two h')
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .right ∨ r.graph = .both)
    (hr' : r'.graph = .right ∨ r'.graph = .both) :
    currentView Proc.two (History.append h r) ≠
      currentView Proc.two (History.append h' r') := by
  rw [currentView_two_append_recv h r hr,
    currentView_two_append_recv h' r' hr']
  intro heq
  exact hne (View.recv.inj heq).1

/-- **The four-corner successor test.**  Extend both old variants through an
arbitrary common right-block direction.  At either resolved old variant, the
next receive offers a fresh `right`/`both` pair.  Each row is one process-two
view class, while every cross-row pair is distinguishable.  Hence the four
histories split into two fresh classes of size two; they never form one
four-history class.

The tree direction chooses the resolved old variant (the row), and its child
is the corresponding fresh paired entry. -/
theorem procTwoFreshPairs_of_procOnePair_disjoint
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : ProcOnePairedEntryRep strategy)
    (moves : List (In₂ × In₁))
    (inputOne : In₁) (inputTwo : In₂) :
    let leftBase :=
      extendPrefix strategy entry.leftHistory (moves.map rightEnvironment)
    let bothBase :=
      extendPrefix strategy entry.bothHistory (moves.map rightEnvironment)
    let leftChild :=
      procTwoFreshPair strategy leftBase
        (strategyGenerated_extendPrefix_basic strategy entry.leftGenerated _)
        inputOne inputTwo
    let bothChild :=
      procTwoFreshPair strategy bothBase
        (strategyGenerated_extendPrefix_basic strategy entry.bothGenerated _)
        inputOne inputTwo
    currentView Proc.two leftChild.rightHistory =
        currentView Proc.two leftChild.bothHistory ∧
      currentView Proc.two bothChild.rightHistory =
        currentView Proc.two bothChild.bothHistory ∧
      currentView Proc.two leftChild.rightHistory ≠
        currentView Proc.two bothChild.rightHistory ∧
      currentView Proc.two leftChild.rightHistory ≠
        currentView Proc.two bothChild.bothHistory ∧
      currentView Proc.two leftChild.bothHistory ≠
        currentView Proc.two bothChild.rightHistory ∧
      currentView Proc.two leftChild.bothHistory ≠
        currentView Proc.two bothChild.bothHistory := by
  dsimp only
  have hbase :
      currentView Proc.two
          (extendPrefix strategy entry.leftHistory
            (moves.map rightEnvironment)) ≠
        currentView Proc.two
          (extendPrefix strategy entry.bothHistory
            (moves.map rightEnvironment)) :=
    procTwo_ne_preserved_by_right_extension strategy _ _ entry.other_view_ne moves
  refine ⟨(procTwoFreshPair strategy _ _ inputOne inputTwo).view_eq,
    (procTwoFreshPair strategy _ _ inputOne inputTwo).view_eq, ?_⟩
  let leftBase :=
    extendPrefix strategy entry.leftHistory (moves.map rightEnvironment)
  let bothBase :=
    extendPrefix strategy entry.bothHistory (moves.map rightEnvironment)
  let lr := nextRound strategy leftBase ⟨inputOne, inputTwo, Graph.right⟩
  let lb := nextRound strategy leftBase ⟨inputOne, inputTwo, Graph.both⟩
  let br := nextRound strategy bothBase ⟨inputOne, inputTwo, Graph.right⟩
  let bb := nextRound strategy bothBase ⟨inputOne, inputTwo, Graph.both⟩
  change
    currentView Proc.two (History.append leftBase lr) ≠
        currentView Proc.two (History.append bothBase br) ∧
      currentView Proc.two (History.append leftBase lr) ≠
        currentView Proc.two (History.append bothBase bb) ∧
      currentView Proc.two (History.append leftBase lb) ≠
        currentView Proc.two (History.append bothBase br) ∧
      currentView Proc.two (History.append leftBase lb) ≠
        currentView Proc.two (History.append bothBase bb)
  exact ⟨procTwo_receive_preserves_base_ne leftBase bothBase hbase lr br
      (Or.inl rfl) (Or.inl rfl),
    procTwo_receive_preserves_base_ne leftBase bothBase hbase lr bb
      (Or.inl rfl) (Or.inr rfl),
    procTwo_receive_preserves_base_ne leftBase bothBase hbase lb br
      (Or.inr rfl) (Or.inl rfl),
    procTwo_receive_preserves_base_ne leftBase bothBase hbase lb bb
      (Or.inr rfl) (Or.inr rfl)⟩

end DetParityAutomaton

end DistributedSynthesis
