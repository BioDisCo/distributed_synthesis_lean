/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedEntryTransitionFactor

/-!
# Mirror paired-entry transition factor

This file closes the process-two-pending/left-block orientation of the
paired-entry Bérard construction.  It is the literal semantic mirror of
`LemPairedEntryTransitionFactor`: process two is now the blind sender, the
ordered entry pair is `right`/`both`, and a reversal creates a fresh
process-one `left`/`both` pair.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- A paired left-block lambda.  Process two's sender fragment is shared by
the `right`/`both` entry variants; the informed process-one fragments remain
variant-indexed. -/
structure ProcTwoPairedLeftLambda where
  blind : SenderBlockStrategy In₂ Out₂
  informedRight : ReceiverBlockStrategy In₁ In₂ Out₁
  informedBoth : ReceiverBlockStrategy In₁ In₂ Out₁
  bothTwoRight : ReceiverBlockStrategy In₁ In₂ Out₂
  bothTwoBoth : ReceiverBlockStrategy In₁ In₂ Out₂

/-- Equal process-two base views yield equal complete left-block sender
fragments. -/
theorem blockSenderTwo_eq_of_view_eq
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    {h h' : History In₁ In₂ Graph Out₁ Out₂}
    (hview : currentView Proc.two h = currentView Proc.two h') :
    blockSenderTwo strategy h = blockSenderTwo strategy h' := by
  funext word input
  unfold blockSenderTwo
  rw [nextView_two_of_graph_left _ _ rfl,
    nextView_two_of_graph_left _ _ rfl]
  have hleft :
      ∀ env ∈ word.map
          (fun sIn => leftEnvironment ((default : In₁), sIn)),
        env.graph = Graph.left := by
    intro env henv
    rcases List.mem_map.mp henv with ⟨sIn, _, rfl⟩
    rfl
  rw [currentView_two_extendPrefix_left strategy h _ hleft,
    currentView_two_extendPrefix_left strategy h' _ hleft, hview]

namespace ProcTwoPairedEntryRep

/-- The possibly infinite shared lambda selected by the raw strategy at a
process-two paired entry. -/
def lambdaOfStrategy
    [Inhabited In₁]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcTwoPairedEntryRep strategy) :
    ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) where
  blind := blockSenderTwo strategy entry.rightHistory
  informedRight := blockReceiverOne strategy entry.rightHistory
  informedBoth := blockReceiverOne strategy entry.bothHistory
  bothTwoRight := fun node move =>
    strategy.two
      (nextView Proc.two
        (extendPrefix strategy entry.rightHistory (node.map leftEnvironment))
        ⟨move.1, move.2, Graph.both⟩)
  bothTwoBoth := fun node move =>
    strategy.two
      (nextView Proc.two
        (extendPrefix strategy entry.bothHistory (node.map leftEnvironment))
        ⟨move.1, move.2, Graph.both⟩)

theorem lambdaOfStrategy_blind_eq_both
    [Inhabited In₁]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcTwoPairedEntryRep strategy) :
    entry.lambdaOfStrategy.blind =
      blockSenderTwo strategy entry.bothHistory :=
  blockSenderTwo_eq_of_view_eq strategy entry.view_eq

end ProcTwoPairedEntryRep

/-- Play a finite left block from a paired lambda. -/
def pairedLeftWordFrom
    (blind : SenderBlockStrategy In₂ Out₂)
    (informed : ReceiverBlockStrategy In₁ In₂ Out₁) :
    List (In₁ × In₂) -> List (In₁ × In₂) ->
      List (RoundRecord In₁ In₂ Graph Out₁ Out₂)
  | _, [] => []
  | past, move :: rest =>
      leftRoundRecord move (informed past move)
          (blind (senderWord past) move.2) ::
        pairedLeftWordFrom blind informed (past ++ [move]) rest

def ProcTwoPairedLeftLambda.rightWord
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (moves : List (In₁ × In₂)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  pairedLeftWordFrom lambda.blind lambda.informedRight [] moves

def ProcTwoPairedLeftLambda.bothWord
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (moves : List (In₁ × In₂)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  pairedLeftWordFrom lambda.blind lambda.informedBoth [] moves

/-- History-free finite update for the mirror orientation. -/
def pairedLeftSuccessorCode
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (moves : List (In₁ × In₂)) : A.State × A.State :=
  ((lambda.rightWord moves).foldl A.step code.1,
    (lambda.bothWord moves).foldl A.step code.2)

/-- Fresh process-one child after resolving the old pair to its `right` row. -/
def pairedLeftFreshChildCodeRight
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    A.State × A.State :=
  let state := (pairedLeftSuccessorCode A code lambda past).1
  let outOne := lambda.informedRight past move
  let outTwoLeft := lambda.blind (senderWord past) move.2
  let outTwoBoth := lambda.bothTwoRight past move
  (A.step state (leftRoundRecord move outOne outTwoLeft),
    A.step state (bothRoundRecord move outOne outTwoBoth))

/-- Fresh child after resolving the old pair to its `both` row. -/
def pairedLeftFreshChildCodeBoth
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    A.State × A.State :=
  let state := (pairedLeftSuccessorCode A code lambda past).2
  let outOne := lambda.informedBoth past move
  let outTwoLeft := lambda.blind (senderWord past) move.2
  let outTwoBoth := lambda.bothTwoBoth past move
  (A.step state (leftRoundRecord move outOne outTwoLeft),
    A.step state (bothRoundRecord move outOne outTwoBoth))

theorem pairedLeftSuccessorCode_congr
    {code code' : A.State × A.State} (hcode : code = code')
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (moves : List (In₁ × In₂)) :
    pairedLeftSuccessorCode A code lambda moves =
      pairedLeftSuccessorCode A code' lambda moves := by
  rw [hcode]

theorem extendPrefix_eq_append_pairedLeftWordFrom
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (past moves : List (In₁ × In₂)) :
    extendPrefix strategy base ((past ++ moves).map leftEnvironment) =
      extendPrefix strategy base (past.map leftEnvironment) ++
        pairedLeftWordFrom (blockSenderTwo strategy base)
          (blockReceiverOne strategy base) past moves := by
  induction moves generalizing past with
  | nil => simp [pairedLeftWordFrom]
  | cons move rest ih =>
      have hrecord :
          leftRoundRecord move
              (blockReceiverOne strategy base past move)
              (blockSenderTwo strategy base (senderWord past) move.2) =
            nextRound strategy
              (extendPrefix strategy base (past.map leftEnvironment))
              (leftEnvironment move) := by
        rw [blockSenderTwo_eq strategy base past move]
        rfl
      calc
        extendPrefix strategy base
              ((past ++ move :: rest).map leftEnvironment) =
            extendPrefix strategy base
              (((past ++ [move]) ++ rest).map leftEnvironment) := by
                simp [List.append_assoc]
        _ = extendPrefix strategy base
                ((past ++ [move]).map leftEnvironment) ++
              pairedLeftWordFrom (blockSenderTwo strategy base)
                (blockReceiverOne strategy base) (past ++ [move]) rest := by
              exact ih (past ++ [move])
        _ = History.append
                (extendPrefix strategy base (past.map leftEnvironment))
                (nextRound strategy
                  (extendPrefix strategy base (past.map leftEnvironment))
                  (leftEnvironment move)) ++
              pairedLeftWordFrom (blockSenderTwo strategy base)
                (blockReceiverOne strategy base) (past ++ [move]) rest := by
              simp only [List.map_append, List.map_singleton]
              rw [extendPrefix_snoc]
        _ = extendPrefix strategy base (past.map leftEnvironment) ++
              leftRoundRecord move
                  (blockReceiverOne strategy base past move)
                  (blockSenderTwo strategy base (senderWord past) move.2) ::
                pairedLeftWordFrom (blockSenderTwo strategy base)
                  (blockReceiverOne strategy base) (past ++ [move]) rest := by
              rw [hrecord]
              simp [History.append, List.append_assoc]
        _ = extendPrefix strategy base (past.map leftEnvironment) ++
              pairedLeftWordFrom (blockSenderTwo strategy base)
                (blockReceiverOne strategy base) past (move :: rest) := by
              rw [pairedLeftWordFrom]

/-- The mirror finite update reproduces both real strategy histories. -/
theorem pairedLeftSuccessorCode_lambdaOfStrategy
    [Inhabited In₁]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcTwoPairedEntryRep strategy)
    (moves : List (In₁ × In₂)) :
    pairedLeftSuccessorCode A entry.code entry.lambdaOfStrategy moves =
      (entryState (A := A)
          (extendPrefix strategy entry.rightHistory
            (moves.map leftEnvironment)),
        entryState (A := A)
          (extendPrefix strategy entry.bothHistory
            (moves.map leftEnvironment))) := by
  have hright :=
    extendPrefix_eq_append_pairedLeftWordFrom
      strategy entry.rightHistory [] moves
  have hboth :=
    extendPrefix_eq_append_pairedLeftWordFrom
      strategy entry.bothHistory [] moves
  simp only [List.nil_append, List.map_nil, extendPrefix_nil,
    ProcTwoPairedEntryRep.lambdaOfStrategy] at hright ⊢
  rw [← entry.lambdaOfStrategy_blind_eq_both] at hboth
  simp only [List.nil_append, List.map_nil, extendPrefix_nil,
    ProcTwoPairedEntryRep.lambdaOfStrategy] at hboth
  apply Prod.ext
  · change
      (pairedLeftWordFrom (blockSenderTwo strategy entry.rightHistory)
          (blockReceiverOne strategy entry.rightHistory) [] moves).foldl A.step
          (entryState (A := A) entry.rightHistory) =
        entryState (A := A)
          (extendPrefix strategy entry.rightHistory
            (moves.map leftEnvironment))
    rw [hright]
    simp [entryState, List.foldl_append]
  · change
      (pairedLeftWordFrom (blockSenderTwo strategy entry.rightHistory)
          (blockReceiverOne strategy entry.bothHistory) [] moves).foldl A.step
          (entryState (A := A) entry.bothHistory) =
        entryState (A := A)
          (extendPrefix strategy entry.bothHistory
            (moves.map leftEnvironment))
    rw [hboth]
    simp [entryState, List.foldl_append]

/-! ## Successor-class stitching -/

/-- Different process-one views remain different under a common left-block
extension. -/
theorem procOne_ne_preserved_by_left_extension
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (hne : currentView Proc.one h ≠ currentView Proc.one h')
    (moves : List (In₁ × In₂)) :
    currentView Proc.one
        (extendPrefix strategy h (moves.map leftEnvironment)) ≠
      currentView Proc.one
        (extendPrefix strategy h' (moves.map leftEnvironment)) := by
  induction moves using List.reverseRecOn with
  | nil => simpa using hne
  | append_singleton moves move ih =>
      simp only [List.map_append, List.map_singleton]
      rw [extendPrefix_snoc, extendPrefix_snoc]
      simp only [currentView_one_append, nextRound]
      intro heq
      exact ih (View.recv.inj heq).1

/-- The informed process distinguishes the two histories of a process-two
pending pair. -/
theorem ProcTwoPairedEntryRep.other_view_ne
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcTwoPairedEntryRep strategy) :
    currentView Proc.one entry.rightHistory ≠
      currentView Proc.one entry.bothHistory := by
  obtain ⟨base, rRight, rBoth, suffix, _hinOne, _hinTwo, hright, hboth,
    hsuffix, hentryRight, hentryBoth⟩ := entry.pending
  rw [hentryRight, hentryBoth]
  apply procOne_ne_preserved_by_left_suffix
  · simp [currentView_one_append, hright, hboth]
  · exact hsuffix

/-- Create the fresh process-one `left`/`both` pair at a generated base. -/
def procOneFreshPair
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (hgen : StrategyGeneratedPrefix strategy base)
    (inputOne : In₁) (inputTwo : In₂) :
    ProcOnePairedEntryRep strategy where
  leftHistory :=
    History.append base
      (nextRound strategy base ⟨inputOne, inputTwo, Graph.left⟩)
  bothHistory :=
    History.append base
      (nextRound strategy base ⟨inputOne, inputTwo, Graph.both⟩)
  leftGenerated := StrategyGeneratedPrefix.append hgen _
  bothGenerated := StrategyGeneratedPrefix.append hgen _
  pending := ⟨base,
    nextRound strategy base ⟨inputOne, inputTwo, Graph.left⟩,
    nextRound strategy base ⟨inputOne, inputTwo, Graph.both⟩,
    [], by simp [nextRound]⟩

/-- The process-one receiver output on `left` is also its output on the
indistinguishable `both` alternative. -/
theorem blockReceiverOne_eq_both
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    blockReceiverOne strategy base past move =
      strategy.one
        (nextView Proc.one
          (extendPrefix strategy base (past.map leftEnvironment))
          ⟨move.1, move.2, Graph.both⟩) := by
  rfl

/-- The finite right-row child computation is the actual fresh pair code. -/
theorem pairedLeftFreshChildCodeRight_lambdaOfStrategy
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    pairedLeftFreshChildCodeRight A entry.code entry.lambdaOfStrategy past move =
      (procOneFreshPair strategy
        (extendPrefix strategy entry.rightHistory (past.map leftEnvironment))
        (strategyGenerated_extendPrefix_basic strategy entry.rightGenerated _)
        move.1 move.2).code (A := A) := by
  have hstate := congrArg Prod.fst
    (pairedLeftSuccessorCode_lambdaOfStrategy A entry past)
  simp only at hstate
  rw [pairedLeftFreshChildCodeRight, hstate]
  apply Prod.ext
  · change
      A.step (entryState (A := A)
          (extendPrefix strategy entry.rightHistory
            (past.map leftEnvironment)))
          (leftRoundRecord move
            (blockReceiverOne strategy entry.rightHistory past move)
            (blockSenderTwo strategy entry.rightHistory
              (senderWord past) move.2)) =
        entryState (A := A)
          (History.append
            (extendPrefix strategy entry.rightHistory
              (past.map leftEnvironment))
            (nextRound strategy
              (extendPrefix strategy entry.rightHistory
                (past.map leftEnvironment))
              ⟨move.1, move.2, Graph.left⟩))
    rw [blockSenderTwo_eq strategy entry.rightHistory past move]
    simp [entryState, History.append, List.foldl_append, nextRound,
      leftRoundRecord, blockReceiverOne, leftEnvironment]
  · change
      A.step (entryState (A := A)
          (extendPrefix strategy entry.rightHistory
            (past.map leftEnvironment)))
          (bothRoundRecord move
            (blockReceiverOne strategy entry.rightHistory past move)
            (strategy.two
              (nextView Proc.two
                (extendPrefix strategy entry.rightHistory
                  (past.map leftEnvironment))
                ⟨move.1, move.2, Graph.both⟩))) =
        entryState (A := A)
          (History.append
            (extendPrefix strategy entry.rightHistory
              (past.map leftEnvironment))
            (nextRound strategy
              (extendPrefix strategy entry.rightHistory
                (past.map leftEnvironment))
              ⟨move.1, move.2, Graph.both⟩))
    rw [blockReceiverOne_eq_both]
    simp [entryState, History.append, List.foldl_append, nextRound,
      bothRoundRecord]

/-- The finite `both`-row child computation is the actual fresh pair code. -/
theorem pairedLeftFreshChildCodeBoth_lambdaOfStrategy
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    pairedLeftFreshChildCodeBoth A entry.code entry.lambdaOfStrategy past move =
      (procOneFreshPair strategy
        (extendPrefix strategy entry.bothHistory (past.map leftEnvironment))
        (strategyGenerated_extendPrefix_basic strategy entry.bothGenerated _)
        move.1 move.2).code (A := A) := by
  have hstate := congrArg Prod.snd
    (pairedLeftSuccessorCode_lambdaOfStrategy A entry past)
  simp only at hstate
  rw [pairedLeftFreshChildCodeBoth, hstate]
  apply Prod.ext
  · change
      A.step (entryState (A := A)
          (extendPrefix strategy entry.bothHistory
            (past.map leftEnvironment)))
          (leftRoundRecord move
            (blockReceiverOne strategy entry.bothHistory past move)
            (blockSenderTwo strategy entry.rightHistory
              (senderWord past) move.2)) =
        entryState (A := A)
          (History.append
            (extendPrefix strategy entry.bothHistory
              (past.map leftEnvironment))
            (nextRound strategy
              (extendPrefix strategy entry.bothHistory
                (past.map leftEnvironment))
              ⟨move.1, move.2, Graph.left⟩))
    have hblind := congrArg
      (fun sender : SenderBlockStrategy In₂ Out₂ =>
        sender (senderWord past) move.2)
      entry.lambdaOfStrategy_blind_eq_both
    change blockSenderTwo strategy entry.rightHistory (senderWord past) move.2 =
      blockSenderTwo strategy entry.bothHistory (senderWord past) move.2 at hblind
    rw [hblind, blockSenderTwo_eq strategy entry.bothHistory past move]
    simp [entryState, History.append, List.foldl_append, nextRound,
      leftRoundRecord, blockReceiverOne, leftEnvironment]
  · change
      A.step (entryState (A := A)
          (extendPrefix strategy entry.bothHistory
            (past.map leftEnvironment)))
          (bothRoundRecord move
            (blockReceiverOne strategy entry.bothHistory past move)
            (strategy.two
              (nextView Proc.two
                (extendPrefix strategy entry.bothHistory
                  (past.map leftEnvironment))
                ⟨move.1, move.2, Graph.both⟩))) =
        entryState (A := A)
          (History.append
            (extendPrefix strategy entry.bothHistory
              (past.map leftEnvironment))
            (nextRound strategy
              (extendPrefix strategy entry.bothHistory
                (past.map leftEnvironment))
              ⟨move.1, move.2, Graph.both⟩))
    rw [blockReceiverOne_eq_both]
    simp [entryState, History.append, List.foldl_append, nextRound,
      bothRoundRecord]

/-- Receiving on `left` or `both` preserves inequality of the old
process-one views. -/
theorem procOne_receive_preserves_base_ne
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (hne : currentView Proc.one h ≠ currentView Proc.one h')
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .left ∨ r.graph = .both)
    (hr' : r'.graph = .left ∨ r'.graph = .both) :
    currentView Proc.one (History.append h r) ≠
      currentView Proc.one (History.append h' r') := by
  rw [currentView_one_append_recv h r hr,
    currentView_one_append_recv h' r' hr']
  intro heq
  exact hne (View.recv.inj heq).1

/-- Mirror four-corner test: the four apparent continuations split into two
fresh process-one pairs and never accumulate into one four-history class. -/
theorem procOneFreshPairs_of_procTwoPair_disjoint
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : ProcTwoPairedEntryRep strategy)
    (moves : List (In₁ × In₂))
    (inputOne : In₁) (inputTwo : In₂) :
    let rightBase :=
      extendPrefix strategy entry.rightHistory (moves.map leftEnvironment)
    let bothBase :=
      extendPrefix strategy entry.bothHistory (moves.map leftEnvironment)
    let rightChild :=
      procOneFreshPair strategy rightBase
        (strategyGenerated_extendPrefix_basic strategy entry.rightGenerated _)
        inputOne inputTwo
    let bothChild :=
      procOneFreshPair strategy bothBase
        (strategyGenerated_extendPrefix_basic strategy entry.bothGenerated _)
        inputOne inputTwo
    currentView Proc.one rightChild.leftHistory =
        currentView Proc.one rightChild.bothHistory ∧
      currentView Proc.one bothChild.leftHistory =
        currentView Proc.one bothChild.bothHistory ∧
      currentView Proc.one rightChild.leftHistory ≠
        currentView Proc.one bothChild.leftHistory ∧
      currentView Proc.one rightChild.leftHistory ≠
        currentView Proc.one bothChild.bothHistory ∧
      currentView Proc.one rightChild.bothHistory ≠
        currentView Proc.one bothChild.leftHistory ∧
      currentView Proc.one rightChild.bothHistory ≠
        currentView Proc.one bothChild.bothHistory := by
  dsimp only
  have hbase :
      currentView Proc.one
          (extendPrefix strategy entry.rightHistory
            (moves.map leftEnvironment)) ≠
        currentView Proc.one
          (extendPrefix strategy entry.bothHistory
            (moves.map leftEnvironment)) :=
    procOne_ne_preserved_by_left_extension strategy _ _ entry.other_view_ne moves
  refine ⟨(procOneFreshPair strategy _ _ inputOne inputTwo).view_eq,
    (procOneFreshPair strategy _ _ inputOne inputTwo).view_eq, ?_⟩
  let rightBase :=
    extendPrefix strategy entry.rightHistory (moves.map leftEnvironment)
  let bothBase :=
    extendPrefix strategy entry.bothHistory (moves.map leftEnvironment)
  let rl := nextRound strategy rightBase ⟨inputOne, inputTwo, Graph.left⟩
  let rb := nextRound strategy rightBase ⟨inputOne, inputTwo, Graph.both⟩
  let bl := nextRound strategy bothBase ⟨inputOne, inputTwo, Graph.left⟩
  let bb := nextRound strategy bothBase ⟨inputOne, inputTwo, Graph.both⟩
  change
    currentView Proc.one (History.append rightBase rl) ≠
        currentView Proc.one (History.append bothBase bl) ∧
      currentView Proc.one (History.append rightBase rl) ≠
        currentView Proc.one (History.append bothBase bb) ∧
      currentView Proc.one (History.append rightBase rb) ≠
        currentView Proc.one (History.append bothBase bl) ∧
      currentView Proc.one (History.append rightBase rb) ≠
        currentView Proc.one (History.append bothBase bb)
  exact ⟨procOne_receive_preserves_base_ne rightBase bothBase hbase rl bl
      (Or.inl rfl) (Or.inl rfl),
    procOne_receive_preserves_base_ne rightBase bothBase hbase rl bb
      (Or.inl rfl) (Or.inr rfl),
    procOne_receive_preserves_base_ne rightBase bothBase hbase rb bl
      (Or.inr rfl) (Or.inl rfl),
    procOne_receive_preserves_base_ne rightBase bothBase hbase rb bb
      (Or.inr rfl) (Or.inr rfl)⟩

end DetParityAutomaton

end DistributedSynthesis
