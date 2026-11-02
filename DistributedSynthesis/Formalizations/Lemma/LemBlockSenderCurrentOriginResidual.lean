/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedEntryTransitionFactorMirror

/-!
# Current-origin residuals for blind block senders

The finite-family table used across a strict cut has to be chosen at the
current common origin.  It must not be chosen independently after the hidden
input has already selected one semantic child.  The equations in this file
make the needed timing change explicit: retaining a sender control after a
finite one-sided prefix is the same as retaining the residual of the one
sender strategy chosen at the origin.

The hidden partner inputs disappear by local-view equality.  No graph side,
leader bit, hierarchy bit, or semantic representative is supplied to an
executable sender.
-/

namespace DistributedSynthesis

universe u v x y

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-! ## Pure residual equations -/

/-- Reading a visible prefix from a process-one sender strategy and then
continuing is definitionally the sender strategy rooted after the canonical
strict-right completion of that prefix. -/
theorem blockSenderOne_append_residual
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (headWord suffix : List In₁) (input : In₁) :
    blockSenderOne strategy base (headWord ++ suffix) input =
      blockSenderOne strategy
        (extendPrefix strategy base
          (headWord.map
            (fun senderInput =>
              rightEnvironment ((default : In₂), senderInput))))
        suffix input := by
  unfold blockSenderOne
  simp only [List.map_append]
  rw [show
    extendPrefix strategy base
        (headWord.map
            (fun senderInput =>
              rightEnvironment ((default : In₂), senderInput)) ++
          suffix.map
            (fun senderInput =>
              rightEnvironment ((default : In₂), senderInput))) =
      extendPrefix strategy
        (extendPrefix strategy base
          (headWord.map
            (fun senderInput =>
              rightEnvironment ((default : In₂), senderInput))))
        (suffix.map
          (fun senderInput =>
            rightEnvironment ((default : In₂), senderInput))) by
      simp [extendPrefix, List.foldl_append]]

/-- Process-two mirror of `blockSenderOne_append_residual`. -/
theorem blockSenderTwo_append_residual
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (headWord suffix : List In₂) (input : In₂) :
    blockSenderTwo strategy base (headWord ++ suffix) input =
      blockSenderTwo strategy
        (extendPrefix strategy base
          (headWord.map
            (fun senderInput =>
              leftEnvironment ((default : In₁), senderInput))))
        suffix input := by
  unfold blockSenderTwo
  simp only [List.map_append]
  rw [show
    extendPrefix strategy base
        (headWord.map
            (fun senderInput =>
              leftEnvironment ((default : In₁), senderInput)) ++
          suffix.map
            (fun senderInput =>
              leftEnvironment ((default : In₁), senderInput))) =
      extendPrefix strategy
        (extendPrefix strategy base
          (headWord.map
            (fun senderInput =>
              leftEnvironment ((default : In₁), senderInput))))
        (suffix.map
          (fun senderInput =>
            leftEnvironment ((default : In₁), senderInput))) by
      simp [extendPrefix, List.foldl_append]]

/-! ## Actual one-sided prefixes -/

/-- Partner inputs in an actual strict-right prefix do not change the
process-one residual sender. -/
theorem blockSenderOne_after_right_prefix_eq_canonical
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (moves : List (In₂ × In₁)) :
    blockSenderOne strategy
        (extendPrefix strategy base (moves.map rightEnvironment)) =
      blockSenderOne strategy
        (extendPrefix strategy base
          ((senderWord moves).map
            (fun senderInput =>
              rightEnvironment ((default : In₂), senderInput)))) := by
  apply blockSenderOne_eq_of_view_eq strategy
  rw [currentView_one_extendPrefix_right strategy,
    currentView_one_extendPrefix_right strategy]
  · simp [senderWord, rightEnvironment, List.foldl_map, List.map_map,
      Function.comp_def]
  · intro env henv
    rcases List.mem_map.mp henv with ⟨senderInput, _, rfl⟩
    rfl
  · intro env henv
    rcases List.mem_map.mp henv with ⟨move, _, rfl⟩
    rfl

/-- Partner inputs in an actual strict-left prefix do not change the
process-two residual sender. -/
theorem blockSenderTwo_after_left_prefix_eq_canonical
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (moves : List (In₁ × In₂)) :
    blockSenderTwo strategy
        (extendPrefix strategy base (moves.map leftEnvironment)) =
      blockSenderTwo strategy
        (extendPrefix strategy base
          ((senderWord moves).map
            (fun senderInput =>
              leftEnvironment ((default : In₁), senderInput)))) := by
  apply blockSenderTwo_eq_of_view_eq strategy
  rw [currentView_two_extendPrefix_left strategy,
    currentView_two_extendPrefix_left strategy]
  · simp [senderWord, leftEnvironment, List.foldl_map, List.map_map,
      Function.comp_def]
  · intro env henv
    rcases List.mem_map.mp henv with ⟨senderInput, _, rfl⟩
    rfl
  · intro env henv
    rcases List.mem_map.mp henv with ⟨move, _, rfl⟩
    rfl

/-- Full current-origin equation for a process-one strict-right block.  The
left side is the one sender selected at the origin; the right side is its
semantic residual after an arbitrary actual one-sided prefix. -/
theorem blockSenderOne_currentOrigin_residual
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (moves : List (In₂ × In₁)) (suffix : List In₁) (input : In₁) :
    blockSenderOne strategy base (senderWord moves ++ suffix) input =
      blockSenderOne strategy
        (extendPrefix strategy base (moves.map rightEnvironment)) suffix input := by
  rw [blockSenderOne_append_residual]
  exact congrFun
    (congrFun
      (blockSenderOne_after_right_prefix_eq_canonical strategy base moves).symm
      suffix) input

/-- Full current-origin equation for a process-two strict-left block. -/
theorem blockSenderTwo_currentOrigin_residual
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (moves : List (In₁ × In₂)) (suffix : List In₂) (input : In₂) :
    blockSenderTwo strategy base (senderWord moves ++ suffix) input =
      blockSenderTwo strategy
        (extendPrefix strategy base (moves.map leftEnvironment)) suffix input := by
  rw [blockSenderTwo_append_residual]
  exact congrFun
    (congrFun
      (blockSenderTwo_after_left_prefix_eq_canonical strategy base moves).symm
      suffix) input

end DetParityAutomaton

end DistributedSynthesis
