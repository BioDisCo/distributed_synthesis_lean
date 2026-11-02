/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialLocallyConsistentNarrowing

/-!
# Finite local readback of the initial blocks

The table-first extraction gives a finite rational-tree control and a finite
block-monitor control.  This file packages their product as the actual finite
state carried during an initial one-directional block.  At a reversing round,
the process that does not receive evaluates its table at an arbitrary default
partner input.  Local consistency proves that this finite, locally available
answer is equal to the semantic readback at the real (hidden) partner input.

There is no strict-leader bit in these states or steps.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

variable [Inhabited In₁] [Inhabited In₂]

/-! ## Initial-left finite control -/

/-- Finite state jointly tracking the rational sender tree and the pinned
initial-left monitor.  Both components can be maintained by the informed
process during a left block. -/
abbrev InitialLeftFiniteReadbackState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy) :=
  controllers.leftController.Control ×
    ((initialLeftBlockMonitor A).rootPinned
      (fun move => initialLeftLetterAt
        (initialLeftLambdaOfStrategy strategy) [] move)).State

noncomputable def initialLeftFiniteReadbackInitial
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy) :
    InitialLeftFiniteReadbackState A strategy controllers :=
  (controllers.leftController.initial,
    ((initialLeftBlockMonitor A).rootPinned
      (fun move => initialLeftLetterAt
        (initialLeftLambdaOfStrategy strategy) [] move)).initial)

/-- One ordinary left-block update.  The informed process knows the complete
move; the rational-tree component itself advances only on process two's
input, exactly as required by the blind process-two copy. -/
noncomputable def stepInitialLeftFiniteReadback
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (state : InitialLeftFiniteReadbackState A strategy controllers)
    (move : In₁ × In₂) :
    InitialLeftFiniteReadbackState A strategy controllers :=
  let monitor := (initialLeftBlockMonitor A).rootPinned
    (fun current => initialLeftLetterAt
      (initialLeftLambdaOfStrategy strategy) [] current)
  let label := controllers.leftController.labelOf state.1
  (controllers.leftController.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def initialLeftFiniteReadbackAfter
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (past : List (In₁ × In₂)) :
    InitialLeftFiniteReadbackState A strategy controllers :=
  past.foldl (stepInitialLeftFiniteReadback A strategy controllers)
    (initialLeftFiniteReadbackInitial A strategy controllers)

/-- The explicit finite product computes exactly the two semantic controls
used by the pinned-controller lambda. -/
theorem initialLeftFiniteReadbackAfter_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy) :
    ∀ past : List (In₁ × In₂),
    initialLeftFiniteReadbackAfter A strategy controllers past =
      (controllers.leftController.controlAt (senderWord past),
        narrowedControl
          ((initialLeftBlockMonitor A).rootPinned
            (fun move => initialLeftLetterAt
              (initialLeftLambdaOfStrategy strategy) [] move))
          controllers.leftController.labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [initialLeftFiniteReadbackAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepInitialLeftFiniteReadback A strategy controllers
        (initialLeftFiniteReadbackAfter A strategy controllers past) move = _
      rw [ih]
      rw [senderWord_append,
        TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

/-- The process-one action at a right close, computed without the hidden
current input of process two. -/
noncomputable def initialLeftNoRecvOneOutput
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (state : InitialLeftFiniteReadbackState A strategy controllers)
    (inputOne : In₁) : Out₁ :=
  ((controllers.leftController.labelOf state.1).2 state.2
    (inputOne, default)).reversingOne

/-- The finite no-receive action agrees with the semantic controller at
every real partner input.  This is the executable local-action bridge. -/
theorem initialLeftNoRecvOneOutput_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (past : List (In₁ × In₂)) (inputOne : In₁) (inputTwo : In₂) :
    initialLeftNoRecvOneOutput A strategy controllers
        (initialLeftFiniteReadbackAfter A strategy controllers past) inputOne =
      (initialLeftLambdaOfPinnedController A strategy
        controllers.toRootCompatibleInitialControllers).reversingOne
        past (inputOne, inputTwo) := by
  rw [initialLeftFiniteReadbackAfter_eq]
  change
    (initialLeftLambdaOfPinnedController A strategy
      controllers.toRootCompatibleInitialControllers).reversingOne
        past (inputOne, default) = _
  exact controllers.left_reversingOne_independent A strategy past inputOne
    default inputTwo

/-! ## Initial-right finite control -/

/-- Mirror finite product for an initial right block. -/
abbrev InitialRightFiniteReadbackState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy) :=
  controllers.rightController.Control ×
    ((initialRightBlockMonitor A).rootPinned
      (fun move => initialRightLetterAt
        (initialRightLambdaOfStrategy strategy) [] move)).State

noncomputable def initialRightFiniteReadbackInitial
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy) :
    InitialRightFiniteReadbackState A strategy controllers :=
  (controllers.rightController.initial,
    ((initialRightBlockMonitor A).rootPinned
      (fun move => initialRightLetterAt
        (initialRightLambdaOfStrategy strategy) [] move)).initial)

noncomputable def stepInitialRightFiniteReadback
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (state : InitialRightFiniteReadbackState A strategy controllers)
    (move : In₂ × In₁) :
    InitialRightFiniteReadbackState A strategy controllers :=
  let monitor := (initialRightBlockMonitor A).rootPinned
    (fun current => initialRightLetterAt
      (initialRightLambdaOfStrategy strategy) [] current)
  let label := controllers.rightController.labelOf state.1
  (controllers.rightController.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def initialRightFiniteReadbackAfter
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (past : List (In₂ × In₁)) :
    InitialRightFiniteReadbackState A strategy controllers :=
  past.foldl (stepInitialRightFiniteReadback A strategy controllers)
    (initialRightFiniteReadbackInitial A strategy controllers)

theorem initialRightFiniteReadbackAfter_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy) :
    ∀ past : List (In₂ × In₁),
    initialRightFiniteReadbackAfter A strategy controllers past =
      (controllers.rightController.controlAt (senderWord past),
        narrowedControl
          ((initialRightBlockMonitor A).rootPinned
            (fun move => initialRightLetterAt
              (initialRightLambdaOfStrategy strategy) [] move))
          controllers.rightController.labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [initialRightFiniteReadbackAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepInitialRightFiniteReadback A strategy controllers
        (initialRightFiniteReadbackAfter A strategy controllers past) move = _
      rw [ih]
      rw [senderWord_append,
        TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

/-- Process-two action at a left close, without process one's hidden current
input. -/
noncomputable def initialRightNoRecvTwoOutput
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (state : InitialRightFiniteReadbackState A strategy controllers)
    (inputTwo : In₂) : Out₂ :=
  ((controllers.rightController.labelOf state.1).2 state.2
    (inputTwo, default)).reversingTwo

theorem initialRightNoRecvTwoOutput_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (past : List (In₂ × In₁)) (inputTwo : In₂) (inputOne : In₁) :
    initialRightNoRecvTwoOutput A strategy controllers
        (initialRightFiniteReadbackAfter A strategy controllers past) inputTwo =
      (initialRightLambdaOfPinnedController A strategy
        controllers.toRootCompatibleInitialControllers).reversingTwo
        past (inputTwo, inputOne) := by
  rw [initialRightFiniteReadbackAfter_eq]
  change
    (initialRightLambdaOfPinnedController A strategy
      controllers.toRootCompatibleInitialControllers).reversingTwo
        past (inputTwo, default) = _
  exact controllers.right_reversingTwo_independent A strategy past inputTwo
    default inputOne

end

end DetParityAutomaton

end DistributedSynthesis
