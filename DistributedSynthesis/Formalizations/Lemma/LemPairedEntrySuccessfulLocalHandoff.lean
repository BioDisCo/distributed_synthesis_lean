/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryLocalHandoff

/-!
# Inverting a successful paired-entry local handoff

The receiver steps in `ThmPairedEntryLocalHandoff` are total: outside the
checked part of the finite controller they return no staged successor.  This
file proves the converse fact needed by an acceptance trace.  Whenever a
receiver does return a successor, that successor is exactly the finite close
computed by the current scan, it keeps the same root policy, and it is an
`Allowed` edge of that policy.

These are proof-side inversion lemmas.  The executable receiver still uses
only its finite controller state, its locally retained entry row, the delivered
owner control, and the current inputs.  No graph, orientation, leader, or
strict-leader bit is added.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  {strategy : StrategyPair In₁ In₂ Out₁ Out₂}

namespace FirstEntryFinitePolicyFamilies

variable
  (families : FirstEntryFinitePolicyFamilies A strategy)

/-- A successful right-block receiver step exposes the exact checked edge of
the unchanged root policy. -/
theorem stepRightReceiverFor_some_exact
    (source : ReachableRightMacro A families)
    (ownerControl : (rightControllerAt A families source).Control)
    (row : PairedEntryRow)
    (monitorState : (rightMonitorAt A families source).State)
    (move : In₂ × In₁)
    (target : ReachableLeftMacro A families)
    (hstage :
      (stepRightReceiverFor A families source ownerControl row monitorState
        move).2.2 = some target) :
    target.1 = source.1 ∧
      target.2.1 =
        rightCloseMacro A families source monitorState.2.1 row
          (move,
            (rightControllerAt A families source).labelOf ownerControl |>.2
              monitorState move,
            (rightControllerAt A families source).labelOf ownerControl |>.1
              move.2) ∧
      PairedRationalPolicy.Allowed A (rootPolicy A families source.1)
        (rightMacroState A source.2.1) (leftMacroState A target.2.1) := by
  classical
  unfold stepRightReceiverFor at hstage
  dsimp only at hstage
  split at hstage
  · rename_i hallowed
    simp only [Option.some.injEq] at hstage
    subst target
    exact ⟨rfl, rfl, hallowed⟩
  · simp at hstage

/-- Left-block mirror of `stepRightReceiverFor_some_exact`. -/
theorem stepLeftReceiverFor_some_exact
    (source : ReachableLeftMacro A families)
    (ownerControl : (leftControllerAt A families source).Control)
    (row : PairedEntryRow)
    (monitorState : (leftMonitorAt A families source).State)
    (move : In₁ × In₂)
    (target : ReachableRightMacro A families)
    (hstage :
      (stepLeftReceiverFor A families source ownerControl row monitorState
        move).2.2 = some target) :
    target.1 = source.1 ∧
      target.2.1 =
        leftCloseMacro A families source monitorState.2.1 row
          (move,
            (leftControllerAt A families source).labelOf ownerControl |>.2
              monitorState move,
            (leftControllerAt A families source).labelOf ownerControl |>.1
              move.2) ∧
      PairedRationalPolicy.Allowed A (rootPolicy A families source.1)
        (leftMacroState A source.2.1) (rightMacroState A target.2.1) := by
  classical
  unfold stepLeftReceiverFor at hstage
  dsimp only at hstage
  split at hstage
  · rename_i hallowed
    simp only [Option.some.injEq] at hstage
    subst target
    exact ⟨rfl, rfl, hallowed⟩
  · simp at hstage

end FirstEntryFinitePolicyFamilies

end DetParityAutomaton

end DistributedSynthesis
