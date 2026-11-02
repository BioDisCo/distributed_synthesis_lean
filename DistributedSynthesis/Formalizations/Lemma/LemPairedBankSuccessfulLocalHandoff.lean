/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedBankLocalHandoff

/-!
# Inverting a successful feasible-bank handoff

This is the feasible-policy-bank form of the paired-entry receiver inversion.
It is the form consumed after the delayed initial block: a successful finite
receiver step preserves the selected bank entry and exposes the exact
`Allowed` edge of that entry's single rational policy.

The result is proof-side only.  The receiver computation remains graph-blind
and leader-blind and uses exactly the locally available finite controls.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- A successful recurrent right-block receiver step keeps the same feasible
bank and is exactly an `Allowed` edge of that bank's rational policy. -/
theorem stepBankRightReceiverFor_some_exact
    (source : BankRightMacro A)
    (ownerControl : (bankRightControllerAt A source).Control)
    (row : PairedEntryRow)
    (monitorState : (bankRightMonitorAt A source).State)
    (move : In₂ × In₁)
    (target : BankLeftMacro A)
    (hstage :
      (stepBankRightReceiverFor A source ownerControl row monitorState
        move).2.2 = some target) :
    target.1 = source.1 ∧
      target.2.1 =
        bankRightCloseMacro A source monitorState.2.1 row
          (move,
            (bankRightControllerAt A source).labelOf ownerControl |>.2
              monitorState move,
            (bankRightControllerAt A source).labelOf ownerControl |>.1
              move.2) ∧
      PairedRationalPolicy.Allowed A (feasiblePolicy A source.1)
        (Sum.inr (Sum.inl source.2.1))
        (Sum.inr (Sum.inr target.2.1)) := by
  classical
  unfold stepBankRightReceiverFor at hstage
  dsimp only at hstage
  split at hstage
  · rename_i hallowed
    simp only [Option.some.injEq] at hstage
    subst target
    exact ⟨rfl, rfl, hallowed⟩
  · simp at hstage

/-- Left-block mirror of `stepBankRightReceiverFor_some_exact`. -/
theorem stepBankLeftReceiverFor_some_exact
    (source : BankLeftMacro A)
    (ownerControl : (bankLeftControllerAt A source).Control)
    (row : PairedEntryRow)
    (monitorState : (bankLeftMonitorAt A source).State)
    (move : In₁ × In₂)
    (target : BankRightMacro A)
    (hstage :
      (stepBankLeftReceiverFor A source ownerControl row monitorState
        move).2.2 = some target) :
    target.1 = source.1 ∧
      target.2.1 =
        bankLeftCloseMacro A source monitorState.2.1 row
          (move,
            (bankLeftControllerAt A source).labelOf ownerControl |>.2
              monitorState move,
            (bankLeftControllerAt A source).labelOf ownerControl |>.1
              move.2) ∧
      PairedRationalPolicy.Allowed A (feasiblePolicy A source.1)
        (Sum.inr (Sum.inr source.2.1))
        (Sum.inr (Sum.inl target.2.1)) := by
  classical
  unfold stepBankLeftReceiverFor at hstage
  dsimp only at hstage
  split at hstage
  · rename_i hallowed
    simp only [Option.some.injEq] at hstage
    subst target
    exact ⟨rfl, rfl, hallowed⟩
  · simp at hstage

end DetParityAutomaton

end DistributedSynthesis
