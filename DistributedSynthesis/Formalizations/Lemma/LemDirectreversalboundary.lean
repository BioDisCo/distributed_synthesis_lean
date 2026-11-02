/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemSyncblockinfo
import DistributedSynthesis.Formalizations.Lemma.LemHistoryembedding

/-!
# Direct reversal boundaries

This file packages the view-equation part of Lemma
`lem:directreversalboundary`.
-/

namespace DistributedSynthesis

universe u v x y

/-- At a left-to-right reversal, process `2` receives both previous views and current inputs. -/
theorem directReversal_leftToRight_receiver_view
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .right) :
    currentView Proc.two (History.append h r) =
      .recv (currentView Proc.two h) (.inr r.inputTwo)
        (currentView Proc.one h) (.inl r.inputOne) := by
  exact syncBlock_right_receiver_view h r hr

/-- At a left-to-right reversal, process `1` sees only its own previous view and input. -/
theorem directReversal_leftToRight_sender_view
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .right) :
    currentView Proc.one (History.append h r) =
      .noRecv (currentView Proc.one h) (.inl r.inputOne) := by
  exact syncBlock_right_sender_view h r hr

/-- Process `2` has the same receive view for a final `right` or `both` round with equal data. -/
theorem procTwo_right_both_current_view_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rRight rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hright : rRight.graph = .right)
    (hboth : rBoth.graph = .both)
    (hinputOne : rRight.inputOne = rBoth.inputOne)
    (hinputTwo : rRight.inputTwo = rBoth.inputTwo) :
    currentView Proc.two (History.append h rRight) =
      currentView Proc.two (History.append h rBoth) := by
  simp [currentView_two_append, hright, hboth, hinputOne, hinputTwo]

/--
At a final `right` round, the new dominant process `2`'s full view determines
both previous full views and the current input pair.  This is the direct
left-to-right handoff fact used by the epoch-relative hierarchy proof.
-/
theorem directReversal_leftToRight_receiver_determines_previousViewsAndInputs
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .right)
    (hr' : r'.graph = .right)
    (hview :
      currentView Proc.two (History.append h r) =
        currentView Proc.two (History.append h' r')) :
    currentView Proc.one h = currentView Proc.one h' ∧
      currentView Proc.two h = currentView Proc.two h' ∧
      r.inputOne = r'.inputOne ∧ r.inputTwo = r'.inputTwo := by
  rw [directReversal_leftToRight_receiver_view h r hr,
    directReversal_leftToRight_receiver_view h' r' hr'] at hview
  injection hview with _ hprevTwo hinputTwo hprevOne hinputOne
  exact ⟨hprevOne, hprevTwo, by simpa using hinputOne, by simpa using hinputTwo⟩

/--
At a left-to-right reversal, the new dominant process `2` can read its previous
receipt tag from its current non-fringe view.  This is the Lean handle for the
frozen counterpart bit being the new dominant's own previous receipt.
-/
theorem directReversal_leftToRight_receiver_recovers_oldOwnReceipt
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (_hr : r.graph = .right) :
    (currentNonFringe Proc.two (History.append h r)).previousView.receiptTag =
      (currentView Proc.two h).receiptTag := by
  exact previousReceiptTag_from_nonFringe_append Proc.two h r

/-- Symmetrically, at a right-to-left reversal process `1` receives both previous views. -/
theorem directReversal_rightToLeft_receiver_view
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .left) :
    currentView Proc.one (History.append h r) =
      .recv (currentView Proc.one h) (.inl r.inputOne)
        (currentView Proc.two h) (.inr r.inputTwo) := by
  exact syncBlock_left_receiver_view h r hr

/-- Symmetrically, process `1` has the same receive view for final `left` or `both`. -/
theorem procOne_left_both_current_view_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rLeft rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hleft : rLeft.graph = .left)
    (hboth : rBoth.graph = .both)
    (hinputOne : rLeft.inputOne = rBoth.inputOne)
    (hinputTwo : rLeft.inputTwo = rBoth.inputTwo) :
    currentView Proc.one (History.append h rLeft) =
      currentView Proc.one (History.append h rBoth) := by
  simp [currentView_one_append, hleft, hboth, hinputOne, hinputTwo]

/--
At a final `left` round, the new dominant process `1`'s full view determines
both previous full views and the current input pair.  This is the symmetric
right-to-left handoff fact used by the epoch-relative hierarchy proof.
-/
theorem directReversal_rightToLeft_receiver_determines_previousViewsAndInputs
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .left)
    (hr' : r'.graph = .left)
    (hview :
      currentView Proc.one (History.append h r) =
        currentView Proc.one (History.append h' r')) :
    currentView Proc.one h = currentView Proc.one h' ∧
      currentView Proc.two h = currentView Proc.two h' ∧
      r.inputOne = r'.inputOne ∧ r.inputTwo = r'.inputTwo := by
  rw [directReversal_rightToLeft_receiver_view h r hr,
    directReversal_rightToLeft_receiver_view h' r' hr'] at hview
  injection hview with _ hprevOne hinputOne hprevTwo hinputTwo
  exact ⟨hprevOne, hprevTwo, by simpa using hinputOne, by simpa using hinputTwo⟩

/--
At a right-to-left reversal, the new dominant process `1` can read its previous
receipt tag from its current non-fringe view.  This is the symmetric frozen-bit
alignment fact.
-/
theorem directReversal_rightToLeft_receiver_recovers_oldOwnReceipt
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (_hr : r.graph = .left) :
    (currentNonFringe Proc.one (History.append h r)).previousView.receiptTag =
      (currentView Proc.one h).receiptTag := by
  exact previousReceiptTag_from_nonFringe_append Proc.one h r

/-- Paper-facing Lemma `lem:directreversalboundary`, positive view-equation form. -/
theorem direct_reversal_is_one_sided_boundary
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y} :
    (∀ (h : History In₁ In₂ Graph Out₁ Out₂)
        (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      r.graph = .right ->
        currentView Proc.two (History.append h r) =
          .recv (currentView Proc.two h) (.inr r.inputTwo)
            (currentView Proc.one h) (.inl r.inputOne)) ∧
    (∀ (h : History In₁ In₂ Graph Out₁ Out₂)
        (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      r.graph = .right ->
        currentView Proc.one (History.append h r) =
          .noRecv (currentView Proc.one h) (.inl r.inputOne)) ∧
    (∀ (h : History In₁ In₂ Graph Out₁ Out₂)
        (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      r.graph = .left ->
        currentView Proc.one (History.append h r) =
          .recv (currentView Proc.one h) (.inl r.inputOne)
            (currentView Proc.two h) (.inr r.inputTwo)) := by
  exact ⟨
    directReversal_leftToRight_receiver_view,
    directReversal_leftToRight_sender_view,
    directReversal_rightToLeft_receiver_view⟩

end DistributedSynthesis
