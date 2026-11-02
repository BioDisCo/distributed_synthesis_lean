/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemDirectreversalboundary
import DistributedSynthesis.Formalizations.Definition.DefEpochAbstractions
import DistributedSynthesis.Formalizations.Definition.DefPairedCopy

/-!
# Two one-bit uncertainties at direct reversal
-/

namespace DistributedSynthesis

universe u v x y

/-- Interpret a receipt tag as the pending-copy bit used by the paired-copy game. -/
def pendingCopyOfReceipt : ReceiptTag -> PendingCopy
  | .noRecv => false
  | .recv => true

@[simp]
theorem pendingCopyOfReceipt_noRecv :
    pendingCopyOfReceipt .noRecv = false := rfl

@[simp]
theorem pendingCopyOfReceipt_recv :
    pendingCopyOfReceipt .recv = true := rfl

@[simp]
theorem graphForProcessOneCopy_noRecv :
    graphForProcessOneCopy (pendingCopyOfReceipt .noRecv) = .left := rfl

@[simp]
theorem graphForProcessOneCopy_recv :
    graphForProcessOneCopy (pendingCopyOfReceipt .recv) = .both := rfl

@[simp]
theorem graphForProcessTwoCopy_noRecv :
    graphForProcessTwoCopy (pendingCopyOfReceipt .noRecv) = .right := rfl

@[simp]
theorem graphForProcessTwoCopy_recv :
    graphForProcessTwoCopy (pendingCopyOfReceipt .recv) = .both := rfl

/-- The two-bit direct-reversal component is finite. -/
instance : Fintype DirectReversalBits where
  elems := {⟨false, false⟩, ⟨false, true⟩, ⟨true, false⟩, ⟨true, true⟩}
  complete := by
    intro bits
    cases bits with
    | mk oldBit newBit =>
      cases oldBit <;> cases newBit <;> simp

/-- A direct reversal's two finite ambiguity flags are represented by `DirectReversalBits`. -/
theorem directReversalBits_exhaustive (bits : DirectReversalBits) :
    bits.oldReceiverAmbiguity = false ∨ bits.oldReceiverAmbiguity = true := by
  cases bits.oldReceiverAmbiguity <;> simp

/-- At a left-to-right reversal, process `2`'s current receive view cannot distinguish `right` from `both`. -/
theorem leftToRight_newReceiver_right_both_bit
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rRight rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hright : rRight.graph = .right)
    (hboth : rBoth.graph = .both)
    (hinputOne : rRight.inputOne = rBoth.inputOne)
    (hinputTwo : rRight.inputTwo = rBoth.inputTwo) :
    currentView Proc.two (History.append h rRight) =
      currentView Proc.two (History.append h rBoth) :=
  procTwo_right_both_current_view_eq h rRight rBoth hright hboth hinputOne hinputTwo

/-- At a right-to-left reversal, process `1`'s current receive view cannot distinguish `left` from `both`. -/
theorem rightToLeft_newReceiver_left_both_bit
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rLeft rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hleft : rLeft.graph = .left)
    (hboth : rBoth.graph = .both)
    (hinputOne : rLeft.inputOne = rBoth.inputOne)
    (hinputTwo : rLeft.inputTwo = rBoth.inputTwo) :
    currentView Proc.one (History.append h rLeft) =
      currentView Proc.one (History.append h rBoth) :=
  procOne_left_both_current_view_eq h rLeft rBoth hleft hboth hinputOne hinputTwo

/--
At a left-to-right direct reversal, the old dominant process `1`'s pending
counterpart-copy graph is selected by process `2`'s previous receipt tag, and
the new dominant process `2` can read that tag from its current non-fringe
view.
-/
theorem leftToRight_pendingCounterpartCopyGraph_readBy_newDominant
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hright : r.graph = .right) :
    graphForProcessOneCopy
        (pendingCopyOfReceipt
          ((currentNonFringe Proc.two (History.append h r)).previousView.receiptTag)) =
      graphForProcessOneCopy
        (pendingCopyOfReceipt ((currentView Proc.two h).receiptTag)) := by
  rw [directReversal_leftToRight_receiver_recovers_oldOwnReceipt h r hright]

/--
At a right-to-left direct reversal, the old dominant process `2`'s pending
counterpart-copy graph is selected by process `1`'s previous receipt tag, and
the new dominant process `1` can read that tag from its current non-fringe
view.
-/
theorem rightToLeft_pendingCounterpartCopyGraph_readBy_newDominant
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hleft : r.graph = .left) :
    graphForProcessTwoCopy
        (pendingCopyOfReceipt
          ((currentNonFringe Proc.one (History.append h r)).previousView.receiptTag)) =
      graphForProcessTwoCopy
        (pendingCopyOfReceipt ((currentView Proc.one h).receiptTag)) := by
  rw [directReversal_rightToLeft_receiver_recovers_oldOwnReceipt h r hleft]

/-- Paper-facing Lemma `lem:reversaltwobits`: the direct-reversal ambiguity component is finite. -/
theorem direct_reversal_carries_two_one_bit_uncertainties :
    Nonempty (Fintype DirectReversalBits) ∧
      (∀ bits : DirectReversalBits,
        (bits.oldReceiverAmbiguity = false ∨ bits.oldReceiverAmbiguity = true) ∧
        (bits.newReceiverAmbiguity = false ∨ bits.newReceiverAmbiguity = true)) := by
  constructor
  · exact ⟨inferInstance⟩
  · intro bits
    cases bits with
    | mk oldBit newBit =>
      cases oldBit <;> cases newBit <;> simp

end DistributedSynthesis
