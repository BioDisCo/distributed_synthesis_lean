/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndFamilyReceiverStep
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyReceiverBank

/-!
# Executable simultaneous receiver-bank steps

The blind sender advances one shared family overlay.  Its informed partner
advances both receiver projections of that same table.  The synchronized
past anchor chooses the physical receiver output, exactly as in the old
two-shadow carrier, while both monitor states and both staged successors are
retained for future ambiguity.

The anchor is historical local-summary data.  These definitions never inspect
the current graph and do not provide a strict-leader test.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-! ## Right-family bank, stored by process two -/

/-- Advance one right-family receiver projection. -/
noncomputable def stepEndToEndRightFamilyReceiverBankMember
    (sender : EndToEndRightFamilyOneControl A package)
    (bank : EndToEndRightFamilyReceiverBank A package sender.1)
    (member : Bool) (move : In₂ × In₁) :
    EndToEndRightFamilyReceiverMemberState A package sender.1 member := by
  let current := bank member
  let result := stepEndToEndRightFamilyReceiver A package sender member
    current.1 current.2.1 move
  let label := endToEndRightFamilyMemberLabel A package sender member
  exact ⟨current.1,
    ((sender.1.1 member).1.monitor A package).step current.2.1
      (move, result.1, label.1 move.2),
    result.2.2⟩

/-- Advance both possible receiver projections. -/
noncomputable def stepEndToEndRightFamilyReceiverBank
    (sender : EndToEndRightFamilyOneControl A package)
    (bank : EndToEndRightFamilyReceiverBank A package sender.1)
    (move : In₂ × In₁) :
    EndToEndRightFamilyReceiverBank A package sender.1 :=
  fun member =>
    stepEndToEndRightFamilyReceiverBankMember A package sender bank member move

/-- Physical process-two output selected by the synchronized past anchor.
The right-family indexing convention is `false = current right` and
`true = fresh right staged by the left shadow`, so the anchor is used
directly. -/
noncomputable def endToEndRightFamilyReceiverBankOutput
    (sender : EndToEndRightFamilyOneControl A package)
    (bank : EndToEndRightFamilyReceiverBank A package sender.1)
    (pastAnchor : Bool) (move : In₂ × In₁) : Out₂ :=
  let current := bank pastAnchor
  let result := stepEndToEndRightFamilyReceiver A package sender pastAnchor
    current.1 current.2.1 move
  pairedRightInformedForRow current.1 result.1.physical

/-- One complete informed process-two step against a shared right sender. -/
noncomputable def stepEndToEndRightFamilyReceiverBankFor
    (sender : EndToEndRightFamilyOneControl A package)
    (bank : EndToEndRightFamilyReceiverBank A package sender.1)
    (pastAnchor : Bool) (move : In₂ × In₁) :
    Out₂ × EndToEndRightFamilyReceiverBank A package sender.1 :=
  (endToEndRightFamilyReceiverBankOutput A package sender bank pastAnchor move,
    stepEndToEndRightFamilyReceiverBank A package sender bank move)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem stepEndToEndRightFamilyReceiverBankFor_fst
    (sender : EndToEndRightFamilyOneControl A package)
    (bank : EndToEndRightFamilyReceiverBank A package sender.1)
    (pastAnchor : Bool) (move : In₂ × In₁) :
    (stepEndToEndRightFamilyReceiverBankFor A package sender bank pastAnchor
      move).1 =
      endToEndRightFamilyReceiverBankOutput A package sender bank pastAnchor
        move :=
  rfl

@[simp] theorem stepEndToEndRightFamilyReceiverBankFor_snd
    (sender : EndToEndRightFamilyOneControl A package)
    (bank : EndToEndRightFamilyReceiverBank A package sender.1)
    (pastAnchor : Bool) (move : In₂ × In₁) :
    (stepEndToEndRightFamilyReceiverBankFor A package sender bank pastAnchor
      move).2 = stepEndToEndRightFamilyReceiverBank A package sender bank move :=
  rfl

@[simp] theorem stepEndToEndRightFamilyReceiverBank_row
    (sender : EndToEndRightFamilyOneControl A package)
    (bank : EndToEndRightFamilyReceiverBank A package sender.1)
    (move : In₂ × In₁) (member : Bool) :
    (stepEndToEndRightFamilyReceiverBank A package sender bank move member).1 =
      (bank member).1 :=
  rfl

@[simp] theorem stepEndToEndRightFamilyReceiverBank_pending
    (sender : EndToEndRightFamilyOneControl A package)
    (bank : EndToEndRightFamilyReceiverBank A package sender.1)
    (move : In₂ × In₁) (member : Bool) :
    (stepEndToEndRightFamilyReceiverBank A package sender bank move member).2.2 =
      (stepEndToEndRightFamilyReceiver A package sender member
        (bank member).1 (bank member).2.1 move).2.2 :=
  rfl

end

/-! ## Left-family bank, stored by process one -/

noncomputable def stepEndToEndLeftFamilyReceiverBankMember
    (sender : EndToEndLeftFamilyTwoControl A package)
    (bank : EndToEndLeftFamilyReceiverBank A package sender.1)
    (member : Bool) (move : In₁ × In₂) :
    EndToEndLeftFamilyReceiverMemberState A package sender.1 member := by
  let current := bank member
  let result := stepEndToEndLeftFamilyReceiver A package sender member
    current.1 current.2.1 move
  let label := endToEndLeftFamilyMemberLabel A package sender member
  exact ⟨current.1,
    ((sender.1.1 member).1.monitor A package).step current.2.1
      (move, result.1, label.1 move.2),
    result.2.2⟩

noncomputable def stepEndToEndLeftFamilyReceiverBank
    (sender : EndToEndLeftFamilyTwoControl A package)
    (bank : EndToEndLeftFamilyReceiverBank A package sender.1)
    (move : In₁ × In₂) :
    EndToEndLeftFamilyReceiverBank A package sender.1 :=
  fun member =>
    stepEndToEndLeftFamilyReceiverBankMember A package sender bank member move

/-- The left-family source map uses `false = current left` and
`true = fresh left staged by the right shadow`.  Hence the physical left
projection belonging to the same common historical anchor is its complement:
right-anchored overlap uses the fresh left member, while left-anchored overlap
uses the current left member. -/
noncomputable def endToEndLeftFamilyReceiverBankOutput
    (sender : EndToEndLeftFamilyTwoControl A package)
    (bank : EndToEndLeftFamilyReceiverBank A package sender.1)
    (pastAnchor : Bool) (move : In₁ × In₂) : Out₁ :=
  let member := !pastAnchor
  let current := bank member
  let result := stepEndToEndLeftFamilyReceiver A package sender member
    current.1 current.2.1 move
  pairedLeftInformedForRow current.1 result.1.physical

noncomputable def stepEndToEndLeftFamilyReceiverBankFor
    (sender : EndToEndLeftFamilyTwoControl A package)
    (bank : EndToEndLeftFamilyReceiverBank A package sender.1)
    (pastAnchor : Bool) (move : In₁ × In₂) :
    Out₁ × EndToEndLeftFamilyReceiverBank A package sender.1 :=
  (endToEndLeftFamilyReceiverBankOutput A package sender bank pastAnchor move,
    stepEndToEndLeftFamilyReceiverBank A package sender bank move)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem stepEndToEndLeftFamilyReceiverBankFor_fst
    (sender : EndToEndLeftFamilyTwoControl A package)
    (bank : EndToEndLeftFamilyReceiverBank A package sender.1)
    (pastAnchor : Bool) (move : In₁ × In₂) :
    (stepEndToEndLeftFamilyReceiverBankFor A package sender bank pastAnchor
      move).1 =
      endToEndLeftFamilyReceiverBankOutput A package sender bank pastAnchor
        move :=
  rfl

@[simp] theorem stepEndToEndLeftFamilyReceiverBankFor_snd
    (sender : EndToEndLeftFamilyTwoControl A package)
    (bank : EndToEndLeftFamilyReceiverBank A package sender.1)
    (pastAnchor : Bool) (move : In₁ × In₂) :
    (stepEndToEndLeftFamilyReceiverBankFor A package sender bank pastAnchor
      move).2 = stepEndToEndLeftFamilyReceiverBank A package sender bank move :=
  rfl

@[simp] theorem stepEndToEndLeftFamilyReceiverBank_row
    (sender : EndToEndLeftFamilyTwoControl A package)
    (bank : EndToEndLeftFamilyReceiverBank A package sender.1)
    (move : In₁ × In₂) (member : Bool) :
    (stepEndToEndLeftFamilyReceiverBank A package sender bank move member).1 =
      (bank member).1 :=
  rfl

@[simp] theorem stepEndToEndLeftFamilyReceiverBank_pending
    (sender : EndToEndLeftFamilyTwoControl A package)
    (bank : EndToEndLeftFamilyReceiverBank A package sender.1)
    (move : In₁ × In₂) (member : Bool) :
    (stepEndToEndLeftFamilyReceiverBank A package sender bank move member).2.2 =
      (stepEndToEndLeftFamilyReceiver A package sender member
        (bank member).1 (bank member).2.1 move).2.2 :=
  rfl

end

end


end DetParityAutomaton

end DistributedSynthesis
