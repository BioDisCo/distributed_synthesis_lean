/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyReceiveActivation

/-!
# Receipt-correct row metadata at lazy family activation

The lazy sync-or-activate wiring correctly retains the active receiver bank
and activates a newly delivered sender table on a move mismatch.  An earlier
fail-fast version of this audit exposed that the staged (`true`) member was
hard-wired to `.both`; that is wrong after a strict reversal, whose new
receiver did not receive in the preceding one-directional round.

Activation now takes the receiver's locally remembered previous-receipt bit.
The theorems below check the repair directly in the executable definitions:
the staged row is exactly `guardedEntryRowOfReceived previouslyReceived`, so
strict reversal gives `.first` and a preceding simultaneous receive gives
`.both`.  This bit is local view data, not an orientation or leader signal.
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

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- Activating a delivered left family installs exactly the row determined by
the new receiver's previous-receipt bit. -/
@[simp] theorem endToEndFamilyFullRecvOneBankActivate_stagedRow
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (previouslyReceived : Bool) :
    ((endToEndFamilyFullRecvOneBankActivate A package self inputOne other
      inputTwo previouslyReceived).1.leftReceiver.2.2 true).1 =
        guardedEntryRowOfReceived previouslyReceived := by
  rfl

/-- Right-family mirror. -/
@[simp] theorem endToEndFamilyFullRecvTwoBankActivate_stagedRow
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (previouslyReceived : Bool) :
    ((endToEndFamilyFullRecvTwoBankActivate A package self inputTwo other
      inputOne previouslyReceived).1.rightReceiver.2.2 true).1 =
        guardedEntryRowOfReceived previouslyReceived := by
  rfl

/-- At a strict right-to-left reversal process one did not receive in the
preceding right round, and activation therefore installs `.first`. -/
@[simp] theorem endToEndFamilyFullRecvOneBankActivate_stagedRow_strict
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂) :
    ((endToEndFamilyFullRecvOneBankActivate A package self inputOne other
      inputTwo false).1.leftReceiver.2.2 true).1 = .first := by
  rfl

/-- Strict left-to-right mirror. -/
@[simp] theorem endToEndFamilyFullRecvTwoBankActivate_stagedRow_strict
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁) :
    ((endToEndFamilyFullRecvTwoBankActivate A package self inputTwo other
      inputOne false).1.rightReceiver.2.2 true).1 = .first := by
  rfl

/-- If the receiver also received in the preceding round (the ambiguous
`both` case), the activated staged row is `.both`. -/
@[simp] theorem endToEndFamilyFullRecvOneBankActivate_stagedRow_both
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂) :
    ((endToEndFamilyFullRecvOneBankActivate A package self inputOne other
      inputTwo true).1.leftReceiver.2.2 true).1 = .both := by
  rfl

/-- Simultaneous-predecessor mirror. -/
@[simp] theorem endToEndFamilyFullRecvTwoBankActivate_stagedRow_both
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁) :
    ((endToEndFamilyFullRecvTwoBankActivate A package self inputTwo other
      inputOne true).1.rightReceiver.2.2 true).1 = .both := by
  rfl

end

end


end DetParityAutomaton

end DistributedSynthesis
