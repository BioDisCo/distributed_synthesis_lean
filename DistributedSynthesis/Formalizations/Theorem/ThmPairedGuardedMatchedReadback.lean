/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedBankFiniteReadback

/-!
# Matched physical readback inside guarded recurrent blocks

A receiving process sees the partner's previous finite summary.  On the
reachable paired states, that summary contains the owner control for the same
finite block key.  This file makes the dependent-key lookup total (using the
controller's initial control only on mismatched, unreachable tuples), selects
the physical output belonging to the receiver's locally stored entry row, and
packages the updated monitor and staged next key back into finite memory.

There is no strict-leader or graph tag in these operations.  The receiver uses
only its own row and the partner summary delivered by `stepRecv`.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Physical projections of the two latent entry rows -/

def pairedRightInformedForRow (row : PairedEntryRow)
    (output : PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) : Out₂ :=
  match row with
  | .first => output.informedFirst
  | .both => output.informedBoth

def pairedRightClosingForRow (row : PairedEntryRow)
    (output : PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) : Out₁ :=
  match row with
  | .first => output.closingFirst
  | .both => output.closingBoth

def pairedLeftInformedForRow (row : PairedEntryRow)
    (output : PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) : Out₁ :=
  match row with
  | .first => output.informedFirst
  | .both => output.informedBoth

def pairedLeftClosingForRow (row : PairedEntryRow)
    (output : PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) : Out₂ :=
  match row with
  | .first => output.closingFirst
  | .both => output.closingBoth

/-! ## Exceptional first block -/

variable (bank : FiniteGuardedFirstControllerBank A)

/-- Read the exceptional right-block owner control at the receiver's key.
The fallback is used only to totalize the function outside the paired-state
invariant. -/
noncomputable def guardedFirstRightOwnerControlFor
    (receiver : GuardedFirstRightReceiverControl A)
    (owner : GuardedFirstRightOwnerControl A bank) :
    (guardedFirstRightControllerAt A bank receiver.1).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else (guardedFirstRightControllerAt A bank receiver.1).initial

noncomputable def guardedFirstLeftOwnerControlFor
    (receiver : GuardedFirstLeftReceiverControl A)
    (owner : GuardedFirstLeftOwnerControl A bank) :
    (guardedFirstLeftControllerAt A bank receiver.1).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else (guardedFirstLeftControllerAt A bank receiver.1).initial

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem guardedFirstRightOwnerControlFor_of_key_eq
    (receiver : GuardedFirstRightReceiverControl A)
    (owner : GuardedFirstRightOwnerControl A bank)
    (h : owner.1 = receiver.1) :
    guardedFirstRightOwnerControlFor A bank receiver owner = h ▸ owner.2 := by
  classical
  simp only [guardedFirstRightOwnerControlFor, dif_pos h]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem guardedFirstLeftOwnerControlFor_of_key_eq
    (receiver : GuardedFirstLeftReceiverControl A)
    (owner : GuardedFirstLeftOwnerControl A bank)
    (h : owner.1 = receiver.1) :
    guardedFirstLeftOwnerControlFor A bank receiver owner = h ▸ owner.2 := by
  classical
  simp only [guardedFirstLeftOwnerControlFor, dif_pos h]

/-- One physical receive step in the exceptional right block. -/
noncomputable def continueGuardedFirstRightReceiver
    (receiver : GuardedFirstRightReceiverControl A)
    (owner : GuardedFirstRightOwnerControl A bank) (move : In₂ × In₁) :
    Out₂ × GuardedFirstRightReceiverControl A :=
  let result := stepGuardedFirstRightReceiverFor A bank receiver.1
    (guardedFirstRightOwnerControlFor A bank receiver owner)
    receiver.2.1 receiver.2.2.1 move
  (pairedRightInformedForRow receiver.2.1 result.1,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

/-- Process-two/left-block mirror. -/
noncomputable def continueGuardedFirstLeftReceiver
    (receiver : GuardedFirstLeftReceiverControl A)
    (owner : GuardedFirstLeftOwnerControl A bank) (move : In₁ × In₂) :
    Out₁ × GuardedFirstLeftReceiverControl A :=
  let result := stepGuardedFirstLeftReceiverFor A bank receiver.1
    (guardedFirstLeftOwnerControlFor A bank receiver owner)
    receiver.2.1 receiver.2.2.1 move
  (pairedLeftInformedForRow receiver.2.1 result.1,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem continueGuardedFirstRightReceiver_key
    (receiver : GuardedFirstRightReceiverControl A)
    (owner : GuardedFirstRightOwnerControl A bank) (move : In₂ × In₁) :
    (continueGuardedFirstRightReceiver A bank receiver owner move).2.1 = receiver.1 := rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem continueGuardedFirstLeftReceiver_key
    (receiver : GuardedFirstLeftReceiverControl A)
    (owner : GuardedFirstLeftOwnerControl A bank) (move : In₁ × In₂) :
    (continueGuardedFirstLeftReceiver A bank receiver owner move).2.1 = receiver.1 := rfl

/-! ## Ordinary recurrent bank -/

noncomputable def bankRightOwnerControlFor
    (receiver : BankRightReceiverControl A) (owner : BankRightOwnerControl A) :
    (bankRightControllerAt A receiver.1).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else (bankRightControllerAt A receiver.1).initial

noncomputable def bankLeftOwnerControlFor
    (receiver : BankLeftReceiverControl A) (owner : BankLeftOwnerControl A) :
    (bankLeftControllerAt A receiver.1).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else (bankLeftControllerAt A receiver.1).initial

theorem bankRightOwnerControlFor_of_source_eq
    (receiver : BankRightReceiverControl A) (owner : BankRightOwnerControl A)
    (h : owner.1 = receiver.1) :
    bankRightOwnerControlFor A receiver owner = h ▸ owner.2 := by
  classical
  simp only [bankRightOwnerControlFor, dif_pos h]

theorem bankLeftOwnerControlFor_of_source_eq
    (receiver : BankLeftReceiverControl A) (owner : BankLeftOwnerControl A)
    (h : owner.1 = receiver.1) :
    bankLeftOwnerControlFor A receiver owner = h ▸ owner.2 := by
  classical
  simp only [bankLeftOwnerControlFor, dif_pos h]

/-- One physical receive step in an ordinary right block, including the next
left key staged by the finite close check. -/
noncomputable def continueBankRightReceiver
    (receiver : BankRightReceiverControl A) (owner : BankRightOwnerControl A)
    (move : In₂ × In₁) : Out₂ × BankRightReceiverControl A :=
  let result := stepBankRightReceiverFor A receiver.1
    (bankRightOwnerControlFor A receiver owner)
    receiver.2.1 receiver.2.2.1 move
  (pairedRightInformedForRow receiver.2.1 result.1,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

/-- Ordinary left mirror. -/
noncomputable def continueBankLeftReceiver
    (receiver : BankLeftReceiverControl A) (owner : BankLeftOwnerControl A)
    (move : In₁ × In₂) : Out₁ × BankLeftReceiverControl A :=
  let result := stepBankLeftReceiverFor A receiver.1
    (bankLeftOwnerControlFor A receiver owner)
    receiver.2.1 receiver.2.2.1 move
  (pairedLeftInformedForRow receiver.2.1 result.1,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

@[simp] theorem continueBankRightReceiver_source
    (receiver : BankRightReceiverControl A) (owner : BankRightOwnerControl A)
    (move : In₂ × In₁) :
    (continueBankRightReceiver A receiver owner move).2.1 = receiver.1 := rfl

@[simp] theorem continueBankLeftReceiver_source
    (receiver : BankLeftReceiverControl A) (owner : BankLeftOwnerControl A)
    (move : In₁ × In₂) :
    (continueBankLeftReceiver A receiver owner move).2.1 = receiver.1 := rfl

end

end DetParityAutomaton

end DistributedSynthesis
