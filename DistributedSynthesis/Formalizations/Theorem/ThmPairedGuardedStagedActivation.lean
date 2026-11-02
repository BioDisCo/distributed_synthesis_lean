/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedInitialLocalHandoff

/-!
# Activating staged guarded and ordinary handoffs

At a possible reversal the current receiver stores an optional next-bank key.
On the following round that same finite key initializes both local sides: the
old receiver retains it and becomes the new blind owner, while the new
receiver obtains it from the delivered partner summary.  The only row datum
is the local receipt bit at the boundary.

This is the asynchronous phase-switch law.  It does not require the processes
to share a phase tag or to recognize the strict leader.
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

/-- The two latent entry rows encoded by the process's own receipt bit at the
preceding boundary. -/
def guardedEntryRowOfReceived : Bool -> PairedEntryRow
  | false => .first
  | true => .both

/-! ## Exceptional first block to the ordinary bank -/

/-- Activate the ordinary left bank from the key staged by the receiver of an
exceptional first-right round. -/
noncomputable def activateBankLeftFromGuardedFirstRight
    {key : GuardedFirstRightMacro A}
    (result : GuardedFirstRightReceiverRoundResult A key)
    (received : Bool) :
    Option (BankLeftOwnerControl A × BankLeftReceiverControl A) :=
  result.2.2.map fun source =>
    (initialBankLeftOwner A source,
      initialBankLeftReceiver A source (guardedEntryRowOfReceived received))

/-- Mirror activation into the ordinary right bank. -/
noncomputable def activateBankRightFromGuardedFirstLeft
    {key : GuardedFirstLeftMacro A}
    (result : GuardedFirstLeftReceiverRoundResult A key)
    (received : Bool) :
    Option (BankRightOwnerControl A × BankRightReceiverControl A) :=
  result.2.2.map fun source =>
    (initialBankRightOwner A source,
      initialBankRightReceiver A source (guardedEntryRowOfReceived received))

theorem activateBankLeftFromGuardedFirstRight_common_source
    {key : GuardedFirstRightMacro A}
    (result : GuardedFirstRightReceiverRoundResult A key)
    (received : Bool)
    (activated : BankLeftOwnerControl A × BankLeftReceiverControl A)
    (hactivated : activateBankLeftFromGuardedFirstRight A result received =
      some activated) :
    activated.1.1 = activated.2.1 := by
  rcases result with ⟨output, monitor, staged⟩
  cases staged with
  | none => simp [activateBankLeftFromGuardedFirstRight] at hactivated
  | some source =>
      simp only [activateBankLeftFromGuardedFirstRight, Option.map_some,
        Option.some.injEq] at hactivated
      subst activated
      rfl

theorem activateBankRightFromGuardedFirstLeft_common_source
    {key : GuardedFirstLeftMacro A}
    (result : GuardedFirstLeftReceiverRoundResult A key)
    (received : Bool)
    (activated : BankRightOwnerControl A × BankRightReceiverControl A)
    (hactivated : activateBankRightFromGuardedFirstLeft A result received =
      some activated) :
    activated.1.1 = activated.2.1 := by
  rcases result with ⟨output, monitor, staged⟩
  cases staged with
  | none => simp [activateBankRightFromGuardedFirstLeft] at hactivated
  | some source =>
      simp only [activateBankRightFromGuardedFirstLeft, Option.map_some,
        Option.some.injEq] at hactivated
      subst activated
      rfl

/-- Every real exceptional first-right close activates an ordinary left-bank
pair on the next round. -/
theorem activateBankLeftFromGuardedFirstRight_real_isSome
    (bank : FiniteGuardedFirstControllerBank A)
    (key : GuardedFirstRightMacro A)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) (received : Bool) :
    (activateBankLeftFromGuardedFirstRight A
      (stepGuardedFirstRightReceiverFor A bank key
        (guardedFirstRightFiniteStateAfter A bank key past).1 row
        (guardedFirstRightFiniteStateAfter A bank key past).2 move)
      received).isSome := by
  simpa [activateBankLeftFromGuardedFirstRight] using
    guardedFirstRight_real_close_staged A bank key row past move

/-- Left mirror. -/
theorem activateBankRightFromGuardedFirstLeft_real_isSome
    (bank : FiniteGuardedFirstControllerBank A)
    (key : GuardedFirstLeftMacro A)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) (received : Bool) :
    (activateBankRightFromGuardedFirstLeft A
      (stepGuardedFirstLeftReceiverFor A bank key
        (guardedFirstLeftFiniteStateAfter A bank key past).1 row
        (guardedFirstLeftFiniteStateAfter A bank key past).2 move)
      received).isSome := by
  simpa [activateBankRightFromGuardedFirstLeft] using
    guardedFirstLeft_real_close_staged A bank key row past move

/-! ## Ordinary recurrent bank switching -/

/-- Activate a left-bank pair from a right-bank receiver result. -/
noncomputable def activateBankLeftFromBankRight
    {source : BankRightMacro A}
    (result : BankRightReceiverRoundResult A source)
    (received : Bool) :
    Option (BankLeftOwnerControl A × BankLeftReceiverControl A) :=
  result.2.2.map fun target =>
    (initialBankLeftOwner A target,
      initialBankLeftReceiver A target (guardedEntryRowOfReceived received))

/-- Mirror recurrent switch. -/
noncomputable def activateBankRightFromBankLeft
    {source : BankLeftMacro A}
    (result : BankLeftReceiverRoundResult A source)
    (received : Bool) :
    Option (BankRightOwnerControl A × BankRightReceiverControl A) :=
  result.2.2.map fun target =>
    (initialBankRightOwner A target,
      initialBankRightReceiver A target (guardedEntryRowOfReceived received))

theorem activateBankLeftFromBankRight_common_source
    {source : BankRightMacro A}
    (result : BankRightReceiverRoundResult A source)
    (received : Bool)
    (activated : BankLeftOwnerControl A × BankLeftReceiverControl A)
    (hactivated : activateBankLeftFromBankRight A result received =
      some activated) :
    activated.1.1 = activated.2.1 := by
  rcases result with ⟨output, monitor, staged⟩
  cases staged with
  | none => simp [activateBankLeftFromBankRight] at hactivated
  | some target =>
      simp only [activateBankLeftFromBankRight, Option.map_some,
        Option.some.injEq] at hactivated
      subst activated
      rfl

theorem activateBankRightFromBankLeft_common_source
    {source : BankLeftMacro A}
    (result : BankLeftReceiverRoundResult A source)
    (received : Bool)
    (activated : BankRightOwnerControl A × BankRightReceiverControl A)
    (hactivated : activateBankRightFromBankLeft A result received =
      some activated) :
    activated.1.1 = activated.2.1 := by
  rcases result with ⟨output, monitor, staged⟩
  cases staged with
  | none => simp [activateBankRightFromBankLeft] at hactivated
  | some target =>
      simp only [activateBankRightFromBankLeft, Option.map_some,
        Option.some.injEq] at hactivated
      subst activated
      rfl

end


end DetParityAutomaton

end DistributedSynthesis
