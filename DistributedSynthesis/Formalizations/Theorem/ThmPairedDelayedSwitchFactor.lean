/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialDelayedRootNarrowing
import DistributedSynthesis.Formalizations.Theorem.ThmPairedBankLocalHandoff

/-!
# Fail-fast factorization of the delay-one switch

This file checks the operational type boundary before the full summary
automaton is built.  A `left`/`both` boundary stages a right-block bank source;
a `right`/`both` boundary stages a left-block bank source.  Both local
activation controls carry exactly that same source.  The construction has no
strict-leader selector and no current opposite-round input.
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

/-- Concrete paired macro data staged at an initial `left`/`both` boundary. -/
def initialLeftDelayedMacroData
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    (A.State × A.State) × A.State :=
  let leftState := A.step scan.1
    (leftRoundRecord letter.1 letter.2.1.informedOne letter.2.2)
  let bothState := A.step scan.1
    (bothRoundRecord letter.1 letter.2.1.informedOne
      letter.2.1.reversingTwo)
  ((leftState, bothState), scan.2)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem initialLeftDelayedTarget_eq_macroData
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    initialLeftDelayedTarget A scan letter =
      Sum.inr (Sum.inl (initialLeftDelayedMacroData A scan letter)) := rfl

/-- A feasible delayed initial-left target is immediately a reachable source
of the right-block policy bank. -/
def initialLeftDelayedBankHandoff
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hfeasible :
      (pairedEntryRunAutomaton A
        (initialLeftDelayedTarget A scan letter)).HasRationalRun) :
    BankRightMacro A :=
  let target : FeasiblePairedState A :=
    ⟨initialLeftDelayedTarget A scan letter, hfeasible⟩
  bankRightRoot A target (initialLeftDelayedMacroData A scan letter) rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem initialLeftDelayedBankHandoff_state
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hfeasible :
      (pairedEntryRunAutomaton A
        (initialLeftDelayedTarget A scan letter)).HasRationalRun) :
    (initialLeftDelayedBankHandoff A scan letter hfeasible).2.1 =
      initialLeftDelayedMacroData A scan letter := rfl

/-- Mirror macro data staged at an initial `right`/`both` boundary. -/
def initialRightDelayedMacroData
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    (A.State × A.State) × A.State :=
  let move : In₁ × In₂ := (letter.1.2, letter.1.1)
  let rightState := A.step scan.1
    (rightRoundRecord letter.1 letter.2.2 letter.2.1.informedTwo)
  let bothState := A.step scan.1
    (bothRoundRecord move letter.2.1.reversingOne
      letter.2.1.informedTwo)
  ((rightState, bothState), scan.2)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem initialRightDelayedTarget_eq_macroData
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    initialRightDelayedTarget A scan letter =
      Sum.inr (Sum.inr (initialRightDelayedMacroData A scan letter)) := rfl

def initialRightDelayedBankHandoff
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hfeasible :
      (pairedEntryRunAutomaton A
        (initialRightDelayedTarget A scan letter)).HasRationalRun) :
    BankLeftMacro A :=
  let target : FeasiblePairedState A :=
    ⟨initialRightDelayedTarget A scan letter, hfeasible⟩
  bankLeftRoot A target (initialRightDelayedMacroData A scan letter) rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem initialRightDelayedBankHandoff_state
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hfeasible :
      (pairedEntryRunAutomaton A
        (initialRightDelayedTarget A scan letter)).HasRationalRun) :
    (initialRightDelayedBankHandoff A scan letter hfeasible).2.1 =
      initialRightDelayedMacroData A scan letter := rfl

/-! ## Common-source activation test -/

/-- The two finite controls initialized at a switch into a right block.  The
first is retained by the new blind owner; the second is reconstructible by
the receiver from the owner's previous summary. -/
noncomputable def activateBankRight
    (source : BankRightMacro A) (row : PairedEntryRow) :
    BankRightOwnerControl A × BankRightReceiverControl A :=
  (initialBankRightOwner A source, initialBankRightReceiver A source row)

@[simp] theorem activateBankRight_owner_source
    (source : BankRightMacro A) (row : PairedEntryRow) :
    (activateBankRight A source row).1.1 = source := rfl

@[simp] theorem activateBankRight_receiver_source
    (source : BankRightMacro A) (row : PairedEntryRow) :
    (activateBankRight A source row).2.1 = source := rfl

/-- Both sides therefore initialize from literally the same paired-bank
source, not merely extensionally equivalent independently chosen policies. -/
theorem activateBankRight_common_source
    (source : BankRightMacro A) (row : PairedEntryRow) :
    (activateBankRight A source row).1.1 =
      (activateBankRight A source row).2.1 := rfl

noncomputable def activateBankLeft
    (source : BankLeftMacro A) (row : PairedEntryRow) :
    BankLeftOwnerControl A × BankLeftReceiverControl A :=
  (initialBankLeftOwner A source, initialBankLeftReceiver A source row)

@[simp] theorem activateBankLeft_owner_source
    (source : BankLeftMacro A) (row : PairedEntryRow) :
    (activateBankLeft A source row).1.1 = source := rfl

@[simp] theorem activateBankLeft_receiver_source
    (source : BankLeftMacro A) (row : PairedEntryRow) :
    (activateBankLeft A source row).2.1 = source := rfl

theorem activateBankLeft_common_source
    (source : BankLeftMacro A) (row : PairedEntryRow) :
    (activateBankLeft A source row).1.1 =
      (activateBankLeft A source row).2.1 := rfl

end

end DetParityAutomaton

end DistributedSynthesis
