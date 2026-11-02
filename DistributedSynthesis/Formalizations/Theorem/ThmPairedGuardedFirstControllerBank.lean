/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedFirstBlockSoundness

/-!
# Finite bank of guarded first-block controllers

There are only finitely many guarded sources and paired entry coordinates.
This file selects the regularized first-block controller at every such key and
packages its semantic readback.  Proof components are subsingletons; they do
not provide a process with a leader test or any additional observation.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Finite key for the exceptional right block: a guarded source together
with the process-one shape already carried by its target. -/
abbrev GuardedFirstRightMacro :=
  Σ source : GuardedRightEntrySource A,
    {stateData : (A.State × A.State) × A.State //
      source.1.1 = Sum.inr (Sum.inl stateData)}

/-- Process-two mirror. -/
abbrev GuardedFirstLeftMacro :=
  Σ source : GuardedLeftEntrySource A,
    {stateData : (A.State × A.State) × A.State //
      source.1.1 = Sum.inr (Sum.inr stateData)}

noncomputable instance [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] :
    Fintype (GuardedFirstRightMacro A) := by
  classical
  infer_instance

noncomputable instance [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] :
    Fintype (GuardedFirstLeftMacro A) := by
  classical
  infer_instance

def guardedFirstRightMacroOfShape
    (source : GuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (hshape : source.1.1 = Sum.inr (Sum.inl (code, minimum))) :
    GuardedFirstRightMacro A :=
  ⟨source, ⟨(code, minimum), hshape⟩⟩

def guardedFirstLeftMacroOfShape
    (source : GuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (hshape : source.1.1 = Sum.inr (Sum.inr (code, minimum))) :
    GuardedFirstLeftMacro A :=
  ⟨source, ⟨(code, minimum), hshape⟩⟩

/-- Retype a guarded source known to be an initial-left delayed target as the
finite key of its first right block. -/
def guardedFirstRightMacroOfDelayedTarget
    (source : GuardedRightEntrySource A)
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (htarget : source.1.1 = initialLeftDelayedTarget A scan letter) :
    GuardedFirstRightMacro A := by
  let leftState := A.step scan.1
    (leftRoundRecord letter.1 letter.2.1.informedOne letter.2.2)
  let bothState := A.step scan.1
    (bothRoundRecord letter.1 letter.2.1.informedOne letter.2.1.reversingTwo)
  refine ⟨source, ⟨((leftState, bothState), scan.2), ?_⟩⟩
  rw [htarget]
  rfl

/-- Initial-right/process-two mirror. -/
def guardedFirstLeftMacroOfDelayedTarget
    (source : GuardedLeftEntrySource A)
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (htarget : source.1.1 = initialRightDelayedTarget A scan letter) :
    GuardedFirstLeftMacro A := by
  let move : In₁ × In₂ := (letter.1.2, letter.1.1)
  let rightState := A.step scan.1
    (rightRoundRecord letter.1 letter.2.2 letter.2.1.informedTwo)
  let bothState := A.step scan.1
    (bothRoundRecord move letter.2.1.reversingOne letter.2.1.informedTwo)
  refine ⟨source, ⟨((rightState, bothState), scan.2), ?_⟩⟩
  rw [htarget]
  rfl

/-- Simultaneous selection of every exceptional first-block controller. -/
structure FiniteGuardedFirstControllerBank
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂] where
  rightController : ∀ key : GuardedFirstRightMacro A,
    TransitionRationalTree.{u, max u v x y s, s} In₁
      (GuardedFirstRightNarrowedLabel A key.1 key.2.1.1)
  rightWins : ∀ key : GuardedFirstRightMacro A,
    NarrowedAllThreadsWin (GuardedFirstRightMonitor A key.1 key.2.1.1)
      (rightController key).labeledTree
  leftController : ∀ key : GuardedFirstLeftMacro A,
    TransitionRationalTree.{v, max u v x y s, s} In₂
      (GuardedFirstLeftNarrowedLabel A key.1 key.2.1.1)
  leftWins : ∀ key : GuardedFirstLeftMacro A,
    NarrowedAllThreadsWin (GuardedFirstLeftMonitor A key.1 key.2.1.1)
      (leftController key).labeledTree

/-- The entire exceptional bank exists unconditionally once the finite
alphabets are fixed. -/
noncomputable def finiteGuardedFirstControllerBank
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂] :
    FiniteGuardedFirstControllerBank A := by
  classical
  let chooseRight := fun key : GuardedFirstRightMacro A =>
    Classical.choose (exists_finite_guardedFirstRightController
      A key.1 key.2.1.1 key.2.1.2 key.2.2)
  let chooseLeft := fun key : GuardedFirstLeftMacro A =>
    Classical.choose (exists_finite_guardedFirstLeftController
      A key.1 key.2.1.1 key.2.1.2 key.2.2)
  exact {
    rightController := chooseRight
    rightWins := fun key => Classical.choose_spec
      (exists_finite_guardedFirstRightController
        A key.1 key.2.1.1 key.2.1.2 key.2.2)
    leftController := chooseLeft
    leftWins := fun key => Classical.choose_spec
      (exists_finite_guardedFirstLeftController
        A key.1 key.2.1.1 key.2.1.2 key.2.2)
  }

/-- Every selected right controller reads back to the complete guarded
activation payload at its key. -/
noncomputable def FiniteGuardedFirstControllerBank.rightActivation
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (bank : FiniteGuardedFirstControllerBank A)
    (key : GuardedFirstRightMacro A) :
    GuardedRightActivation A key.1 key.2.1.1 key.2.1.2 :=
  guardedFirstRightController_sound A key.1 key.2.1.1 key.2.1.2
    (bank.rightController key) (bank.rightWins key)

/-- Left mirror. -/
noncomputable def FiniteGuardedFirstControllerBank.leftActivation
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (bank : FiniteGuardedFirstControllerBank A)
    (key : GuardedFirstLeftMacro A) :
    GuardedLeftActivation A key.1 key.2.1.1 key.2.1.2 :=
  guardedFirstLeftController_sound A key.1 key.2.1.1 key.2.1.2
    (bank.leftController key) (bank.leftWins key)

/-! ## Concrete handoff from guarded initial controllers -/

/-- The emitted source at an initial-left boundary, retyped as the key of the
first-right finite-controller bank. -/
noncomputable def guardedInitialLeftFirstMacroAt
    [Inhabited (In₁ × In₂)]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (receiver : ReceiverBlockStrategy In₁ In₂ (GuardedInitialLeftReceiverOutput A))
    (sender : SenderBlockStrategy In₂ Out₂)
    (hmonitor : ∀ env : Nat -> In₁ × In₂,
      (guardedInitialLeftBlockMonitor A).WinsPlay (pairPlay receiver sender env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    GuardedFirstRightMacro A :=
  guardedFirstRightMacroOfDelayedTarget A
    (guardedInitialLeftSourceAt A receiver sender hmonitor past move)
    (initialLeftScanAfter A (initialLeftLambdaOfGuardedPair A receiver sender) past)
    (initialLeftLetterAt (initialLeftLambdaOfGuardedPair A receiver sender) past move)
    (guardedInitialLeftSourceAt_target A receiver sender hmonitor past move)

/-- Initial-right mirror. -/
noncomputable def guardedInitialRightFirstMacroAt
    [Inhabited (In₂ × In₁)]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (receiver : ReceiverBlockStrategy In₂ In₁ (GuardedInitialRightReceiverOutput A))
    (sender : SenderBlockStrategy In₁ Out₁)
    (hmonitor : ∀ env : Nat -> In₂ × In₁,
      (guardedInitialRightBlockMonitor A).WinsPlay (pairPlay receiver sender env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    GuardedFirstLeftMacro A :=
  guardedFirstLeftMacroOfDelayedTarget A
    (guardedInitialRightSourceAt A receiver sender hmonitor past move)
    (initialRightScanAfter A (initialRightLambdaOfGuardedPair A receiver sender) past)
    (initialRightLetterAt (initialRightLambdaOfGuardedPair A receiver sender) past move)
    (guardedInitialRightSourceAt_target A receiver sender hmonitor past move)

/-- The first recurrent right block selected at a concrete initial-left
boundary has the full guarded semantic payload. -/
noncomputable def FiniteGuardedFirstControllerBank.activationAfterInitialLeft
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (bank : FiniteGuardedFirstControllerBank A)
    (receiver : ReceiverBlockStrategy In₁ In₂ (GuardedInitialLeftReceiverOutput A))
    (sender : SenderBlockStrategy In₂ Out₂)
    (hmonitor : ∀ env : Nat -> In₁ × In₂,
      (guardedInitialLeftBlockMonitor A).WinsPlay (pairPlay receiver sender env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :=
  bank.rightActivation A
    (guardedInitialLeftFirstMacroAt A receiver sender hmonitor past move)

/-- Initial-right mirror. -/
noncomputable def FiniteGuardedFirstControllerBank.activationAfterInitialRight
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (bank : FiniteGuardedFirstControllerBank A)
    (receiver : ReceiverBlockStrategy In₂ In₁ (GuardedInitialRightReceiverOutput A))
    (sender : SenderBlockStrategy In₁ Out₁)
    (hmonitor : ∀ env : Nat -> In₂ × In₁,
      (guardedInitialRightBlockMonitor A).WinsPlay (pairPlay receiver sender env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :=
  bank.leftActivation A
    (guardedInitialRightFirstMacroAt A receiver sender hmonitor past move)

end DetParityAutomaton

end DistributedSynthesis
