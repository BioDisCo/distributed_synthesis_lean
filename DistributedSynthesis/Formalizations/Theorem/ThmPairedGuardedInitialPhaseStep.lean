/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedPhaseSummary

/-!
# Local initial-phase steps and the first asynchronous reversal

At a strict reversal the staged key is initialized and stepped on the current
round: the old receiver becomes the new blind owner, and the new receiver
obtains the same key from the delivered partner summary.  At a `both` round
the old receiver cannot detect the reversal and continues the old candidate,
whereas the other side steps the new candidate.  The guarded root-overlap law
is exactly what makes their physical outputs compatible in that case.

All functions are local.  In particular the old receiver's close takes only
its own input, and the new receiver is told only its own previous receipt bit
when choosing the latent entry row.
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
variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (rightBasis : ∀ target profile,
    (rightProfileGuardedAutomaton A target profile).RationalRunBasis)
  (leftBasis : ∀ target profile,
    (leftProfileGuardedAutomaton A target profile).RationalRunBasis)
  (controllers : LocallyConsistentGuardedInitialControllers
    A strategy hwin rightBasis leftBasis)
  (bank : FiniteGuardedFirstControllerBank A)

/-! ## Continuing the two guarded initial orientations -/

/-- Process one receives another initial-left round, emits its informed
output, advances finite readback, and stages this round's possible right key. -/
noncomputable def continueGuardedInitialLeftReceiver
    (state : GuardedInitialLeftReceiverControl A strategy hwin rightBasis
      leftBasis controllers) (move : In₁ × In₂) :
    Out₁ × GuardedInitialLeftReceiverControl A strategy hwin rightBasis
      leftBasis controllers :=
  let label := controllers.leftController.labelOf state.1.1
  let answer := label.2 state.1.2 move
  (answer.1.informedOne,
    (stepGuardedInitialLeftFiniteReadback A strategy hwin rightBasis leftBasis
        controllers state.1 move,
      guardedInitialLeftLocalFirstMacro A strategy hwin rightBasis leftBasis
        controllers state.1 move))

/-- Process two's blind continuation in the initial-left orientation. -/
noncomputable def continueGuardedInitialLeftBlind
    (control : controllers.leftController.Control) (inputTwo : In₂) :
    Out₂ × controllers.leftController.Control :=
  ((controllers.leftController.labelOf control).1 inputTwo,
    controllers.leftController.step control inputTwo)

/-- Initial-right receiving mirror. -/
noncomputable def continueGuardedInitialRightReceiver
    (state : GuardedInitialRightReceiverControl A strategy hwin rightBasis
      leftBasis controllers) (move : In₂ × In₁) :
    Out₂ × GuardedInitialRightReceiverControl A strategy hwin rightBasis
      leftBasis controllers :=
  let label := controllers.rightController.labelOf state.1.1
  let answer := label.2 state.1.2 move
  (answer.1.informedTwo,
    (stepGuardedInitialRightFiniteReadback A strategy hwin rightBasis leftBasis
        controllers state.1 move,
      guardedInitialRightLocalFirstMacro A strategy hwin rightBasis leftBasis
        controllers state.1 move))

/-- Process one's blind initial-right continuation. -/
noncomputable def continueGuardedInitialRightBlind
    (control : controllers.rightController.Control) (inputOne : In₁) :
    Out₁ × controllers.rightController.Control :=
  ((controllers.rightController.labelOf control).1 inputOne,
    controllers.rightController.step control inputOne)

/-! ## Closing initial left into exceptional first right -/

/-- The old receiver sees no receive.  Its retained staged key initializes
and steps the new blind owner on the current strict-right round.  The fallback
output is used only at an unreachable state with no staged key. -/
noncomputable def closeGuardedInitialLeftOne
    (state : GuardedInitialLeftReceiverControl A strategy hwin rightBasis
      leftBasis controllers) (inputOne : In₁) :
    Out₁ × Option (GuardedFirstRightOwnerControl A bank) :=
  match state.2 with
  | none =>
      (guardedInitialLeftNoRecvOneOutput A strategy hwin rightBasis leftBasis
        controllers state.1 inputOne, none)
  | some key =>
      let result := stepGuardedFirstRightOwner A bank
        (initialGuardedFirstRightOwner A bank key) inputOne
      (result.1, some result.2)

/-- The new receiver reads the old receiver's previous summary, initializes
the exceptional receiver at that staged key, and performs its current receive
step against the matching initial owner control. -/
noncomputable def closeGuardedInitialLeftTwo
    (partner : GuardedInitialLeftReceiverControl A strategy hwin rightBasis
      leftBasis controllers) (move : In₂ × In₁)
    (previouslyReceived : Bool) :
    Out₂ × Option (GuardedFirstRightReceiverControl A) :=
  match partner.2 with
  | none =>
      let label := controllers.leftController.labelOf partner.1.1
      let answer := label.2 partner.1.2 (move.2, move.1)
      (answer.1.reversingTwo, none)
  | some key =>
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueGuardedFirstRightReceiver A bank
        (initialGuardedFirstRightReceiver A key row)
        (initialGuardedFirstRightOwner A bank key) move
      (result.1, some result.2)

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem closeGuardedInitialLeft_common_key
    (state : GuardedInitialLeftReceiverControl A strategy hwin rightBasis
      leftBasis controllers) (inputOne : In₁) (move : In₂ × In₁)
    (previouslyReceived : Bool)
    (owner : GuardedFirstRightOwnerControl A bank)
    (receiver : GuardedFirstRightReceiverControl A)
    (howner : (closeGuardedInitialLeftOne A strategy hwin rightBasis leftBasis
      controllers bank state inputOne).2 = some owner)
    (hreceiver : (closeGuardedInitialLeftTwo A strategy hwin rightBasis leftBasis
      controllers bank state move previouslyReceived).2 = some receiver) :
    owner.1 = receiver.1 := by
  rcases state with ⟨finite, staged⟩
  cases staged with
  | none => simp [closeGuardedInitialLeftOne] at howner
  | some key =>
      simp only [closeGuardedInitialLeftOne, Option.some.injEq] at howner
      simp only [closeGuardedInitialLeftTwo, Option.some.injEq] at hreceiver
      subst owner
      subst receiver
      rw [continueGuardedFirstRightReceiver_key]
      rfl

/-! ## Initial-right mirror -/

noncomputable def closeGuardedInitialRightTwo
    (state : GuardedInitialRightReceiverControl A strategy hwin rightBasis
      leftBasis controllers) (inputTwo : In₂) :
    Out₂ × Option (GuardedFirstLeftOwnerControl A bank) :=
  match state.2 with
  | none =>
      (guardedInitialRightNoRecvTwoOutput A strategy hwin rightBasis leftBasis
        controllers state.1 inputTwo, none)
  | some key =>
      let result := stepGuardedFirstLeftOwner A bank
        (initialGuardedFirstLeftOwner A bank key) inputTwo
      (result.1, some result.2)

noncomputable def closeGuardedInitialRightOne
    (partner : GuardedInitialRightReceiverControl A strategy hwin rightBasis
      leftBasis controllers) (move : In₁ × In₂)
    (previouslyReceived : Bool) :
    Out₁ × Option (GuardedFirstLeftReceiverControl A) :=
  match partner.2 with
  | none =>
      let label := controllers.rightController.labelOf partner.1.1
      let answer := label.2 partner.1.2 (move.2, move.1)
      (answer.1.reversingOne, none)
  | some key =>
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueGuardedFirstLeftReceiver A bank
        (initialGuardedFirstLeftReceiver A key row)
        (initialGuardedFirstLeftOwner A bank key) move
      (result.1, some result.2)

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem closeGuardedInitialRight_common_key
    (state : GuardedInitialRightReceiverControl A strategy hwin rightBasis
      leftBasis controllers) (inputTwo : In₂) (move : In₁ × In₂)
    (previouslyReceived : Bool)
    (owner : GuardedFirstLeftOwnerControl A bank)
    (receiver : GuardedFirstLeftReceiverControl A)
    (howner : (closeGuardedInitialRightTwo A strategy hwin rightBasis leftBasis
      controllers bank state inputTwo).2 = some owner)
    (hreceiver : (closeGuardedInitialRightOne A strategy hwin rightBasis leftBasis
      controllers bank state move previouslyReceived).2 = some receiver) :
    owner.1 = receiver.1 := by
  rcases state with ⟨finite, staged⟩
  cases staged with
  | none => simp [closeGuardedInitialRightTwo] at howner
  | some key =>
      simp only [closeGuardedInitialRightTwo, Option.some.injEq] at howner
      simp only [closeGuardedInitialRightOne, Option.some.injEq] at hreceiver
      subst owner
      subst receiver
      rw [continueGuardedFirstLeftReceiver_key]
      rfl

end


end DetParityAutomaton

end DistributedSynthesis
