/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedInitialFiniteReadback

/-!
# Finite local handoff out of the guarded initial phase

The initial controller emits only raw guarded-source data.  This file checks
that data against the finite monitor state and, when the checks succeed,
retypes it as the key of the exceptional first-block controller bank.  Along
every real controller path the checks succeed and the locally computed key is
the semantic guarded handoff key.

The operation reads the finite Moore state and the current complete move at
the receiving side.  It contains no strict-leader predicate.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

variable [Inhabited In₁] [Inhabited In₂]
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

/-- The concrete initial-left letter read from the finite Moore state. -/
noncomputable def guardedInitialLeftFiniteLetter
    (state : GuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₁ × In₂) :
    InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let label := controllers.leftController.labelOf state.1
  (move, (label.2 state.2 move).1, label.1 move.2)

/-- The guarded source data emitted by the same finite table lookup. -/
noncomputable def guardedInitialLeftFiniteSourceData
    (state : GuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₁ × In₂) : GuardedRightEntryData A :=
  ((controllers.leftController.labelOf state.1).2 state.2 move).2

/-- Local, partial retyping of an emitted initial-left source as a first-right
bank key.  Failure values are used only on unreachable control tuples. -/
noncomputable def guardedInitialLeftLocalFirstMacro
    (state : GuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₁ × In₂) : Option (GuardedFirstRightMacro A) := by
  classical
  let data := guardedInitialLeftFiniteSourceData A strategy hwin rightBasis
    leftBasis controllers state move
  let letter := guardedInitialLeftFiniteLetter A strategy hwin rightBasis
    leftBasis controllers state move
  if hfeasible :
      (rightProfileGuardedAutomaton A data.1 data.2).HasRationalRun then
    let source : GuardedRightEntrySource A := ⟨data, hfeasible⟩
    if htarget : source.1.1 =
        initialLeftDelayedTarget A state.2.base.1.1 letter then
      exact some (guardedFirstRightMacroOfDelayedTarget A source
        state.2.base.1.1 letter htarget)
    else exact none
  else exact none

/-- Process-two mirror letter. -/
noncomputable def guardedInitialRightFiniteLetter
    (state : GuardedInitialRightFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₂ × In₁) :
    InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let label := controllers.rightController.labelOf state.1
  (move, (label.2 state.2 move).1, label.1 move.2)

noncomputable def guardedInitialRightFiniteSourceData
    (state : GuardedInitialRightFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₂ × In₁) : GuardedLeftEntryData A :=
  ((controllers.rightController.labelOf state.1).2 state.2 move).2

noncomputable def guardedInitialRightLocalFirstMacro
    (state : GuardedInitialRightFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₂ × In₁) : Option (GuardedFirstLeftMacro A) := by
  classical
  let data := guardedInitialRightFiniteSourceData A strategy hwin rightBasis
    leftBasis controllers state move
  let letter := guardedInitialRightFiniteLetter A strategy hwin rightBasis
    leftBasis controllers state move
  if hfeasible :
      (leftProfileGuardedAutomaton A data.1 data.2).HasRationalRun then
    let source : GuardedLeftEntrySource A := ⟨data, hfeasible⟩
    if htarget : source.1.1 =
        initialRightDelayedTarget A state.2.base.1.1 letter then
      exact some (guardedFirstLeftMacroOfDelayedTarget A source
        state.2.base.1.1 letter htarget)
    else exact none
  else exact none

theorem guardedInitialLeftFiniteLetter_eq
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    guardedInitialLeftFiniteLetter A strategy hwin rightBasis leftBasis controllers
        (guardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move =
      initialLeftLetterAt
        (initialLeftLambdaOfGuardedPair A
          (guardedInitialLeftReceiverOfController A strategy hwin rightBasis
            leftBasis controllers)
          (guardedInitialLeftSenderOfController A strategy hwin rightBasis
            leftBasis controllers)) past move := by
  rw [guardedInitialLeftFiniteReadbackAfter_eq]
  rfl

theorem guardedInitialRightFiniteLetter_eq
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    guardedInitialRightFiniteLetter A strategy hwin rightBasis leftBasis controllers
        (guardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move =
      initialRightLetterAt
        (initialRightLambdaOfGuardedPair A
          (guardedInitialRightReceiverOfController A strategy hwin rightBasis
            leftBasis controllers)
          (guardedInitialRightSenderOfController A strategy hwin rightBasis
            leftBasis controllers)) past move := by
  rw [guardedInitialRightFiniteReadbackAfter_eq]
  rfl

theorem guardedInitialLeftFiniteSourceData_eq
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    guardedInitialLeftFiniteSourceData A strategy hwin rightBasis leftBasis
        controllers
        (guardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move =
      (guardedInitialLeftReceiverOfController A strategy hwin rightBasis
        leftBasis controllers past move).2 := by
  rw [guardedInitialLeftFiniteReadbackAfter_eq]
  rfl

theorem guardedInitialRightFiniteSourceData_eq
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    guardedInitialRightFiniteSourceData A strategy hwin rightBasis leftBasis
        controllers
        (guardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move =
      (guardedInitialRightReceiverOfController A strategy hwin rightBasis
        leftBasis controllers past move).2 := by
  rw [guardedInitialRightFiniteReadbackAfter_eq]
  rfl

/-- On every real finite-controller path, the local initial-left handoff is
present and is exactly the semantic guarded key. -/
theorem guardedInitialLeftLocalFirstMacro_eq_some
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    guardedInitialLeftLocalFirstMacro A strategy hwin rightBasis leftBasis
        controllers
        (guardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move =
      some (guardedInitialLeftController_firstMacroAt A strategy hwin rightBasis
        leftBasis controllers past move) := by
  classical
  let receiver := guardedInitialLeftReceiverOfController A strategy hwin
    rightBasis leftBasis controllers
  let sender := guardedInitialLeftSenderOfController A strategy hwin
    rightBasis leftBasis controllers
  have hconditions := guardedInitialLeft_stepConditions A receiver sender
    (guardedInitialLeftController_baseWins A strategy hwin rightBasis leftBasis
      controllers) past move
  dsimp only at hconditions
  unfold guardedInitialLeftLocalFirstMacro
  rw [guardedInitialLeftFiniteSourceData_eq,
    guardedInitialLeftFiniteLetter_eq,
    guardedInitialLeftFiniteReadback_scan]
  rw [dif_pos hconditions.2, dif_pos hconditions.1]
  unfold guardedInitialLeftController_firstMacroAt
    guardedInitialLeftFirstMacroAt guardedInitialLeftSourceAt
  congr

/-- Process-two mirror. -/
theorem guardedInitialRightLocalFirstMacro_eq_some
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    guardedInitialRightLocalFirstMacro A strategy hwin rightBasis leftBasis
        controllers
        (guardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move =
      some (guardedInitialRightController_firstMacroAt A strategy hwin rightBasis
        leftBasis controllers past move) := by
  classical
  let receiver := guardedInitialRightReceiverOfController A strategy hwin
    rightBasis leftBasis controllers
  let sender := guardedInitialRightSenderOfController A strategy hwin
    rightBasis leftBasis controllers
  have hconditions := guardedInitialRight_stepConditions A receiver sender
    (guardedInitialRightController_baseWins A strategy hwin rightBasis leftBasis
      controllers) past move
  dsimp only at hconditions
  unfold guardedInitialRightLocalFirstMacro
  rw [guardedInitialRightFiniteSourceData_eq,
    guardedInitialRightFiniteLetter_eq,
    guardedInitialRightFiniteReadback_scan]
  rw [dif_pos hconditions.2, dif_pos hconditions.1]
  unfold guardedInitialRightController_firstMacroAt
    guardedInitialRightFirstMacroAt guardedInitialRightSourceAt
  congr

section Activation

variable [Inhabited Out₁] [Inhabited Out₂]
variable (bank : FiniteGuardedFirstControllerBank A)

/-- Initialize both finite controls of the exceptional first-right block from
the locally checked initial-left key. -/
noncomputable def activateGuardedFirstRightFromInitial
    (state : GuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₁ × In₂) (row : PairedEntryRow) :
    Option (GuardedFirstRightOwnerControl A bank ×
      GuardedFirstRightReceiverControl A) :=
  (guardedInitialLeftLocalFirstMacro A strategy hwin rightBasis leftBasis
    controllers state move).map fun key =>
      (initialGuardedFirstRightOwner A bank key,
        initialGuardedFirstRightReceiver A key row)

/-- Process-two mirror. -/
noncomputable def activateGuardedFirstLeftFromInitial
    (state : GuardedInitialRightFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₂ × In₁) (row : PairedEntryRow) :
    Option (GuardedFirstLeftOwnerControl A bank ×
      GuardedFirstLeftReceiverControl A) :=
  (guardedInitialRightLocalFirstMacro A strategy hwin rightBasis leftBasis
    controllers state move).map fun key =>
      (initialGuardedFirstLeftOwner A bank key,
        initialGuardedFirstLeftReceiver A key row)

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The reachable initial-left seam activates the two sides from the exact
same semantic key. -/
theorem activateGuardedFirstRightFromInitial_eq_some
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) :
    activateGuardedFirstRightFromInitial A strategy hwin rightBasis leftBasis
        controllers bank
        (guardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move row =
      some
        (initialGuardedFirstRightOwner A bank
            (guardedInitialLeftController_firstMacroAt A strategy hwin
              rightBasis leftBasis controllers past move),
          initialGuardedFirstRightReceiver A
            (guardedInitialLeftController_firstMacroAt A strategy hwin
              rightBasis leftBasis controllers past move) row) := by
  rw [activateGuardedFirstRightFromInitial,
    guardedInitialLeftLocalFirstMacro_eq_some]
  rfl

theorem activateGuardedFirstLeftFromInitial_eq_some
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) :
    activateGuardedFirstLeftFromInitial A strategy hwin rightBasis leftBasis
        controllers bank
        (guardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move row =
      some
        (initialGuardedFirstLeftOwner A bank
            (guardedInitialRightController_firstMacroAt A strategy hwin
              rightBasis leftBasis controllers past move),
          initialGuardedFirstLeftReceiver A
            (guardedInitialRightController_firstMacroAt A strategy hwin
              rightBasis leftBasis controllers past move) row) := by
  rw [activateGuardedFirstLeftFromInitial,
    guardedInitialRightLocalFirstMacro_eq_some]
  rfl

theorem activateGuardedFirstRightFromInitial_common_key
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow)
    (activated : GuardedFirstRightOwnerControl A bank ×
      GuardedFirstRightReceiverControl A)
    (hactivated : activateGuardedFirstRightFromInitial A strategy hwin
      rightBasis leftBasis controllers bank
      (guardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis
        leftBasis controllers past) move row = some activated) :
    activated.1.1 = activated.2.1 := by
  rw [activateGuardedFirstRightFromInitial_eq_some] at hactivated
  cases Option.some.inj hactivated.symm
  rfl

theorem activateGuardedFirstLeftFromInitial_common_key
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow)
    (activated : GuardedFirstLeftOwnerControl A bank ×
      GuardedFirstLeftReceiverControl A)
    (hactivated : activateGuardedFirstLeftFromInitial A strategy hwin
      rightBasis leftBasis controllers bank
      (guardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis
        leftBasis controllers past) move row = some activated) :
    activated.1.1 = activated.2.1 := by
  rw [activateGuardedFirstLeftFromInitial_eq_some] at hactivated
  cases Option.some.inj hactivated.symm
  rfl

end

end Activation

end

end DetParityAutomaton

end DistributedSynthesis
