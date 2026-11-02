/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedInitialFiniteReadback

/-!
# Finite local handoff out of the profiledGuarded initial phase

The initial controller emits only raw profiledGuarded-source data.  This file checks
that data against the finite monitor state and, when the checks succeed,
retypes it as the key of the exceptional first-block controller bank.  Along
every real controller path the checks succeed and the locally computed key is
the semantic profiledGuarded handoff key.

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
  [outOneDefault : Inhabited Out₁] [outTwoDefault : Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (rightBasis : ∀ target profile,
    (rightProfiledGuardedAutomaton A target profile).RationalRunBasis)
  (leftBasis : ∀ target profile,
    (leftProfiledGuardedAutomaton A target profile).RationalRunBasis)
  (controllers : LocallyConsistentProfiledGuardedInitialControllers
    A strategy hwin rightBasis leftBasis)

/-- The concrete initial-left letter read from the finite Moore state. -/
noncomputable def profiledGuardedInitialLeftFiniteLetter
    (state : ProfiledGuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₁ × In₂) :
    InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let label := controllers.leftController.labelOf state.1
  (move, (label.2 state.2 move).1, label.1 move.2)

/-- The profiledGuarded source data emitted by the same finite table lookup. -/
noncomputable def profiledGuardedInitialLeftFiniteSourceData
    (state : ProfiledGuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₁ × In₂) : ProfiledGuardedRightEntryData A :=
  ((controllers.leftController.labelOf state.1).2 state.2 move).2

/-- Local, partial retyping of an emitted initial-left source as a first-right
bank key.  Failure values are used only on unreachable control tuples. -/
noncomputable def profiledGuardedInitialLeftLocalFirstMacro
    (state : ProfiledGuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₁ × In₂) : Option (ProfiledGuardedFirstRightMacro A) := by
  classical
  let data := profiledGuardedInitialLeftFiniteSourceData A strategy hwin rightBasis
    leftBasis controllers state move
  let letter := profiledGuardedInitialLeftFiniteLetter A strategy hwin rightBasis
    leftBasis controllers state move
  if hfeasible :
      (rightProfiledGuardedAutomaton A data.1 data.2).HasRationalRun then
    let source : ProfiledGuardedRightEntrySource A := ⟨data, hfeasible⟩
    if htarget : erasePairedProfiledState A source.1.1 =
        initialLeftDelayedTarget A state.2.base.1.1 letter then
      exact some (profiledGuardedFirstRightMacroOfDelayedTarget A source
        state.2.base.1.1 letter htarget)
    else exact none
  else exact none

/-- Process-two mirror letter. -/
noncomputable def profiledGuardedInitialRightFiniteLetter
    (state : ProfiledGuardedInitialRightFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₂ × In₁) :
    InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let label := controllers.rightController.labelOf state.1
  (move, (label.2 state.2 move).1, label.1 move.2)

noncomputable def profiledGuardedInitialRightFiniteSourceData
    (state : ProfiledGuardedInitialRightFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₂ × In₁) : ProfiledGuardedLeftEntryData A :=
  ((controllers.rightController.labelOf state.1).2 state.2 move).2

noncomputable def profiledGuardedInitialRightLocalFirstMacro
    (state : ProfiledGuardedInitialRightFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₂ × In₁) : Option (ProfiledGuardedFirstLeftMacro A) := by
  classical
  let data := profiledGuardedInitialRightFiniteSourceData A strategy hwin rightBasis
    leftBasis controllers state move
  let letter := profiledGuardedInitialRightFiniteLetter A strategy hwin rightBasis
    leftBasis controllers state move
  if hfeasible :
      (leftProfiledGuardedAutomaton A data.1 data.2).HasRationalRun then
    let source : ProfiledGuardedLeftEntrySource A := ⟨data, hfeasible⟩
    if htarget : erasePairedProfiledState A source.1.1 =
        initialRightDelayedTarget A state.2.base.1.1 letter then
      exact some (profiledGuardedFirstLeftMacroOfDelayedTarget A source
        state.2.base.1.1 letter htarget)
    else exact none
  else exact none

section
omit outOneDefault outTwoDefault

theorem profiledGuardedInitialLeftFiniteLetter_eq
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    profiledGuardedInitialLeftFiniteLetter A strategy hwin rightBasis leftBasis controllers
        (profiledGuardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move =
      initialLeftLetterAt
        (initialLeftLambdaOfProfiledGuardedPair A
          (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis
            leftBasis controllers)
          (profiledGuardedInitialLeftSenderOfController A strategy hwin rightBasis
            leftBasis controllers)) past move := by
  rw [profiledGuardedInitialLeftFiniteReadbackAfter_eq]
  rfl

theorem profiledGuardedInitialRightFiniteLetter_eq
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    profiledGuardedInitialRightFiniteLetter A strategy hwin rightBasis leftBasis controllers
        (profiledGuardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move =
      initialRightLetterAt
        (initialRightLambdaOfProfiledGuardedPair A
          (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis
            leftBasis controllers)
          (profiledGuardedInitialRightSenderOfController A strategy hwin rightBasis
            leftBasis controllers)) past move := by
  rw [profiledGuardedInitialRightFiniteReadbackAfter_eq]
  rfl

theorem profiledGuardedInitialLeftFiniteSourceData_eq
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    profiledGuardedInitialLeftFiniteSourceData A strategy hwin rightBasis leftBasis
        controllers
        (profiledGuardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move =
      (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis
        leftBasis controllers past move).2 := by
  rw [profiledGuardedInitialLeftFiniteReadbackAfter_eq]
  rfl

theorem profiledGuardedInitialRightFiniteSourceData_eq
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    profiledGuardedInitialRightFiniteSourceData A strategy hwin rightBasis leftBasis
        controllers
        (profiledGuardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move =
      (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis
        leftBasis controllers past move).2 := by
  rw [profiledGuardedInitialRightFiniteReadbackAfter_eq]
  rfl

/-- On every real finite-controller path, the local initial-left handoff is
present and is exactly the semantic profiledGuarded key. -/
theorem profiledGuardedInitialLeftLocalFirstMacro_eq_some
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    profiledGuardedInitialLeftLocalFirstMacro A strategy hwin rightBasis leftBasis
        controllers
        (profiledGuardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move =
      some (profiledGuardedInitialLeftController_firstMacroAt A strategy hwin rightBasis
        leftBasis controllers past move) := by
  classical
  let receiver := profiledGuardedInitialLeftReceiverOfController A strategy hwin
    rightBasis leftBasis controllers
  let sender := profiledGuardedInitialLeftSenderOfController A strategy hwin
    rightBasis leftBasis controllers
  have hconditions := profiledGuardedInitialLeft_stepConditions A receiver sender
    (profiledGuardedInitialLeftController_baseWins A strategy hwin rightBasis leftBasis
      controllers) past move
  dsimp only at hconditions
  unfold profiledGuardedInitialLeftLocalFirstMacro
  rw [profiledGuardedInitialLeftFiniteSourceData_eq,
    profiledGuardedInitialLeftFiniteLetter_eq,
    profiledGuardedInitialLeftFiniteReadback_scan]
  rw [dif_pos hconditions.2, dif_pos hconditions.1]
  unfold profiledGuardedInitialLeftController_firstMacroAt
    profiledGuardedInitialLeftFirstMacroAt profiledGuardedInitialLeftSourceAt
  congr

/-- Process-two mirror. -/
theorem profiledGuardedInitialRightLocalFirstMacro_eq_some
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    profiledGuardedInitialRightLocalFirstMacro A strategy hwin rightBasis leftBasis
        controllers
        (profiledGuardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move =
      some (profiledGuardedInitialRightController_firstMacroAt A strategy hwin rightBasis
        leftBasis controllers past move) := by
  classical
  let receiver := profiledGuardedInitialRightReceiverOfController A strategy hwin
    rightBasis leftBasis controllers
  let sender := profiledGuardedInitialRightSenderOfController A strategy hwin
    rightBasis leftBasis controllers
  have hconditions := profiledGuardedInitialRight_stepConditions A receiver sender
    (profiledGuardedInitialRightController_baseWins A strategy hwin rightBasis leftBasis
      controllers) past move
  dsimp only at hconditions
  unfold profiledGuardedInitialRightLocalFirstMacro
  rw [profiledGuardedInitialRightFiniteSourceData_eq,
    profiledGuardedInitialRightFiniteLetter_eq,
    profiledGuardedInitialRightFiniteReadback_scan]
  rw [dif_pos hconditions.2, dif_pos hconditions.1]
  unfold profiledGuardedInitialRightController_firstMacroAt
    profiledGuardedInitialRightFirstMacroAt profiledGuardedInitialRightSourceAt
  congr

end

section Activation

variable [Inhabited Out₁] [Inhabited Out₂]
variable (bank : FiniteProfiledGuardedFirstControllerBank A)

/-- Initialize both finite controls of the exceptional first-right block from
the locally checked initial-left key. -/
noncomputable def activateProfiledGuardedFirstRightFromInitial
    (state : ProfiledGuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₁ × In₂) (row : PairedEntryRow) :
    Option (ProfiledGuardedFirstRightOwnerControl A bank ×
      ProfiledGuardedFirstRightReceiverControl A) :=
  (profiledGuardedInitialLeftLocalFirstMacro A strategy hwin rightBasis leftBasis
    controllers state move).map fun key =>
      (initialProfiledGuardedFirstRightOwner A bank key,
        initialProfiledGuardedFirstRightReceiver A key row)

/-- Process-two mirror. -/
noncomputable def activateProfiledGuardedFirstLeftFromInitial
    (state : ProfiledGuardedInitialRightFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers)
    (move : In₂ × In₁) (row : PairedEntryRow) :
    Option (ProfiledGuardedFirstLeftOwnerControl A bank ×
      ProfiledGuardedFirstLeftReceiverControl A) :=
  (profiledGuardedInitialRightLocalFirstMacro A strategy hwin rightBasis leftBasis
    controllers state move).map fun key =>
      (initialProfiledGuardedFirstLeftOwner A bank key,
        initialProfiledGuardedFirstLeftReceiver A key row)

section
omit outOneDefault outTwoDefault

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The reachable initial-left seam activates the two sides from the exact
same semantic key. -/
theorem activateProfiledGuardedFirstRightFromInitial_eq_some
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) :
    activateProfiledGuardedFirstRightFromInitial A strategy hwin rightBasis leftBasis
        controllers bank
        (profiledGuardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move row =
      some
        (initialProfiledGuardedFirstRightOwner A bank
            (profiledGuardedInitialLeftController_firstMacroAt A strategy hwin
              rightBasis leftBasis controllers past move),
          initialProfiledGuardedFirstRightReceiver A
            (profiledGuardedInitialLeftController_firstMacroAt A strategy hwin
              rightBasis leftBasis controllers past move) row) := by
  rw [activateProfiledGuardedFirstRightFromInitial,
    profiledGuardedInitialLeftLocalFirstMacro_eq_some]
  rfl

theorem activateProfiledGuardedFirstLeftFromInitial_eq_some
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) :
    activateProfiledGuardedFirstLeftFromInitial A strategy hwin rightBasis leftBasis
        controllers bank
        (profiledGuardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move row =
      some
        (initialProfiledGuardedFirstLeftOwner A bank
            (profiledGuardedInitialRightController_firstMacroAt A strategy hwin
              rightBasis leftBasis controllers past move),
          initialProfiledGuardedFirstLeftReceiver A
            (profiledGuardedInitialRightController_firstMacroAt A strategy hwin
              rightBasis leftBasis controllers past move) row) := by
  rw [activateProfiledGuardedFirstLeftFromInitial,
    profiledGuardedInitialRightLocalFirstMacro_eq_some]
  rfl

theorem activateProfiledGuardedFirstRightFromInitial_common_key
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow)
    (activated : ProfiledGuardedFirstRightOwnerControl A bank ×
      ProfiledGuardedFirstRightReceiverControl A)
    (hactivated : activateProfiledGuardedFirstRightFromInitial A strategy hwin
      rightBasis leftBasis controllers bank
      (profiledGuardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis
        leftBasis controllers past) move row = some activated) :
    activated.1.1 = activated.2.1 := by
  rw [activateProfiledGuardedFirstRightFromInitial_eq_some] at hactivated
  cases Option.some.inj hactivated.symm
  rfl

theorem activateProfiledGuardedFirstLeftFromInitial_common_key
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow)
    (activated : ProfiledGuardedFirstLeftOwnerControl A bank ×
      ProfiledGuardedFirstLeftReceiverControl A)
    (hactivated : activateProfiledGuardedFirstLeftFromInitial A strategy hwin
      rightBasis leftBasis controllers bank
      (profiledGuardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis
        leftBasis controllers past) move row = some activated) :
    activated.1.1 = activated.2.1 := by
  rw [activateProfiledGuardedFirstLeftFromInitial_eq_some] at hactivated
  cases Option.some.inj hactivated.symm
  rfl

end

end

end Activation

end

end DetParityAutomaton

end DistributedSynthesis
