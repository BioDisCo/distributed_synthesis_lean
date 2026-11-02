/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialFiniteReadback

/-!
# Local recurrent handoff over the feasible policy bank

This is the final-root version of `ThmPairedEntryLocalHandoff`.  Its bank key
is the paired target selected by the finite initial-block controller, rather
than the first input pair of the original strategy.  All run-time carriers are
finite.  The only latent-row selector remains the locally observable receipt
bit; no strict-leader predicate occurs in the state or transition functions.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Initial-controller handoff into the bank -/

/-- Concrete process-two macro data staged by an initial-left close. -/
def initialLeftCloseMacroData
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    (A.State × A.State) × A.State :=
  let rightState := A.step scan.1
    (rightRoundRecord (letter.1.2, letter.1.1)
      letter.2.1.reversingOne letter.2.1.reversingTwo)
  let bothState := A.step scan.1
    (bothRoundRecord letter.1 letter.2.1.informedOne
      letter.2.1.reversingTwo)
  ((rightState, bothState), scan.2)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem initialLeftCloseTarget_eq_macroData
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    initialLeftCloseTarget A scan letter =
      Sum.inr (Sum.inr (initialLeftCloseMacroData A scan letter)) := rfl

/-- Concrete process-one macro data staged by an initial-right close. -/
def initialRightCloseMacroData
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    (A.State × A.State) × A.State :=
  let move : In₁ × In₂ := (letter.1.2, letter.1.1)
  let leftState := A.step scan.1
    (leftRoundRecord move letter.2.1.reversingOne
      letter.2.1.reversingTwo)
  let bothState := A.step scan.1
    (bothRoundRecord move letter.2.1.reversingOne
      letter.2.1.informedTwo)
  ((leftState, bothState), scan.2)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem initialRightCloseTarget_eq_macroData
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    initialRightCloseTarget A scan letter =
      Sum.inr (Sum.inl (initialRightCloseMacroData A scan letter)) := rfl

/-! ## Locally executable initial close data -/

/-- Initial-left close data computed with process one's genuinely local
no-receive action.  The receiving process may still use the complete current
move for the other entries. -/
noncomputable def initialLeftLocalCloseMacroData
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    (A.State × A.State) × A.State :=
  let lambda := initialLeftLambdaOfPinnedController A strategy
    controllers.toRootCompatibleInitialControllers
  let scan := initialLeftScanAfter A lambda past
  let letter := initialLeftLetterAt lambda past move
  let localOne := initialLeftNoRecvOneOutput A strategy controllers
    (initialLeftFiniteReadbackAfter A strategy controllers past) move.1
  let rightState := A.step scan.1
    (rightRoundRecord (move.2, move.1) localOne
      letter.2.1.reversingTwo)
  let bothState := A.step scan.1
    (bothRoundRecord move letter.2.1.informedOne
      letter.2.1.reversingTwo)
  ((rightState, bothState), scan.2)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Removing the hidden current input from process one's action does not
change the staged recurrent state. -/
theorem initialLeftLocalCloseMacroData_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    initialLeftLocalCloseMacroData A strategy controllers past move =
      initialLeftCloseMacroData A
        (initialLeftScanAfter A
          (initialLeftLambdaOfPinnedController A strategy
            controllers.toRootCompatibleInitialControllers) past)
        (initialLeftLetterAt
          (initialLeftLambdaOfPinnedController A strategy
            controllers.toRootCompatibleInitialControllers) past move) := by
  unfold initialLeftLocalCloseMacroData initialLeftCloseMacroData
  dsimp only
  rw [initialLeftNoRecvOneOutput_eq A strategy controllers past move.1 move.2]
  rfl

/-- Initial-right mirror, using process two's locally executable action at
the first left close. -/
noncomputable def initialRightLocalCloseMacroData
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    (A.State × A.State) × A.State :=
  let lambda := initialRightLambdaOfPinnedController A strategy
    controllers.toRootCompatibleInitialControllers
  let scan := initialRightScanAfter A lambda past
  let letter := initialRightLetterAt lambda past move
  let localTwo := initialRightNoRecvTwoOutput A strategy controllers
    (initialRightFiniteReadbackAfter A strategy controllers past) move.1
  let ordinaryMove : In₁ × In₂ := (move.2, move.1)
  let leftState := A.step scan.1
    (leftRoundRecord ordinaryMove letter.2.1.reversingOne localTwo)
  let bothState := A.step scan.1
    (bothRoundRecord ordinaryMove letter.2.1.reversingOne
      letter.2.1.informedTwo)
  ((leftState, bothState), scan.2)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem initialRightLocalCloseMacroData_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    initialRightLocalCloseMacroData A strategy controllers past move =
      initialRightCloseMacroData A
        (initialRightScanAfter A
          (initialRightLambdaOfPinnedController A strategy
            controllers.toRootCompatibleInitialControllers) past)
        (initialRightLetterAt
          (initialRightLambdaOfPinnedController A strategy
            controllers.toRootCompatibleInitialControllers) past move) := by
  unfold initialRightLocalCloseMacroData initialRightCloseMacroData
  dsimp only
  rw [initialRightNoRecvTwoOutput_eq A strategy controllers past move.1 move.2]
  rfl

/-- Every close generated by the finite pinned initial-left controller is a
reachable root of the feasible recurrent left bank. -/
noncomputable def initialLeftBankHandoff
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : RootCompatibleInitialControllers A strategy)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    BankLeftMacro A := by
  let lambda := initialLeftLambdaOfPinnedController A strategy controllers
  let scan := initialLeftScanAfter A lambda past
  let letter := initialLeftLetterAt lambda past move
  let target : FeasiblePairedState A :=
    ⟨initialLeftCloseTarget A scan letter,
      (controllers.left_sound A strategy).2 past move⟩
  exact bankLeftRoot A target (initialLeftCloseMacroData A scan letter) rfl

/-- Initial-right mirror. -/
noncomputable def initialRightBankHandoff
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : RootCompatibleInitialControllers A strategy)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    BankRightMacro A := by
  let lambda := initialRightLambdaOfPinnedController A strategy controllers
  let scan := initialRightScanAfter A lambda past
  let letter := initialRightLetterAt lambda past move
  let target : FeasiblePairedState A :=
    ⟨initialRightCloseTarget A scan letter,
      (controllers.right_sound A strategy).2 past move⟩
  exact bankRightRoot A target (initialRightCloseMacroData A scan letter) rfl

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem initialLeftBankHandoff_state
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : RootCompatibleInitialControllers A strategy)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    (initialLeftBankHandoff A strategy controllers past move).2.1 =
      initialLeftCloseMacroData A
        (initialLeftScanAfter A
          (initialLeftLambdaOfPinnedController A strategy controllers) past)
        (initialLeftLetterAt
          (initialLeftLambdaOfPinnedController A strategy controllers) past move) := rfl

@[simp] theorem initialRightBankHandoff_state
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : RootCompatibleInitialControllers A strategy)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    (initialRightBankHandoff A strategy controllers past move).2.1 =
      initialRightCloseMacroData A
        (initialRightScanAfter A
          (initialRightLambdaOfPinnedController A strategy controllers) past)
        (initialRightLetterAt
          (initialRightLambdaOfPinnedController A strategy controllers) past move) := rfl

/-- The bank handoff selected by an initial-left close is exactly the one
computed using process one's local no-receive output. -/
theorem initialLeftBankHandoff_state_local
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    (initialLeftBankHandoff A strategy
      controllers.toRootCompatibleInitialControllers past move).2.1 =
        initialLeftLocalCloseMacroData A strategy controllers past move := by
  rw [initialLeftBankHandoff_state, initialLeftLocalCloseMacroData_eq]

/-- Initial-right mirror. -/
theorem initialRightBankHandoff_state_local
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    (initialRightBankHandoff A strategy
      controllers.toRootCompatibleInitialControllers past move).2.1 =
        initialRightLocalCloseMacroData A strategy controllers past move := by
  rw [initialRightBankHandoff_state, initialRightLocalCloseMacroData_eq]

end

/-- Selected recurrent right-block controller at a bank macro. -/
noncomputable def bankRightControllerAt (source : BankRightMacro A) :=
  (feasibleControllerFamily A source.1).rightController
    source.2.1.1 source.2.1.2 source.2.2

/-- Selected recurrent left-block controller at a bank macro. -/
noncomputable def bankLeftControllerAt (source : BankLeftMacro A) :=
  (feasibleControllerFamily A source.1).leftController
    source.2.1.1 source.2.1.2 source.2.2

/-- Finite blind process-one control in a recurrent right block. -/
abbrev BankRightOwnerControl :=
  Σ source : BankRightMacro A, (bankRightControllerAt A source).Control

/-- Finite blind process-two control in a recurrent left block. -/
abbrev BankLeftOwnerControl :=
  Σ source : BankLeftMacro A, (bankLeftControllerAt A source).Control

noncomputable instance : Fintype (BankRightOwnerControl A) := by
  classical
  infer_instance

noncomputable instance : Fintype (BankLeftOwnerControl A) := by
  classical
  infer_instance

/-- Monitor selected by a recurrent right-bank source. -/
noncomputable abbrev bankRightMonitorAt (source : BankRightMacro A) :=
  RightPairedMonitor A (feasiblePolicy A source.1)
    source.2.1.1 source.2.1.2

/-- Mirror monitor. -/
noncomputable abbrev bankLeftMonitorAt (source : BankLeftMacro A) :=
  LeftPairedMonitor A (feasiblePolicy A source.1)
    source.2.1.1 source.2.1.2

/-- Finite informed process-two memory in a recurrent right block. -/
abbrev BankRightReceiverControl :=
  Σ source : BankRightMacro A,
    PairedEntryRow × (bankRightMonitorAt A source).State ×
      Option (BankLeftMacro A)

/-- Finite informed process-one memory in a recurrent left block. -/
abbrev BankLeftReceiverControl :=
  Σ source : BankLeftMacro A,
    PairedEntryRow × (bankLeftMonitorAt A source).State ×
      Option (BankRightMacro A)

noncomputable instance : Fintype (BankRightReceiverControl A) := by
  classical
  infer_instance

noncomputable instance : Fintype (BankLeftReceiverControl A) := by
  classical
  infer_instance

noncomputable def initialBankRightOwner (source : BankRightMacro A) :
    BankRightOwnerControl A :=
  ⟨source, (bankRightControllerAt A source).initial⟩

noncomputable def initialBankLeftOwner (source : BankLeftMacro A) :
    BankLeftOwnerControl A :=
  ⟨source, (bankLeftControllerAt A source).initial⟩

noncomputable def initialBankRightReceiver
    (source : BankRightMacro A) (row : PairedEntryRow) :
    BankRightReceiverControl A :=
  ⟨source, row, (bankRightMonitorAt A source).initial, none⟩

noncomputable def initialBankLeftReceiver
    (source : BankLeftMacro A) (row : PairedEntryRow) :
    BankLeftReceiverControl A :=
  ⟨source, row, (bankLeftMonitorAt A source).initial, none⟩

/-- One blind process-one output and controller update. -/
noncomputable def stepBankRightOwner
    (owner : BankRightOwnerControl A) (input : In₁) :
    Out₁ × BankRightOwnerControl A :=
  let controller := bankRightControllerAt A owner.1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

/-- Blind process-two mirror. -/
noncomputable def stepBankLeftOwner
    (owner : BankLeftOwnerControl A) (input : In₂) :
    Out₂ × BankLeftOwnerControl A :=
  let controller := bankLeftControllerAt A owner.1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

@[simp] theorem stepBankRightOwner_source
    (owner : BankRightOwnerControl A) (input : In₁) :
    (stepBankRightOwner A owner input).2.1 = owner.1 := rfl

@[simp] theorem stepBankLeftOwner_source
    (owner : BankLeftOwnerControl A) (input : In₂) :
    (stepBankLeftOwner A owner input).2.1 = owner.1 := rfl

/-- Extract the left-bank macro data from a right-block close. -/
def bankRightCloseMacro
    (source : BankRightMacro A) (scan : PairedRightScanState A)
    (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    (A.State × A.State) × A.State :=
  match pairedRightCloseTarget A scan row letter with
  | Sum.inr (Sum.inr target) => target
  | _ => source.2.1

/-- Mirror extraction. -/
def bankLeftCloseMacro
    (source : BankLeftMacro A) (scan : PairedLeftScanState A)
    (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    (A.State × A.State) × A.State :=
  match pairedLeftCloseTarget A scan row letter with
  | Sum.inr (Sum.inl target) => target
  | _ => source.2.1

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem bankRightCloseMacro_state
    (source : BankRightMacro A) (scan : PairedRightScanState A)
    (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    Sum.inr (Sum.inr (bankRightCloseMacro A source scan row letter)) =
      pairedRightCloseTarget A scan row letter := by
  cases row <;> rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem bankLeftCloseMacro_state
    (source : BankLeftMacro A) (scan : PairedLeftScanState A)
    (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    Sum.inr (Sum.inl (bankLeftCloseMacro A source scan row letter)) =
      pairedLeftCloseTarget A scan row letter := by
  cases row <;> rfl

abbrev BankRightReceiverRoundResult (source : BankRightMacro A) :=
  PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂) ×
    (bankRightMonitorAt A source).State × Option (BankLeftMacro A)

abbrev BankLeftReceiverRoundResult (source : BankLeftMacro A) :=
  PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂) ×
    (bankLeftMonitorAt A source).State × Option (BankRightMacro A)

/-- Full-information process-two computation in a recurrent right block. -/
noncomputable def stepBankRightReceiverFor
    (source : BankRightMacro A)
    (ownerControl : (bankRightControllerAt A source).Control)
    (row : PairedEntryRow)
    (monitorState : (bankRightMonitorAt A source).State)
    (move : In₂ × In₁) : BankRightReceiverRoundResult A source := by
  classical
  let controller := bankRightControllerAt A source
  let label := controller.labelOf ownerControl
  let receiverOutput := label.2 monitorState move
  let letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
    (move, receiverOutput, label.1 move.2)
  let nextMonitor := (bankRightMonitorAt A source).step monitorState letter
  let targetData := bankRightCloseMacro A source monitorState.2.1 row letter
  if hallowed : PairedRationalPolicy.Allowed A (feasiblePolicy A source.1)
      (Sum.inr (Sum.inl source.2.1)) (Sum.inr (Sum.inr targetData)) then
    exact (receiverOutput, nextMonitor,
      some (bankStageLeftOfAllowed A source targetData hallowed))
  else
    exact (receiverOutput, nextMonitor, none)

/-- Full-information process-one mirror. -/
noncomputable def stepBankLeftReceiverFor
    (source : BankLeftMacro A)
    (ownerControl : (bankLeftControllerAt A source).Control)
    (row : PairedEntryRow)
    (monitorState : (bankLeftMonitorAt A source).State)
    (move : In₁ × In₂) : BankLeftReceiverRoundResult A source := by
  classical
  let controller := bankLeftControllerAt A source
  let label := controller.labelOf ownerControl
  let receiverOutput := label.2 monitorState move
  let letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
    (move, receiverOutput, label.1 move.2)
  let nextMonitor := (bankLeftMonitorAt A source).step monitorState letter
  let targetData := bankLeftCloseMacro A source monitorState.2.1 row letter
  if hallowed : PairedRationalPolicy.Allowed A (feasiblePolicy A source.1)
      (Sum.inr (Sum.inr source.2.1)) (Sum.inr (Sum.inl targetData)) then
    exact (receiverOutput, nextMonitor,
      some (bankStageRightOfAllowed A source targetData hallowed))
  else
    exact (receiverOutput, nextMonitor, none)

theorem stepBankRightReceiverFor_staged_of_allowed
    (source : BankRightMacro A)
    (ownerControl : (bankRightControllerAt A source).Control)
    (row : PairedEntryRow)
    (monitorState : (bankRightMonitorAt A source).State)
    (move : In₂ × In₁)
    (hallowed : PairedRationalPolicy.Allowed A (feasiblePolicy A source.1)
      (Sum.inr (Sum.inl source.2.1))
      (Sum.inr (Sum.inr
        (bankRightCloseMacro A source monitorState.2.1 row
          (move,
            (bankRightControllerAt A source).labelOf ownerControl |>.2
              monitorState move,
            (bankRightControllerAt A source).labelOf ownerControl |>.1
              move.2))))) :
    (stepBankRightReceiverFor A source ownerControl row monitorState move).2.2 =
      some (bankStageLeftOfAllowed A source
        (bankRightCloseMacro A source monitorState.2.1 row
          (move,
            (bankRightControllerAt A source).labelOf ownerControl |>.2
              monitorState move,
            (bankRightControllerAt A source).labelOf ownerControl |>.1
              move.2)) hallowed) := by
  classical
  simp [stepBankRightReceiverFor, hallowed]

theorem stepBankLeftReceiverFor_staged_of_allowed
    (source : BankLeftMacro A)
    (ownerControl : (bankLeftControllerAt A source).Control)
    (row : PairedEntryRow)
    (monitorState : (bankLeftMonitorAt A source).State)
    (move : In₁ × In₂)
    (hallowed : PairedRationalPolicy.Allowed A (feasiblePolicy A source.1)
      (Sum.inr (Sum.inr source.2.1))
      (Sum.inr (Sum.inl
        (bankLeftCloseMacro A source monitorState.2.1 row
          (move,
            (bankLeftControllerAt A source).labelOf ownerControl |>.2
              monitorState move,
            (bankLeftControllerAt A source).labelOf ownerControl |>.1
              move.2))))) :
    (stepBankLeftReceiverFor A source ownerControl row monitorState move).2.2 =
      some (bankStageRightOfAllowed A source
        (bankLeftCloseMacro A source monitorState.2.1 row
          (move,
            (bankLeftControllerAt A source).labelOf ownerControl |>.2
              monitorState move,
            (bankLeftControllerAt A source).labelOf ownerControl |>.1
              move.2)) hallowed) := by
  classical
  simp [stepBankLeftReceiverFor, hallowed]

end

end DetParityAutomaton

end DistributedSynthesis
