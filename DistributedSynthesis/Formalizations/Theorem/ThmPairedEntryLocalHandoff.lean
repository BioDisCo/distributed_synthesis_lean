/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryControllerSoundness

/-!
# Finite local carriers for paired-entry transitions

A runtime state stores a finite first-entry key, a reachable finite macro
state, and the control of the selected finite block controller. The rational
policy and its lambda are functions of the key, not process observations.

`FirstEntryFinitePolicyFamilies` applies after a selected first entry.
It does not provide a controller for an arbitrarily long initial one-sided
block. The row selector `entryRowOfReceived` uses the process's preceding
receipt event; a blind process uses the shared sender component.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  {strategy : StrategyPair In₁ In₂ Out₁ Out₂}

/-- Finite key selecting which first-entry rational policy is in use. -/
inductive PairedRootKey
    (In₁ : Type u) (In₂ : Type v)
  | processOne : In₁ -> In₂ -> PairedRootKey In₁ In₂
  | processTwo : In₁ -> In₂ -> PairedRootKey In₁ In₂
deriving Fintype

namespace FirstEntryFinitePolicyFamilies

variable
  (families : FirstEntryFinitePolicyFamilies A strategy)

/-- Initial paired automaton state selected by a root key. -/
def rootInitial : PairedRootKey In₁ In₂ -> PairedEntryTreeState A
  | .processOne inputOne inputTwo =>
      (firstProcOneMemory A strategy inputOne inputTwo).toTreeState
  | .processTwo inputOne inputTwo =>
      (firstProcTwoMemory A strategy inputOne inputTwo).toTreeState

/-- Rational transition policy selected by a finite root key. -/
def rootPolicy (key : PairedRootKey In₁ In₂) :
    (pairedEntryRunAutomaton A
      (rootInitial (strategy := strategy) A key)).RationalTransitionPolicy :=
  match key with
  | .processOne inputOne inputTwo => families.processOnePolicy inputOne inputTwo
  | .processTwo inputOne inputTwo => families.processTwoPolicy inputOne inputTwo

/-- Finite controller family selected by a finite root key. -/
def rootFamily (key : PairedRootKey In₁ In₂) :
    FinitePairedPolicyFamily A (rootPolicy A families key) :=
  match key with
  | .processOne inputOne inputTwo => families.processOneFamily inputOne inputTwo
  | .processTwo inputOne inputTwo => families.processTwoFamily inputOne inputTwo

/-- The initial macro state selected by any root key is reachable. -/
theorem root_reachable (key : PairedRootKey In₁ In₂) :
    PairedRationalPolicy.Reachable A (rootPolicy A families key)
      (rootInitial (strategy := strategy) A key) := by
  cases key with
  | processOne inputOne inputTwo =>
      exact FirstEntryFinitePolicyFamilies.processOne_root_reachable
        A families inputOne inputTwo
  | processTwo inputOne inputTwo =>
      exact FirstEntryFinitePolicyFamilies.processTwo_root_reachable
        A families inputOne inputTwo

/-- Finite data of a live macro state, without its orientation tag. -/
abbrev MacroCode := (A.State × A.State) × A.State

def rightMacroState (stateData : MacroCode A) : PairedEntryTreeState A :=
  Sum.inr (Sum.inl stateData)

def leftMacroState (stateData : MacroCode A) : PairedEntryTreeState A :=
  Sum.inr (Sum.inr stateData)

/-- A reachable process-one/right-block macro state, including its finite root
key. -/
abbrev ReachableRightMacro :=
  Σ key : PairedRootKey In₁ In₂,
    {stateData : MacroCode A //
      PairedRationalPolicy.Reachable A (rootPolicy A families key)
        (rightMacroState A stateData)}

/-- Process-two/left-block mirror. -/
abbrev ReachableLeftMacro :=
  Σ key : PairedRootKey In₁ In₂,
    {stateData : MacroCode A //
      PairedRationalPolicy.Reachable A (rootPolicy A families key)
        (leftMacroState A stateData)}

noncomputable instance [Fintype In₁] [Fintype In₂] :
    Fintype (ReachableRightMacro A families) := by
  classical
  infer_instance

noncomputable instance [Fintype In₁] [Fintype In₂] :
    Fintype (ReachableLeftMacro A families) := by
  classical
  infer_instance

/-- Selected controller at a reachable right macro state. -/
def rightControllerAt (stateData : ReachableRightMacro A families) :=
  (rootFamily A families stateData.1).rightController
    stateData.2.1.1 stateData.2.1.2 stateData.2.2

/-- Selected controller at a reachable left macro state. -/
def leftControllerAt (stateData : ReachableLeftMacro A families) :=
  (rootFamily A families stateData.1).leftController
    stateData.2.1.1 stateData.2.1.2 stateData.2.2

/-- Finite sender-control carrier for every reachable process-one state. -/
abbrev RightOwnerControl :=
  Σ stateData : ReachableRightMacro A families,
    (rightControllerAt A families stateData).Control

/-- Finite sender-control carrier for every reachable process-two state. -/
abbrev LeftOwnerControl :=
  Σ stateData : ReachableLeftMacro A families,
    (leftControllerAt A families stateData).Control

noncomputable instance [Fintype In₁] [Fintype In₂] :
    Fintype (RightOwnerControl A families) := by
  classical
  infer_instance

noncomputable instance [Fintype In₁] [Fintype In₂] :
    Fintype (LeftOwnerControl A families) := by
  classical
  infer_instance

/-- The only row information used by the handoff: did this process receive at
the preceding ambiguous boundary? -/
def entryRowOfReceived : Bool -> PairedEntryRow
  | false => .first
  | true => .both

@[simp] theorem entryRowOfReceived_false :
    entryRowOfReceived false = PairedEntryRow.first := rfl

@[simp] theorem entryRowOfReceived_true :
    entryRowOfReceived true = PairedEntryRow.both := rfl

/-- Receipt bits cover exactly the two latent rows. -/
theorem exists_received_eq_entryRow (row : PairedEntryRow) :
    ∃ received : Bool, entryRowOfReceived received = row := by
  cases row
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

/-! ## Staging an allowed opposite-orientation handoff -/

/-- An allowed close from a reachable right macro state is a reachable left
macro state under the same finite root policy. -/
def stageLeftOfAllowed
    (source : ReachableRightMacro A families)
    (target : MacroCode A)
    (hallowed : PairedRationalPolicy.Allowed A
      (rootPolicy A families source.1)
      (rightMacroState A source.2.1) (leftMacroState A target)) :
    ReachableLeftMacro A families :=
  ⟨source.1, target,
    PairedRationalPolicy.reachable_of_allowed A
      (rootPolicy A families source.1) source.2.2 hallowed⟩

/-- Mirror: an allowed close from a reachable left macro state is a reachable
right macro state under the same root policy. -/
def stageRightOfAllowed
    (source : ReachableLeftMacro A families)
    (target : MacroCode A)
    (hallowed : PairedRationalPolicy.Allowed A
      (rootPolicy A families source.1)
      (leftMacroState A source.2.1) (rightMacroState A target)) :
    ReachableRightMacro A families :=
  ⟨source.1, target,
    PairedRationalPolicy.reachable_of_allowed A
      (rootPolicy A families source.1) source.2.2 hallowed⟩

@[simp]
theorem stageLeftOfAllowed_key
    (source : ReachableRightMacro A families)
    (target : MacroCode A)
    (hallowed : PairedRationalPolicy.Allowed A
      (rootPolicy A families source.1)
      (rightMacroState A source.2.1) (leftMacroState A target)) :
    (stageLeftOfAllowed A families source target hallowed).1 = source.1 := rfl

@[simp]
theorem stageLeftOfAllowed_data
    (source : ReachableRightMacro A families)
    (target : MacroCode A)
    (hallowed : PairedRationalPolicy.Allowed A
      (rootPolicy A families source.1)
      (rightMacroState A source.2.1) (leftMacroState A target)) :
    (stageLeftOfAllowed A families source target hallowed).2.1 = target := rfl

@[simp]
theorem stageRightOfAllowed_key
    (source : ReachableLeftMacro A families)
    (target : MacroCode A)
    (hallowed : PairedRationalPolicy.Allowed A
      (rootPolicy A families source.1)
      (leftMacroState A source.2.1) (rightMacroState A target)) :
    (stageRightOfAllowed A families source target hallowed).1 = source.1 := rfl

@[simp]
theorem stageRightOfAllowed_data
    (source : ReachableLeftMacro A families)
    (target : MacroCode A)
    (hallowed : PairedRationalPolicy.Allowed A
      (rootPolicy A families source.1)
      (leftMacroState A source.2.1) (rightMacroState A target)) :
    (stageRightOfAllowed A families source target hallowed).2.1 = target := rfl

/-! ## Finite per-round owner and receiver controls -/

/-- The concrete right-block monitor selected at a reachable source. -/
noncomputable abbrev rightMonitorAt
    (source : ReachableRightMacro A families) :=
  RightPairedMonitor A (rootPolicy A families source.1)
    source.2.1.1 source.2.1.2

/-- The concrete left-block monitor selected at a reachable source. -/
noncomputable abbrev leftMonitorAt
    (source : ReachableLeftMacro A families) :=
  LeftPairedMonitor A (rootPolicy A families source.1)
    source.2.1.1 source.2.1.2

/-- Receiver memory in a right block.  `staged` is the candidate left macro
computed after the latest round.  It is optional only to totalize junk states;
the real-play invariant will keep it present. -/
abbrev RightReceiverControl :=
  Σ source : ReachableRightMacro A families,
    PairedEntryRow × (rightMonitorAt A families source).State ×
      Option (ReachableLeftMacro A families)

/-- Left-block mirror. -/
abbrev LeftReceiverControl :=
  Σ source : ReachableLeftMacro A families,
    PairedEntryRow × (leftMonitorAt A families source).State ×
      Option (ReachableRightMacro A families)

noncomputable instance [Fintype In₁] [Fintype In₂] :
    Fintype (RightReceiverControl A families) := by
  classical
  infer_instance

noncomputable instance [Fintype In₁] [Fintype In₂] :
    Fintype (LeftReceiverControl A families) := by
  classical
  infer_instance

/-- Initial sender control of a right block. -/
def initialRightOwner (source : ReachableRightMacro A families) :
    RightOwnerControl A families :=
  ⟨source, (rightControllerAt A families source).initial⟩

/-- Initial sender control of a left block. -/
def initialLeftOwner (source : ReachableLeftMacro A families) :
    LeftOwnerControl A families :=
  ⟨source, (leftControllerAt A families source).initial⟩

/-- Initial receiver control of a right block. -/
noncomputable def initialRightReceiver (source : ReachableRightMacro A families)
    (row : PairedEntryRow) : RightReceiverControl A families :=
  ⟨source, row, (rightMonitorAt A families source).initial, none⟩

/-- Initial receiver control of a left block. -/
noncomputable def initialLeftReceiver (source : ReachableLeftMacro A families)
    (row : PairedEntryRow) : LeftReceiverControl A families :=
  ⟨source, row, (leftMonitorAt A families source).initial, none⟩

/-- One blind process-one action and finite-control update. -/
def stepRightOwner (owner : RightOwnerControl A families) (input : In₁) :
    Out₁ × RightOwnerControl A families :=
  let controller := rightControllerAt A families owner.1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

/-- One blind process-two action and finite-control update. -/
def stepLeftOwner (owner : LeftOwnerControl A families) (input : In₂) :
    Out₂ × LeftOwnerControl A families :=
  let controller := leftControllerAt A families owner.1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

@[simp] theorem stepRightOwner_key
    (owner : RightOwnerControl A families) (input : In₁) :
    (stepRightOwner A families owner input).2.1 = owner.1 := rfl

@[simp] theorem stepLeftOwner_key
    (owner : LeftOwnerControl A families) (input : In₂) :
    (stepLeftOwner A families owner input).2.1 = owner.1 := rfl

/-- Finite target data staged after one right-block round. -/
def rightCloseMacro
    (source : ReachableRightMacro A families)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    MacroCode A :=
  match pairedRightCloseTarget A scan row letter with
  | Sum.inr (Sum.inr target) => target
  | _ => source.2.1

/-- Finite target data staged after one left-block round. -/
def leftCloseMacro
    (source : ReachableLeftMacro A families)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    MacroCode A :=
  match pairedLeftCloseTarget A scan row letter with
  | Sum.inr (Sum.inl target) => target
  | _ => source.2.1

theorem leftMacroState_rightCloseMacro
    (source : ReachableRightMacro A families)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    leftMacroState A (rightCloseMacro A families source scan row letter) =
      pairedRightCloseTarget A scan row letter := by
  cases row <;> rfl

theorem rightMacroState_leftCloseMacro
    (source : ReachableLeftMacro A families)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    rightMacroState A (leftCloseMacro A families source scan row letter) =
      pairedLeftCloseTarget A scan row letter := by
  cases row <;> rfl

/-- Result of one receiver computation in a right block. -/
abbrev RightReceiverRoundResult (source : ReachableRightMacro A families) :=
  PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂) ×
    (rightMonitorAt A families source).State ×
      Option (ReachableLeftMacro A families)

/-- Result of one receiver computation in a left block. -/
abbrev LeftReceiverRoundResult (source : ReachableLeftMacro A families) :=
  PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂) ×
    (leftMonitorAt A families source).State ×
      Option (ReachableRightMacro A families)

/-- One full-information receiver computation in a right block.  The
receiver table returns both latent-row outputs at once.  The target is staged
iff its finite `Allowed` test succeeds. -/
noncomputable def stepRightReceiverFor
    (source : ReachableRightMacro A families)
    (ownerControl : (rightControllerAt A families source).Control)
    (row : PairedEntryRow)
    (monitorState : (rightMonitorAt A families source).State)
    (move : In₂ × In₁) : RightReceiverRoundResult A families source := by
  classical
  let controller := rightControllerAt A families source
  let label := controller.labelOf ownerControl
  let receiverOutput := label.2 monitorState move
  let letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
    (move, receiverOutput, label.1 move.2)
  let nextMonitor := (rightMonitorAt A families source).step monitorState letter
  let target := rightCloseMacro A families source monitorState.2.1 row letter
  if hallowed : PairedRationalPolicy.Allowed A
      (rootPolicy A families source.1)
      (rightMacroState A source.2.1) (leftMacroState A target) then
    exact (receiverOutput, nextMonitor,
      some (stageLeftOfAllowed A families source target hallowed))
  else
    exact (receiverOutput, nextMonitor, none)

/-- Left-block mirror. -/
noncomputable def stepLeftReceiverFor
    (source : ReachableLeftMacro A families)
    (ownerControl : (leftControllerAt A families source).Control)
    (row : PairedEntryRow)
    (monitorState : (leftMonitorAt A families source).State)
    (move : In₁ × In₂) : LeftReceiverRoundResult A families source := by
  classical
  let controller := leftControllerAt A families source
  let label := controller.labelOf ownerControl
  let receiverOutput := label.2 monitorState move
  let letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
    (move, receiverOutput, label.1 move.2)
  let nextMonitor := (leftMonitorAt A families source).step monitorState letter
  let target := leftCloseMacro A families source monitorState.2.1 row letter
  if hallowed : PairedRationalPolicy.Allowed A
      (rootPolicy A families source.1)
      (leftMacroState A source.2.1) (rightMacroState A target) then
    exact (receiverOutput, nextMonitor,
      some (stageRightOfAllowed A families source target hallowed))
  else
    exact (receiverOutput, nextMonitor, none)

/-- Under the exact close-safety premise, the right receiver stages the
opposite macro rather than taking the junk branch. -/
theorem stepRightReceiverFor_staged_of_allowed
    (source : ReachableRightMacro A families)
    (ownerControl : (rightControllerAt A families source).Control)
    (row : PairedEntryRow)
    (monitorState : (rightMonitorAt A families source).State)
    (move : In₂ × In₁)
    (hallowed : PairedRationalPolicy.Allowed A
      (rootPolicy A families source.1)
      (rightMacroState A source.2.1)
      (leftMacroState A
        (rightCloseMacro A families source monitorState.2.1 row
          (move,
            (rightControllerAt A families source).labelOf ownerControl |>.2
              monitorState move,
            (rightControllerAt A families source).labelOf ownerControl |>.1
              move.2)))) :
    (stepRightReceiverFor A families source ownerControl row monitorState move).2.2 =
      some (stageLeftOfAllowed A families source
        (rightCloseMacro A families source monitorState.2.1 row
          (move,
            (rightControllerAt A families source).labelOf ownerControl |>.2
              monitorState move,
            (rightControllerAt A families source).labelOf ownerControl |>.1
              move.2)) hallowed) := by
  classical
  simp [stepRightReceiverFor, hallowed]

/-- Left-block mirror of `stepRightReceiverFor_staged_of_allowed`. -/
theorem stepLeftReceiverFor_staged_of_allowed
    (source : ReachableLeftMacro A families)
    (ownerControl : (leftControllerAt A families source).Control)
    (row : PairedEntryRow)
    (monitorState : (leftMonitorAt A families source).State)
    (move : In₁ × In₂)
    (hallowed : PairedRationalPolicy.Allowed A
      (rootPolicy A families source.1)
      (leftMacroState A source.2.1)
      (rightMacroState A
        (leftCloseMacro A families source monitorState.2.1 row
          (move,
            (leftControllerAt A families source).labelOf ownerControl |>.2
              monitorState move,
            (leftControllerAt A families source).labelOf ownerControl |>.1
              move.2)))) :
    (stepLeftReceiverFor A families source ownerControl row monitorState move).2.2 =
      some (stageRightOfAllowed A families source
        (leftCloseMacro A families source monitorState.2.1 row
          (move,
            (leftControllerAt A families source).labelOf ownerControl |>.2
              monitorState move,
            (leftControllerAt A families source).labelOf ownerControl |>.1
              move.2)) hallowed) := by
  classical
  simp [stepLeftReceiverFor, hallowed]

end FirstEntryFinitePolicyFamilies

end DetParityAutomaton

end DistributedSynthesis
