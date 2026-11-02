/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointInitialLeftGuardedFirstController
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointInitialRightGuardedFirstController

/-!
# Finite bank of raw-joint exceptional initial controllers

The guarded initial monitor emits one finite key.  For every such key this
file chooses, once and for all, the root-pinned activation, its exceptional
controller, and the controller's winning certificate.  The resulting bank is
indexed only by the finite guarded key; choosing a controller at run time does
not require a graph, an orientation signal, or knowledge of the strict leader.

We also expose the finite owner and receiver controls and the executable
interior transitions.  Their equations identify the generated label and the
next monitor state directly.  The closing handoff is deliberately left to the
separate exceptional-to-ordinary seam: this module carries no speculative
leader bit in its state.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## One selected controller at each guarded key -/

/-- The complete selected exceptional right controller at one initial-left
key.  The activation and package are retained because they determine the
finite target alphabet of the controller. -/
structure ProfiledRawJointInitialLeftControllerAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) where
  activation : ProfiledRawJointInitialLeftRootPinnedActivation A strategy key
  package : ProfiledRawJointInitialLeftGuardedFirstControllerPackage A
    strategy key activation
  controller :
    TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
      (NarrowedBlockLabel In₂ In₁
        (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy
          activation.source
          (ProfiledRawJointInitialLeftRootPredicate A strategy key)
          activation.pinned) Out₁
        (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
            max u v x y s} A strategy
          activation.source
          (ProfiledRawJointInitialLeftRootPredicate A strategy key)
          activation.pinned package.source).State)
  wins : NarrowedAllThreadsWin
    (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy
      activation.source
      (ProfiledRawJointInitialLeftRootPredicate A strategy key)
      activation.pinned package.source) controller.labeledTree

/-- Mirror selected exceptional left controller at one initial-right key. -/
structure ProfiledRawJointInitialRightControllerAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) where
  activation : ProfiledRawJointInitialRightRootPinnedActivation A strategy key
  package : ProfiledRawJointInitialRightGuardedFirstControllerPackage A
    strategy key activation
  controller :
    TransitionRationalTree.{v, max u v x y s, max u v x y s} In₂
      (NarrowedBlockLabel In₁ In₂
        (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy
          activation.source
          (ProfiledRawJointInitialRightRootPredicate A strategy key)
          activation.pinned) Out₂
        (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
            max u v x y s} A strategy
          activation.source
          (ProfiledRawJointInitialRightRootPredicate A strategy key)
          activation.pinned package.source).State)
  wins : NarrowedAllThreadsWin
    (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy
      activation.source
      (ProfiledRawJointInitialRightRootPredicate A strategy key)
      activation.pinned package.source) controller.labeledTree

/-- Select the exceptional right controller at a fixed initial-left key. -/
noncomputable def profiledRawJointInitialLeftControllerAtOfWinning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) :
    ProfiledRawJointInitialLeftControllerAt A strategy key := by
  let selected :=
    profiledRawJointInitialLeftGuardedFirstControllerOfWinning A strategy hwin
      key
  let controller := Classical.choose selected.2.existsController
  exact {
    activation := selected.1
    package := selected.2
    controller := controller
    wins := Classical.choose_spec selected.2.existsController }

/-- Select the mirror exceptional left controller at a fixed key. -/
noncomputable def profiledRawJointInitialRightControllerAtOfWinning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) :
    ProfiledRawJointInitialRightControllerAt A strategy key := by
  let selected :=
    profiledRawJointInitialRightGuardedFirstControllerOfWinning A strategy hwin
      key
  let controller := Classical.choose selected.2.existsController
  exact {
    activation := selected.1
    package := selected.2
    controller := controller
    wins := Classical.choose_spec selected.2.existsController }

/-! ## The finite key-indexed bank -/

/-- Both exceptional orientations selected simultaneously.  The orientation
is in the static sum of local control types, not supplied as an observable
run-time argument. -/
structure ProfiledRawJointInitialControllerBank
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) where
  initialLeft : ∀ key : ProfiledRawJointInitialLeftGuardedKey A strategy,
    ProfiledRawJointInitialLeftControllerAt A strategy key
  initialRight : ∀ key : ProfiledRawJointInitialRightGuardedKey A strategy,
    ProfiledRawJointInitialRightControllerAt A strategy key

/-- Assemble the complete exceptional bank from the original winner. -/
noncomputable def profiledRawJointInitialControllerBankOfWinning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    ProfiledRawJointInitialControllerBank A strategy where
  initialLeft := profiledRawJointInitialLeftControllerAtOfWinning A strategy
    hwin
  initialRight := profiledRawJointInitialRightControllerAtOfWinning A strategy
    hwin

/-! ## Finite local controls -/

/-- Process one owns the exceptional right controller following an
initial-left key. -/
abbrev ProfiledRawJointInitialLeftOwnerControl
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy) :=
  Σ key : ProfiledRawJointInitialLeftGuardedKey A strategy,
    (bank.initialLeft key).controller.Control

/-- Process two owns the mirror exceptional left controller. -/
abbrev ProfiledRawJointInitialRightOwnerControl
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy) :=
  Σ key : ProfiledRawJointInitialRightGuardedKey A strategy,
    (bank.initialRight key).controller.Control

/-- The receiver of an exceptional right block stores only its key, closing
row, and finite monitor state. -/
abbrev ProfiledRawJointInitialLeftReceiverControl
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy) :=
  Σ key : ProfiledRawJointInitialLeftGuardedKey A strategy,
    PairedEntryRow ×
      (profiledRawJointGuardedFirstRightBlockMonitor A strategy
        (bank.initialLeft key).activation.source
        (ProfiledRawJointInitialLeftRootPredicate A strategy key)
        (bank.initialLeft key).activation.pinned
        (bank.initialLeft key).package.source).State

/-- Mirror receiver control. -/
abbrev ProfiledRawJointInitialRightReceiverControl
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy) :=
  Σ key : ProfiledRawJointInitialRightGuardedKey A strategy,
    PairedEntryRow ×
      (profiledRawJointGuardedFirstLeftBlockMonitor A strategy
        (bank.initialRight key).activation.source
        (ProfiledRawJointInitialRightRootPredicate A strategy key)
        (bank.initialRight key).activation.pinned
        (bank.initialRight key).package.source).State

noncomputable instance profiledRawJointInitialLeftOwnerControlFintype
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy) :
    Fintype (ProfiledRawJointInitialLeftOwnerControl A strategy bank) := by
  classical
  infer_instance

noncomputable instance profiledRawJointInitialRightOwnerControlFintype
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy) :
    Fintype (ProfiledRawJointInitialRightOwnerControl A strategy bank) := by
  classical
  infer_instance

noncomputable instance profiledRawJointInitialLeftReceiverControlFintype
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy) :
    Fintype (ProfiledRawJointInitialLeftReceiverControl A strategy bank) := by
  classical
  infer_instance

noncomputable instance profiledRawJointInitialRightReceiverControlFintype
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy) :
    Fintype (ProfiledRawJointInitialRightReceiverControl A strategy bank) := by
  classical
  infer_instance

/-! ## Initialization and executable owner steps -/

noncomputable def initialProfiledRawJointInitialLeftOwner
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) :
    ProfiledRawJointInitialLeftOwnerControl A strategy bank :=
  ⟨key, (bank.initialLeft key).controller.initial⟩

noncomputable def initialProfiledRawJointInitialRightOwner
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) :
    ProfiledRawJointInitialRightOwnerControl A strategy bank :=
  ⟨key, (bank.initialRight key).controller.initial⟩

noncomputable def initialProfiledRawJointInitialLeftReceiver
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy)
    (row : PairedEntryRow) :
    ProfiledRawJointInitialLeftReceiverControl A strategy bank :=
  ⟨key, row,
    (profiledRawJointGuardedFirstRightBlockMonitor A strategy
      (bank.initialLeft key).activation.source
      (ProfiledRawJointInitialLeftRootPredicate A strategy key)
      (bank.initialLeft key).activation.pinned
      (bank.initialLeft key).package.source).initial⟩

noncomputable def initialProfiledRawJointInitialRightReceiver
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy)
    (row : PairedEntryRow) :
    ProfiledRawJointInitialRightReceiverControl A strategy bank :=
  ⟨key, row,
    (profiledRawJointGuardedFirstLeftBlockMonitor A strategy
      (bank.initialRight key).activation.source
      (ProfiledRawJointInitialRightRootPredicate A strategy key)
      (bank.initialRight key).activation.pinned
      (bank.initialRight key).package.source).initial⟩

noncomputable def stepProfiledRawJointInitialLeftOwner
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (owner : ProfiledRawJointInitialLeftOwnerControl A strategy bank)
    (input : In₁) :
    Out₁ × ProfiledRawJointInitialLeftOwnerControl A strategy bank :=
  let controller := (bank.initialLeft owner.1).controller
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

noncomputable def stepProfiledRawJointInitialRightOwner
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (owner : ProfiledRawJointInitialRightOwnerControl A strategy bank)
    (input : In₂) :
    Out₂ × ProfiledRawJointInitialRightOwnerControl A strategy bank :=
  let controller := (bank.initialRight owner.1).controller
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem stepProfiledRawJointInitialLeftOwner_key
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (owner : ProfiledRawJointInitialLeftOwnerControl A strategy bank)
    (input : In₁) :
    (stepProfiledRawJointInitialLeftOwner A strategy bank owner input).2.1 =
      owner.1 := rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem stepProfiledRawJointInitialRightOwner_key
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (owner : ProfiledRawJointInitialRightOwnerControl A strategy bank)
    (input : In₂) :
    (stepProfiledRawJointInitialRightOwner A strategy bank owner input).2.1 =
      owner.1 := rfl

/-! ## Executable receiver scan and readback equations -/

abbrev ProfiledRawJointInitialLeftReceiverRoundResultAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) :=
  ProfiledRawJointGuardedFirstRightReceiverOutput A strategy
      (bank.initialLeft key).activation.source
      (ProfiledRawJointInitialLeftRootPredicate A strategy key)
      (bank.initialLeft key).activation.pinned ×
    (profiledRawJointGuardedFirstRightBlockMonitor A strategy
      (bank.initialLeft key).activation.source
      (ProfiledRawJointInitialLeftRootPredicate A strategy key)
      (bank.initialLeft key).activation.pinned
      (bank.initialLeft key).package.source).State

abbrev ProfiledRawJointInitialRightReceiverRoundResultAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) :=
  ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy
      (bank.initialRight key).activation.source
      (ProfiledRawJointInitialRightRootPredicate A strategy key)
      (bank.initialRight key).activation.pinned ×
    (profiledRawJointGuardedFirstLeftBlockMonitor A strategy
      (bank.initialRight key).activation.source
      (ProfiledRawJointInitialRightRootPredicate A strategy key)
      (bank.initialRight key).activation.pinned
      (bank.initialRight key).package.source).State

noncomputable def stepProfiledRawJointInitialLeftReceiverFor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy)
    (ownerControl : (bank.initialLeft key).controller.Control)
    (monitorState :
      (profiledRawJointGuardedFirstRightBlockMonitor A strategy
        (bank.initialLeft key).activation.source
        (ProfiledRawJointInitialLeftRootPredicate A strategy key)
        (bank.initialLeft key).activation.pinned
        (bank.initialLeft key).package.source).State)
    (move : In₂ × In₁) :
    ProfiledRawJointInitialLeftReceiverRoundResultAt A strategy bank key :=
  let monitor := profiledRawJointGuardedFirstRightBlockMonitor A strategy
    (bank.initialLeft key).activation.source
    (ProfiledRawJointInitialLeftRootPredicate A strategy key)
    (bank.initialLeft key).activation.pinned
    (bank.initialLeft key).package.source
  let controller := (bank.initialLeft key).controller
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  (output, monitor.step monitorState (move, output, label.1 move.2))

noncomputable def stepProfiledRawJointInitialRightReceiverFor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy)
    (ownerControl : (bank.initialRight key).controller.Control)
    (monitorState :
      (profiledRawJointGuardedFirstLeftBlockMonitor A strategy
        (bank.initialRight key).activation.source
        (ProfiledRawJointInitialRightRootPredicate A strategy key)
        (bank.initialRight key).activation.pinned
        (bank.initialRight key).package.source).State)
    (move : In₁ × In₂) :
    ProfiledRawJointInitialRightReceiverRoundResultAt A strategy bank key :=
  let monitor := profiledRawJointGuardedFirstLeftBlockMonitor A strategy
    (bank.initialRight key).activation.source
    (ProfiledRawJointInitialRightRootPredicate A strategy key)
    (bank.initialRight key).activation.pinned
    (bank.initialRight key).package.source
  let controller := (bank.initialRight key).controller
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  (output, monitor.step monitorState (move, output, label.1 move.2))

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem stepProfiledRawJointInitialLeftReceiverFor_output
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy)
    (ownerControl : (bank.initialLeft key).controller.Control)
    (monitorState :
      (profiledRawJointGuardedFirstRightBlockMonitor A strategy
        (bank.initialLeft key).activation.source
        (ProfiledRawJointInitialLeftRootPredicate A strategy key)
        (bank.initialLeft key).activation.pinned
        (bank.initialLeft key).package.source).State)
    (move : In₂ × In₁) :
    (stepProfiledRawJointInitialLeftReceiverFor A strategy bank key
      ownerControl monitorState move).1 =
      ((bank.initialLeft key).controller.labelOf ownerControl).2 monitorState
        move := rfl

@[simp] theorem stepProfiledRawJointInitialRightReceiverFor_output
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy)
    (ownerControl : (bank.initialRight key).controller.Control)
    (monitorState :
      (profiledRawJointGuardedFirstLeftBlockMonitor A strategy
        (bank.initialRight key).activation.source
        (ProfiledRawJointInitialRightRootPredicate A strategy key)
        (bank.initialRight key).activation.pinned
        (bank.initialRight key).package.source).State)
    (move : In₁ × In₂) :
    (stepProfiledRawJointInitialRightReceiverFor A strategy bank key
      ownerControl monitorState move).1 =
      ((bank.initialRight key).controller.labelOf ownerControl).2 monitorState
        move := rfl

@[simp] theorem stepProfiledRawJointInitialLeftReceiverFor_state
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy)
    (ownerControl : (bank.initialLeft key).controller.Control)
    (monitorState :
      (profiledRawJointGuardedFirstRightBlockMonitor A strategy
        (bank.initialLeft key).activation.source
        (ProfiledRawJointInitialLeftRootPredicate A strategy key)
        (bank.initialLeft key).activation.pinned
        (bank.initialLeft key).package.source).State)
    (move : In₂ × In₁) :
    (stepProfiledRawJointInitialLeftReceiverFor A strategy bank key
      ownerControl monitorState move).2 =
      (profiledRawJointGuardedFirstRightBlockMonitor A strategy
        (bank.initialLeft key).activation.source
        (ProfiledRawJointInitialLeftRootPredicate A strategy key)
        (bank.initialLeft key).activation.pinned
        (bank.initialLeft key).package.source).step monitorState
          (move,
            ((bank.initialLeft key).controller.labelOf ownerControl).2
              monitorState move,
            ((bank.initialLeft key).controller.labelOf ownerControl).1
              move.2) := rfl

@[simp] theorem stepProfiledRawJointInitialRightReceiverFor_state
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy)
    (ownerControl : (bank.initialRight key).controller.Control)
    (monitorState :
      (profiledRawJointGuardedFirstLeftBlockMonitor A strategy
        (bank.initialRight key).activation.source
        (ProfiledRawJointInitialRightRootPredicate A strategy key)
        (bank.initialRight key).activation.pinned
        (bank.initialRight key).package.source).State)
    (move : In₁ × In₂) :
    (stepProfiledRawJointInitialRightReceiverFor A strategy bank key
      ownerControl monitorState move).2 =
      (profiledRawJointGuardedFirstLeftBlockMonitor A strategy
        (bank.initialRight key).activation.source
        (ProfiledRawJointInitialRightRootPredicate A strategy key)
        (bank.initialRight key).activation.pinned
        (bank.initialRight key).package.source).step monitorState
          (move,
            ((bank.initialRight key).controller.labelOf ownerControl).2
              monitorState move,
            ((bank.initialRight key).controller.labelOf ownerControl).1
              move.2) := rfl

end

/-! ## Whole-prefix finite-state readback -/

/-- The synchronized proof state of one exceptional right block.  Its two
components are precisely the local owner control and local receiver monitor
control stored above. -/
abbrev ProfiledRawJointInitialLeftFiniteState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) :=
  (bank.initialLeft key).controller.Control ×
    (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
      max u v x y s} A strategy
      (bank.initialLeft key).activation.source
      (ProfiledRawJointInitialLeftRootPredicate A strategy key)
      (bank.initialLeft key).activation.pinned
      (bank.initialLeft key).package.source).State

/-- Mirror synchronized proof state. -/
abbrev ProfiledRawJointInitialRightFiniteState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) :=
  (bank.initialRight key).controller.Control ×
    (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
      max u v x y s} A strategy
      (bank.initialRight key).activation.source
      (ProfiledRawJointInitialRightRootPredicate A strategy key)
      (bank.initialRight key).activation.pinned
      (bank.initialRight key).package.source).State

noncomputable def stepProfiledRawJointInitialLeftFiniteState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy)
    (state : ProfiledRawJointInitialLeftFiniteState A strategy bank key)
    (move : In₂ × In₁) :
    ProfiledRawJointInitialLeftFiniteState A strategy bank key :=
  let controller := (bank.initialLeft key).controller
  let monitor := profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y,
    s, max u v x y s} A strategy
    (bank.initialLeft key).activation.source
    (ProfiledRawJointInitialLeftRootPredicate A strategy key)
    (bank.initialLeft key).activation.pinned
    (bank.initialLeft key).package.source
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def stepProfiledRawJointInitialRightFiniteState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy)
    (state : ProfiledRawJointInitialRightFiniteState A strategy bank key)
    (move : In₁ × In₂) :
    ProfiledRawJointInitialRightFiniteState A strategy bank key :=
  let controller := (bank.initialRight key).controller
  let monitor := profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y,
    s, max u v x y s} A strategy
    (bank.initialRight key).activation.source
    (ProfiledRawJointInitialRightRootPredicate A strategy key)
    (bank.initialRight key).activation.pinned
    (bank.initialRight key).package.source
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def profiledRawJointInitialLeftFiniteStateAfter
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy)
    (past : List (In₂ × In₁)) :
    ProfiledRawJointInitialLeftFiniteState A strategy bank key :=
  past.foldl (stepProfiledRawJointInitialLeftFiniteState A strategy bank key)
    ((bank.initialLeft key).controller.initial,
      (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy
        (bank.initialLeft key).activation.source
        (ProfiledRawJointInitialLeftRootPredicate A strategy key)
        (bank.initialLeft key).activation.pinned
        (bank.initialLeft key).package.source).initial)

noncomputable def profiledRawJointInitialRightFiniteStateAfter
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy)
    (past : List (In₁ × In₂)) :
    ProfiledRawJointInitialRightFiniteState A strategy bank key :=
  past.foldl (stepProfiledRawJointInitialRightFiniteState A strategy bank key)
    ((bank.initialRight key).controller.initial,
      (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy
        (bank.initialRight key).activation.source
        (ProfiledRawJointInitialRightRootPredicate A strategy key)
        (bank.initialRight key).activation.pinned
        (bank.initialRight key).package.source).initial)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Executing the finite local transitions on a right-block prefix is exactly
the controller control and narrowed monitor readback at that prefix. -/
theorem profiledRawJointInitialLeftFiniteStateAfter_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) :
    ∀ past : List (In₂ × In₁),
      profiledRawJointInitialLeftFiniteStateAfter A strategy bank key past =
        ((bank.initialLeft key).controller.controlAt (senderWord past),
          narrowedControl
            (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
              max u v x y s} A strategy
              (bank.initialLeft key).activation.source
              (ProfiledRawJointInitialLeftRootPredicate A strategy key)
              (bank.initialLeft key).activation.pinned
              (bank.initialLeft key).package.source)
            (bank.initialLeft key).controller.labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [profiledRawJointInitialLeftFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepProfiledRawJointInitialLeftFiniteState A strategy bank key
        (profiledRawJointInitialLeftFiniteStateAfter A strategy bank key past)
          move = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirror whole-prefix readback. -/
theorem profiledRawJointInitialRightFiniteStateAfter_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) :
    ∀ past : List (In₁ × In₂),
      profiledRawJointInitialRightFiniteStateAfter A strategy bank key past =
        ((bank.initialRight key).controller.controlAt (senderWord past),
          narrowedControl
            (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
              max u v x y s} A strategy
              (bank.initialRight key).activation.source
              (ProfiledRawJointInitialRightRootPredicate A strategy key)
              (bank.initialRight key).activation.pinned
              (bank.initialRight key).package.source)
            (bank.initialRight key).controller.labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [profiledRawJointInitialRightFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepProfiledRawJointInitialRightFiniteState A strategy bank key
        (profiledRawJointInitialRightFiniteStateAfter A strategy bank key past)
          move = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

end

end DetParityAutomaton

end DistributedSynthesis
