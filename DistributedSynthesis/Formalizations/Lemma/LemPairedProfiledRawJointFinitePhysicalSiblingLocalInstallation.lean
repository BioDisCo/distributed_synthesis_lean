/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingLocalFront
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialFiniteSiblingMove

/-!
# Local installation and delivery of finite physical sibling moves

The full input pair needed to choose an initial physical sibling move is
available on the correct side.  For a right/common--strict-left sibling,
process one is the `left`/`both` receiver and therefore installs the right
move from its own and delivered current inputs.  Process two is the strict
nonreceiver and retains its old finite shadow.  The left orientation is the
literal mirror.

This file also supplies the finite front receiver controls.  Once an owner
control is honestly delivered, the receiver advances the same narrowed
table and stores the emitted finite target.  These are the front-right and
front-left fields needed before handing a checked target to the recurrent
target-indexed kernel.

No executable function below accepts `Graph`, an orientation, a leader bit,
or an `EnvironmentRound`.  A receive takes the own and delivered input; a
non-receive takes only the own input.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

/-! ## The common locally known prefix -/

/-- The literal history after the first simultaneous round.  Both processes
know the full first input pair at this point. -/
def profiledRawJointHybridInitialSiblingBase
    (first : In₁ × In₂) : History In₁ In₂ Graph Out₁ Out₂ :=
  ((ProfiledRawJointHybridInitialRootPinnedWorld A strategy first).procOne A
    ).bothHistory

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The two descriptions of the first simultaneous prefix coincide. -/
theorem profiledRawJointHybridInitialSiblingBase_eq_procTwo
    (first : In₁ × In₂) :
    profiledRawJointHybridInitialSiblingBase A strategy first =
      ((ProfiledRawJointHybridInitialRootPinnedWorld A strategy first).procTwo
        A).bothHistory :=
  rfl

/-! ## Finite installation provenance -/

/-- The two finite input pairs from which an initial sibling table was
selected.  Keeping this index in the runtime control is essential: the
physical move itself need not determine the semantic family and direction
whose checked target is installed at close. -/
structure ProfiledRawJointHybridInitialSiblingInstallation where
  first : In₁ × In₂
  current : In₁ × In₂

noncomputable instance :
    Fintype (ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂)) := by
  classical
  let Rep := (In₁ × In₂) × (In₁ × In₂)
  let equiv :
      ProfiledRawJointHybridInitialSiblingInstallation
          (In₁ := In₁) (In₂ := In₂) ≃ Rep := {
    toFun := fun installation ↦ (installation.first, installation.current)
    invFun := fun data ↦ ⟨data.1, data.2⟩
    left_inv := by intro installation; cases installation; rfl
    right_inv := by intro data; cases data; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- The right physical move definitionally selected by one installation. -/
noncomputable def profiledRawJointHybridInitialRightMoveAt
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointRightPhysicalSiblingMove A :=
  profiledRawJointHybridInitialRightPhysicalSiblingMove A strategy hwin
    installation.first installation.current

/-- The left physical move definitionally selected by one installation. -/
noncomputable def profiledRawJointHybridInitialLeftMoveAt
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointLeftPhysicalSiblingMove A :=
  profiledRawJointHybridInitialLeftPhysicalSiblingMove A strategy hwin
    installation.first installation.current

/-- Process one's installed front-right owner, indexed by the exact finite
origin of its table. -/
noncomputable abbrev ProfiledRawJointHybridInitialRightOwnerAt
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂)) :=
  ((profiledRawJointHybridInitialRightMoveAt A strategy hwin installation
    ).memberController A false).Control

/-- Process two's installed front-left owner, with the mirror provenance. -/
noncomputable abbrev ProfiledRawJointHybridInitialLeftOwnerAt
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂)) :=
  ((profiledRawJointHybridInitialLeftMoveAt A strategy hwin installation
    ).memberController A false).Control

noncomputable abbrev ProfiledRawJointHybridInitialRightInstalledOwner :=
  Sigma (ProfiledRawJointHybridInitialRightOwnerAt A strategy hwin)

noncomputable abbrev ProfiledRawJointHybridInitialLeftInstalledOwner :=
  Sigma (ProfiledRawJointHybridInitialLeftOwnerAt A strategy hwin)

noncomputable instance :
    Fintype (ProfiledRawJointHybridInitialRightInstalledOwner A strategy
      hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointHybridInitialLeftInstalledOwner A strategy
      hwin) := by
  classical
  infer_instance

/-- Forget only the provenance, retaining the same literal right move and
owner control expected by the generic exceptional front. -/
noncomputable def profiledRawJointHybridInitialRightInstalledOwnerExceptional
    (installed : ProfiledRawJointHybridInitialRightInstalledOwner A strategy
      hwin) : ProfiledRawJointRightPhysicalSiblingExceptional A :=
  ⟨profiledRawJointHybridInitialRightMoveAt A strategy hwin installed.1,
    installed.2⟩

/-- Left mirror of provenance erasure. -/
noncomputable def profiledRawJointHybridInitialLeftInstalledOwnerExceptional
    (installed : ProfiledRawJointHybridInitialLeftInstalledOwner A strategy
      hwin) : ProfiledRawJointLeftPhysicalSiblingExceptional A :=
  ⟨profiledRawJointHybridInitialLeftMoveAt A strategy hwin installed.1,
    installed.2⟩

/-! ## Finite front-right receiver -/

/-- Process two's finite state while receiving a front-right sibling block.
The latest emitted target is retained for the checked close handoff. -/
noncomputable abbrev ProfiledRawJointRightPhysicalSiblingReceiver :=
  Sigma fun move : ProfiledRawJointRightPhysicalSiblingMove A ↦
    PairedEntryRow ×
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State ×
      Option (ProfiledRawJointUnitTarget A)

noncomputable instance :
    Fintype (ProfiledRawJointRightPhysicalSiblingReceiver A) := by
  classical
  infer_instance

/-- Start the receiver of an installed front-right move. -/
noncomputable def initialProfiledRawJointRightPhysicalSiblingReceiver
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (row : PairedEntryRow) :
    ProfiledRawJointRightPhysicalSiblingReceiver A :=
  ⟨move, row,
    (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).initial,
    none⟩

/-- Advance the exact front-right receiver from a delivered owner control.
The signature is the honest receive signature: delivered finite control and
the two current inputs. -/
noncomputable def stepProfiledRawJointRightPhysicalSiblingReceiverFor
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (state : (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State)
    (input : In₂ × In₁) :
    Out₂ × ProfiledRawJointRightPhysicalSiblingReceiver A :=
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  let label := controller.labelOf owner
  let output := label.2 state input
  let nextState := monitor.step state (input, output, label.1 input.2)
  (pairedRightInformedForRow row output.physical,
    ⟨move, row, nextState, some (output.target row)⟩)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem stepProfiledRawJointRightPhysicalSiblingReceiverFor_move
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (state : (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State)
    (input : In₂ × In₁) :
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A move owner row
      state input).2.1 = move :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem stepProfiledRawJointRightPhysicalSiblingReceiverFor_target
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (state : (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State)
    (input : In₂ × In₁) :
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A move owner row
      state input).2.2.2.2 =
      some (((move.memberController A false).labelOf owner).2 state input
        |>.target row) :=
  rfl

/-! ### Provenance-indexed initial right receiver -/

/-- Receiver state below one exact initial installation.  The target remains
an `Option` because the total local machine also has an unstepped initial
state; reachable close handoff uses the `some` branch together with the
all-thread target-safety theorem. -/
noncomputable abbrev ProfiledRawJointHybridInitialRightReceiverAt
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂)) :=
  PairedEntryRow ×
    (profiledRawJointRightPhysicalSiblingMonitor A
      (profiledRawJointHybridInitialRightMoveAt A strategy hwin
        installation).1 false).State ×
    Option (ProfiledRawJointUnitTarget A)

noncomputable abbrev ProfiledRawJointHybridInitialRightInstalledReceiver :=
  Sigma (ProfiledRawJointHybridInitialRightReceiverAt A strategy hwin)

noncomputable instance :
    Fintype (ProfiledRawJointHybridInitialRightInstalledReceiver A strategy
      hwin) := by
  classical
  infer_instance

noncomputable def initialProfiledRawJointHybridInitialRightInstalledReceiver
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂)) (row : PairedEntryRow) :
    ProfiledRawJointHybridInitialRightInstalledReceiver A strategy hwin :=
  let move := profiledRawJointHybridInitialRightMoveAt A strategy hwin
    installation
  ⟨installation, row,
    (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).initial,
    none⟩

/-- Advance a provenance-indexed front-right receiver.  Both output and
target are computed from the same delivered owner table. -/
noncomputable def stepProfiledRawJointHybridInitialRightReceiverAt
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂))
    (owner : ProfiledRawJointHybridInitialRightOwnerAt A strategy hwin
      installation)
    (state : ProfiledRawJointHybridInitialRightReceiverAt A strategy hwin
      installation)
    (input : In₂ × In₁) :
    Out₂ × ProfiledRawJointHybridInitialRightReceiverAt A strategy hwin
      installation :=
  let move := profiledRawJointHybridInitialRightMoveAt A strategy hwin
    installation
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  let label := controller.labelOf owner
  let output := label.2 state.2.1 input
  let nextState := monitor.step state.2.1
    (input, output, label.1 input.2)
  (pairedRightInformedForRow state.1 output.physical,
    (state.1, nextState, some (output.target state.1)))

@[simp] theorem stepProfiledRawJointHybridInitialRightReceiverAt_row
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂))
    (owner : ProfiledRawJointHybridInitialRightOwnerAt A strategy hwin
      installation)
    (state : ProfiledRawJointHybridInitialRightReceiverAt A strategy hwin
      installation)
    (input : In₂ × In₁) :
    (stepProfiledRawJointHybridInitialRightReceiverAt A strategy hwin
      installation owner state input).2.1 = state.1 :=
  rfl

@[simp] theorem stepProfiledRawJointHybridInitialRightReceiverAt_target
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂))
    (owner : ProfiledRawJointHybridInitialRightOwnerAt A strategy hwin
      installation)
    (state : ProfiledRawJointHybridInitialRightReceiverAt A strategy hwin
      installation)
    (input : In₂ × In₁) :
    (stepProfiledRawJointHybridInitialRightReceiverAt A strategy hwin
      installation owner state input).2.2.2 =
      some (((((profiledRawJointHybridInitialRightMoveAt A strategy hwin
        installation).memberController A false).labelOf owner).2 state.2.1
          input).target state.1) :=
  rfl

/-! ## Finite front-left receiver -/

noncomputable abbrev ProfiledRawJointLeftPhysicalSiblingReceiver :=
  Sigma fun move : ProfiledRawJointLeftPhysicalSiblingMove A ↦
    PairedEntryRow ×
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State ×
      Option (ProfiledRawJointUnitTarget A)

noncomputable instance :
    Fintype (ProfiledRawJointLeftPhysicalSiblingReceiver A) := by
  classical
  infer_instance

noncomputable def initialProfiledRawJointLeftPhysicalSiblingReceiver
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (row : PairedEntryRow) :
    ProfiledRawJointLeftPhysicalSiblingReceiver A :=
  ⟨move, row,
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).initial,
    none⟩

noncomputable def stepProfiledRawJointLeftPhysicalSiblingReceiverFor
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (state : (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State)
    (input : In₁ × In₂) :
    Out₁ × ProfiledRawJointLeftPhysicalSiblingReceiver A :=
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  let label := controller.labelOf owner
  let output := label.2 state input
  let nextState := monitor.step state (input, output, label.1 input.2)
  (pairedLeftInformedForRow row output.physical,
    ⟨move, row, nextState, some (output.target row)⟩)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem stepProfiledRawJointLeftPhysicalSiblingReceiverFor_move
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (state : (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State)
    (input : In₁ × In₂) :
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A move owner row state
      input).2.1 = move :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem stepProfiledRawJointLeftPhysicalSiblingReceiverFor_target
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (state : (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State)
    (input : In₁ × In₂) :
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A move owner row state
      input).2.2.2.2 =
      some (((move.memberController A false).labelOf owner).2 state input
        |>.target row) :=
  rfl

/-! ### Provenance-indexed initial left receiver -/

noncomputable abbrev ProfiledRawJointHybridInitialLeftReceiverAt
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂)) :=
  PairedEntryRow ×
    (profiledRawJointLeftPhysicalSiblingMonitor A
      (profiledRawJointHybridInitialLeftMoveAt A strategy hwin
        installation).1 false).State ×
    Option (ProfiledRawJointUnitTarget A)

noncomputable abbrev ProfiledRawJointHybridInitialLeftInstalledReceiver :=
  Sigma (ProfiledRawJointHybridInitialLeftReceiverAt A strategy hwin)

noncomputable instance :
    Fintype (ProfiledRawJointHybridInitialLeftInstalledReceiver A strategy
      hwin) := by
  classical
  infer_instance

noncomputable def initialProfiledRawJointHybridInitialLeftInstalledReceiver
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂)) (row : PairedEntryRow) :
    ProfiledRawJointHybridInitialLeftInstalledReceiver A strategy hwin :=
  let move := profiledRawJointHybridInitialLeftMoveAt A strategy hwin
    installation
  ⟨installation, row,
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).initial,
    none⟩

noncomputable def stepProfiledRawJointHybridInitialLeftReceiverAt
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂))
    (owner : ProfiledRawJointHybridInitialLeftOwnerAt A strategy hwin
      installation)
    (state : ProfiledRawJointHybridInitialLeftReceiverAt A strategy hwin
      installation)
    (input : In₁ × In₂) :
    Out₁ × ProfiledRawJointHybridInitialLeftReceiverAt A strategy hwin
      installation :=
  let move := profiledRawJointHybridInitialLeftMoveAt A strategy hwin
    installation
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  let label := controller.labelOf owner
  let output := label.2 state.2.1 input
  let nextState := monitor.step state.2.1
    (input, output, label.1 input.2)
  (pairedLeftInformedForRow state.1 output.physical,
    (state.1, nextState, some (output.target state.1)))

@[simp] theorem stepProfiledRawJointHybridInitialLeftReceiverAt_row
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂))
    (owner : ProfiledRawJointHybridInitialLeftOwnerAt A strategy hwin
      installation)
    (state : ProfiledRawJointHybridInitialLeftReceiverAt A strategy hwin
      installation)
    (input : In₁ × In₂) :
    (stepProfiledRawJointHybridInitialLeftReceiverAt A strategy hwin
      installation owner state input).2.1 = state.1 :=
  rfl

@[simp] theorem stepProfiledRawJointHybridInitialLeftReceiverAt_target
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂))
    (owner : ProfiledRawJointHybridInitialLeftOwnerAt A strategy hwin
      installation)
    (state : ProfiledRawJointHybridInitialLeftReceiverAt A strategy hwin
      installation)
    (input : In₁ × In₂) :
    (stepProfiledRawJointHybridInitialLeftReceiverAt A strategy hwin
      installation owner state input).2.2.2 =
      some (((((profiledRawJointHybridInitialLeftMoveAt A strategy hwin
        installation).memberController A false).labelOf owner).2 state.2.1
          input).target state.1) :=
  rfl

/-! ## Initial receive installation versus strict non-receive -/

/-- The process-one receive installs the exact front-right move using the
full current pair that it genuinely observes. -/
noncomputable def profiledRawJointHybridInitialRightRecvInstallOne
    (first : In₁ × In₂) (own : In₁) (delivered : In₂) :
    Out₁ × ProfiledRawJointHybridInitialRightInstalledOwner A strategy hwin :=
  let current := (own, delivered)
  let installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂) := ⟨first, current⟩
  let move := profiledRawJointHybridInitialRightMoveAt A strategy hwin
    installation
  let output := (nextRound strategy
    (profiledRawJointHybridInitialSiblingBase A strategy first)
    ⟨own, delivered, Graph.left⟩).outputOne
  (output, ⟨installation, (move.memberController A false).initial⟩)

@[simp] theorem profiledRawJointHybridInitialRightRecvInstallOne_first
    (first : In₁ × In₂) (own : In₁) (delivered : In₂) :
    (profiledRawJointHybridInitialRightRecvInstallOne A strategy hwin first own
      delivered).2.1.first = first :=
  rfl

@[simp] theorem profiledRawJointHybridInitialRightRecvInstallOne_current
    (first : In₁ × In₂) (own : In₁) (delivered : In₂) :
    (profiledRawJointHybridInitialRightRecvInstallOne A strategy hwin first own
      delivered).2.1.current = (own, delivered) :=
  rfl

/-- On the same strict-left round process two receives no partner data.  It
emits the strategy's blind output from its own input and retains the old
finite first-round shadow unchanged. -/
noncomputable def profiledRawJointHybridInitialRightNoRecvRetainTwo
    (first : In₁ × In₂) (own : In₂) : Out₂ × (In₁ × In₂) :=
  (blockSenderTwo strategy
    (profiledRawJointHybridInitialSiblingBase A strategy first) [] own,
    first)

/-- The local receive/non-receive pair is the literal strict-left strategy
round. -/
theorem profiledRawJointHybridInitialRightInstall_pair
    (first current : In₁ × In₂) :
    ((profiledRawJointHybridInitialRightRecvInstallOne A strategy hwin first
        current.1 current.2).1,
      (profiledRawJointHybridInitialRightNoRecvRetainTwo A strategy first
        current.2).1) =
      let round := nextRound strategy
        (profiledRawJointHybridInitialSiblingBase A strategy first)
        ⟨current.1, current.2, Graph.left⟩
      (round.outputOne, round.outputTwo) := by
  dsimp only [profiledRawJointHybridInitialRightRecvInstallOne,
    profiledRawJointHybridInitialRightNoRecvRetainTwo]
  congr 1

/-- Mirror: process two receives and installs the exact front-left move. -/
noncomputable def profiledRawJointHybridInitialLeftRecvInstallTwo
    (first : In₁ × In₂) (own : In₂) (delivered : In₁) :
    Out₂ × ProfiledRawJointHybridInitialLeftInstalledOwner A strategy hwin :=
  let current := (delivered, own)
  let installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂) := ⟨first, current⟩
  let move := profiledRawJointHybridInitialLeftMoveAt A strategy hwin
    installation
  let output := (nextRound strategy
    (profiledRawJointHybridInitialSiblingBase A strategy first)
    ⟨delivered, own, Graph.right⟩).outputTwo
  (output, ⟨installation, (move.memberController A false).initial⟩)

@[simp] theorem profiledRawJointHybridInitialLeftRecvInstallTwo_first
    (first : In₁ × In₂) (own : In₂) (delivered : In₁) :
    (profiledRawJointHybridInitialLeftRecvInstallTwo A strategy hwin first own
      delivered).2.1.first = first :=
  rfl

@[simp] theorem profiledRawJointHybridInitialLeftRecvInstallTwo_current
    (first : In₁ × In₂) (own : In₂) (delivered : In₁) :
    (profiledRawJointHybridInitialLeftRecvInstallTwo A strategy hwin first own
      delivered).2.1.current = (delivered, own) :=
  rfl

/-- Process one is the strict-right nonreceiver and retains the old shadow. -/
noncomputable def profiledRawJointHybridInitialLeftNoRecvRetainOne
    (first : In₁ × In₂) (own : In₁) : Out₁ × (In₁ × In₂) :=
  (blockSenderOne strategy
    (profiledRawJointHybridInitialSiblingBase A strategy first) [] own,
    first)

theorem profiledRawJointHybridInitialLeftInstall_pair
    (first current : In₁ × In₂) :
    ((profiledRawJointHybridInitialLeftNoRecvRetainOne A strategy first
        current.1).1,
      (profiledRawJointHybridInitialLeftRecvInstallTwo A strategy hwin first
        current.2 current.1).1) =
      let round := nextRound strategy
        (profiledRawJointHybridInitialSiblingBase A strategy first)
        ⟨current.1, current.2, Graph.right⟩
      (round.outputOne, round.outputTwo) := by
  dsimp only [profiledRawJointHybridInitialLeftNoRecvRetainOne,
    profiledRawJointHybridInitialLeftRecvInstallTwo]
  congr 1

end

end DetParityAutomaton

end DistributedSynthesis
