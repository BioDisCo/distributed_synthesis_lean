/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndGuardedFirstHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRecurrentHandoff

/-!
# Finite controller bank for all one-policy boundary activations

An initial streaming controller may stage only finitely many combinations of
scan state, physical letter, and common-policy source state.  We use that
finite triple as the runtime bank key.  The direction witnessing membership
in the global policy image and the derived guarded policy are chosen only in
the definition of the controller indexed by that key; neither occurs in a
local control value.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-! ## Initial-left boundary, followed by a guarded first-right block -/

/-- The complete finite data visible at an admissible initial-left boundary. -/
abbrev EndToEndInitialLeftBoundaryKey :=
  {data : InitialBlockScan A ×
      InitialLeftLetter
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) ×
      PairedInitialProfiledBankState A //
    endToEndInitialLeftSourceOK A package data.1 data.2.1 data.2.2}

noncomputable instance : Fintype (EndToEndInitialLeftBoundaryKey A package) := by
  classical
  infer_instance

noncomputable def endToEndInitialLeftBoundaryActivation
    (key : EndToEndInitialLeftBoundaryKey A package) :
    EndToEndInitialLeftActivation A package key.1.1 key.1.2.1 key.1.2.2 :=
  Classical.choice
    (nonempty_endToEndInitialLeftActivation_of_sourceOK A package key.1.1
      key.1.2.1 key.1.2.2 key.2)

/-- Finite live shape forced by the checked delayed target. -/
structure EndToEndInitialLeftBoundaryShape
    (key : EndToEndInitialLeftBoundaryKey A package) where
  code : A.State × A.State
  minimum : A.State
  profile : RightInitialActionProfile
    (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)
  source_eq : key.1.2.2.2 = .inr (.inl ((code, minimum), profile))

noncomputable def endToEndInitialLeftBoundaryShape
    (key : EndToEndInitialLeftBoundaryKey A package) :
    EndToEndInitialLeftBoundaryShape A package key :=
  Classical.choice (by
  let activation := endToEndInitialLeftBoundaryActivation A package key
  obtain ⟨code, minimum, profile, hshape⟩ :=
    exists_right_profiled_shape_of_initialLeftDelayedTarget A key.1.1 key.1.2.1
      key.1.2.2.2 activation.target
  exact ⟨⟨code, minimum, profile, hshape⟩⟩)

noncomputable def endToEndInitialLeftBoundaryController
    (key : EndToEndInitialLeftBoundaryKey A package) :=
  let activation := endToEndInitialLeftBoundaryActivation A package key
  let shape := endToEndInitialLeftBoundaryShape A package key
  Classical.choose (exists_finite_endToEndGuardedFirstRightController A
    key.1.2.2.2 activation.profile activation.policy shape.code shape.minimum
      shape.profile shape.source_eq)

theorem endToEndInitialLeftBoundaryController_wins
    (key : EndToEndInitialLeftBoundaryKey A package) :
    let activation := endToEndInitialLeftBoundaryActivation A package key
    let shape := endToEndInitialLeftBoundaryShape A package key
    NarrowedAllThreadsWin
      (endToEndGuardedFirstRightBlockMonitor A key.1.2.2.2
        activation.profile activation.policy shape.code shape.minimum
          shape.profile)
      (endToEndInitialLeftBoundaryController A package key).labeledTree := by
  dsimp only
  exact Classical.choose_spec
    (exists_finite_endToEndGuardedFirstRightController A key.1.2.2.2
      (endToEndInitialLeftBoundaryActivation A package key).profile
      (endToEndInitialLeftBoundaryActivation A package key).policy
      (endToEndInitialLeftBoundaryShape A package key).code
      (endToEndInitialLeftBoundaryShape A package key).minimum
      (endToEndInitialLeftBoundaryShape A package key).profile
      (endToEndInitialLeftBoundaryShape A package key).source_eq)

/-- Runtime owner controls contain only a finite boundary key and a finite
controller state. -/
abbrev EndToEndGuardedFirstRightOwnerControl :=
  Σ key : EndToEndInitialLeftBoundaryKey A package,
    (endToEndInitialLeftBoundaryController A package key).Control

noncomputable instance :
    Fintype (EndToEndGuardedFirstRightOwnerControl A package) := by
  classical
  infer_instance

/-- Receiver controls stage only a finite admitted child.  The policy and
image direction occur in the key-indexed definitions, not in the value. -/
abbrev EndToEndGuardedFirstRightReceiverControl :=
  Σ key : EndToEndInitialLeftBoundaryKey A package,
    PairedEntryRow ×
      (endToEndGuardedFirstRightBlockMonitor A key.1.2.2.2
        (endToEndInitialLeftBoundaryActivation A package key).profile
        (endToEndInitialLeftBoundaryActivation A package key).policy
        (endToEndInitialLeftBoundaryShape A package key).code
        (endToEndInitialLeftBoundaryShape A package key).minimum
        (endToEndInitialLeftBoundaryShape A package key).profile).State ×
      Option (EndToEndGuardedRightRecurrentLeftMacro A
        (rightGuarded :=
          (endToEndInitialLeftBoundaryActivation A package key).policy))

noncomputable instance :
    Fintype (EndToEndGuardedFirstRightReceiverControl A package) := by
  classical
  infer_instance

/-! ## Initial-right boundary, followed by a guarded first-left block -/

abbrev EndToEndInitialRightBoundaryKey :=
  {data : InitialBlockScan A ×
      InitialRightLetter
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) ×
      PairedInitialProfiledBankState A //
    endToEndInitialRightSourceOK A package data.1 data.2.1 data.2.2}

noncomputable instance : Fintype (EndToEndInitialRightBoundaryKey A package) := by
  classical
  infer_instance

noncomputable def endToEndInitialRightBoundaryActivation
    (key : EndToEndInitialRightBoundaryKey A package) :
    EndToEndInitialRightActivation A package key.1.1 key.1.2.1 key.1.2.2 :=
  Classical.choice
    (nonempty_endToEndInitialRightActivation_of_sourceOK A package key.1.1
      key.1.2.1 key.1.2.2 key.2)

structure EndToEndInitialRightBoundaryShape
    (key : EndToEndInitialRightBoundaryKey A package) where
  code : A.State × A.State
  minimum : A.State
  profile : LeftInitialActionProfile
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
  source_eq : key.1.2.2.2 = .inr (.inr ((code, minimum), profile))

noncomputable def endToEndInitialRightBoundaryShape
    (key : EndToEndInitialRightBoundaryKey A package) :
    EndToEndInitialRightBoundaryShape A package key :=
  Classical.choice (by
  let activation := endToEndInitialRightBoundaryActivation A package key
  obtain ⟨code, minimum, profile, hshape⟩ :=
    exists_left_profiled_shape_of_initialRightDelayedTarget A key.1.1 key.1.2.1
      key.1.2.2.2 activation.target
  exact ⟨⟨code, minimum, profile, hshape⟩⟩)

noncomputable def endToEndInitialRightBoundaryController
    (key : EndToEndInitialRightBoundaryKey A package) :=
  let activation := endToEndInitialRightBoundaryActivation A package key
  let shape := endToEndInitialRightBoundaryShape A package key
  Classical.choose (exists_finite_endToEndGuardedFirstLeftController A
    key.1.2.2.2 activation.profile activation.policy shape.code shape.minimum
      shape.profile shape.source_eq)

theorem endToEndInitialRightBoundaryController_wins
    (key : EndToEndInitialRightBoundaryKey A package) :
    let activation := endToEndInitialRightBoundaryActivation A package key
    let shape := endToEndInitialRightBoundaryShape A package key
    NarrowedAllThreadsWin
      (endToEndGuardedFirstLeftBlockMonitor A key.1.2.2.2
        activation.profile activation.policy shape.code shape.minimum
          shape.profile)
      (endToEndInitialRightBoundaryController A package key).labeledTree := by
  dsimp only
  exact Classical.choose_spec
    (exists_finite_endToEndGuardedFirstLeftController A key.1.2.2.2
      (endToEndInitialRightBoundaryActivation A package key).profile
      (endToEndInitialRightBoundaryActivation A package key).policy
      (endToEndInitialRightBoundaryShape A package key).code
      (endToEndInitialRightBoundaryShape A package key).minimum
      (endToEndInitialRightBoundaryShape A package key).profile
      (endToEndInitialRightBoundaryShape A package key).source_eq)

abbrev EndToEndGuardedFirstLeftOwnerControl :=
  Σ key : EndToEndInitialRightBoundaryKey A package,
    (endToEndInitialRightBoundaryController A package key).Control

noncomputable instance :
    Fintype (EndToEndGuardedFirstLeftOwnerControl A package) := by
  classical
  infer_instance

abbrev EndToEndGuardedFirstLeftReceiverControl :=
  Σ key : EndToEndInitialRightBoundaryKey A package,
    PairedEntryRow ×
      (endToEndGuardedFirstLeftBlockMonitor A key.1.2.2.2
        (endToEndInitialRightBoundaryActivation A package key).profile
        (endToEndInitialRightBoundaryActivation A package key).policy
        (endToEndInitialRightBoundaryShape A package key).code
        (endToEndInitialRightBoundaryShape A package key).minimum
        (endToEndInitialRightBoundaryShape A package key).profile).State ×
      Option (EndToEndGuardedLeftRecurrentRightMacro A
        (leftGuarded :=
          (endToEndInitialRightBoundaryActivation A package key).policy))

noncomputable instance :
    Fintype (EndToEndGuardedFirstLeftReceiverControl A package) := by
  classical
  infer_instance

end


end DetParityAutomaton

end DistributedSynthesis
