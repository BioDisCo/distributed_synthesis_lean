/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndFirstLocalHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledPolicyLocalHandoff

/-!
# The package-wide finite recurrent bank

After the exceptional first block, a recurrent macro remembers the finite
initial boundary key and the admitted guarded child.  Its last component is
the live macro of the child's one fixed ordinary policy.  The two possible
initial orientations are finite summands; no process is given a strict-leader
bit.  Reversal changes only the live orientation and preserves the origin and
child definitionally.
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

/-! ## Macros retaining their finite origin -/

/-- A recurrent right macro descended from an initial-left boundary. -/
abbrev EndToEndRightOriginRecurrentRightMacro :=
  Σ key : EndToEndInitialLeftBoundaryKey A package,
    EndToEndGuardedRightRecurrentRightMacro A
      (rightGuarded :=
        (endToEndInitialLeftBoundaryActivation A package key).policy)

/-- Its left-oriented mirror, with the same boundary key and guarded child. -/
abbrev EndToEndRightOriginRecurrentLeftMacro :=
  Σ key : EndToEndInitialLeftBoundaryKey A package,
    EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded :=
        (endToEndInitialLeftBoundaryActivation A package key).policy)

/-- A recurrent right macro descended from an initial-right boundary. -/
abbrev EndToEndLeftOriginRecurrentRightMacro :=
  Σ key : EndToEndInitialRightBoundaryKey A package,
    EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded :=
        (endToEndInitialRightBoundaryActivation A package key).policy)

/-- Its left-oriented mirror, with the same boundary key and guarded child. -/
abbrev EndToEndLeftOriginRecurrentLeftMacro :=
  Σ key : EndToEndInitialRightBoundaryKey A package,
    EndToEndGuardedLeftRecurrentLeftMacro A
      (leftGuarded :=
        (endToEndInitialRightBoundaryActivation A package key).policy)

/-- All recurrent right macros of the package. -/
abbrev EndToEndRecurrentRightMacro :=
  EndToEndRightOriginRecurrentRightMacro A package ⊕
    EndToEndLeftOriginRecurrentRightMacro A package

/-- All recurrent left macros of the package. -/
abbrev EndToEndRecurrentLeftMacro :=
  EndToEndRightOriginRecurrentLeftMacro A package ⊕
    EndToEndLeftOriginRecurrentLeftMacro A package

noncomputable instance :
    Fintype (EndToEndRightOriginRecurrentRightMacro A package) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndRightOriginRecurrentLeftMacro A package) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndLeftOriginRecurrentRightMacro A package) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndLeftOriginRecurrentLeftMacro A package) := by
  classical
  infer_instance

noncomputable instance : Fintype (EndToEndRecurrentRightMacro A package) := by
  classical
  infer_instance

noncomputable instance : Fintype (EndToEndRecurrentLeftMacro A package) := by
  classical
  infer_instance

/-! ## First-block embeddings -/

def endToEndRecurrentLeftOfFirstRight
    (key : EndToEndInitialLeftBoundaryKey A package)
    (target : EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded :=
        (endToEndInitialLeftBoundaryActivation A package key).policy)) :
    EndToEndRecurrentLeftMacro A package :=
  .inl ⟨key, target⟩

def endToEndRecurrentRightOfFirstLeft
    (key : EndToEndInitialRightBoundaryKey A package)
    (target : EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded :=
        (endToEndInitialRightBoundaryActivation A package key).policy)) :
    EndToEndRecurrentRightMacro A package :=
  .inr ⟨key, target⟩

/-! ## Origin-specific finite local controls -/

abbrev EndToEndRightOriginRecurrentRightOwnerControl :=
  Σ source : EndToEndRightOriginRecurrentRightMacro A package,
    (endToEndGuardedRightRecurrentRightController A source.2).Control

abbrev EndToEndRightOriginRecurrentLeftOwnerControl :=
  Σ source : EndToEndRightOriginRecurrentLeftMacro A package,
    (endToEndGuardedRightRecurrentLeftController A source.2).Control

abbrev EndToEndLeftOriginRecurrentRightOwnerControl :=
  Σ source : EndToEndLeftOriginRecurrentRightMacro A package,
    (endToEndGuardedLeftRecurrentRightController A source.2).Control

abbrev EndToEndLeftOriginRecurrentLeftOwnerControl :=
  Σ source : EndToEndLeftOriginRecurrentLeftMacro A package,
    (endToEndGuardedLeftRecurrentLeftController A source.2).Control

abbrev EndToEndRightOriginRecurrentRightReceiverControl :=
  Σ source : EndToEndRightOriginRecurrentRightMacro A package,
    PairedEntryRow ×
      (endToEndGuardedRightRecurrentRightMonitor A source.2).State ×
        Option (EndToEndRightOriginRecurrentLeftMacro A package)

abbrev EndToEndRightOriginRecurrentLeftReceiverControl :=
  Σ source : EndToEndRightOriginRecurrentLeftMacro A package,
    PairedEntryRow ×
      (endToEndGuardedRightRecurrentLeftMonitor A source.2).State ×
        Option (EndToEndRightOriginRecurrentRightMacro A package)

abbrev EndToEndLeftOriginRecurrentRightReceiverControl :=
  Σ source : EndToEndLeftOriginRecurrentRightMacro A package,
    PairedEntryRow ×
      (endToEndGuardedLeftRecurrentRightMonitor A source.2).State ×
        Option (EndToEndLeftOriginRecurrentLeftMacro A package)

abbrev EndToEndLeftOriginRecurrentLeftReceiverControl :=
  Σ source : EndToEndLeftOriginRecurrentLeftMacro A package,
    PairedEntryRow ×
      (endToEndGuardedLeftRecurrentLeftMonitor A source.2).State ×
        Option (EndToEndLeftOriginRecurrentRightMacro A package)

/-! ## Package-wide recurrent local controls -/

abbrev EndToEndRecurrentRightOwnerControl :=
  EndToEndRightOriginRecurrentRightOwnerControl A package ⊕
    EndToEndLeftOriginRecurrentRightOwnerControl A package

abbrev EndToEndRecurrentLeftOwnerControl :=
  EndToEndRightOriginRecurrentLeftOwnerControl A package ⊕
    EndToEndLeftOriginRecurrentLeftOwnerControl A package

abbrev EndToEndRecurrentRightReceiverControl :=
  EndToEndRightOriginRecurrentRightReceiverControl A package ⊕
    EndToEndLeftOriginRecurrentRightReceiverControl A package

abbrev EndToEndRecurrentLeftReceiverControl :=
  EndToEndRightOriginRecurrentLeftReceiverControl A package ⊕
    EndToEndLeftOriginRecurrentLeftReceiverControl A package

noncomputable instance :
    Fintype (EndToEndRightOriginRecurrentRightOwnerControl A package) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndRightOriginRecurrentLeftOwnerControl A package) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndLeftOriginRecurrentRightOwnerControl A package) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndLeftOriginRecurrentLeftOwnerControl A package) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndRightOriginRecurrentRightReceiverControl A package) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndRightOriginRecurrentLeftReceiverControl A package) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndLeftOriginRecurrentRightReceiverControl A package) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndLeftOriginRecurrentLeftReceiverControl A package) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndRecurrentRightOwnerControl A package) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndRecurrentLeftOwnerControl A package) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndRecurrentRightReceiverControl A package) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndRecurrentLeftReceiverControl A package) := by
  classical
  infer_instance

end

end DetParityAutomaton

end DistributedSynthesis
