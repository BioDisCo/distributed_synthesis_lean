/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndMatchedPhase

/-!
# Independent finite local carriers for the one-policy phase machine

The matched phase is a correctness relation, not shared memory.  This file
forgets it to the two actual local finite carriers.  Their summands record
only which local controller/monitor is currently active.  In particular,
there is no bit saying which process is the strict information leader.
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

/-- Process one's actual post-initial finite local memory. -/
abbrev EndToEndPhaseOneControl :=
  EndToEndGuardedFirstRightOwnerControl A package ⊕
    EndToEndGuardedFirstLeftReceiverControl.{u, v, x, y, s, 1} A package ⊕
    EndToEndRightOriginRecurrentRightOwnerControl A package ⊕
    EndToEndRightOriginRecurrentLeftReceiverControl A package ⊕
    EndToEndLeftOriginRecurrentRightOwnerControl A package ⊕
    EndToEndLeftOriginRecurrentLeftReceiverControl A package

/-- Process two's actual post-initial finite local memory. -/
abbrev EndToEndPhaseTwoControl :=
  EndToEndGuardedFirstRightReceiverControl.{u, v, x, y, s, 1} A package ⊕
    EndToEndGuardedFirstLeftOwnerControl A package ⊕
    EndToEndRightOriginRecurrentRightReceiverControl A package ⊕
    EndToEndRightOriginRecurrentLeftOwnerControl A package ⊕
    EndToEndLeftOriginRecurrentRightReceiverControl A package ⊕
    EndToEndLeftOriginRecurrentLeftOwnerControl A package

noncomputable instance : Fintype (EndToEndPhaseOneControl A package) := by
  classical
  infer_instance

noncomputable instance : Fintype (EndToEndPhaseTwoControl A package) := by
  classical
  infer_instance

/-- Forget the proof relation to process one's local state. -/
def EndToEndMatchedPhase.oneControl :
    EndToEndMatchedPhase A package → EndToEndPhaseOneControl A package
  | .firstRight owner _ _ => .inl owner
  | .firstLeft receiver _ _ => .inr (.inl receiver)
  | .rightOriginRight owner _ _ => .inr (.inr (.inl owner))
  | .rightOriginLeft receiver _ _ => .inr (.inr (.inr (.inl receiver)))
  | .leftOriginRight owner _ _ => .inr (.inr (.inr (.inr (.inl owner))))
  | .leftOriginLeft receiver _ _ =>
      .inr (.inr (.inr (.inr (.inr receiver))))

/-- Forget the proof relation to process two's local state. -/
def EndToEndMatchedPhase.twoControl :
    EndToEndMatchedPhase A package → EndToEndPhaseTwoControl A package
  | .firstRight _ receiver _ => .inl receiver
  | .firstLeft _ owner _ => .inr (.inl owner)
  | .rightOriginRight _ receiver _ => .inr (.inr (.inl receiver))
  | .rightOriginLeft _ owner _ => .inr (.inr (.inr (.inl owner)))
  | .leftOriginRight _ receiver _ =>
      .inr (.inr (.inr (.inr (.inl receiver))))
  | .leftOriginLeft _ owner _ => .inr (.inr (.inr (.inr (.inr owner))))

end


end DetParityAutomaton

end DistributedSynthesis
