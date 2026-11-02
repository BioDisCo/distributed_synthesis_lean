/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRecurrentReversal

/-!
# The matched phase invariant for the one-policy package

The six constructors are proof-level synchronized configurations: two
exceptional first-block orientations and four recurrent combinations of
origin and orientation.  They relate independent finite local controls; they
are not a shared run-time phase and give neither process a strict-leader bit.

Closure below covers every interior round and every strict reversal.  In the
recurrent cases the boundary origin and guarded child are retained by type,
so closure also proves that no later phase can select a new policy.
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

/-- The proof-level synchronized phases of the package controller. -/
inductive EndToEndMatchedPhase where
  | firstRight
      (owner : EndToEndGuardedFirstRightOwnerControl A package)
      (receiver : EndToEndGuardedFirstRightReceiverControl.{u, v, x, y, s, 1}
        A package)
      (sameSource : owner.1 = receiver.1)
  | firstLeft
      (receiver : EndToEndGuardedFirstLeftReceiverControl.{u, v, x, y, s, 1}
        A package)
      (owner : EndToEndGuardedFirstLeftOwnerControl A package)
      (sameSource : receiver.1 = owner.1)
  | rightOriginRight
      (owner : EndToEndRightOriginRecurrentRightOwnerControl A package)
      (receiver : EndToEndRightOriginRecurrentRightReceiverControl A package)
      (sameSource : owner.1 = receiver.1)
  | rightOriginLeft
      (receiver : EndToEndRightOriginRecurrentLeftReceiverControl A package)
      (owner : EndToEndRightOriginRecurrentLeftOwnerControl A package)
      (sameSource : receiver.1 = owner.1)
  | leftOriginRight
      (owner : EndToEndLeftOriginRecurrentRightOwnerControl A package)
      (receiver : EndToEndLeftOriginRecurrentRightReceiverControl A package)
      (sameSource : owner.1 = receiver.1)
  | leftOriginLeft
      (receiver : EndToEndLeftOriginRecurrentLeftReceiverControl A package)
      (owner : EndToEndLeftOriginRecurrentLeftOwnerControl A package)
      (sameSource : receiver.1 = owner.1)

/-! ## Interior closure -/

noncomputable def EndToEndMatchedPhase.continue
    (phase : EndToEndMatchedPhase A package) (move : In₁ × In₂) :
    (Out₁ × Out₂) × EndToEndMatchedPhase A package :=
  match phase with
  | .firstRight owner receiver sameSource =>
      let one := stepEndToEndGuardedFirstRightOwner A package owner move.1
      let two := continueEndToEndGuardedFirstRightReceiver A package receiver
        owner (move.2, move.1)
      ((one.1, two.1), .firstRight one.2 two.2 (by
        rw [stepEndToEndGuardedFirstRightOwner_key,
          continueEndToEndGuardedFirstRightReceiver_key]
        exact sameSource))
  | .firstLeft receiver owner sameSource =>
      let one := continueEndToEndGuardedFirstLeftReceiver A package receiver
        owner move
      let two := stepEndToEndGuardedFirstLeftOwner A package owner move.2
      ((one.1, two.1), .firstLeft one.2 two.2 (by
        rw [continueEndToEndGuardedFirstLeftReceiver_key,
          stepEndToEndGuardedFirstLeftOwner_key]
        exact sameSource))
  | .rightOriginRight owner receiver sameSource =>
      let one := stepEndToEndRightOriginRecurrentRightOwner A package owner
        move.1
      let two := continueEndToEndRightOriginRecurrentRightReceiver A package
        receiver owner (move.2, move.1)
      ((one.1, two.1), .rightOriginRight one.2 two.2 (by
        rw [stepEndToEndRightOriginRecurrentRightOwner_source,
          continueEndToEndRightOriginRecurrentRightReceiver_source]
        exact sameSource))
  | .rightOriginLeft receiver owner sameSource =>
      let one := continueEndToEndRightOriginRecurrentLeftReceiver A package
        receiver owner move
      let two := stepEndToEndRightOriginRecurrentLeftOwner A package owner
        move.2
      ((one.1, two.1), .rightOriginLeft one.2 two.2 (by
        rw [continueEndToEndRightOriginRecurrentLeftReceiver_source,
          stepEndToEndRightOriginRecurrentLeftOwner_source]
        exact sameSource))
  | .leftOriginRight owner receiver sameSource =>
      let one := stepEndToEndLeftOriginRecurrentRightOwner A package owner
        move.1
      let two := continueEndToEndLeftOriginRecurrentRightReceiver A package
        receiver owner (move.2, move.1)
      ((one.1, two.1), .leftOriginRight one.2 two.2 (by
        rw [stepEndToEndLeftOriginRecurrentRightOwner_source,
          continueEndToEndLeftOriginRecurrentRightReceiver_source]
        exact sameSource))
  | .leftOriginLeft receiver owner sameSource =>
      let one := continueEndToEndLeftOriginRecurrentLeftReceiver A package
        receiver owner move
      let two := stepEndToEndLeftOriginRecurrentLeftOwner A package owner
        move.2
      ((one.1, two.1), .leftOriginLeft one.2 two.2 (by
        rw [continueEndToEndLeftOriginRecurrentLeftReceiver_source,
          stepEndToEndLeftOriginRecurrentLeftOwner_source]
        exact sameSource))

/-! ## Strict-reversal closure -/

noncomputable def EndToEndMatchedPhase.reverseRightToLeft
    (phase : EndToEndMatchedPhase A package) (move : In₁ × In₂)
    (previouslyReceived : Bool) :
    (Out₁ × Out₂) × Option (EndToEndMatchedPhase A package) :=
  match phase with
  | .firstRight owner receiver _ =>
      let one := switchEndToEndFirstRightOwnerToRecurrentLeftReceiver A package
        owner receiver move previouslyReceived
      let two := switchEndToEndFirstRightReceiverToRecurrentLeftOwner A package
        receiver move.2
      let next :=
        match hOne : one.2, hTwo : two.2 with
        | some nextReceiver, some nextOwner =>
            some (.rightOriginLeft nextReceiver nextOwner
              (switchEndToEndFirstRight_common_source A package owner receiver
                move previouslyReceived nextReceiver nextOwner hOne hTwo))
        | _, _ => none
      ((one.1, two.1), next)
  | .rightOriginRight owner receiver _ =>
      let one := switchEndToEndRightOriginRightOwnerToLeftReceiver A package
        owner receiver move previouslyReceived
      let two := switchEndToEndRightOriginRightReceiverToLeftOwner A package
        receiver move.2
      let next :=
        match hOne : one.2, hTwo : two.2 with
        | some nextReceiver, some nextOwner =>
            some (.rightOriginLeft nextReceiver nextOwner
              (switchEndToEndRightOriginRight_common_source A package owner
                receiver move previouslyReceived nextReceiver nextOwner hOne
                hTwo))
        | _, _ => none
      ((one.1, two.1), next)
  | .leftOriginRight owner receiver _ =>
      let one := switchEndToEndLeftOriginRightOwnerToLeftReceiver A package
        owner receiver move previouslyReceived
      let two := switchEndToEndLeftOriginRightReceiverToLeftOwner A package
        receiver move.2
      let next :=
        match hOne : one.2, hTwo : two.2 with
        | some nextReceiver, some nextOwner =>
            some (.leftOriginLeft nextReceiver nextOwner
              (switchEndToEndLeftOriginRight_common_source A package owner
                receiver move previouslyReceived nextReceiver nextOwner hOne
                hTwo))
        | _, _ => none
      ((one.1, two.1), next)
  | .firstLeft _ _ _ => ((default, default), none)
  | .rightOriginLeft _ _ _ => ((default, default), none)
  | .leftOriginLeft _ _ _ => ((default, default), none)

noncomputable def EndToEndMatchedPhase.reverseLeftToRight
    (phase : EndToEndMatchedPhase A package) (move : In₂ × In₁)
    (previouslyReceived : Bool) :
    (Out₁ × Out₂) × Option (EndToEndMatchedPhase A package) :=
  match phase with
  | .firstLeft receiver owner _ =>
      let one := switchEndToEndFirstLeftReceiverToRecurrentRightOwner A package
        receiver move.2
      let two := switchEndToEndFirstLeftOwnerToRecurrentRightReceiver A package
        owner receiver move previouslyReceived
      let next :=
        match hOne : one.2, hTwo : two.2 with
        | some nextOwner, some nextReceiver =>
            some (.leftOriginRight nextOwner nextReceiver
              (switchEndToEndFirstLeft_common_source A package owner receiver
                move previouslyReceived nextReceiver nextOwner hTwo hOne).symm)
        | _, _ => none
      ((one.1, two.1), next)
  | .rightOriginLeft receiver owner _ =>
      let one := switchEndToEndRightOriginLeftReceiverToRightOwner A package
        receiver move.2
      let two := switchEndToEndRightOriginLeftOwnerToRightReceiver A package
        owner receiver move previouslyReceived
      let next :=
        match hOne : one.2, hTwo : two.2 with
        | some nextOwner, some nextReceiver =>
            some (.rightOriginRight nextOwner nextReceiver
              (switchEndToEndRightOriginLeft_common_source A package owner
                receiver move previouslyReceived nextReceiver nextOwner hTwo
                hOne).symm)
        | _, _ => none
      ((one.1, two.1), next)
  | .leftOriginLeft receiver owner _ =>
      let one := switchEndToEndLeftOriginLeftReceiverToRightOwner A package
        receiver move.2
      let two := switchEndToEndLeftOriginLeftOwnerToRightReceiver A package
        owner receiver move previouslyReceived
      let next :=
        match hOne : one.2, hTwo : two.2 with
        | some nextOwner, some nextReceiver =>
            some (.leftOriginRight nextOwner nextReceiver
              (switchEndToEndLeftOriginLeft_common_source A package owner
                receiver move previouslyReceived nextReceiver nextOwner hTwo
                hOne).symm)
        | _, _ => none
      ((one.1, two.1), next)
  | .firstRight _ _ _ => ((default, default), none)
  | .rightOriginRight _ _ _ => ((default, default), none)
  | .leftOriginRight _ _ _ => ((default, default), none)

end


end DetParityAutomaton

end DistributedSynthesis
