/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionPathBookkeeping
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixRetainedCutReadback

/-!
# Reference-word alignment for marked-bank direction paths

Concrete finite controllers are often verified in two independent steps:

1. their global trace word is proved equal to a proof-side reference word;
2. cut packets are calculated on that simpler reference word.

The marked-bank acceptance endpoint instead mentions the controller's actual
trace word.  This file performs exactly that rewrite.  It also isolates the
only semantic seam left after a retained root-aligned cut stream is known:
the packet root at cut `k` must be the selected bank path's lineage thread at
the corresponding offset.  The seam is stated only as equality of priorities,
which is the weakest fact consumed by parity readback.

Directions, bank indices, roots, offsets, and cuts remain proof-side data.
No executable endpoint is given any graph orientation or leader bit.
-/

namespace DistributedSynthesis

universe u v x y s w

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

private abbrev CommonControl :=
  ProfiledRawJointHybridCommonControl A strategy hwin

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev PhysicalController :=
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂

private abbrev ReferenceWord :=
  OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)

private abbrev Installed
    (control : CommonControl A strategy hwin) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
    hwin control

private abbrev DirectionPath
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath A
    strategy hwin control direction

private abbrev DirectionBareCodeWord
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :=
  ((DirectionPath A strategy hwin control direction).toExtraAllowedPath A
    strategy hwin).bareCodeWord A strategy hwin

/-! ## A generic reference-word cut alignment -/

/-- Physical cut alignment stated on an arbitrary reference word together
with a whole-word equality to the controller trace. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionReferenceCutAlignment
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂)
    (reference : ReferenceWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (start : Nat) (cuts : Nat → Nat) where
  traceWord_eq_reference :
    controller.globalMachine.globalMachineTraceWord
        controller.globalOutputOne controller.globalOutputTwo env = reference
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  initialSide : IndexedLineageSide
  offset : Nat
  blockMin_eq_threadPriority : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority (A.run reference (start + n))) cuts k =
      (codedAlternatingIndexedLineageCodeThreadSystem
        (.common
          ((profiledRawJointCommonWorldFamily A
            (Installed A strategy hwin control).world).incidenceCode A))
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun
          (.common
            ((profiledRawJointCommonWorldFamily A
              (Installed A strategy hwin control).world).incidenceCode A))
          (profiledRawJointHybridCurrentSlots A)
          (DirectionBareCodeWord A strategy hwin control direction)
          initialSide () (offset + k))

namespace
  ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionReferenceCutAlignment

/-- Rewrite the reference-word calculation to the genuine controller trace. -/
noncomputable def toPhysicalCutAlignment
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    {reference : ReferenceWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {control : CommonControl A strategy hwin}
    {direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)}
    {start : Nat} {cuts : Nat → Nat}
    (alignment :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionReferenceCutAlignment
        A strategy hwin controller env reference control direction start cuts) :
    ProfiledRawJointHybridPhysicalCompatibleValidatedExtraPhysicalCutAlignment
      A strategy hwin (DirectionPath A strategy hwin control direction)
        controller.globalMachine controller.globalOutputOne
          controller.globalOutputTwo env start cuts where
  cuts_strictMono := alignment.cuts_strictMono
  cuts_zero := alignment.cuts_zero
  initialSide := alignment.initialSide
  offset := alignment.offset
  blockMin_eq_threadPriority := fun k ↦ by
    rw [alignment.traceWord_eq_reference]
    exact alignment.blockMin_eq_threadPriority k

/-- A root-priority packet stream on the reference word supplies the generic
reference alignment once its roots are identified with the selected bank
thread priorities.  This theorem exposes the sole semantic seam explicitly. -/
noncomputable def ofRootPriorities
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    {reference : ReferenceWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {control : CommonControl A strategy hwin}
    {direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)}
    {start : Nat} {cuts : Nat → Nat}
    (traceWord_eq_reference :
      controller.globalMachine.globalMachineTraceWord
          controller.globalOutputOne controller.globalOutputTwo env = reference)
    (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (initialSide : IndexedLineageSide) (offset : Nat)
    (root : Nat → ProfiledRawJointThreadRoot A)
    (blockMin_eq_rootPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority (A.run reference (start + n))) cuts k =
        profiledRawJointThreadRootPriority A (root k))
    (rootPriority_eq_threadPriority : ∀ k : Nat,
      profiledRawJointThreadRootPriority A (root k) =
        (codedAlternatingIndexedLineageCodeThreadSystem
          (.common
            ((profiledRawJointCommonWorldFamily A
              (Installed A strategy hwin control).world).incidenceCode A))
          (profiledRawJointHybridCurrentSlots A)
          (profiledRawJointThreadRootPriority A)).priority
          (codedAlternatingIndexedLineageCodeRun
            (.common
              ((profiledRawJointCommonWorldFamily A
                (Installed A strategy hwin control).world).incidenceCode A))
            (profiledRawJointHybridCurrentSlots A)
            (DirectionBareCodeWord A strategy hwin control direction)
            initialSide () (offset + k))) :
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionReferenceCutAlignment
      A strategy hwin controller env reference control direction start cuts where
  traceWord_eq_reference := traceWord_eq_reference
  cuts_strictMono := cuts_strictMono
  cuts_zero := cuts_zero
  initialSide := initialSide
  offset := offset
  blockMin_eq_threadPriority := fun k ↦
    (blockMin_eq_rootPriority k).trans (rootPriority_eq_threadPriority k)

/-- A reference alignment is already the canonical direction-path hard
certificate consumed by the preceding bookkeeping adapter. -/
noncomputable def toDirectionHardCertificate
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    {reference : ReferenceWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {control : CommonControl A strategy hwin}
    {direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)}
    {start : Nat} {cuts : Nat → Nat}
    (alignment :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionReferenceCutAlignment
        A strategy hwin controller env reference control direction start cuts) :
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionHardCertificateBundle
      A strategy hwin controller env :=
  ⟨control, direction, start, cuts,
    alignment.toPhysicalCutAlignment A strategy hwin⟩

end
  ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionReferenceCutAlignment

/-! ## Direct reuse of the retained cut-readback packet stream -/

private abbrev RightMove :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A

private abbrev LeftMove :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

private abbrev RetainedController
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) :=
  profiledRawJointHybridLiteralPrefixRetainedController A rightMove leftMove
    rightAnchor leftAnchor

private abbrev ShadowTag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

/-- The existing retained cut readback becomes a marked-bank direction hard
certificate after supplying only a priority alignment from its packet roots
to the selected bank thread.  All trace equality and cut arithmetic are
reused unchanged. -/
noncomputable def
    ProfiledRawJointHybridLiteralPrefixRetainedCutReadback.toBankDirectionHardCertificate
    {rightMove : RightMove A} {leftMove : LeftMove A}
    {rightAnchor leftAnchor : Bool}
    {env : EnvironmentSequence In₁ In₂}
    {tag : ShadowTag A strategy hwin}
    {start : Nat} {cuts : Nat → Nat}
    (readback :
      ProfiledRawJointHybridLiteralPrefixRetainedCutReadback A strategy hwin
        rightMove leftMove rightAnchor leftAnchor env tag start cuts)
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (offset : Nat)
    (rootPriority_eq_threadPriority : ∀ k : Nat,
      profiledRawJointThreadRootPriority A
          (readback.stream.packet k).root =
        (codedAlternatingIndexedLineageCodeThreadSystem
          (.common
            ((profiledRawJointCommonWorldFamily A
              (Installed A strategy hwin control).world).incidenceCode A))
          (profiledRawJointHybridCurrentSlots A)
          (profiledRawJointThreadRootPriority A)).priority
          (codedAlternatingIndexedLineageCodeRun
            (.common
              ((profiledRawJointCommonWorldFamily A
                (Installed A strategy hwin control).world).incidenceCode A))
            (profiledRawJointHybridCurrentSlots A)
            (DirectionBareCodeWord A strategy hwin control direction)
            initialSide () (offset + k))) :
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionHardCertificateBundle
      A strategy hwin
        (RetainedController A rightMove leftMove rightAnchor leftAnchor) env := by
  let reference :=
    profiledRawJointHybridLiteralPrefixRetainedReferenceWord A rightMove
      leftMove rightAnchor leftAnchor env
  let alignment :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionReferenceCutAlignment.ofRootPriorities
      A strategy hwin
      (profiledRawJointHybridLiteralPrefixRetained_globalMachineTraceWord_eq A
        rightMove leftMove rightAnchor leftAnchor env)
      readback.cuts_strictMono readback.cuts_zero initialSide offset
      (fun k ↦ (readback.stream.packet k).root)
      (fun k ↦ (readback.stream.packet k).blockMin_eq_rootPriority)
      rootPriority_eq_threadPriority
  exact alignment.toDirectionHardCertificate A strategy hwin

end

end DetParityAutomaton

end DistributedSynthesis
