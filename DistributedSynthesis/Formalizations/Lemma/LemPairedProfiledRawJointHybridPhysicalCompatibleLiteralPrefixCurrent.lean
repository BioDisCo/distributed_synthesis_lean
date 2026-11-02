/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLiteralRetainedRelation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixExtraReadback

/-!
# Current-source provenance for recurring literal-prefix tables

The ordinary extra-parent link explains the *children* selected from a
semantic source, but intentionally says nothing about the extra already
stored at the current state.  A retained strict-block controller needs that
stronger fact: the table used before the first strict input must belong to the
current semantic occurrence, rather than merely to some code-equal
predecessor representative.

This file supplies the concrete invariant for the literal-prefix payload.
The initial common world is seeded by a pair of exact uniform tables which is
chosen before any future input.  Every non-root current payload is the
literal annotation of one actual incoming semantic edge.  The invariant is
preserved definitionally because the recurring annotation is replace-only.

No fresh input occurs in the seed table identifier.  Inputs are consumed only
later by its receiver and shared-sender controller transitions.
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

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev LiteralAnnotation :=
  ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A

/-! ## Exact input-independent seed at the initial common world -/

/-- The policy-free installed interface of a literal common world. -/
def profiledRawJointHybridLiteralPrefixSeedInstalled
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    ProfiledRawJointHybridCommonMoveData A strategy where
  incidenceCode := (profiledRawJointCommonWorldFamily A world).incidenceCode A
  rawMove := (profiledRawJointCommonWorldFamily A world).move A
  world := world
  incidence_eq := rfl
  move_eq := rfl

/-- One exact right-block table at the current common world.  Its definition
contains no future input pair: the receiver accepts those inputs only when
the local carrier runs. -/
noncomputable def profiledRawJointHybridRightLiteralPrefixSeedMove
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    ProfiledRawJointGuardedCommonRightLiteralCrossMove A := by
  let installed :=
    profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
  let descriptor :=
    profiledRawJointHybridExactRightUniformDescriptor A strategy hwin installed
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let activation :=
    profiledRawJointHybridExactRightUniformActivation A strategy hwin installed
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨activation.target .first [] default⟩
  apply finiteCrossAnchorLiteralPrefixMove
    (fun descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A ↦
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false)
    (fun _ ↦ descriptor)
    (fun _ ↦ monitor.initial)
    (fun _ ↦ profiledRawJointTargetRightReceiverStrategy A activation)
    (pairedRightSenderStrategy activation.lambda)
  intro _anchor env
  simpa [monitor, descriptor] using
    (profiledRawJointHybridExactRightUniformMonitor_realizable A strategy hwin
      installed env)

/-- Exact left-block seed, selected at the same common occurrence. -/
noncomputable def profiledRawJointHybridLeftLiteralPrefixSeedMove
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    ProfiledRawJointGuardedCommonLeftLiteralCrossMove A := by
  let installed :=
    profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
  let descriptor :=
    profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin installed
  let baseMonitor :=
    profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
  let monitor :=
    profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor
  let activation :=
    profiledRawJointHybridExactLeftUniformActivation A strategy hwin installed
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨activation.target .first [] default⟩
  apply finiteCrossAnchorLiteralPrefixMove
    (fun descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A ↦
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor)
    (fun _ ↦ descriptor)
    (fun _ ↦ monitor.initial)
    (fun _ ↦ profiledRawJointTargetLeftReceiverStrategy A activation)
    (pairedLeftSenderStrategy activation.lambda)
  intro _anchor env
  apply (BlockRecordMonitor.raiseState_winsPlay_iff baseMonitor _).2
  simpa [baseMonitor, descriptor] using
    (profiledRawJointHybridExactLeftUniformMonitor_realizable A strategy hwin
      installed env)

/-- Both exact seed tables, chosen jointly before the first future graph or
input pair. -/
noncomputable def profiledRawJointHybridLiteralPrefixSeedAnnotation
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    LiteralAnnotation A :=
  (some (profiledRawJointHybridRightLiteralPrefixSeedMove A strategy hwin
      world),
    some (profiledRawJointHybridLeftLiteralPrefixSeedMove A strategy hwin
      world))

/-- Explicit construction-time locality: changing a hypothetical future
partner input does not change the seed selected by the blind endpoint. -/
theorem profiledRawJointHybridLiteralPrefixSeedAnnotation_hidden_irrel
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (_inputOne : In₁) (hidden hidden' : In₂) :
    profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy hwin world =
      profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy hwin world :=
  rfl

/-! ## Retaining the seed through the first strict input -/

/-- Full first output pair of a recurring right edge table. -/
theorem profiledRawJointRightLiteralPrefixMoveOf_initial_first_pair
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (first : In₂ × In₁) :
    let move := profiledRawJointRightLiteralPrefixMoveOf A strategy hwin family
      direction semanticMember hmember
    let senderRoot :=
      profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A move
    let receiverRoot :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
        anchor
    ((profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A receiverRoot
        first.1 first.2).1,
      (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A senderRoot
        first.2).1) =
      (profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
          semanticMember hmember anchor [] first,
        profiledRawJointRightSiblingSender A semanticMember [] first.2) := by
  classical
  let descriptor :=
    profiledRawJointRightPhysicalSiblingDescriptorOf A family direction
      semanticMember
  let monitorFamily :=
    fun descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A ↦
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let monitor := monitorFamily descriptor
  let receiver := fun member ↦
    profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
      semanticMember hmember member
  let sender := profiledRawJointRightSiblingSender A semanticMember
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨family.incidenceCode A⟩
  let hrealizable : ∀ member env,
      (monitor.restartAt monitor.initial).WinsPlay
        (pairPlay (receiver member) sender env) := by
    intro member env
    simpa [monitor, monitorFamily, receiver, sender, descriptor] using
      (profiledRawJointRightPhysicalSiblingMonitor_realizable A hwin family
        direction semanticMember hmember member env)
  simpa [profiledRawJointRightLiteralPrefixMoveOf, descriptor, monitorFamily,
    monitor, receiver, sender] using
    (finiteCrossAnchorLiteralPrefix_initial_outputs_eq_first monitorFamily
      (fun _ : Bool ↦ descriptor) (fun _ : Bool ↦ monitor.initial) receiver
      sender hrealizable anchor first)

/-- Full first output pair of a recurring left edge table. -/
theorem profiledRawJointLeftLiteralPrefixMoveOf_initial_first_pair
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (first : In₁ × In₂) :
    let move := profiledRawJointLeftLiteralPrefixMoveOf A strategy hwin family
      direction semanticMember hmember
    let senderRoot :=
      profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A move
    let receiverRoot :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move anchor
    ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A receiverRoot
        first.1 first.2).1,
      (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A senderRoot
        first.2).1) =
      (profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
          semanticMember hmember anchor [] first,
        profiledRawJointLeftSiblingSender A semanticMember [] first.2) := by
  classical
  let descriptor :=
    profiledRawJointLeftPhysicalSiblingDescriptorOf A family direction
      semanticMember
  let baseMonitor :=
    profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
  let monitorFamily :=
    fun descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A ↦
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor
  let monitor := monitorFamily descriptor
  let receiver := fun member ↦
    profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
      semanticMember hmember member
  let sender := profiledRawJointLeftSiblingSender A semanticMember
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨family.incidenceCode A⟩
  let hrealizable : ∀ member env,
      (monitor.restartAt monitor.initial).WinsPlay
        (pairPlay (receiver member) sender env) := by
    intro member env
    apply (BlockRecordMonitor.raiseState_winsPlay_iff baseMonitor _).2
    simpa [baseMonitor, monitor, monitorFamily, receiver, sender, descriptor]
      using
        (profiledRawJointLeftPhysicalSiblingMonitor_realizable A hwin family
          direction semanticMember hmember member env)
  simpa [profiledRawJointLeftLiteralPrefixMoveOf, descriptor, baseMonitor,
    monitorFamily, monitor, receiver, sender,
    profiledRawJointGuardedCommonLeftLiteralCrossMonitor] using
    (finiteCrossAnchorLiteralPrefix_initial_outputs_eq_first monitorFamily
      (fun _ : Bool ↦ descriptor) (fun _ : Bool ↦ monitor.initial) receiver
      sender hrealizable anchor first)

/-- A recurring right edge table has the same retained-controller equation
as the initial seed.  This is the full output pair; the existing readback
theorem is its receiver projection. -/
theorem profiledRawJointRightLiteralPrefixMoveOf_retained_second_pair
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (first second : In₂ × In₁) :
    let move := profiledRawJointRightLiteralPrefixMoveOf A strategy hwin family
      direction semanticMember hmember
    let senderRoot :=
      profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A move
    let receiverRoot :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
        anchor
    let senderAfterFirst :=
      (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A senderRoot
        first.2).2
    let receiverAfterFirst :=
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A receiverRoot
        first.1 first.2).2
    ((profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
        receiverAfterFirst second.1 second.2).1,
      (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A
        senderAfterFirst second.2).1) =
      (profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
          semanticMember hmember anchor [first] second,
        profiledRawJointRightSiblingSender A semanticMember [first.2]
          second.2) := by
  classical
  let descriptor :=
    profiledRawJointRightPhysicalSiblingDescriptorOf A family direction
      semanticMember
  let monitorFamily :=
    fun descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A ↦
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let monitor := monitorFamily descriptor
  let receiver := fun member ↦
    profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
      semanticMember hmember member
  let sender := profiledRawJointRightSiblingSender A semanticMember
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨family.incidenceCode A⟩
  let hrealizable : ∀ member env,
      (monitor.restartAt monitor.initial).WinsPlay
        (pairPlay (receiver member) sender env) := by
    intro member env
    simpa [monitor, monitorFamily, receiver, sender, descriptor] using
      (profiledRawJointRightPhysicalSiblingMonitor_realizable A hwin family
        direction semanticMember hmember member env)
  simpa [profiledRawJointRightLiteralPrefixMoveOf, descriptor, monitorFamily,
    monitor, receiver, sender] using
    (finiteCrossAnchorLiteralPrefix_retained_outputs_eq_second monitorFamily
      (fun _ : Bool ↦ descriptor) (fun _ : Bool ↦ monitor.initial) receiver
      sender hrealizable anchor first second)

/-- Recurring left-edge mirror. -/
theorem profiledRawJointLeftLiteralPrefixMoveOf_retained_second_pair
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (first second : In₁ × In₂) :
    let move := profiledRawJointLeftLiteralPrefixMoveOf A strategy hwin family
      direction semanticMember hmember
    let senderRoot :=
      profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A move
    let receiverRoot :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move anchor
    let senderAfterFirst :=
      (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A senderRoot
        first.2).2
    let receiverAfterFirst :=
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A receiverRoot
        first.1 first.2).2
    ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
        receiverAfterFirst second.1 second.2).1,
      (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A
        senderAfterFirst second.2).1) =
      (profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
          semanticMember hmember anchor [first] second,
        profiledRawJointLeftSiblingSender A semanticMember [first.2]
          second.2) := by
  classical
  let descriptor :=
    profiledRawJointLeftPhysicalSiblingDescriptorOf A family direction
      semanticMember
  let baseMonitor :=
    profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
  let monitorFamily :=
    fun descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A ↦
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor
  let monitor := monitorFamily descriptor
  let receiver := fun member ↦
    profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
      semanticMember hmember member
  let sender := profiledRawJointLeftSiblingSender A semanticMember
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨family.incidenceCode A⟩
  let hrealizable : ∀ member env,
      (monitor.restartAt monitor.initial).WinsPlay
        (pairPlay (receiver member) sender env) := by
    intro member env
    apply (BlockRecordMonitor.raiseState_winsPlay_iff baseMonitor _).2
    simpa [baseMonitor, monitor, monitorFamily, receiver, sender, descriptor]
      using
        (profiledRawJointLeftPhysicalSiblingMonitor_realizable A hwin family
          direction semanticMember hmember member env)
  simpa [profiledRawJointLeftLiteralPrefixMoveOf, descriptor, baseMonitor,
    monitorFamily, monitor, receiver, sender,
    profiledRawJointGuardedCommonLeftLiteralCrossMonitor] using
    (finiteCrossAnchorLiteralPrefix_retained_outputs_eq_second monitorFamily
      (fun _ : Bool ↦ descriptor) (fun _ : Bool ↦ monitor.initial) receiver
      sender hrealizable anchor first second)

/-- The installed right seed emits the full first literal pair.  In
particular, the blind coordinate is read from the very same preselected
controller as the receiver coordinate. -/
theorem profiledRawJointHybridRightLiteralPrefixSeed_initial_first
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (anchor : Bool) (first : In₂ × In₁) :
    let move :=
      profiledRawJointHybridRightLiteralPrefixSeedMove A strategy hwin world
    let senderRoot :=
      profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A move
    let receiverRoot :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
        anchor
    ((profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A receiverRoot
        first.1 first.2).1,
      (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A senderRoot
        first.2).1) =
      ((profiledRawJointTargetRightReceiverStrategy A
          (profiledRawJointHybridExactRightUniformActivation A strategy hwin
            (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
              world))) [] first,
        pairedRightSenderStrategy
          (profiledRawJointHybridExactRightUniformActivation A strategy hwin
            (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
              world)).lambda [] first.2) := by
  classical
  let installed :=
    profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
  let descriptor :=
    profiledRawJointHybridExactRightUniformDescriptor A strategy hwin installed
  let monitorFamily :=
    fun descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A ↦
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let monitor := monitorFamily descriptor
  let activation :=
    profiledRawJointHybridExactRightUniformActivation A strategy hwin installed
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨activation.target .first [] default⟩
  let receiver := fun _ : Bool ↦
    profiledRawJointTargetRightReceiverStrategy A activation
  let sender := pairedRightSenderStrategy activation.lambda
  let hrealizable : ∀ member env,
      (monitor.restartAt monitor.initial).WinsPlay
        (pairPlay (receiver member) sender env) := by
    intro _member env
    simpa [monitor, monitorFamily, receiver, sender, descriptor, activation]
      using
        (profiledRawJointHybridExactRightUniformMonitor_realizable A strategy
          hwin installed env)
  simpa [profiledRawJointHybridRightLiteralPrefixSeedMove,
    installed, descriptor, monitorFamily, monitor, activation, receiver,
    sender] using
    (finiteCrossAnchorLiteralPrefix_initial_outputs_eq_first monitorFamily
      (fun _ : Bool ↦ descriptor) (fun _ : Bool ↦ monitor.initial) receiver
      sender hrealizable anchor first)

/-- The exact right seed passes the dangerous two-letter test when its sender
control is retained.  The second local output pair is the literal semantic
second record, with the first full input in both receiver and sender pasts.
There is no `sender [] = sender [first]` premise. -/
theorem profiledRawJointHybridRightLiteralPrefixSeed_retained_second
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (anchor : Bool) (first second : In₂ × In₁) :
    let move :=
      profiledRawJointHybridRightLiteralPrefixSeedMove A strategy hwin world
    let senderRoot :=
      profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A move
    let receiverRoot :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
        anchor
    let senderAfterFirst :=
      (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A senderRoot
        first.2).2
    let receiverAfterFirst :=
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A receiverRoot
        first.1 first.2).2
    ((profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
        receiverAfterFirst second.1 second.2).1,
      (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A
        senderAfterFirst second.2).1) =
      ((profiledRawJointTargetRightReceiverStrategy A
          (profiledRawJointHybridExactRightUniformActivation A strategy hwin
            (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
              world))) [first] second,
        pairedRightSenderStrategy
          (profiledRawJointHybridExactRightUniformActivation A strategy hwin
            (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
              world)).lambda [first.2] second.2) := by
  classical
  let installed :=
    profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
  let descriptor :=
    profiledRawJointHybridExactRightUniformDescriptor A strategy hwin installed
  let monitorFamily :=
    fun descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A ↦
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let monitor := monitorFamily descriptor
  let activation :=
    profiledRawJointHybridExactRightUniformActivation A strategy hwin installed
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨activation.target .first [] default⟩
  let receiver := fun _ : Bool ↦
    profiledRawJointTargetRightReceiverStrategy A activation
  let sender := pairedRightSenderStrategy activation.lambda
  let hrealizable : ∀ member env,
      (monitor.restartAt monitor.initial).WinsPlay
        (pairPlay (receiver member) sender env) := by
    intro _member env
    simpa [monitor, monitorFamily, receiver, sender, descriptor, activation]
      using
        (profiledRawJointHybridExactRightUniformMonitor_realizable A strategy
          hwin installed env)
  simpa [profiledRawJointHybridRightLiteralPrefixSeedMove,
    installed, descriptor, monitorFamily, monitor, activation, receiver,
    sender] using
    (finiteCrossAnchorLiteralPrefix_retained_outputs_eq_second monitorFamily
      (fun _ : Bool ↦ descriptor) (fun _ : Bool ↦ monitor.initial) receiver
      sender hrealizable anchor first second)

/-- Left mirror of the full first-record theorem. -/
theorem profiledRawJointHybridLeftLiteralPrefixSeed_initial_first
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (anchor : Bool) (first : In₁ × In₂) :
    let move :=
      profiledRawJointHybridLeftLiteralPrefixSeedMove A strategy hwin world
    let senderRoot :=
      profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A move
    let receiverRoot :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move anchor
    ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A receiverRoot
        first.1 first.2).1,
      (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A senderRoot
        first.2).1) =
      ((profiledRawJointTargetLeftReceiverStrategy A
          (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
            (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
              world))) [] first,
        pairedLeftSenderStrategy
          (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
            (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
              world)).lambda [] first.2) := by
  classical
  let installed :=
    profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
  let descriptor :=
    profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin installed
  let baseMonitor :=
    profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
  let monitorFamily :=
    fun descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A ↦
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor
  let monitor := monitorFamily descriptor
  let activation :=
    profiledRawJointHybridExactLeftUniformActivation A strategy hwin installed
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨activation.target .first [] default⟩
  let receiver := fun _ : Bool ↦
    profiledRawJointTargetLeftReceiverStrategy A activation
  let sender := pairedLeftSenderStrategy activation.lambda
  let hrealizable : ∀ member env,
      (monitor.restartAt monitor.initial).WinsPlay
        (pairPlay (receiver member) sender env) := by
    intro _member env
    apply (BlockRecordMonitor.raiseState_winsPlay_iff baseMonitor _).2
    simpa [baseMonitor, monitor, monitorFamily, receiver, sender, descriptor,
      activation] using
        (profiledRawJointHybridExactLeftUniformMonitor_realizable A strategy
          hwin installed env)
  simpa [profiledRawJointHybridLeftLiteralPrefixSeedMove,
    installed, descriptor, baseMonitor, monitorFamily, monitor, activation,
    receiver, sender] using
    (finiteCrossAnchorLiteralPrefix_initial_outputs_eq_first monitorFamily
      (fun _ : Bool ↦ descriptor) (fun _ : Bool ↦ monitor.initial) receiver
      sender hrealizable anchor first)

/-- The exact left seed passes the same retained-controller two-letter test.
Both local controls remember the first strict input. -/
theorem profiledRawJointHybridLeftLiteralPrefixSeed_retained_second
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (anchor : Bool) (first second : In₁ × In₂) :
    let move :=
      profiledRawJointHybridLeftLiteralPrefixSeedMove A strategy hwin world
    let senderRoot :=
      profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A move
    let receiverRoot :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move anchor
    let senderAfterFirst :=
      (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A senderRoot
        first.2).2
    let receiverAfterFirst :=
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A receiverRoot
        first.1 first.2).2
    ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
        receiverAfterFirst second.1 second.2).1,
      (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A
        senderAfterFirst second.2).1) =
      ((profiledRawJointTargetLeftReceiverStrategy A
          (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
            (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
              world))) [first] second,
        pairedLeftSenderStrategy
          (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
            (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
              world)).lambda [first.2] second.2) := by
  classical
  let installed :=
    profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
  let descriptor :=
    profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin installed
  let baseMonitor :=
    profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
  let monitorFamily :=
    fun descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A ↦
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor
  let monitor := monitorFamily descriptor
  let activation :=
    profiledRawJointHybridExactLeftUniformActivation A strategy hwin installed
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨activation.target .first [] default⟩
  let receiver := fun _ : Bool ↦
    profiledRawJointTargetLeftReceiverStrategy A activation
  let sender := pairedLeftSenderStrategy activation.lambda
  let hrealizable : ∀ member env,
      (monitor.restartAt monitor.initial).WinsPlay
        (pairPlay (receiver member) sender env) := by
    intro _member env
    apply (BlockRecordMonitor.raiseState_winsPlay_iff baseMonitor _).2
    simpa [baseMonitor, monitor, monitorFamily, receiver, sender, descriptor,
      activation] using
        (profiledRawJointHybridExactLeftUniformMonitor_realizable A strategy
          hwin installed env)
  simpa [profiledRawJointHybridLeftLiteralPrefixSeedMove,
    installed, descriptor, baseMonitor, monitorFamily, monitor, activation,
    receiver, sender] using
    (finiteCrossAnchorLiteralPrefix_retained_outputs_eq_second monitorFamily
      (fun _ : Bool ↦ descriptor) (fun _ : Bool ↦ monitor.initial) receiver
      sender hrealizable anchor first second)

/-! ## The concrete current-extra invariant -/

/-- A current literal payload either is the exact seed at the initial world,
or was produced by one actual incoming semantic edge.  The predecessor and
old payload are proof-only witnesses. -/
def ProfiledRawJointHybridLiteralPrefixCurrentCompatible
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (source : HybridState A strategy)
    (extra : LiteralAnnotation A) : Prop :=
  (source = .common initial ∧
      extra = profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy
        hwin initial) ∨
    ∃ (parent : HybridState A strategy) (old : LiteralAnnotation A)
        (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)),
      parent.step A direction = source ∧
        profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
          parent old direction = extra

/-- The seeded initial annotation is compatible with the literal initial
semantic state. -/
theorem profiledRawJointHybridLiteralPrefixCurrentCompatible_initial
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
      initial (.common initial)
      (profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy hwin
        initial) :=
  Or.inl ⟨rfl, rfl⟩

/-- Replace-only advancement establishes current provenance at the child in
one step.  No assumption about the old payload is required. -/
theorem profiledRawJointHybridLiteralPrefixCurrentCompatible_advance
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (source : HybridState A strategy) (old : LiteralAnnotation A)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
      initial (source.step A direction)
      (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        source old direction) :=
  Or.inr ⟨source, old, direction, rfl, rfl⟩

/-! ## Sidewise origin eliminators -/

/-- Proof-only origin information for a right table stored at the current
node.  At the root it is the input-independent exact seed.  At every other
node it is literally the right component installed by one incoming semantic
edge. -/
def ProfiledRawJointHybridRightLiteralPrefixCurrentMoveValid
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (source : HybridState A strategy)
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A) : Prop :=
  (source = .common initial ∧
      move = profiledRawJointHybridRightLiteralPrefixSeedMove A strategy hwin
        initial) ∨
    ∃ (parent : HybridState A strategy) (old : LiteralAnnotation A)
        (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)),
      parent.step A direction = source ∧
        (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
          parent old direction).1 = some move

/-- Left-table mirror of current origin validity. -/
def ProfiledRawJointHybridLeftLiteralPrefixCurrentMoveValid
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (source : HybridState A strategy)
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A) : Prop :=
  (source = .common initial ∧
      move = profiledRawJointHybridLeftLiteralPrefixSeedMove A strategy hwin
        initial) ∨
    ∃ (parent : HybridState A strategy) (old : LiteralAnnotation A)
        (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)),
      parent.step A direction = source ∧
        (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
          parent old direction).2 = some move

/-- A non-root right table together with the exact semantic family edge that
constructed it.  Keeping `annotation_eq` prevents a later proof from pairing
the table with an unrelated family that merely happens to build an equal
finite value. -/
def ProfiledRawJointHybridRightLiteralPrefixIncomingOrigin
    (source : HybridState A strategy)
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A) : Prop :=
  ∃ (parent : HybridState A strategy) (old : LiteralAnnotation A)
      (direction : HybridDirection (In₁ := In₁) (In₂ := In₂))
      (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
      (familyDirection : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂))
      (semanticMember : ProcOnePairedEntryRep strategy × A.State),
    ∃ member_eq : (family.semanticChild A familyDirection).right () =
        some semanticMember,
      parent.step A direction = source ∧
        profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
            parent old direction =
          profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin family
            familyDirection ∧
        (∀ (current : ProfiledRawJointOneSidedSemanticState A strategy
              (I := Unit)),
            source = .oneSided current →
              ∀ (currentMember : ProcOnePairedEntryRep strategy × A.State),
                current.family.right () = some currentMember →
                  ∀ (row : PairedEntryRow) (past : List (In₂ × In₁))
                      (input : In₂ × In₁),
                    (current.step A
                        (profiledRawJointUnitRightActualDirection
                          (In₁ := In₁) (In₂ := In₂) row past input)).code A =
                      profiledRawJointOneSidedNext A
                        ((profiledRawJointRightSiblingFamily A family
                          familyDirection false).incidenceCode A)
                        ((profiledRawJointRightSiblingFamily A family
                          familyDirection false).move A)
                        (profiledRawJointUnitRightActualDirection
                          (In₁ := In₁) (In₂ := In₂) row past input)) ∧
        move = profiledRawJointRightLiteralPrefixMoveOf A strategy hwin
          family familyDirection semanticMember member_eq

/-- Left incoming-origin mirror. -/
def ProfiledRawJointHybridLeftLiteralPrefixIncomingOrigin
    (source : HybridState A strategy)
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A) : Prop :=
  ∃ (parent : HybridState A strategy) (old : LiteralAnnotation A)
      (direction : HybridDirection (In₁ := In₁) (In₂ := In₂))
      (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
      (familyDirection : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂))
      (semanticMember : ProcTwoPairedEntryRep strategy × A.State),
    ∃ member_eq : (family.semanticChild A familyDirection).left () =
        some semanticMember,
      parent.step A direction = source ∧
        profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
            parent old direction =
          profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin family
            familyDirection ∧
        (∀ (current : ProfiledRawJointOneSidedSemanticState A strategy
              (I := Unit)),
            source = .oneSided current →
              ∀ (currentMember : ProcTwoPairedEntryRep strategy × A.State),
                current.family.left () = some currentMember →
                  ∀ (row : PairedEntryRow) (past : List (In₁ × In₂))
                      (input : In₁ × In₂),
                    (current.step A
                        (profiledRawJointUnitLeftActualDirection
                          (In₁ := In₁) (In₂ := In₂) row past input)).code A =
                      profiledRawJointOneSidedNext A
                        ((profiledRawJointLeftSiblingFamily A family
                          familyDirection false).incidenceCode A)
                        ((profiledRawJointLeftSiblingFamily A family
                          familyDirection false).move A)
                        (profiledRawJointUnitLeftActualDirection
                          (In₁ := In₁) (In₂ := In₂) row past input)) ∧
        move = profiledRawJointLeftLiteralPrefixMoveOf A strategy hwin
          family familyDirection semanticMember member_eq

/-- A present right component of a compatible current annotation has one of
the two exact origins above.  The witness is semantic proof data only. -/
theorem
    ProfiledRawJointHybridLiteralPrefixCurrentCompatible.rightMoveValid
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {source : HybridState A strategy} {extra : LiteralAnnotation A}
    (hcurrent :
      ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial source extra)
    {move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A}
    (hmove : extra.1 = some move) :
    ProfiledRawJointHybridRightLiteralPrefixCurrentMoveValid A strategy hwin
      initial source move := by
  rcases hcurrent with ⟨rfl, rfl⟩ | ⟨parent, old, direction, hsource, hextra⟩
  · left
    refine ⟨rfl, ?_⟩
    exact (Option.some.inj hmove).symm
  · right
    refine ⟨parent, old, direction, hsource, ?_⟩
    calc
      (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
          parent old direction).1 = extra.1 := congrArg Prod.fst hextra
      _ = some move := hmove

/-- Left mirror. -/
theorem
    ProfiledRawJointHybridLiteralPrefixCurrentCompatible.leftMoveValid
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {source : HybridState A strategy} {extra : LiteralAnnotation A}
    (hcurrent :
      ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial source extra)
    {move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A}
    (hmove : extra.2 = some move) :
    ProfiledRawJointHybridLeftLiteralPrefixCurrentMoveValid A strategy hwin
      initial source move := by
  rcases hcurrent with ⟨rfl, rfl⟩ | ⟨parent, old, direction, hsource, hextra⟩
  · left
    refine ⟨rfl, ?_⟩
    exact (Option.some.inj hmove).symm
  · right
    refine ⟨parent, old, direction, hsource, ?_⟩
    calc
      (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
          parent old direction).2 = extra.2 := congrArg Prod.snd hextra
      _ = some move := hmove

/-- Eliminate a present right table to either the unique initial seed or one
fully linked incoming semantic edge. -/
theorem
    ProfiledRawJointHybridLiteralPrefixCurrentCompatible.rightOrigin
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {source : HybridState A strategy} {extra : LiteralAnnotation A}
    (hcurrent :
      ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial source extra)
    {move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A}
    (hmove : extra.1 = some move) :
    (source = .common initial ∧
        move = profiledRawJointHybridRightLiteralPrefixSeedMove A strategy hwin
          initial) ∨
      ProfiledRawJointHybridRightLiteralPrefixIncomingOrigin A strategy hwin
        source move := by
  rcases hcurrent.rightMoveValid A strategy hwin hmove with hroot | hincoming
  · exact Or.inl hroot
  · rcases hincoming with ⟨parent, old, direction, hsource, hinstalled⟩
    cases parent with
    | common world =>
        cases direction with
        | simultaneous input =>
            let family := profiledRawJointCommonWorldFamily A world
            let familyDirection := profiledRawJointBothRestartDirection input
            have hoption :
                (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy
                  hwin family familyDirection).1 = some move := by
              simpa [family, familyDirection,
                profiledRawJointHybridLiteralPrefixAnnotationAdvance] using
                hinstalled
            obtain ⟨member, hmember, hmoveEq⟩ :=
              profiledRawJointRightLiteralPrefixMoveOption_spec A strategy hwin
                family familyDirection move (by
                  simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                    using hoption)
            right
            exact ⟨.common world, old, .simultaneous input, family,
              familyDirection, member, hmember, hsource, rfl, (by
                intro current hcurrent
                have himpossible :
                    (ProfiledRawJointHybridSemanticState.common world).step A
                        (.simultaneous input) = .oneSided current :=
                  hsource.trans hcurrent
                simp [ProfiledRawJointHybridSemanticState.step] at himpossible),
              hmoveEq⟩
        | strict actual =>
            let family := profiledRawJointCommonWorldFamily A world
            let familyDirection :=
              (profiledRawJointCommonActualDirection actual).direction
            have hoption :
                (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy
                  hwin family familyDirection).1 = some move := by
              simpa [family, familyDirection,
                profiledRawJointHybridLiteralPrefixAnnotationAdvance] using
                hinstalled
            obtain ⟨member, hmember, hmoveEq⟩ :=
              profiledRawJointRightLiteralPrefixMoveOption_spec A strategy hwin
                family familyDirection move (by
                  simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                    using hoption)
            right
            exact ⟨.common world, old, .strict actual, family,
              familyDirection, member, hmember, hsource, rfl, (by
                intro current hcurrent currentMember hcurrentMember row past
                  input
                have hstate :
                    (ProfiledRawJointHybridSemanticState.common world).step A
                        (.strict actual) = .oneSided current :=
                  hsource.trans hcurrent
                cases hside : actual.side with
                | right =>
                    have hfamily := congrArg
                      ProfiledRawJointOneSidedSemanticState.family
                      (ProfiledRawJointHybridSemanticState.oneSided.inj hstate)
                    simp [profiledRawJointCommonExitState, hside] at hfamily
                    rw [← hfamily] at hcurrentMember
                    simp at hcurrentMember
                | left =>
                    have hfamily := congrArg
                      ProfiledRawJointOneSidedSemanticState.family
                      (ProfiledRawJointHybridSemanticState.oneSided.inj hstate)
                    simp [profiledRawJointCommonExitState, hside] at hfamily
                    rw [ProfiledRawJointOneSidedSemanticState.step_code]
                    change
                      profiledRawJointOneSidedNext A (current.code A)
                          (current.move A)
                          (profiledRawJointUnitRightActualDirection
                            (In₁ := In₁) (In₂ := In₂) row past input) = _
                    simp only [ProfiledRawJointOneSidedSemanticState.code,
                      ProfiledRawJointOneSidedSemanticState.move]
                    rw [← hfamily]
                    exact
                      profiledRawJointRightSibling_oneSidedNext_eq_false A
                        family familyDirection true row past input), hmoveEq⟩
    | oneSided parentState =>
        cases direction with
        | simultaneous input =>
            simp [profiledRawJointHybridLiteralPrefixAnnotationAdvance,
              profiledRawJointHybridInitialLiteralPrefixAnnotation] at hinstalled
        | strict actual =>
            let family := parentState.family
            let familyDirection := actual.direction
            have hoption :
                (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy
                  hwin family familyDirection).1 = some move := by
              simpa [family, familyDirection,
                profiledRawJointHybridLiteralPrefixAnnotationAdvance] using
                hinstalled
            obtain ⟨member, hmember, hmoveEq⟩ :=
              profiledRawJointRightLiteralPrefixMoveOption_spec A strategy hwin
                family familyDirection move (by
                  simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                    using hoption)
            right
            exact ⟨.oneSided parentState, old, .strict actual, family,
              familyDirection, member, hmember, hsource, rfl, (by
                intro current hcurrent currentMember hcurrentMember row past
                  input
                have hstate :
                    (ProfiledRawJointHybridSemanticState.oneSided parentState
                      ).step A (.strict actual) = .oneSided current :=
                  hsource.trans hcurrent
                cases hside : actual.side with
                | right =>
                    have hfamily := congrArg
                      ProfiledRawJointOneSidedSemanticState.family
                      (ProfiledRawJointHybridSemanticState.oneSided.inj hstate)
                    simp [ProfiledRawJointOneSidedSemanticState.step, hside]
                      at hfamily
                    rw [← hfamily] at hcurrentMember
                    simp at hcurrentMember
                | left =>
                    have hfamily := congrArg
                      ProfiledRawJointOneSidedSemanticState.family
                      (ProfiledRawJointHybridSemanticState.oneSided.inj hstate)
                    simp [ProfiledRawJointOneSidedSemanticState.step, hside]
                      at hfamily
                    rw [ProfiledRawJointOneSidedSemanticState.step_code]
                    change
                      profiledRawJointOneSidedNext A (current.code A)
                          (current.move A)
                          (profiledRawJointUnitRightActualDirection
                            (In₁ := In₁) (In₂ := In₂) row past input) = _
                    simp only [ProfiledRawJointOneSidedSemanticState.code,
                      ProfiledRawJointOneSidedSemanticState.move]
                    rw [← hfamily]
                    exact
                      profiledRawJointRightSibling_oneSidedNext_eq_false A
                        family familyDirection true row past input), hmoveEq⟩
    | dead =>
        cases direction <;>
          simp [profiledRawJointHybridLiteralPrefixAnnotationAdvance,
            profiledRawJointHybridInitialLiteralPrefixAnnotation] at hinstalled

/-- Left-table mirror of the exact origin eliminator. -/
theorem
    ProfiledRawJointHybridLiteralPrefixCurrentCompatible.leftOrigin
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {source : HybridState A strategy} {extra : LiteralAnnotation A}
    (hcurrent :
      ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial source extra)
    {move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A}
    (hmove : extra.2 = some move) :
    (source = .common initial ∧
        move = profiledRawJointHybridLeftLiteralPrefixSeedMove A strategy hwin
          initial) ∨
      ProfiledRawJointHybridLeftLiteralPrefixIncomingOrigin A strategy hwin
        source move := by
  rcases hcurrent.leftMoveValid A strategy hwin hmove with hroot | hincoming
  · exact Or.inl hroot
  · rcases hincoming with ⟨parent, old, direction, hsource, hinstalled⟩
    cases parent with
    | common world =>
        cases direction with
        | simultaneous input =>
            let family := profiledRawJointCommonWorldFamily A world
            let familyDirection := profiledRawJointBothRestartDirection input
            have hoption :
                (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy
                  hwin family familyDirection).2 = some move := by
              simpa [family, familyDirection,
                profiledRawJointHybridLiteralPrefixAnnotationAdvance] using
                hinstalled
            obtain ⟨member, hmember, hmoveEq⟩ :=
              profiledRawJointLeftLiteralPrefixMoveOption_spec A strategy hwin
                family familyDirection move (by
                  simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                    using hoption)
            right
            exact ⟨.common world, old, .simultaneous input, family,
              familyDirection, member, hmember, hsource, rfl, (by
                intro current hcurrent
                have himpossible :
                    (ProfiledRawJointHybridSemanticState.common world).step A
                        (.simultaneous input) = .oneSided current :=
                  hsource.trans hcurrent
                simp [ProfiledRawJointHybridSemanticState.step] at himpossible),
              hmoveEq⟩
        | strict actual =>
            let family := profiledRawJointCommonWorldFamily A world
            let familyDirection :=
              (profiledRawJointCommonActualDirection actual).direction
            have hoption :
                (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy
                  hwin family familyDirection).2 = some move := by
              simpa [family, familyDirection,
                profiledRawJointHybridLiteralPrefixAnnotationAdvance] using
                hinstalled
            obtain ⟨member, hmember, hmoveEq⟩ :=
              profiledRawJointLeftLiteralPrefixMoveOption_spec A strategy hwin
                family familyDirection move (by
                  simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                    using hoption)
            right
            exact ⟨.common world, old, .strict actual, family,
              familyDirection, member, hmember, hsource, rfl, (by
                intro current hcurrent currentMember hcurrentMember row past
                  input
                have hstate :
                    (ProfiledRawJointHybridSemanticState.common world).step A
                        (.strict actual) = .oneSided current :=
                  hsource.trans hcurrent
                cases hside : actual.side with
                | right =>
                    have hfamily := congrArg
                      ProfiledRawJointOneSidedSemanticState.family
                      (ProfiledRawJointHybridSemanticState.oneSided.inj hstate)
                    simp [profiledRawJointCommonExitState, hside] at hfamily
                    rw [ProfiledRawJointOneSidedSemanticState.step_code]
                    change
                      profiledRawJointOneSidedNext A (current.code A)
                          (current.move A)
                          (profiledRawJointUnitLeftActualDirection
                            (In₁ := In₁) (In₂ := In₂) row past input) = _
                    simp only [ProfiledRawJointOneSidedSemanticState.code,
                      ProfiledRawJointOneSidedSemanticState.move]
                    rw [← hfamily]
                    exact
                      profiledRawJointLeftSibling_oneSidedNext_eq_false A
                        family familyDirection true row past input
                | left =>
                    have hfamily := congrArg
                      ProfiledRawJointOneSidedSemanticState.family
                      (ProfiledRawJointHybridSemanticState.oneSided.inj hstate)
                    simp [profiledRawJointCommonExitState, hside] at hfamily
                    rw [← hfamily] at hcurrentMember
                    simp at hcurrentMember), hmoveEq⟩
    | oneSided parentState =>
        cases direction with
        | simultaneous input =>
            simp [profiledRawJointHybridLiteralPrefixAnnotationAdvance,
              profiledRawJointHybridInitialLiteralPrefixAnnotation] at hinstalled
        | strict actual =>
            let family := parentState.family
            let familyDirection := actual.direction
            have hoption :
                (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy
                  hwin family familyDirection).2 = some move := by
              simpa [family, familyDirection,
                profiledRawJointHybridLiteralPrefixAnnotationAdvance] using
                hinstalled
            obtain ⟨member, hmember, hmoveEq⟩ :=
              profiledRawJointLeftLiteralPrefixMoveOption_spec A strategy hwin
                family familyDirection move (by
                  simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                    using hoption)
            right
            exact ⟨.oneSided parentState, old, .strict actual, family,
              familyDirection, member, hmember, hsource, rfl, (by
                intro current hcurrent currentMember hcurrentMember row past
                  input
                have hstate :
                    (ProfiledRawJointHybridSemanticState.oneSided parentState
                      ).step A (.strict actual) = .oneSided current :=
                  hsource.trans hcurrent
                cases hside : actual.side with
                | right =>
                    have hfamily := congrArg
                      ProfiledRawJointOneSidedSemanticState.family
                      (ProfiledRawJointHybridSemanticState.oneSided.inj hstate)
                    simp [ProfiledRawJointOneSidedSemanticState.step, hside]
                      at hfamily
                    rw [ProfiledRawJointOneSidedSemanticState.step_code]
                    change
                      profiledRawJointOneSidedNext A (current.code A)
                          (current.move A)
                          (profiledRawJointUnitLeftActualDirection
                            (In₁ := In₁) (In₂ := In₂) row past input) = _
                    simp only [ProfiledRawJointOneSidedSemanticState.code,
                      ProfiledRawJointOneSidedSemanticState.move]
                    rw [← hfamily]
                    exact
                      profiledRawJointLeftSibling_oneSidedNext_eq_false A
                        family familyDirection true row past input
                | left =>
                    have hfamily := congrArg
                      ProfiledRawJointOneSidedSemanticState.family
                      (ProfiledRawJointHybridSemanticState.oneSided.inj hstate)
                    simp [ProfiledRawJointOneSidedSemanticState.step, hside]
                      at hfamily
                    rw [← hfamily] at hcurrentMember
                    simp at hcurrentMember), hmoveEq⟩
    | dead =>
        cases direction <;>
          simp [profiledRawJointHybridLiteralPrefixAnnotationAdvance,
            profiledRawJointHybridInitialLiteralPrefixAnnotation] at hinstalled

end

end DetParityAutomaton

end DistributedSynthesis
