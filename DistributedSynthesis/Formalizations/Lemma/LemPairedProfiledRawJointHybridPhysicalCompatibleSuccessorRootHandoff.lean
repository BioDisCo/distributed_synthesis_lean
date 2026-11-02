/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridLeaderFreeShadowCarrier
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointHybridExactRootGuard

/-!
# Finite common-root handoff to the compatible phase-live overlay

The compatible recurrent carrier starts one whole-block transition after the
common root.  This file isolates that exceptional front stage.  First it
extracts, once from the fixed compatible policy, the literal common move at
`policy.run []`; the already proved exact-right and exact-left controllers for
that move are therefore fixed before an environment is quantified.  Second it
constructs the finite phase-live overlay seed at any retained successor key.

The remaining model interface is intentionally small.  For each actual first
block, the fixed front stage must provide (1) the exact same-policy target
transition selected by its exact controller and (2) equality of the physical
prefix minimum with the selected target root.  Those two facts build the
existing `SuccessorInitialExit` and the recurrent overlay seed in one arrow.

Sides and roots occur only in proof-side witnesses.  Neither exact controller
nor either endpoint seed receives a graph orientation, leader bit, or
strict-leader bit.
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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatibleState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin initial

private abbrev SuccessorTarget
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A strategy hwin
    initial

private abbrev LeaderFreeCommonControl :=
  ProfiledRawJointHybridCommonControl A strategy hwin

/-! ## The fixed common move and its two exact finite controllers -/

/-- One once-chosen inversion of the compatible policy root.  In contrast to
a bare `CommonMoveData`, this bundle retains the parent-linked move, its child
annotation table, and the successor equation from that *same* inversion.
Those fields prevent a later controller target from being paired with an
unrelated compatible-policy key. -/
structure ProfiledRawJointHybridPhysicalCompatibleRootSemanticBundle
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) where
  move : SourceFreeBeliefParentLinkedMove
    (Direction := ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (Move := ProfiledRawJointHybridMove A)
    (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)
  world : ProfiledRawJointCommonBaseWorld A strategy
  rawMove : ProfiledRawJointLambdaFamilyMove A (I := Unit)
  source_code :
    (ProfiledRawJointHybridSemanticState.common world).code A =
      (policy.run []).1.1
  source_move :
    (ProfiledRawJointHybridSemanticState.common world).move A = move.1
  move_raw : move.1 = some rawMove
  current_compatible :
    ProfiledRawJointHybridPhysicalCurrentCompatible A strategy
      (.common world) (policy.run []).1.2
  child_annotations : ∀ direction,
    profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
        (.common world) (policy.run []).1.2 direction =
      move.2 direction
  successor : ∀ direction : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂),
    policy.successor (policy.run [])
        (sourceFreeBeliefParentLinkedNext
          (profiledRawJointHybridNext A) (policy.run []).1 move direction) =
      let childCode := sourceFreeBeliefParentLinkedNext
        (profiledRawJointHybridNext A) (policy.run []).1 move direction
      (childCode,
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)
          (profiledRawJointHybridCodeParityDPA A
            (.common ((profiledRawJointCommonWorldFamily A initial
              ).incidenceCode A)))).step (policy.run []).2 childCode)

/-- The full root inversion exists unconditionally for the selected winning
compatible policy. -/
theorem
    nonempty_profiledRawJointHybridPhysicalCompatibleRootSemanticBundle
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleRootSemanticBundle A strategy
        hwin policy) := by
  have hreachable :=
    profiledRawJointHybridPhysicalCompatiblePolicy_root_reachable A strategy
      hwin policy
  rcases
      exists_profiledRawJointHybridPhysicalCompatibleSemanticSource A strategy
        hwin initial policy (policy.run []) hreachable with
    ⟨move, source, hsourceCode, hsourceMove, hcompatible, hchildren,
      hsuccessor⟩
  have hsourceRoot := hsourceCode
  have hrootCode :=
    profiledRawJointHybridPhysicalCompatiblePolicy_initial_code A strategy
      hwin policy
  rw [hrootCode] at hsourceCode
  cases source with
  | common world =>
      simp only [ProfiledRawJointHybridSemanticState.code,
        ProfiledRawJointHybridSemanticState.move] at hsourceCode hsourceMove
      cases hrawMove : move.1 with
      | none => simp [hrawMove] at hsourceMove
      | some rawMove =>
          exact ⟨{
            move := move
            world := world
            rawMove := rawMove
            source_code := hsourceRoot
            source_move := hsourceMove
            move_raw := hrawMove
            current_compatible := hcompatible
            child_annotations := hchildren
            successor := hsuccessor }⟩
  | oneSided source =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode
  | dead =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode

/-- Select the full semantic inversion once from the fixed policy. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootSemanticBundle
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    ProfiledRawJointHybridPhysicalCompatibleRootSemanticBundle A strategy hwin
      policy :=
  Classical.choice
    (nonempty_profiledRawJointHybridPhysicalCompatibleRootSemanticBundle A
      strategy hwin policy)

/-- Forget only after selection: the exact controllers and the successor
construction now share the same selected semantic root bundle. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootCommonMoveData
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    ProfiledRawJointHybridCommonMoveData A strategy := by
  let bundle :=
    profiledRawJointHybridPhysicalCompatibleRootSemanticBundle A strategy hwin
      policy
  exact {
    incidenceCode :=
      (profiledRawJointCommonWorldFamily A initial).incidenceCode A
    rawMove := bundle.rawMove
    world := bundle.world
    incidence_eq := by
      have hcode := bundle.source_code.trans
        (profiledRawJointHybridPhysicalCompatiblePolicy_initial_code A strategy
          hwin policy)
      exact ProfiledRawJointHybridCode.common.inj hcode
    move_eq := by
      have hmove := bundle.source_move
      rw [bundle.move_raw] at hmove
      exact Option.some.inj hmove }

/-- Backward-compatible existence surface for consumers needing only the
policy-free common data. -/
theorem
    nonempty_profiledRawJointHybridPhysicalCompatibleRootCommonMoveData
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    Nonempty (ProfiledRawJointHybridCommonMoveData A strategy) :=
  ⟨profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy hwin
    policy⟩

/-! ### Same-policy strict children from the retained root inversion -/

/-- The linked strict-right child selected from the very move stored in the
root semantic bundle. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootRightChildCode
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    SourceFreeBeliefParentLinkedCode
      (BeliefCode := ProfiledRawJointHybridCode A)
      (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A) :=
  let bundle :=
    profiledRawJointHybridPhysicalCompatibleRootSemanticBundle A strategy hwin
      policy
  sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)
    (policy.run []).1 bundle.move
    (.strict (profiledRawJointCommonOneRoundStrictRight input))

/-- Strict-left mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootLeftChildCode
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    SourceFreeBeliefParentLinkedCode
      (BeliefCode := ProfiledRawJointHybridCode A)
      (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A) :=
  let bundle :=
    profiledRawJointHybridPhysicalCompatibleRootSemanticBundle A strategy hwin
      policy
  sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)
    (policy.run []).1 bundle.move
    (.strict (profiledRawJointCommonOneRoundStrictLeft input))

/-- The right child code is literally the first component of its successor
under the unchanged compatible policy. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRootRightSuccessor_fst
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    (policy.successor (policy.run [])
      (profiledRawJointHybridPhysicalCompatibleRootRightChildCode A strategy
        hwin policy input)).1 =
      profiledRawJointHybridPhysicalCompatibleRootRightChildCode A strategy
        hwin policy input := by
  let bundle :=
    profiledRawJointHybridPhysicalCompatibleRootSemanticBundle A strategy hwin
      policy
  have h := bundle.successor
    (.strict (profiledRawJointCommonOneRoundStrictRight input))
  exact congrArg Prod.fst h

/-- Left mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRootLeftSuccessor_fst
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    (policy.successor (policy.run [])
      (profiledRawJointHybridPhysicalCompatibleRootLeftChildCode A strategy
        hwin policy input)).1 =
      profiledRawJointHybridPhysicalCompatibleRootLeftChildCode A strategy hwin
        policy input := by
  let bundle :=
    profiledRawJointHybridPhysicalCompatibleRootSemanticBundle A strategy hwin
      policy
  have h := bundle.successor
    (.strict (profiledRawJointCommonOneRoundStrictLeft input))
  exact congrArg Prod.fst h

/-- The exact process-one/right front controller, fixed before the
environment. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootExactRightController
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  profiledRawJointHybridExactRightController A hwin
    (profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy hwin
      policy)

/-- Exact process-two/left mirror, selected from the same common move. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootExactLeftController
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  profiledRawJointHybridExactLeftController A hwin
    (profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy hwin
      policy)

/-! ### Reuse of the executable leader-free common front -/

/-- The policy-free move installed by the already existing leader-free
common/strict shadow table at `control`. -/
noncomputable def
    profiledRawJointHybridLeaderFreeCommonMoveData
    (control : LeaderFreeCommonControl A strategy hwin) :
    ProfiledRawJointHybridCommonMoveData A strategy :=
  ProfiledRawJointHybridCommonInstalledMove.toCommonMoveData A
    (profiledRawJointHybridCommonControlInstalled A strategy hwin control)

/-- The sole index alignment needed to reuse the leader-free shadow's exact
controllers at a compatible-policy root.  It compares finite proof data; it
is not a test available to either endpoint. -/
def ProfiledRawJointHybridPhysicalCompatibleRootCommonMoveAligned
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (control : LeaderFreeCommonControl A strategy hwin) : Prop :=
  profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy hwin
      policy =
    profiledRawJointHybridLeaderFreeCommonMoveData A strategy hwin control

/-! ### Targets read from the fixed exact controllers -/

/-- The literal narrowed record read after a finite right-controller prefix.
The controller, monitor, and installed common move depend only on the fixed
policy; `past` and `input` are proof-side readback data for one environment. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootExactRightRecordAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :=
  let installed :=
    profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy hwin
      policy
  let package := profiledRawJointHybridExactRightPolicy A hwin installed
  let monitor := profiledRawJointHybridExactRightMonitor A installed package
  let controller :=
    profiledRawJointHybridPhysicalCompatibleRootExactRightController A strategy
      hwin policy
  narrowedRecord monitor
    (controller.labelOf (controller.controlAt (senderWord past)))
    (narrowedControl monitor controller.labeledTree past) input

/-- Left-controller mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootExactLeftRecordAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :=
  let installed :=
    profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy hwin
      policy
  let package := profiledRawJointHybridExactLeftPolicy A hwin installed
  let monitor := profiledRawJointHybridExactLeftMonitor A installed package
  let controller :=
    profiledRawJointHybridPhysicalCompatibleRootExactLeftController A strategy
      hwin policy
  narrowedRecord monitor
    (controller.labelOf (controller.controlAt (senderWord past)))
    (narrowedControl monitor controller.labeledTree past) input

/-- Nondependent target-code projection of a fresh exact-right root. -/
noncomputable def profiledRawJointHybridExactRightFreshTargetCode
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (input : In₁ × In₂) : ProfiledRawJointIncidenceCode A (I := Unit) :=
  let package := profiledRawJointHybridExactRightPolicy A hwin installed
  let monitor := profiledRawJointHybridExactRightMonitor A installed package
  let controller := profiledRawJointHybridExactRightController A hwin installed
  ((narrowedRecord monitor (controller.labelOf controller.initial)
    monitor.initial (input.2, input.1)).2.1.target .both).1

/-- Left mirror. -/
noncomputable def profiledRawJointHybridExactLeftFreshTargetCode
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (input : In₁ × In₂) : ProfiledRawJointIncidenceCode A (I := Unit) :=
  let package := profiledRawJointHybridExactLeftPolicy A hwin installed
  let monitor := profiledRawJointHybridExactLeftMonitor A installed package
  let controller := profiledRawJointHybridExactLeftController A hwin installed
  ((narrowedRecord monitor (controller.labelOf controller.initial)
    monitor.initial input).2.1.target .both).1

/-- The nondependent fresh right target is the literal strict-right child of
the same installed common move. -/
theorem profiledRawJointHybridExactRightFreshTargetCode_eq_strictChild
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (input : In₁ × In₂) :
    profiledRawJointHybridExactRightFreshTargetCode A strategy hwin installed
        input =
      profiledRawJointOneSidedNext A installed.incidenceCode installed.rawMove
        (profiledRawJointCommonOneRoundStrictRight input) := by
  simpa [profiledRawJointHybridExactRightFreshTargetCode] using
    profiledRawJointHybridExactRightController_root_strictChild A hwin
      installed (input.2, input.1)

/-- Left mirror. -/
theorem profiledRawJointHybridExactLeftFreshTargetCode_eq_strictChild
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (input : In₁ × In₂) :
    profiledRawJointHybridExactLeftFreshTargetCode A strategy hwin installed
        input =
      profiledRawJointOneSidedNext A installed.incidenceCode installed.rawMove
        (profiledRawJointCommonOneRoundStrictLeft input) := by
  simpa [profiledRawJointHybridExactLeftFreshTargetCode] using
    profiledRawJointHybridExactLeftController_root_strictChild A hwin installed
      input

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointCommonActualDirection_oneRoundStrictRight
    (input : In₁ × In₂) :
    profiledRawJointCommonActualDirection
        (profiledRawJointCommonOneRoundStrictRight input) =
      profiledRawJointCommonOneRoundStrictRight input := by
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointCommonActualDirection_oneRoundStrictLeft
    (input : In₁ × In₂) :
    profiledRawJointCommonActualDirection
        (profiledRawJointCommonOneRoundStrictLeft input) =
      profiledRawJointCommonOneRoundStrictLeft input := by
  rfl

/-- The right target emitted by the exact controller is literally the public
component of the same parent-linked child used for the compatible-policy
successor. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRootRightChildCode_fst
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    (profiledRawJointHybridPhysicalCompatibleRootRightChildCode A strategy hwin
      policy input).1 =
      .oneSided
        (profiledRawJointHybridExactRightFreshTargetCode A strategy hwin
          (profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A
            strategy hwin policy) input) := by
  let bundle :=
    profiledRawJointHybridPhysicalCompatibleRootSemanticBundle A strategy hwin
      policy
  let installed :=
    profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy hwin
      policy
  let direction : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂) :=
    .strict (profiledRawJointCommonOneRoundStrictRight input)
  calc
    (profiledRawJointHybridPhysicalCompatibleRootRightChildCode A strategy hwin
        policy input).1 =
        profiledRawJointHybridNext A
          ((ProfiledRawJointHybridSemanticState.common bundle.world).code A)
          ((ProfiledRawJointHybridSemanticState.common bundle.world).move A)
          direction := by
      change
        profiledRawJointHybridNext A (policy.run []).1.1 bundle.move.1
            direction = _
      rw [bundle.source_code, bundle.source_move]
    _ = ((ProfiledRawJointHybridSemanticState.common bundle.world).step A
          direction).code A :=
      (ProfiledRawJointHybridSemanticState.step_code A
        (.common bundle.world) direction).symm
    _ = .oneSided
          (profiledRawJointOneSidedNext A installed.incidenceCode
            installed.rawMove
            (profiledRawJointCommonOneRoundStrictRight input)) := by
      change
        ProfiledRawJointHybridCode.oneSided
            ((profiledRawJointCommonExitState A bundle.world
              (profiledRawJointCommonOneRoundStrictRight input)).code A) = _
      rw [profiledRawJointCommonExitState_code]
      have hworld : installed.world = bundle.world := rfl
      rw [← hworld, installed.incidence_eq, installed.move_eq]
      rfl
    _ = .oneSided
          (profiledRawJointHybridExactRightFreshTargetCode A strategy hwin
            installed input) := by
      rw [profiledRawJointHybridExactRightFreshTargetCode_eq_strictChild]

/-- Left mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRootLeftChildCode_fst
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    (profiledRawJointHybridPhysicalCompatibleRootLeftChildCode A strategy hwin
      policy input).1 =
      .oneSided
        (profiledRawJointHybridExactLeftFreshTargetCode A strategy hwin
          (profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A
            strategy hwin policy) input) := by
  let bundle :=
    profiledRawJointHybridPhysicalCompatibleRootSemanticBundle A strategy hwin
      policy
  let installed :=
    profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy hwin
      policy
  let direction : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂) :=
    .strict (profiledRawJointCommonOneRoundStrictLeft input)
  calc
    (profiledRawJointHybridPhysicalCompatibleRootLeftChildCode A strategy hwin
        policy input).1 =
        profiledRawJointHybridNext A
          ((ProfiledRawJointHybridSemanticState.common bundle.world).code A)
          ((ProfiledRawJointHybridSemanticState.common bundle.world).move A)
          direction := by
      change
        profiledRawJointHybridNext A (policy.run []).1.1 bundle.move.1
            direction = _
      rw [bundle.source_code, bundle.source_move]
    _ = ((ProfiledRawJointHybridSemanticState.common bundle.world).step A
          direction).code A :=
      (ProfiledRawJointHybridSemanticState.step_code A
        (.common bundle.world) direction).symm
    _ = .oneSided
          (profiledRawJointOneSidedNext A installed.incidenceCode
            installed.rawMove
            (profiledRawJointCommonOneRoundStrictLeft input)) := by
      change
        ProfiledRawJointHybridCode.oneSided
            ((profiledRawJointCommonExitState A bundle.world
              (profiledRawJointCommonOneRoundStrictLeft input)).code A) = _
      rw [profiledRawJointCommonExitState_code]
      have hworld : installed.world = bundle.world := rfl
      rw [← hworld, installed.incidence_eq, installed.move_eq]
      rfl
    _ = .oneSided
          (profiledRawJointHybridExactLeftFreshTargetCode A strategy hwin
            installed input) := by
      rw [profiledRawJointHybridExactLeftFreshTargetCode_eq_strictChild]

/-! ### Canonical live roots of the two distinct target candidates -/

/-- Left slot of the strict-right candidate, computed by the same exact
activation used to prove the controller guard. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootRightTargetSlot
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) : ProfiledRawLeftSlot A :=
  let installed :=
    profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy hwin
      policy
  let activation :=
    profiledRawJointHybridExactRightActivation A hwin installed
  profiledRawRightChildSlot A (installed.world.procOneSlot A)
    activation.lambda .both [] (input.2, input.1)

/-- Right slot of the strict-left candidate. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootLeftTargetSlot
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) : ProfiledRawRightSlot A :=
  let installed :=
    profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy hwin
      policy
  let activation :=
    profiledRawJointHybridExactLeftActivation A hwin installed
  profiledRawLeftChildSlot A (installed.world.procTwoSlot A)
    activation.lambda .both [] input

/-- The fresh exact-right target is live at the activation's crossed slot. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRootRightTarget_live
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    (profiledRawJointHybridExactRightFreshTargetCode A strategy hwin
      (profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy
        hwin policy) input).family.left () =
      some
        (profiledRawJointHybridPhysicalCompatibleRootRightTargetSlot A strategy
          hwin policy input) := by
  let installed :=
    profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy hwin
      policy
  let package := profiledRawJointHybridExactRightPolicy A hwin installed
  let activation := profiledRawJointHybridExactRightActivation A hwin installed
  have hactive := activation.target_active_slot .both [] (input.2, input.1)
  rw [profiledRawJointHybridExactRightFreshTargetCode_eq_strictChild]
  change
    (profiledRawJointOneSidedNext A
      ((profiledRawJointRootPinnedSelectedSource A strategy
        (installed.world.oneSidedState A .right)
        (profiledRawJointHybridExactRightRootPredicate A installed)
        package).code A)
      ((profiledRawJointRootPinnedSelectedSource A strategy
        (installed.world.oneSidedState A .right)
        (profiledRawJointHybridExactRightRootPredicate A installed)
        package).move A)
      (profiledRawJointUnitRightActualDirection
        (In₁ := In₁) (In₂ := In₂) .both [] (input.2, input.1))).family.left
      () = _ at hactive
  rw [profiledRawJointRootPinnedSelectedSource_code A strategy,
    profiledRawJointHybridExactRight_selectedSource_move A installed package,
    profiledRawJointHybridExactRight_literal_strictChild A installed input] at hactive
  exact hactive

/-- Left mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRootLeftTarget_live
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    (profiledRawJointHybridExactLeftFreshTargetCode A strategy hwin
      (profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy
        hwin policy) input).family.right () =
      some
        (profiledRawJointHybridPhysicalCompatibleRootLeftTargetSlot A strategy
          hwin policy input) := by
  let installed :=
    profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy hwin
      policy
  let package := profiledRawJointHybridExactLeftPolicy A hwin installed
  let activation := profiledRawJointHybridExactLeftActivation A hwin installed
  have hactive := activation.target_active_slot .both [] input
  rw [profiledRawJointHybridExactLeftFreshTargetCode_eq_strictChild]
  change
    (profiledRawJointOneSidedNext A
      ((profiledRawJointRootPinnedSelectedSource A strategy
        (installed.world.oneSidedState A .left)
        (profiledRawJointHybridExactLeftRootPredicate A installed)
        package).code A)
      ((profiledRawJointRootPinnedSelectedSource A strategy
        (installed.world.oneSidedState A .left)
        (profiledRawJointHybridExactLeftRootPredicate A installed)
        package).move A)
      (profiledRawJointUnitLeftActualDirection
        (In₁ := In₁) (In₂ := In₂) .both [] input)).family.right () = _ at hactive
  rw [profiledRawJointRootPinnedSelectedSource_code A strategy,
    profiledRawJointHybridExactLeft_selectedSource_move A installed package,
    profiledRawJointHybridExactLeft_literal_strictChild A installed input] at hactive
  exact hactive

/-- The same strict-right edge installs a concrete left physical move in the
linked child annotation.  This is the new `child_move` field required by the
strengthened compatible transition interface. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRootRightChild_move
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      (profiledRawJointHybridPhysicalCompatibleRootRightChildCode A strategy
        hwin policy input).2.2 = some move := by
  let bundle :=
    profiledRawJointHybridPhysicalCompatibleRootSemanticBundle A strategy hwin
      policy
  let target :=
    profiledRawJointHybridExactRightFreshTargetCode A strategy hwin
      (profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy
        hwin policy) input
  let slot :=
    profiledRawJointHybridPhysicalCompatibleRootRightTargetSlot A strategy hwin
      policy input
  let actual := profiledRawJointCommonOneRoundStrictRight input
  have hsemanticChild :
      ((ProfiledRawJointHybridSemanticState.common bundle.world).step A
        (.strict actual)).code A = .oneSided target := by
    calc
      ((ProfiledRawJointHybridSemanticState.common bundle.world).step A
          (.strict actual)).code A =
          profiledRawJointHybridNext A
            ((ProfiledRawJointHybridSemanticState.common bundle.world).code A)
            ((ProfiledRawJointHybridSemanticState.common bundle.world).move A)
            (.strict actual) :=
        ProfiledRawJointHybridSemanticState.step_code A (.common bundle.world)
          (.strict actual)
      _ =
          (profiledRawJointHybridPhysicalCompatibleRootRightChildCode A
            strategy hwin policy input).1 := by
        change
          profiledRawJointHybridNext A
              ((ProfiledRawJointHybridSemanticState.common bundle.world).code A)
              ((ProfiledRawJointHybridSemanticState.common bundle.world).move A)
              (.strict actual) =
            profiledRawJointHybridNext A (policy.run []).1.1 bundle.move.1
              (.strict actual)
        rw [bundle.source_code, bundle.source_move]
      _ = .oneSided target :=
        profiledRawJointHybridPhysicalCompatibleRootRightChildCode_fst A
          strategy hwin policy input
  obtain ⟨nextMove, hnextMove⟩ :=
    exists_profiledRawJointHybridPhysicalCompatible_leftMove_of_strictRight A
      strategy hwin (.common bundle.world) (policy.run []).1.2 actual target slot
        rfl hsemanticChild
        (profiledRawJointHybridPhysicalCompatibleRootRightTarget_live A strategy
          hwin policy input)
  refine ⟨nextMove, ?_⟩
  change (bundle.move.2 (.strict actual)).2 = some nextMove
  rw [← bundle.child_annotations (.strict actual)]
  exact hnextMove

/-- Strict-left/right-move mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRootLeftChild_move
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      (profiledRawJointHybridPhysicalCompatibleRootLeftChildCode A strategy hwin
        policy input).2.1 = some move := by
  let bundle :=
    profiledRawJointHybridPhysicalCompatibleRootSemanticBundle A strategy hwin
      policy
  let target :=
    profiledRawJointHybridExactLeftFreshTargetCode A strategy hwin
      (profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy
        hwin policy) input
  let slot :=
    profiledRawJointHybridPhysicalCompatibleRootLeftTargetSlot A strategy hwin
      policy input
  let actual := profiledRawJointCommonOneRoundStrictLeft input
  have hsemanticChild :
      ((ProfiledRawJointHybridSemanticState.common bundle.world).step A
        (.strict actual)).code A = .oneSided target := by
    calc
      ((ProfiledRawJointHybridSemanticState.common bundle.world).step A
          (.strict actual)).code A =
          profiledRawJointHybridNext A
            ((ProfiledRawJointHybridSemanticState.common bundle.world).code A)
            ((ProfiledRawJointHybridSemanticState.common bundle.world).move A)
            (.strict actual) :=
        ProfiledRawJointHybridSemanticState.step_code A (.common bundle.world)
          (.strict actual)
      _ =
          (profiledRawJointHybridPhysicalCompatibleRootLeftChildCode A strategy
            hwin policy input).1 := by
        change
          profiledRawJointHybridNext A
              ((ProfiledRawJointHybridSemanticState.common bundle.world).code A)
              ((ProfiledRawJointHybridSemanticState.common bundle.world).move A)
              (.strict actual) =
            profiledRawJointHybridNext A (policy.run []).1.1 bundle.move.1
              (.strict actual)
        rw [bundle.source_code, bundle.source_move]
      _ = .oneSided target :=
        profiledRawJointHybridPhysicalCompatibleRootLeftChildCode_fst A strategy
          hwin policy input
  obtain ⟨nextMove, hnextMove⟩ :=
    exists_profiledRawJointHybridPhysicalCompatible_rightMove_of_strictLeft A
      strategy hwin (.common bundle.world) (policy.run []).1.2 actual target slot
        rfl hsemanticChild
        (profiledRawJointHybridPhysicalCompatibleRootLeftTarget_live A strategy
          hwin policy input)
  refine ⟨nextMove, ?_⟩
  change (bundle.move.2 (.strict actual)).1 = some nextMove
  rw [← bundle.child_annotations (.strict actual)]
  exact hnextMove

/-! ### The two exact same-policy successor candidates -/

/-- The strict-right candidate retains both the exact fresh bare target and
the successor of the *same* parent-linked child.  No post-hoc key is chosen. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootRightTarget
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) : SuccessorTarget A strategy hwin initial :=
  (profiledRawJointHybridExactRightFreshTargetCode A strategy hwin
      (profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy
        hwin policy) input,
    (.both,
      policy.successor (policy.run [])
        (profiledRawJointHybridPhysicalCompatibleRootRightChildCode A strategy
          hwin policy input)))

/-- Strict-left mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootLeftTarget
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) : SuccessorTarget A strategy hwin initial :=
  (profiledRawJointHybridExactLeftFreshTargetCode A strategy hwin
      (profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy
        hwin policy) input,
    (.both,
      policy.successor (policy.run [])
        (profiledRawJointHybridPhysicalCompatibleRootLeftChildCode A strategy
          hwin policy input)))

/-- The retained right-candidate key is connected to the common root by the
literal strict-right child, including its physical left-sibling move. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootRightTransition
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A strategy hwin
      policy (policy.run [])
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin
          (profiledRawJointHybridPhysicalCompatibleRootRightTarget A strategy
            hwin policy input))
        .left
        (.inr
          (profiledRawJointHybridPhysicalCompatibleRootRightTargetSlot A
            strategy hwin policy input)) where
  childCode :=
    profiledRawJointHybridPhysicalCompatibleRootRightChildCode A strategy hwin
      policy input
  successor := rfl
  child_oneSided := by
    refine
      ⟨profiledRawJointHybridExactRightFreshTargetCode A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy
          hwin policy) input, ?_⟩
    change
      (policy.successor (policy.run [])
        (profiledRawJointHybridPhysicalCompatibleRootRightChildCode A strategy
          hwin policy input)).1.1 = _
    rw [profiledRawJointHybridPhysicalCompatibleRootRightSuccessor_fst A
      strategy hwin policy input]
    exact
      profiledRawJointHybridPhysicalCompatibleRootRightChildCode_fst A strategy
        hwin policy input
  child_move := by
    change ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      (policy.successor (policy.run [])
        (profiledRawJointHybridPhysicalCompatibleRootRightChildCode A strategy
          hwin policy input)).1.2.2 = some move
    rw [profiledRawJointHybridPhysicalCompatibleRootRightSuccessor_fst A
      strategy hwin policy input]
    exact
      profiledRawJointHybridPhysicalCompatibleRootRightChild_move A strategy
        hwin policy input
  child_live := by
    change
      profiledRawJointHybridCurrentSlots A .left
          (policy.successor (policy.run [])
            (profiledRawJointHybridPhysicalCompatibleRootRightChildCode A
              strategy hwin policy input)).1.1 () =
        some
          (.inr
            (profiledRawJointHybridPhysicalCompatibleRootRightTargetSlot A
              strategy hwin policy input))
    rw [profiledRawJointHybridPhysicalCompatibleRootRightSuccessor_fst A
      strategy hwin policy input]
    rw [profiledRawJointHybridPhysicalCompatibleRootRightChildCode_fst A
      strategy hwin policy input]
    simp only [profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots, Option.map_eq_map]
    rw [profiledRawJointHybridPhysicalCompatibleRootRightTarget_live A strategy
      hwin policy input]
    rfl

/-- Strict-left mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootLeftTransition
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A strategy hwin
      policy (policy.run [])
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin
          (profiledRawJointHybridPhysicalCompatibleRootLeftTarget A strategy
            hwin policy input))
        .right
        (.inl
          (profiledRawJointHybridPhysicalCompatibleRootLeftTargetSlot A strategy
            hwin policy input)) where
  childCode :=
    profiledRawJointHybridPhysicalCompatibleRootLeftChildCode A strategy hwin
      policy input
  successor := rfl
  child_oneSided := by
    refine
      ⟨profiledRawJointHybridExactLeftFreshTargetCode A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy
          hwin policy) input, ?_⟩
    change
      (policy.successor (policy.run [])
        (profiledRawJointHybridPhysicalCompatibleRootLeftChildCode A strategy
          hwin policy input)).1.1 = _
    rw [profiledRawJointHybridPhysicalCompatibleRootLeftSuccessor_fst A
      strategy hwin policy input]
    exact
      profiledRawJointHybridPhysicalCompatibleRootLeftChildCode_fst A strategy
        hwin policy input
  child_move := by
    change ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      (policy.successor (policy.run [])
        (profiledRawJointHybridPhysicalCompatibleRootLeftChildCode A strategy
          hwin policy input)).1.2.1 = some move
    rw [profiledRawJointHybridPhysicalCompatibleRootLeftSuccessor_fst A
      strategy hwin policy input]
    exact
      profiledRawJointHybridPhysicalCompatibleRootLeftChild_move A strategy hwin
        policy input
  child_live := by
    change
      profiledRawJointHybridCurrentSlots A .right
          (policy.successor (policy.run [])
            (profiledRawJointHybridPhysicalCompatibleRootLeftChildCode A strategy
              hwin policy input)).1.1 () =
        some
          (.inl
            (profiledRawJointHybridPhysicalCompatibleRootLeftTargetSlot A
              strategy hwin policy input))
    rw [profiledRawJointHybridPhysicalCompatibleRootLeftSuccessor_fst A
      strategy hwin policy input]
    rw [profiledRawJointHybridPhysicalCompatibleRootLeftChildCode_fst A strategy
      hwin policy input]
    simp only [profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots, Option.map_eq_map]
    rw [profiledRawJointHybridPhysicalCompatibleRootLeftTarget_live A strategy
      hwin policy input]
    rfl

/-- The canonical right candidate has both the crossed bare root and the exact
same-policy successor transition. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootRightTargetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
      policy (policy.run [])
        (profiledRawJointHybridPhysicalCompatibleRootRightTarget A strategy
          hwin policy input)
        .left
        (.inr
          (profiledRawJointHybridPhysicalCompatibleRootRightTargetSlot A
            strategy hwin policy input)) where
  root_at := .right _ _
    (profiledRawJointHybridPhysicalCompatibleRootRightTarget_live A strategy
      hwin policy input)
  transition :=
    ⟨profiledRawJointHybridPhysicalCompatibleRootRightTransition A strategy hwin
      policy input⟩

/-- Canonical left-candidate mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootLeftTargetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
      policy (policy.run [])
        (profiledRawJointHybridPhysicalCompatibleRootLeftTarget A strategy hwin
          policy input)
        .right
        (.inl
          (profiledRawJointHybridPhysicalCompatibleRootLeftTargetSlot A strategy
            hwin policy input)) where
  root_at := .left _ _
    (profiledRawJointHybridPhysicalCompatibleRootLeftTarget_live A strategy hwin
      policy input)
  transition :=
    ⟨profiledRawJointHybridPhysicalCompatibleRootLeftTransition A strategy hwin
      policy input⟩

/-- At an aligned common control the target code emitted by the
policy-specific right controller at its fresh root is the target code stored
by the executable leader-free shadow table.  We compare the nondependent
target projection: the two full records have receiver-output types indexed by
their (propositionally equal) installed moves. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRootExactRightTargetAt_nil_eq_shadow
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (control : LeaderFreeCommonControl A strategy hwin)
    (haligned :
      ProfiledRawJointHybridPhysicalCompatibleRootCommonMoveAligned A strategy
        hwin policy control)
    (input : In₁ × In₂) :
    ((profiledRawJointHybridPhysicalCompatibleRootExactRightRecordAt A strategy
      hwin policy [] (input.2, input.1)).2.1.target .both).1 =
      ((profiledRawJointHybridShadowRightRootRecord A strategy hwin control
        input).2.1.target .both).1 := by
  change
    profiledRawJointHybridExactRightFreshTargetCode A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy
          hwin policy) input =
      profiledRawJointHybridExactRightFreshTargetCode A strategy hwin
        (profiledRawJointHybridLeaderFreeCommonMoveData A strategy hwin control)
        input
  exact congrArg
    (fun installed ↦
      profiledRawJointHybridExactRightFreshTargetCode A strategy hwin installed
        input)
    haligned

/-- Left mirror of the root-record reuse theorem. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRootExactLeftTargetAt_nil_eq_shadow
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (control : LeaderFreeCommonControl A strategy hwin)
    (haligned :
      ProfiledRawJointHybridPhysicalCompatibleRootCommonMoveAligned A strategy
        hwin policy control)
    (input : In₁ × In₂) :
    ((profiledRawJointHybridPhysicalCompatibleRootExactLeftRecordAt A strategy
      hwin policy [] input).2.1.target .both).1 =
      ((profiledRawJointHybridShadowLeftRootRecord A strategy hwin control
        input).2.1.target .both).1 := by
  change
    profiledRawJointHybridExactLeftFreshTargetCode A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleRootCommonMoveData A strategy
          hwin policy) input =
      profiledRawJointHybridExactLeftFreshTargetCode A strategy hwin
        (profiledRawJointHybridLeaderFreeCommonMoveData A strategy hwin control)
        input
  exact congrArg
    (fun installed ↦
      profiledRawJointHybridExactLeftFreshTargetCode A strategy hwin installed
        input)
    haligned

/-- A decorated compatible target is exactly the row selected by one finite
prefix of the fixed exact-right controller. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleRootExactRightTargetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial) where
  past : List (In₂ × In₁)
  input : In₂ × In₁
  row : PairedEntryRow
  row_eq : target.2.1 = row
  target_eq :
    ((profiledRawJointHybridPhysicalCompatibleRootExactRightRecordAt A strategy
      hwin policy past input).2.1.target row).1 = target.1

/-- Exact-left mirror. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleRootExactLeftTargetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial) where
  past : List (In₁ × In₂)
  input : In₁ × In₂
  row : PairedEntryRow
  row_eq : target.2.1 = row
  target_eq :
    ((profiledRawJointHybridPhysicalCompatibleRootExactLeftRecordAt A strategy
      hwin policy past input).2.1.target row).1 = target.1

/-- Proof-side classification of the target emitted by the fixed front
controller.  A right physical block crosses to a left root and conversely.
The side is an index of the witness, never an executable controller input. -/
inductive
    ProfiledRawJointHybridPhysicalCompatibleRootExactControllerTargetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    SuccessorTarget A strategy hwin initial → IndexedLineageSide →
      ProfiledRawJointThreadRoot A → Type _ where
  | right (target : SuccessorTarget A strategy hwin initial)
      (slot : ProfiledRawLeftSlot A)
      (emitted :
        ProfiledRawJointHybridPhysicalCompatibleRootExactRightTargetAt A
          strategy hwin policy target)
      (live : target.1.family.left () = some slot) :
      ProfiledRawJointHybridPhysicalCompatibleRootExactControllerTargetAt
        policy target .left (.inr slot)
  | left (target : SuccessorTarget A strategy hwin initial)
      (slot : ProfiledRawRightSlot A)
      (emitted :
        ProfiledRawJointHybridPhysicalCompatibleRootExactLeftTargetAt A
          strategy hwin policy target)
      (live : target.1.family.right () = some slot) :
      ProfiledRawJointHybridPhysicalCompatibleRootExactControllerTargetAt
        policy target .right (.inl slot)

/-! ### The exact two-candidate front relation -/

/-- The fixed exact-right front literally emits the canonical right candidate. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootRightControllerTarget
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridPhysicalCompatibleRootExactControllerTargetAt A
      strategy hwin policy
        (profiledRawJointHybridPhysicalCompatibleRootRightTarget A strategy
          hwin policy input)
        .left
        (.inr
          (profiledRawJointHybridPhysicalCompatibleRootRightTargetSlot A
            strategy hwin policy input)) :=
  .right
    (profiledRawJointHybridPhysicalCompatibleRootRightTarget A strategy hwin
      policy input)
    (profiledRawJointHybridPhysicalCompatibleRootRightTargetSlot A strategy hwin
      policy input)
    { past := []
      input := (input.2, input.1)
      row := .both
      row_eq := rfl
      target_eq := rfl }
    (profiledRawJointHybridPhysicalCompatibleRootRightTarget_live A strategy
      hwin policy input)

/-- Exact-left mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootLeftControllerTarget
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridPhysicalCompatibleRootExactControllerTargetAt A
      strategy hwin policy
        (profiledRawJointHybridPhysicalCompatibleRootLeftTarget A strategy hwin
          policy input)
        .right
        (.inl
          (profiledRawJointHybridPhysicalCompatibleRootLeftTargetSlot A strategy
            hwin policy input)) :=
  .left
    (profiledRawJointHybridPhysicalCompatibleRootLeftTarget A strategy hwin
      policy input)
    (profiledRawJointHybridPhysicalCompatibleRootLeftTargetSlot A strategy hwin
      policy input)
    { past := []
      input := input
      row := .both
      row_eq := rfl
      target_eq := rfl }
    (profiledRawJointHybridPhysicalCompatibleRootLeftTarget_live A strategy hwin
      policy input)

/-- The honest common-root output is a relation with two exact candidates.
No equality between their target codes or compatible successor keys is
asserted.  A proof-side cut may select either whole candidate later. -/
structure ProfiledRawJointHybridPhysicalCompatibleRootCandidatePair
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) : Type _ where
  right_controller :
    ProfiledRawJointHybridPhysicalCompatibleRootExactControllerTargetAt A
      strategy hwin policy
        (profiledRawJointHybridPhysicalCompatibleRootRightTarget A strategy
          hwin policy input)
        .left
        (.inr
          (profiledRawJointHybridPhysicalCompatibleRootRightTargetSlot A
            strategy hwin policy input))
  right_transition :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
      policy (policy.run [])
        (profiledRawJointHybridPhysicalCompatibleRootRightTarget A strategy
          hwin policy input)
        .left
        (.inr
          (profiledRawJointHybridPhysicalCompatibleRootRightTargetSlot A
            strategy hwin policy input))
  left_controller :
    ProfiledRawJointHybridPhysicalCompatibleRootExactControllerTargetAt A
      strategy hwin policy
        (profiledRawJointHybridPhysicalCompatibleRootLeftTarget A strategy hwin
          policy input)
        .right
        (.inl
          (profiledRawJointHybridPhysicalCompatibleRootLeftTargetSlot A strategy
            hwin policy input))
  left_transition :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
      policy (policy.run [])
        (profiledRawJointHybridPhysicalCompatibleRootLeftTarget A strategy hwin
          policy input)
        .right
        (.inl
          (profiledRawJointHybridPhysicalCompatibleRootLeftTargetSlot A strategy
            hwin policy input))

/-- Canonical two-candidate relation produced entirely before any environment
or physical orientation is supplied. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootCandidatePair
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridPhysicalCompatibleRootCandidatePair A strategy hwin
      policy input where
  right_controller :=
    profiledRawJointHybridPhysicalCompatibleRootRightControllerTarget A strategy
      hwin policy input
  right_transition :=
    profiledRawJointHybridPhysicalCompatibleRootRightTargetAt A strategy hwin
      policy input
  left_controller :=
    profiledRawJointHybridPhysicalCompatibleRootLeftControllerTarget A strategy
      hwin policy input
  left_transition :=
    profiledRawJointHybridPhysicalCompatibleRootLeftTargetAt A strategy hwin
      policy input

/-- The executable leader-free right shadow supplies the proof-side exact
right target witness whenever its installed move is the compatible root move.
No right/left controller product is constructed: the target projection is
transported through the common-move alignment theorem above. -/
def
    profiledRawJointHybridPhysicalCompatibleRootExactRightTargetAt_of_leaderFree
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (control : LeaderFreeCommonControl A strategy hwin)
    (haligned :
      ProfiledRawJointHybridPhysicalCompatibleRootCommonMoveAligned A strategy
        hwin policy control)
    (input : In₁ × In₂)
    (target : SuccessorTarget A strategy hwin initial)
    (row_eq : target.2.1 = .both)
    (target_eq :
      ((profiledRawJointHybridShadowRightRootRecord A strategy hwin control
        input).2.1.target .both).1 = target.1) :
    ProfiledRawJointHybridPhysicalCompatibleRootExactRightTargetAt A strategy
      hwin policy target where
  past := []
  input := (input.2, input.1)
  row := .both
  row_eq := row_eq
  target_eq :=
    (profiledRawJointHybridPhysicalCompatibleRootExactRightTargetAt_nil_eq_shadow
      A strategy hwin policy control haligned input).trans target_eq

/-- Left-shadow mirror. -/
def
    profiledRawJointHybridPhysicalCompatibleRootExactLeftTargetAt_of_leaderFree
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (control : LeaderFreeCommonControl A strategy hwin)
    (haligned :
      ProfiledRawJointHybridPhysicalCompatibleRootCommonMoveAligned A strategy
        hwin policy control)
    (input : In₁ × In₂)
    (target : SuccessorTarget A strategy hwin initial)
    (row_eq : target.2.1 = .both)
    (target_eq :
      ((profiledRawJointHybridShadowLeftRootRecord A strategy hwin control
        input).2.1.target .both).1 = target.1) :
    ProfiledRawJointHybridPhysicalCompatibleRootExactLeftTargetAt A strategy
      hwin policy target where
  past := []
  input := input
  row := .both
  row_eq := row_eq
  target_eq :=
    (profiledRawJointHybridPhysicalCompatibleRootExactLeftTargetAt_nil_eq_shadow
      A strategy hwin policy control haligned input).trans target_eq

/-! ## A phase-free finite overlay seed -/

/-- All finite data needed to initialize both endpoint overlays at one
retained compatible key.  Phases are deliberately absent: each endpoint adds
its own locally computed phase bit when the front-stage handoff fires. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) where
  target : SuccessorTarget A strategy hwin initial
  state : CompatibleState A strategy hwin initial
  oneBaseShared :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwner A strategy
      hwin policy
  oneBasePayload :
    ProfiledRawJointHybridPhysicalCompatibleFrontierOnePayload A strategy hwin
      (initial := initial)
  twoBaseShared :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwner A strategy
      hwin policy
  twoBasePayload :
    ProfiledRawJointHybridPhysicalCompatibleFrontierTwoPayload A strategy hwin
      (initial := initial)
  rightFirst :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiver A strategy
      hwin (initial := initial)
  rightBoth :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiver A strategy
      hwin (initial := initial)
  leftFirst :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiver A strategy
      hwin (initial := initial)
  leftBoth :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiver A strategy
      hwin (initial := initial)
  state_eq : state =
    profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy hwin
      target
  oneBaseShared_state : oneBaseShared.1 = state
  twoBaseShared_state : twoBaseShared.1 = state
  oneBasePayload_target : oneBasePayload.target = target
  twoBasePayload_target : twoBasePayload.target = target
  rightFirst_initial :
    rightFirst = ⟨state,
      profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy hwin
        state .first⟩
  rightBoth_initial :
    rightBoth = ⟨state,
      profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy hwin
        state .both⟩
  leftFirst_initial :
    leftFirst = ⟨state,
      profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy hwin
        state .first⟩
  leftBoth_initial :
    leftBoth = ⟨state,
      profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy hwin
        state .both⟩

namespace
    ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed

/-- Canonical two-sided seed at a retained compatible target.  Both base
payloads retain the same target, while their receiver forks carry the two
possible fresh closing rows. -/
noncomputable def atTarget
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed A strategy
      hwin policy := by
  let state :=
    profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy hwin
      target
  let oneBaseShared :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwner A strategy
        hwin policy :=
    ⟨state,
      profiledRawJointHybridPhysicalCompatibleRightSharedInitial A strategy
        hwin policy state⟩
  let twoBaseShared :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwner A strategy
        hwin policy :=
    ⟨state,
      profiledRawJointHybridPhysicalCompatibleLeftSharedInitial A strategy
        hwin policy state⟩
  let oneBasePayload :
      ProfiledRawJointHybridPhysicalCompatibleFrontierOnePayload A strategy
        hwin (initial := initial) :=
    { target := target
      firstReceiver :=
        profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy
          hwin state .first
      bothReceiver :=
        profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy
          hwin state .both }
  let twoBasePayload :
      ProfiledRawJointHybridPhysicalCompatibleFrontierTwoPayload A strategy
        hwin (initial := initial) :=
    { target := target
      firstReceiver :=
        profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy
          hwin state .first
      bothReceiver :=
        profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy
          hwin state .both }
  exact {
    target := target
    state := state
    oneBaseShared := oneBaseShared
    oneBasePayload := oneBasePayload
    twoBaseShared := twoBaseShared
    twoBasePayload := twoBasePayload
    rightFirst := ⟨state, oneBasePayload.firstReceiver⟩
    rightBoth := ⟨state, oneBasePayload.bothReceiver⟩
    leftFirst := ⟨state, twoBasePayload.firstReceiver⟩
    leftBoth := ⟨state, twoBasePayload.bothReceiver⟩
    state_eq := rfl
    oneBaseShared_state := rfl
    twoBaseShared_state := rfl
    oneBasePayload_target := rfl
    twoBasePayload_target := rfl
    rightFirst_initial := rfl
    rightBoth_initial := rfl
    leftFirst_initial := rfl
    leftBoth_initial := rfl }

/-- Prepare two complete phase-live candidates for one unresolved outer
close.  The candidates may have different target codes and different retained
compatible states; nothing in the construction collapses them into one seed.
An acknowledgement selects the whole candidate afterwards. -/
noncomputable def forkAtTargets
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (openTarget closedTarget : SuccessorTarget A strategy hwin initial) :
    FiniteDelayedFork
      (ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed A
        strategy hwin policy) :=
  ⟨atTarget A strategy hwin policy openTarget,
    atTarget A strategy hwin policy closedTarget⟩

@[simp] theorem forkAtTargets_false_target
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (openTarget closedTarget : SuccessorTarget A strategy hwin initial) :
    ((forkAtTargets A strategy hwin policy openTarget closedTarget).candidate
      false).target = openTarget :=
  rfl

@[simp] theorem forkAtTargets_true_target
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (openTarget closedTarget : SuccessorTarget A strategy hwin initial) :
    ((forkAtTargets A strategy hwin policy openTarget closedTarget).candidate
      true).target = closedTarget :=
  rfl

/-- Add process one's locally maintained phase bit. -/
def oneShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    (seed :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed A
        strategy hwin policy)
    (phase : Bool) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOneShared A strategy hwin
      policy :=
  FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh
    seed.oneBaseShared seed.oneBasePayload phase seed.leftFirst seed.leftBoth

/-- Add process two's independent local phase bit. -/
def twoShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    (seed :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed A
        strategy hwin policy)
    (phase : Bool) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoShared A strategy hwin
      policy :=
  FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh
    seed.twoBaseShared seed.twoBasePayload phase seed.rightFirst seed.rightBoth

end
  ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed

/-! ## One fixed recurrent controller for the two root candidates -/

/-- Process one's unresolved pending control retains the strict-right
candidate.  The member and phase are local finite bits; the candidate key is
fixed by the common-root policy and input. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootPhaseLiveOnePending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) (member phase : Bool) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOnePending A strategy
      hwin policy :=
  FiniteAcknowledgedDelayedCarrier.phaseLivePending member
    (ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed.oneShared A
      strategy hwin
      (ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed.atTarget
        A strategy hwin policy
          (profiledRawJointHybridPhysicalCompatibleRootRightTarget A strategy
            hwin policy input))
      phase)

/-- Process-two mirror retains the strict-left candidate.  In particular the
two endpoint pending values are not forced to share a hypothetical key. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootPhaseLiveTwoPending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) (member phase : Bool) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPending A strategy
      hwin policy :=
  FiniteAcknowledgedDelayedCarrier.phaseLivePending member
    (ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed.twoShared A
      strategy hwin
      (ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed.atTarget
        A strategy hwin policy
          (profiledRawJointHybridPhysicalCompatibleRootLeftTarget A strategy
            hwin policy input))
      phase)

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRootPhaseLiveOnePending_target
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) (member phase : Bool) :
    (profiledRawJointHybridPhysicalCompatibleRootPhaseLiveOnePending A strategy
      hwin policy input member phase).2.1.basePayload.target =
      profiledRawJointHybridPhysicalCompatibleRootRightTarget A strategy hwin
        policy input :=
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRootPhaseLiveTwoPending_target
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) (member phase : Bool) :
    (profiledRawJointHybridPhysicalCompatibleRootPhaseLiveTwoPending A strategy
      hwin policy input member phase).2.1.basePayload.target =
      profiledRawJointHybridPhysicalCompatibleRootLeftTarget A strategy hwin
        policy input :=
  rfl

/-- Harmless totalization output for an unreachable left-receiver branch of
the recurrent controller.  Every row is tagged by that literal row. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootPhaseLiveFallbackLeft
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
      strategy hwin initial :=
  let input : In₁ × In₂ := (default, default)
  let target :=
    profiledRawJointHybridPhysicalCompatibleRootLeftTarget A strategy hwin
      policy input
  RowExactIndexedTargetReceiverOutput.ofTarget default
    (fun row ↦ (target.1, (row, target.2.2))) (fun _ ↦ rfl)

/-- Right-receiver totalization mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootPhaseLiveFallbackRight
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
      strategy hwin initial :=
  let input : In₁ × In₂ := (default, default)
  let target :=
    profiledRawJointHybridPhysicalCompatibleRootRightTarget A strategy hwin
      policy input
  RowExactIndexedTargetReceiverOutput.ofTarget default
    (fun row ↦ (target.1, (row, target.2.2))) (fun _ ↦ rfl)

/-- A single finite recurrent machine fixed before the environment.  Its
standalone initial controls use one arbitrary finite root input; the actual
common front enters it through the activation maps below, after the locally
available input and bits have been computed. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootPairPhaseLiveController
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  profiledRawJointHybridPhysicalCompatiblePhaseLiveController A strategy hwin
    policy
    (profiledRawJointHybridPhysicalCompatibleRootPhaseLiveOnePending A strategy
      hwin policy (default, default) false false)
    (profiledRawJointHybridPhysicalCompatibleRootPhaseLiveTwoPending A strategy
      hwin policy (default, default) false false)
    (profiledRawJointHybridPhysicalCompatibleRootPhaseLiveFallbackLeft A
      strategy hwin policy)
    (profiledRawJointHybridPhysicalCompatibleRootPhaseLiveFallbackRight A
      strategy hwin policy)

/-- Proof-side resolved activation into the already fixed recurrent machine.
This function takes the full pair only because it states the post-close
readback.  A blind local transition must reach this value through the
common/shadow table's finite target fork; it must never call this function
from its own input alone. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootPairPhaseLiveActivateOne
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) (member phase : Bool) :
    FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
      (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOneShared A strategy
        hwin policy) PUnit PUnit :=
  .inl
    (profiledRawJointHybridPhysicalCompatibleRootPhaseLiveOnePending A strategy
      hwin policy input member phase)

/-- Proof-side process-two mirror.  As above, this is the value installed
after acknowledgement, not an executable first-strict local map. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRootPairPhaseLiveActivateTwo
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (input : In₁ × In₂) (member phase : Bool) :
    FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
      (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoShared A strategy
        hwin policy) PUnit PUnit :=
  .inl
    (profiledRawJointHybridPhysicalCompatibleRootPhaseLiveTwoPending A strategy
      hwin policy input member phase)

/-! ## The exact front-stage handoff -/

/-- One environment-specific readback of a fixed finite front stage.

The first field which mentions an orientation is
`exact_controller_target`, a proof-side classification of the target already
emitted by a fixed exact controller.  `exact_transition` says that the same
target extends the unchanged compatible policy.  The sole physical trace
obligation is `physical_prefix_alignment`.

Thus this structure is precisely the reusable reduction requested at the
front/recurrent seam: supplying those two mathematical facts produces both
the established `SuccessorInitialExit` and a canonical phase-live seed. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) : Type _ where
  start : Nat
  cuts : Nat → Nat
  target : SuccessorTarget A strategy hwin initial
  exitSide : IndexedLineageSide
  exitRoot : ProfiledRawJointThreadRoot A
  exact_controller_target :
    ProfiledRawJointHybridPhysicalCompatibleRootExactControllerTargetAt A
      strategy hwin policy target exitSide exitRoot
  exact_transition :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
      policy (policy.run []) target exitSide exitRoot
  physical_prefix_alignment :
    cutBlockMin
        (fun j ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + j)))
        cuts 0 =
      profiledRawJointThreadRootPriority A exitRoot

namespace
    ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}

/-- The two residual seam facts close the existing common-root initial-exit
interface. -/
noncomputable def toInitialExit
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit A strategy
      hwin policy G outputOne outputTwo env handoff.start handoff.cuts := by
  rcases handoff with
    ⟨start, cuts, target, side, root, controllerTarget, transition,
      blockMin⟩
  cases controllerTarget with
  | right slot _emitted live =>
      exact
        ProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit.ofRight
          A strategy hwin target.1 target.2.1 target.2.2 slot live
            transition.transition blockMin
  | left slot _emitted live =>
      exact
        ProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit.ofLeft
          A strategy hwin target.1 target.2.1 target.2.2 slot live
            transition.transition blockMin

/-- The recurrent seed is forced by the checked exit target; it is not an
arbitrary compatible state chosen after the fact. -/
noncomputable def phaseLiveSeed
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed A strategy
      hwin policy :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed.atTarget A
    strategy hwin policy handoff.target

/-- The exact same-policy transition makes the canonical seed reachable. -/
theorem phaseLiveSeed_reachable
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env) :
    ProfiledRawJointHybridPhysicalCompatibleReachable A strategy hwin initial
      policy handoff.phaseLiveSeed.state := by
  rcases handoff.exact_transition.transition with ⟨transition⟩
  have hroot :=
    profiledRawJointHybridPhysicalCompatiblePolicy_root_reachable A strategy
      hwin policy
  have hnext := transition.reachable A strategy hwin hroot
  simpa [phaseLiveSeed,
    ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed.atTarget]
    using hnext

/-- The same transition also supplies the live lineage at the seed state. -/
theorem phaseLiveSeed_live
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env) :
    profiledRawJointHybridCurrentSlots A handoff.exitSide
        handoff.phaseLiveSeed.state.1.1 () =
      some handoff.exitRoot := by
  rcases handoff.exact_transition.transition with ⟨transition⟩
  simpa [phaseLiveSeed,
    ProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveSeed.atTarget]
    using transition.child_live

end
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt

/-! ## A fixed-before-environment adapter -/

/-- A finite front-stage implementation together with its one semantic
readback field.  The machine and both Moore output tables are selected before
`env`; the field `handoff` is the exact remaining model theorem.

The canonical implementation should use
`profiledRawJointHybridLeaderFreeShadowTable` for the common/first-strict
local front.  The alignment lemmas above reduce its fresh strict roots to the
fixed exact-controller witnesses without exposing a side or leader bit. -/
structure ProfiledRawJointHybridPhysicalCompatibleFiniteRootStageAdapter
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) : Type _ where
  machine : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂
  outputOne : machine.State → Out₁
  outputTwo : machine.State → Out₂
  handoff : ∀ env : EnvironmentSequence In₁ In₂,
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy machine outputOne outputTwo env)

namespace
    ProfiledRawJointHybridPhysicalCompatibleFiniteRootStageAdapter

/-- End-to-end consumption theorem for the front adapter: every environment
gets an existing initial-exit certificate and the forced reachable, live
phase seed at exactly the same target. -/
theorem exitAndPhaseLiveSeed
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    (adapter :
      ProfiledRawJointHybridPhysicalCompatibleFiniteRootStageAdapter A
        strategy hwin policy)
    (env : EnvironmentSequence In₁ In₂) :
    ∃ handoff :
        ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
          strategy hwin policy adapter.machine adapter.outputOne
            adapter.outputTwo env,
      Nonempty
          (ProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit A
            strategy hwin policy adapter.machine adapter.outputOne
              adapter.outputTwo env handoff.start handoff.cuts) ∧
        ProfiledRawJointHybridPhysicalCompatibleReachable A strategy hwin
            initial policy handoff.phaseLiveSeed.state ∧
          profiledRawJointHybridCurrentSlots A handoff.exitSide
              handoff.phaseLiveSeed.state.1.1 () =
            some handoff.exitRoot := by
  rcases adapter.handoff env with ⟨handoff⟩
  exact ⟨handoff, ⟨handoff.toInitialExit A strategy hwin⟩,
    handoff.phaseLiveSeed_reachable A strategy hwin,
    handoff.phaseLiveSeed_live A strategy hwin⟩

end
  ProfiledRawJointHybridPhysicalCompatibleFiniteRootStageAdapter

end

end DetParityAutomaton

end DistributedSynthesis
