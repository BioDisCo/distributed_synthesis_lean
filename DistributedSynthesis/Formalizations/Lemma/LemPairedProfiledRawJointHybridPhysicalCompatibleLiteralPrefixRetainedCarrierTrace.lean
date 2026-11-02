/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixRetainedCarrier
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedPhysicalControllerReadback

/-!
# The retained literal carrier on the actual global trace

The list-level authority theorem is connected here to the repository's real
`FinitePairedPhysicalController` semantics.  The graph is inspected only by
the proof-side global dispatcher.  Each endpoint transition remains one of
the controller's local `recv`/`noRecv` callbacks and receives no graph,
orientation, hierarchy, or leader information.
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

private abbrev RightMove :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A

private abbrev LeftMove :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

private abbrev Relay :=
  ProfiledRawJointHybridLiteralPrefixRetainedRelay A

private abbrev OneControl :=
  ProfiledRawJointHybridLiteralPrefixRetainedOneControl A

private abbrev TwoControl :=
  ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A

private abbrev Controller
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) :=
  profiledRawJointHybridLiteralPrefixRetainedController A rightMove leftMove
    rightAnchor leftAnchor

/-- One proof-side spelling of the exact output selected by the three global
event cases.  Its row arguments are endpoint-local `lastRecv` bits from the
pre-round state. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedOutputAt
    (expected : Relay A) (state : OneControl A × TwoControl A)
    (graph : Graph) (input : In₁ × In₂) : Out₁ × Out₂ :=
  match graph with
  | .right =>
      profiledRawJointHybridLiteralPrefixRetainedRightOutput A
        (if state.2.2.1 then .both else .first) expected input
  | .left =>
      profiledRawJointHybridLiteralPrefixRetainedLeftOutput A
        (if state.1.2.1 then .both else .first) expected input
  | .both =>
      (pairedLeftInformedForRow
          (if state.1.2.1 then .both else .first)
          (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
            expected.2.2 input.1 input.2).1.physical,
        pairedRightInformedForRow
          (if state.2.2.1 then .both else .first)
          (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
            expected.1.2 input.2 input.1).1.physical)

/-- The reference relay after exactly `n` real environment rounds.  Graphs
are deliberately absent: every event advances the same complete literal
table once the global semantics has dispatched the local callbacks. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedRelayTrace
    (initial : Relay A) (env : EnvironmentSequence In₁ In₂) : Nat → Relay A
  | 0 => initial
  | n + 1 =>
      profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A
        (profiledRawJointHybridLiteralPrefixRetainedRelayTrace initial env n)
        ((env n).inputOne, (env n).inputTwo)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridLiteralPrefixRetainedRelayTrace_zero
    (initial : Relay A) (env : EnvironmentSequence In₁ In₂) :
    profiledRawJointHybridLiteralPrefixRetainedRelayTrace A initial env 0 =
      initial :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridLiteralPrefixRetainedRelayTrace_succ
    (initial : Relay A) (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    profiledRawJointHybridLiteralPrefixRetainedRelayTrace A initial env (n + 1) =
      profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A
        (profiledRawJointHybridLiteralPrefixRetainedRelayTrace A initial env n)
        ((env n).inputOne, (env n).inputTwo) :=
  rfl

section
omit [Inhabited In₁] [Inhabited In₂]

/-- Definitional agreement between the genuine controller product and the
proof-side graph dispatcher used by the authority calculation. -/
@[simp] theorem
    profiledRawJointHybridLiteralPrefixRetainedController_advanceControls
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool)
    (state : OneControl A × TwoControl A)
    (round : EnvironmentRound In₁ In₂) :
    (Controller A rightMove leftMove rightAnchor leftAnchor).advanceControls
        state round =
      profiledRawJointHybridLiteralPrefixRetainedGraphStep A round.graph state
        (round.inputOne, round.inputTwo) := by
  rcases round with ⟨inputOne, inputTwo, graph⟩
  cases graph <;> rfl

/-- The actual global state trace is authoritative at every time, for an
arbitrary infinite graph/input environment. -/
theorem profiledRawJointHybridLiteralPrefixRetained_globalStateTrace_authority
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    ProfiledRawJointHybridLiteralPrefixRetainedAuthority A
      (profiledRawJointHybridLiteralPrefixRetainedRelayTrace A
        (profiledRawJointHybridLiteralPrefixRetainedRelayInitial A rightMove
          leftMove rightAnchor leftAnchor) env n)
      ((Controller A rightMove leftMove rightAnchor leftAnchor).globalMachine.globalStateTrace
        env n) := by
  intro n
  induction n with
  | zero =>
      simpa [Controller] using
        (profiledRawJointHybridLiteralPrefixRetainedAuthority_initial A
          rightMove leftMove rightAnchor leftAnchor)
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
        profiledRawJointHybridLiteralPrefixRetainedRelayTrace_succ,
        FinitePairedPhysicalController.globalMachine_step,
        profiledRawJointHybridLiteralPrefixRetainedController_advanceControls]
      exact
        profiledRawJointHybridLiteralPrefixRetainedAuthority_step A _ _ ih
          (env n).graph ((env n).inputOne, (env n).inputTwo)

/-- Exact post-round output at an actual strict-right event. -/
theorem profiledRawJointHybridLiteralPrefixRetained_trace_strictRight_output
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .right) :
    let controller := Controller A rightMove leftMove rightAnchor leftAnchor
    let state := controller.globalMachine.globalStateTrace env n
    let expected :=
      profiledRawJointHybridLiteralPrefixRetainedRelayTrace A
        (profiledRawJointHybridLiteralPrefixRetainedRelayInitial A rightMove
          leftMove rightAnchor leftAnchor) env n
    (controller.globalOutputOne
        (controller.globalMachine.globalStateTrace env (n + 1)),
      controller.globalOutputTwo
        (controller.globalMachine.globalStateTrace env (n + 1))) =
      profiledRawJointHybridLiteralPrefixRetainedRightOutput A
        (if state.2.2.1 then .both else .first) expected
        ((env n).inputOne, (env n).inputTwo) := by
  dsimp only
  have hauthority :=
    profiledRawJointHybridLiteralPrefixRetained_globalStateTrace_authority A
      rightMove leftMove rightAnchor leftAnchor env n
  have houtput :=
    profiledRawJointHybridLiteralPrefixRetainedStrictRight_authority_output A
      _ _ hauthority ((env n).inputOne, (env n).inputTwo)
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
    FinitePairedPhysicalController.globalMachine_step,
    profiledRawJointHybridLiteralPrefixRetainedController_advanceControls,
    hgraph]
  simpa [FinitePairedPhysicalController.globalOutputOne,
    FinitePairedPhysicalController.globalOutputTwo] using houtput

/-- Exact post-round output at an actual strict-left event. -/
theorem profiledRawJointHybridLiteralPrefixRetained_trace_strictLeft_output
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .left) :
    let controller := Controller A rightMove leftMove rightAnchor leftAnchor
    let state := controller.globalMachine.globalStateTrace env n
    let expected :=
      profiledRawJointHybridLiteralPrefixRetainedRelayTrace A
        (profiledRawJointHybridLiteralPrefixRetainedRelayInitial A rightMove
          leftMove rightAnchor leftAnchor) env n
    (controller.globalOutputOne
        (controller.globalMachine.globalStateTrace env (n + 1)),
      controller.globalOutputTwo
        (controller.globalMachine.globalStateTrace env (n + 1))) =
      profiledRawJointHybridLiteralPrefixRetainedLeftOutput A
        (if state.1.2.1 then .both else .first) expected
        ((env n).inputOne, (env n).inputTwo) := by
  dsimp only
  have hauthority :=
    profiledRawJointHybridLiteralPrefixRetained_globalStateTrace_authority A
      rightMove leftMove rightAnchor leftAnchor env n
  have houtput :=
    profiledRawJointHybridLiteralPrefixRetainedStrictLeft_authority_output A
      _ _ hauthority ((env n).inputOne, (env n).inputTwo)
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
    FinitePairedPhysicalController.globalMachine_step,
    profiledRawJointHybridLiteralPrefixRetainedController_advanceControls,
    hgraph]
  simpa [FinitePairedPhysicalController.globalOutputOne,
    FinitePairedPhysicalController.globalOutputTwo] using houtput

/-- Exact post-round output at an actual simultaneous event. -/
theorem profiledRawJointHybridLiteralPrefixRetained_trace_both_output
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .both) :
    let controller := Controller A rightMove leftMove rightAnchor leftAnchor
    let state := controller.globalMachine.globalStateTrace env n
    let expected :=
      profiledRawJointHybridLiteralPrefixRetainedRelayTrace A
        (profiledRawJointHybridLiteralPrefixRetainedRelayInitial A rightMove
          leftMove rightAnchor leftAnchor) env n
    (controller.globalOutputOne
        (controller.globalMachine.globalStateTrace env (n + 1)),
      controller.globalOutputTwo
        (controller.globalMachine.globalStateTrace env (n + 1))) =
      (pairedLeftInformedForRow
          (if state.1.2.1 then .both else .first)
          (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
            expected.2.2 (env n).inputOne (env n).inputTwo).1.physical,
        pairedRightInformedForRow
          (if state.2.2.1 then .both else .first)
          (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
            expected.1.2 (env n).inputTwo (env n).inputOne).1.physical) := by
  dsimp only
  have hauthority :=
    profiledRawJointHybridLiteralPrefixRetained_globalStateTrace_authority A
      rightMove leftMove rightAnchor leftAnchor env n
  have houtput :=
    profiledRawJointHybridLiteralPrefixRetainedBoth_authority_output A _ _
      hauthority ((env n).inputOne, (env n).inputTwo)
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
    FinitePairedPhysicalController.globalMachine_step,
    profiledRawJointHybridLiteralPrefixRetainedController_advanceControls,
    hgraph]
  simpa [FinitePairedPhysicalController.globalOutputOne,
    FinitePairedPhysicalController.globalOutputTwo] using houtput

/-- Uniform exact-output statement for an arbitrary real environment round.
The only case split is performed by the proof-side global semantics. -/
theorem profiledRawJointHybridLiteralPrefixRetained_trace_output
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let controller := Controller A rightMove leftMove rightAnchor leftAnchor
    let state := controller.globalMachine.globalStateTrace env n
    let expected :=
      profiledRawJointHybridLiteralPrefixRetainedRelayTrace A
        (profiledRawJointHybridLiteralPrefixRetainedRelayInitial A rightMove
          leftMove rightAnchor leftAnchor) env n
    (controller.globalOutputOne
        (controller.globalMachine.globalStateTrace env (n + 1)),
      controller.globalOutputTwo
        (controller.globalMachine.globalStateTrace env (n + 1))) =
      profiledRawJointHybridLiteralPrefixRetainedOutputAt A expected state
        (env n).graph ((env n).inputOne, (env n).inputTwo) := by
  cases hgraph : (env n).graph with
  | left =>
      simpa [profiledRawJointHybridLiteralPrefixRetainedOutputAt, hgraph] using
        (profiledRawJointHybridLiteralPrefixRetained_trace_strictLeft_output A
          rightMove leftMove rightAnchor leftAnchor env n hgraph)
  | right =>
      simpa [profiledRawJointHybridLiteralPrefixRetainedOutputAt, hgraph] using
        (profiledRawJointHybridLiteralPrefixRetained_trace_strictRight_output A
          rightMove leftMove rightAnchor leftAnchor env n hgraph)
  | both =>
      simpa [profiledRawJointHybridLiteralPrefixRetainedOutputAt, hgraph] using
        (profiledRawJointHybridLiteralPrefixRetained_trace_both_output A
          rightMove leftMove rightAnchor leftAnchor env n hgraph)

end

/-- The exact reference word exposed to subsequent path/cut bookkeeping. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedReferenceWord
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool)
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  let controller := Controller A rightMove leftMove rightAnchor leftAnchor
  let initial :=
    profiledRawJointHybridLiteralPrefixRetainedRelayInitial A rightMove leftMove
      rightAnchor leftAnchor
  fun n =>
    let state := controller.globalMachine.globalStateTrace env n
    let expected :=
      profiledRawJointHybridLiteralPrefixRetainedRelayTrace A initial env n
    let output :=
      profiledRawJointHybridLiteralPrefixRetainedOutputAt A expected state
        (env n).graph ((env n).inputOne, (env n).inputTwo)
    { inputOne := (env n).inputOne
      inputTwo := (env n).inputTwo
      graph := (env n).graph
      outputOne := output.1
      outputTwo := output.2 }

omit [Inhabited In₁] [Inhabited In₂] in
/-- Whole-word equality between the actual finite controller and the exact
retained-table reference. -/
theorem
    profiledRawJointHybridLiteralPrefixRetained_globalMachineTraceWord_eq
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool)
    (env : EnvironmentSequence In₁ In₂) :
    let controller := Controller A rightMove leftMove rightAnchor leftAnchor
    controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo env =
      profiledRawJointHybridLiteralPrefixRetainedReferenceWord A rightMove
        leftMove rightAnchor leftAnchor env := by
  dsimp only
  funext n
  have houtput :=
    profiledRawJointHybridLiteralPrefixRetained_trace_output A rightMove
      leftMove rightAnchor leftAnchor env n
  have hone := congrArg Prod.fst houtput
  have htwo := congrArg Prod.snd houtput
  simp only [Prod.fst] at hone
  simp only [Prod.snd] at htwo
  unfold FiniteGlobalRoundMachine.globalMachineTraceWord
    profiledRawJointHybridLiteralPrefixRetainedReferenceWord
  dsimp only
  rw [hone, htwo]

end

end DetParityAutomaton

end DistributedSynthesis
