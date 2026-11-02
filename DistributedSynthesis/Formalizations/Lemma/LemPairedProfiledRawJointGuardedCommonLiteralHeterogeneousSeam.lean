/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorHeterogeneousPreselection
import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLiteralPrefixDescriptor
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonExactUniformActivation
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitLeftBlockMonitor

/-!
# Conditional heterogeneous preselection at a literal right/`both` seam

The unresolved process-two fork compares two genuinely different left-block
obligations: the literal left block restarted after a strict-right round, and
the first left block of the fresh recurrent policy after a simultaneous
round.  Their receiver certificate alphabets differ, so the ordinary
homogeneous cross table cannot type this comparison.

This file instantiates the heterogeneous table with those exact two monitor
families.  The sole premise is pointwise equality of the two blind physical
emissions.  It does not require equality of semantic histories, complete
lambdas, policy states, or finite codes.  All monitor-realizability and
two-record prefix obligations are discharged from the existing semantic
activations.

The extracted table has a literally shared sender control.  Consequently its
two hidden projections have equal no-receive outputs and equal sender-state
updates at every future control.  The hidden Boolean remains confined to the
receiver/monitor projection.
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

/-- A harmless default for the unused false-side target coordinate in the
heterogeneous receiver product.  It carries no semantic choice: every live
target is still supplied and checked by the exact activation. -/
private noncomputable instance :
    Inhabited (ProfiledRawJointUnitTarget A) :=
  ⟨{
    family := {
      right := fun _ ↦ none
      left := fun _ ↦ none
      rightPattern := fun _ _ ↦ false
      leftPattern := fun _ _ ↦ false
    }
    cross := fun _ _ ↦ false
  }⟩

private abbrev FalseReceiverOutput :=
  ProfiledRawJointTargetLeftReceiverOutput
    (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)

private abbrev TrueReceiverOutput
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit)) :=
  ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode

private noncomputable abbrev FalseMonitor
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  profiledRawJointLeftPhysicalSiblingMonitor A
    (profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
      installed) false

private noncomputable abbrev FalseActivation
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  profiledRawJointHybridExactLeftUniformActivation A strategy hwin installed

private noncomputable abbrev TrueMonitor
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (source : ProfiledRawLeftSlot A) :=
  profiledRawJointUnitLeftBlockMonitor A strategy initialCode policy state
    source

private noncomputable def literalRightBothFalseReceiver
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ReceiverBlockStrategy In₁ In₂
      (FalseReceiverOutput A (Out₁ := Out₁) (Out₂ := Out₂)) :=
  profiledRawJointTargetLeftReceiverStrategy A
    (FalseActivation A strategy hwin installed)

private def literalRightBothTrueReceiver
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source) :
    ReceiverBlockStrategy In₁ In₂
      (TrueReceiverOutput A strategy initialCode) :=
  profiledRawJointUnitLeftReceiverStrategy A activation

private noncomputable def literalRightBothFalseSender
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    SenderBlockStrategy In₂ Out₂ :=
  pairedLeftSenderStrategy (FalseActivation A strategy hwin installed).lambda

private def literalRightBothTrueSender
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source) :
    SenderBlockStrategy In₂ Out₂ :=
  pairedLeftSenderStrategy activation.lambda

/-- The weakest semantic bridge needed by simultaneous preselection.  Only
the physical blind emission is compared, pointwise in the private input
history and next private input. -/
def ProfiledRawJointLiteralRightBothBlindEmissionCompatible
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source) : Prop :=
  ∀ past own,
    (FalseActivation A strategy hwin installed).lambda.blind past own =
      activation.lambda.blind past own

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Pointwise physical compatibility is exactly enough to identify the two
sender strategies consumed by the heterogeneous table constructor. -/
theorem literalRightBoth_sender_eq_of_blindEmissionCompatible
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source)
    (hcompatible :
      ProfiledRawJointLiteralRightBothBlindEmissionCompatible A strategy hwin
        installed activation) :
    literalRightBothFalseSender A strategy hwin installed =
      literalRightBothTrueSender A strategy activation := by
  funext past own
  exact hcompatible past own

private noncomputable def literalRightBothFalseFirstAllowed
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorLiteralFirstAllowed
    (literalRightBothFalseReceiver A strategy hwin installed)
    (literalRightBothFalseSender A strategy hwin installed)

private noncomputable def literalRightBothTrueFirstAllowed
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source) :=
  finiteCrossAnchorLiteralFirstAllowed
    (literalRightBothTrueReceiver A strategy activation)
    (literalRightBothTrueSender A strategy activation)

private noncomputable def literalRightBothFalseSecondAllowed
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorLiteralSecondAllowed
    (literalRightBothFalseReceiver A strategy hwin installed)
    (literalRightBothFalseSender A strategy hwin installed)

private noncomputable def literalRightBothTrueSecondAllowed
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source) :=
  finiteCrossAnchorLiteralSecondAllowed
    (literalRightBothTrueReceiver A strategy activation)
    (literalRightBothTrueSender A strategy activation)

/-- The literal restarted left block and the fresh recurrent left block,
simultaneously narrowed into one finite table.  `false` is the literal
interpretation and `true` the fresh recurrent interpretation. -/
noncomputable def profiledRawJointLiteralRightBothHeterogeneousLeftTable
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source)
    (hcompatible :
      ProfiledRawJointLiteralRightBothBlindEmissionCompatible A strategy hwin
        installed activation) :
    FiniteCrossAnchorFirstTwoTable
      (finiteCrossAnchorHeterogeneousMonitor
        (FalseMonitor A strategy hwin installed)
        (TrueMonitor A strategy initialCode policy state source))
      (finiteCrossAnchorHeterogeneousStart
        (FalseMonitor A strategy hwin installed)
        (TrueMonitor A strategy initialCode policy state source)
        (FalseMonitor A strategy hwin installed).initial
        (TrueMonitor A strategy initialCode policy state source).initial)
      (finiteCrossAnchorHeterogeneousFirstAllowed
        (literalRightBothFalseFirstAllowed A strategy hwin installed)
        (literalRightBothTrueFirstAllowed A strategy activation))
      (finiteCrossAnchorHeterogeneousSecondAllowed
        (literalRightBothFalseSecondAllowed A strategy hwin installed)
        (literalRightBothTrueSecondAllowed A strategy activation)) := by
  let falseMonitor := FalseMonitor A strategy hwin installed
  let trueMonitor := TrueMonitor A strategy initialCode policy state source
  let falseReceiver := literalRightBothFalseReceiver A strategy hwin installed
  let trueReceiver := literalRightBothTrueReceiver A strategy activation
  let falseSender := literalRightBothFalseSender A strategy hwin installed
  let trueSender := literalRightBothTrueSender A strategy activation
  have hsender : falseSender = trueSender :=
    literalRightBoth_sender_eq_of_blindEmissionCompatible A strategy hwin
      installed activation hcompatible
  apply finiteCrossAnchorHeterogeneousFirstTwoTable
    falseMonitor trueMonitor falseMonitor.initial trueMonitor.initial
    (literalRightBothFalseFirstAllowed A strategy hwin installed)
    (literalRightBothTrueFirstAllowed A strategy activation)
    (literalRightBothFalseSecondAllowed A strategy hwin installed)
    (literalRightBothTrueSecondAllowed A strategy activation)
    falseReceiver trueReceiver falseSender
  · intro env
    simpa [falseMonitor] using
      (profiledRawJointHybridExactLeftUniformMonitor_realizable A strategy hwin
        installed env)
  · intro env
    rw [hsender]
    exact profiledRawJointUnitLeftBlockMonitor_realizable A policy state source
      activation env
  · intro env
    exact finiteCrossAnchorLiteralFirstAllowed_pairPlay falseReceiver
      falseSender env
  · intro env
    rw [hsender]
    exact finiteCrossAnchorLiteralFirstAllowed_pairPlay trueReceiver trueSender
      env
  · intro env
    exact finiteCrossAnchorLiteralSecondAllowed_pairPlay falseReceiver
      falseSender env
  · intro env
    rw [hsender]
    exact finiteCrossAnchorLiteralSecondAllowed_pairPlay trueReceiver trueSender
      env

/-- The two seam interpretations emit the same blind no-receive output after
every finite private input history. -/
theorem profiledRawJointLiteralRightBothHeterogeneousLeftTable_noRecv_output_eq
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source)
    (hcompatible :
      ProfiledRawJointLiteralRightBothBlindEmissionCompatible A strategy hwin
        installed activation)
    (past : List In₂) (input : In₂) :
    let table := profiledRawJointLiteralRightBothHeterogeneousLeftTable A
      strategy hwin installed activation hcompatible
    ((table.memberController false).labeledTree past).1 input =
      ((table.memberController true).labeledTree past).1 input := by
  dsimp only
  exact finiteCrossAnchorFirstTwoTableTwo_pending_sender_step_eq
    (profiledRawJointLiteralRightBothHeterogeneousLeftTable A strategy hwin
      installed activation hcompatible) past input

/-- At an arbitrary shared finite control, both seam projections also update
the sender state identically. -/
theorem profiledRawJointLiteralRightBothHeterogeneousLeftTable_noRecv_step_eq
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source)
    (hcompatible :
      ProfiledRawJointLiteralRightBothBlindEmissionCompatible A strategy hwin
        installed activation)
    (control :
      ((profiledRawJointLiteralRightBothHeterogeneousLeftTable A strategy hwin
        installed activation hcompatible).memberController false).Control)
    (input : In₂) :
    let table := profiledRawJointLiteralRightBothHeterogeneousLeftTable A
      strategy hwin installed activation hcompatible
    (table.memberController false).step control input =
      (table.memberController true).step control input := by
  dsimp only
  exact
    (profiledRawJointLiteralRightBothHeterogeneousLeftTable A strategy hwin
      installed activation hcompatible).memberController_step_eq_atControl
        false true control input

/-! ## Unconditional literal-point specialization

At a literal guarded-common occurrence, the recurrent side need not be an
arbitrary unit-policy activation.  It is the exact root-pinned activation of
the same installed world.  Its lambda is the lambda used by the uniform
literal side.  Semantically, the two readings are the immediate
`right`/`both` pending histories, whose process-two views are equal.  This
removes the compatibility premise above at the occurrence actually consumed
by the guarded-common handoff. -/

private noncomputable abbrev LiteralExactPackage
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  profiledRawJointHybridExactLeftPolicy A hwin installed

private abbrev LiteralExactReceiverOutput
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy
    (installed.world.oneSidedState A .left)
    (profiledRawJointHybridExactLeftRootPredicate A installed)
    (LiteralExactPackage A strategy hwin installed)

/-- The unused exact-target coordinate of the heterogeneous product has a
canonical literal child at the empty private word. -/
private noncomputable instance
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    Inhabited (LiteralExactReceiverOutput A strategy hwin installed) :=
  ⟨{
    physical := default
    target := fun row ↦
      (profiledRawJointGuardedFirstLeftTarget A strategy
        (installed.world.oneSidedState A .left)
        (profiledRawJointHybridExactLeftRootPredicate A installed)
        (LiteralExactPackage A strategy hwin installed) row [] default)
  }⟩

private noncomputable abbrev LiteralExactMonitor
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  profiledRawJointHybridExactLeftMonitor A installed
    (LiteralExactPackage A strategy hwin installed)

private noncomputable def literalRightBothExactReceiver
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ReceiverBlockStrategy In₁ In₂
      (LiteralExactReceiverOutput A strategy hwin installed) :=
  profiledRawJointGuardedFirstLeftReceiverStrategy A
    (profiledRawJointHybridExactLeftActivation A hwin installed)

private noncomputable def literalRightBothExactSender
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    SenderBlockStrategy In₂ Out₂ :=
  pairedLeftSenderStrategy
    (profiledRawJointHybridExactLeftActivation A hwin installed).lambda

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The exact-side lambda is literally the uniform-side lambda.  No leader
test, history equality, or finite-code extensionality is used. -/
theorem literalRightBoth_uniformSender_eq_exactSender
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    literalRightBothFalseSender A strategy hwin installed =
      literalRightBothExactSender A strategy hwin installed := by
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- At a semantic occurrence, the common exact sender is also the sender at
the simultaneous history.  The proof uses only the immediate pending-overlap
view equality; neither node is told which graph interpretation occurred. -/
theorem literalRightBoth_exactSender_eq_bothHistory_ofPoint
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy) :
    let installed :=
      profiledRawJointGuardedCommonPointInstalled A strategy point
    literalRightBothExactSender A strategy hwin installed =
      blockSenderTwo strategy ((point.world A strategy).procTwo A).bothHistory := by
  dsimp only
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy point
  have hoverlap :=
    profiledRawJointGuardedCommonPoint_procTwoPendingOverlap A strategy point
  calc
    literalRightBothExactSender A strategy hwin installed =
        literalRightBothFalseSender A strategy hwin installed :=
      (literalRightBoth_uniformSender_eq_exactSender A strategy hwin
        installed).symm
    _ = blockSenderTwo strategy
          ((point.world A strategy).procTwo A).rightHistory := by
      simpa [installed] using
        (profiledRawJointHybridExactLeftUniformSender_eq_rightHistory A
          strategy hwin installed)
    _ = blockSenderTwo strategy
          ((point.world A strategy).procTwo A).bothHistory :=
      blockSenderTwo_eq_of_view_eq strategy hoverlap.view_eq

private noncomputable def literalRightBothExactFirstAllowed
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorLiteralFirstAllowed
    (literalRightBothExactReceiver A strategy hwin installed)
    (literalRightBothExactSender A strategy hwin installed)

private noncomputable def literalRightBothExactSecondAllowed
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorLiteralSecondAllowed
    (literalRightBothExactReceiver A strategy hwin installed)
    (literalRightBothExactSender A strategy hwin installed)

/-! Short private names for the dependent ingredients of the public exact
table fibre.  The public carrier below hides these monitor types completely;
runtime states expose only finite controls. -/

private noncomputable abbrev LiteralExactBase
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorHeterogeneousMonitor
    (FalseMonitor A strategy hwin installed)
    (LiteralExactMonitor A strategy hwin installed)

private noncomputable abbrev LiteralExactStart
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorHeterogeneousStart
    (FalseMonitor A strategy hwin installed)
    (LiteralExactMonitor A strategy hwin installed)
    (FalseMonitor A strategy hwin installed).initial
    (LiteralExactMonitor A strategy hwin installed).initial

private noncomputable abbrev LiteralExactFirstAllowed
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorHeterogeneousFirstAllowed
    (literalRightBothFalseFirstAllowed A strategy hwin installed)
    (literalRightBothExactFirstAllowed A strategy hwin installed)

private noncomputable abbrev LiteralExactSecondAllowed
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorHeterogeneousSecondAllowed
    (literalRightBothFalseSecondAllowed A strategy hwin installed)
    (literalRightBothExactSecondAllowed A strategy hwin installed)

/-- Public receiver alphabet of the code-erased member. -/
abbrev ProfiledRawJointLiteralRightBothExactFalseReceiverOutput :=
  FalseReceiverOutput A (Out₁ := Out₁) (Out₂ := Out₂)

/-- Public receiver alphabet of the exact root-pinned member. -/
abbrev ProfiledRawJointLiteralRightBothExactTrueReceiverOutput
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  LiteralExactReceiverOutput A strategy hwin installed

/-- Product receiver alphabet stored by the shared table. -/
abbrev ProfiledRawJointLiteralRightBothExactProductReceiverOutput
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  ProfiledRawJointLiteralRightBothExactFalseReceiverOutput A ×
    ProfiledRawJointLiteralRightBothExactTrueReceiverOutput A strategy hwin
      installed

/-- Public name for the dependent finite table fibre at one exact installed
occurrence.  Exposing this type lets a surrounding finite key package the
tables in a dependent sum without exposing the private monitor abbreviations
or any semantic history to runtime transitions. -/
noncomputable abbrev
    ProfiledRawJointLiteralRightBothExactHeterogeneousLeftTableType
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  FiniteCrossAnchorFirstTwoTable
    (LiteralExactBase A strategy hwin installed)
    (LiteralExactStart A strategy hwin installed)
    (LiteralExactFirstAllowed A strategy hwin installed)
    (LiteralExactSecondAllowed A strategy hwin installed)

/-- Unconditional heterogeneous seam table for the two literal
interpretations of one installed guarded-common occurrence. -/
noncomputable def profiledRawJointLiteralRightBothExactHeterogeneousLeftTable
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ProfiledRawJointLiteralRightBothExactHeterogeneousLeftTableType A strategy
      hwin installed := by
  let falseMonitor := FalseMonitor A strategy hwin installed
  let trueMonitor := LiteralExactMonitor A strategy hwin installed
  let falseReceiver := literalRightBothFalseReceiver A strategy hwin installed
  let trueReceiver := literalRightBothExactReceiver A strategy hwin installed
  let falseSender := literalRightBothFalseSender A strategy hwin installed
  let trueSender := literalRightBothExactSender A strategy hwin installed
  have hsender : falseSender = trueSender :=
    literalRightBoth_uniformSender_eq_exactSender A strategy hwin installed
  apply finiteCrossAnchorHeterogeneousFirstTwoTable
    falseMonitor trueMonitor falseMonitor.initial trueMonitor.initial
    (literalRightBothFalseFirstAllowed A strategy hwin installed)
    (literalRightBothExactFirstAllowed A strategy hwin installed)
    (literalRightBothFalseSecondAllowed A strategy hwin installed)
    (literalRightBothExactSecondAllowed A strategy hwin installed)
    falseReceiver trueReceiver falseSender
  · intro env
    simpa [falseMonitor] using
      (profiledRawJointHybridExactLeftUniformMonitor_realizable A strategy hwin
        installed env)
  · intro env
    rw [hsender]
    exact profiledRawJointHybridExactLeftMonitor_realizable A installed
      (LiteralExactPackage A strategy hwin installed)
      (profiledRawJointHybridExactLeftActivation A hwin installed) env
  · intro env
    exact finiteCrossAnchorLiteralFirstAllowed_pairPlay falseReceiver
      falseSender env
  · intro env
    rw [hsender]
    exact finiteCrossAnchorLiteralFirstAllowed_pairPlay trueReceiver trueSender
      env
  · intro env
    exact finiteCrossAnchorLiteralSecondAllowed_pairPlay falseReceiver
      falseSender env
  · intro env
    rw [hsender]
    exact finiteCrossAnchorLiteralSecondAllowed_pairPlay trueReceiver trueSender
      env

/-! ## Public finite local carrier at one installed occurrence -/

/-- Blind-sender control of the exact heterogeneous table.  It contains no
hidden member bit. -/
noncomputable abbrev ProfiledRawJointLiteralRightBothExactSenderState
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  FiniteCrossAnchorSenderState
    (LiteralExactBase A strategy hwin installed)
    (LiteralExactStart A strategy hwin installed)
    (LiteralExactFirstAllowed A strategy hwin installed)
    (LiteralExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed)

/-- Receiver control.  Its internal Boolean is candidate-member data carried
by the delayed fork, never a current graph observation. -/
noncomputable abbrev ProfiledRawJointLiteralRightBothExactReceiverState
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  FiniteCrossAnchorReceiverState
    (LiteralExactBase A strategy hwin installed)
    (LiteralExactStart A strategy hwin installed)
    (LiteralExactFirstAllowed A strategy hwin installed)
    (LiteralExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed)

noncomputable instance
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    Fintype
      (ProfiledRawJointLiteralRightBothExactSenderState A strategy hwin
        installed) := by
  infer_instance

noncomputable instance
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    Fintype
      (ProfiledRawJointLiteralRightBothExactReceiverState A strategy hwin
        installed) := by
  classical
  infer_instance

/-- Shared sender root of the preselected table. -/
noncomputable def profiledRawJointLiteralRightBothExactSenderInitial
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ProfiledRawJointLiteralRightBothExactSenderState A strategy hwin installed :=
  finiteCrossAnchorSenderInitial
    (LiteralExactBase A strategy hwin installed)
    (LiteralExactStart A strategy hwin installed)
    (LiteralExactFirstAllowed A strategy hwin installed)
    (LiteralExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed)

/-- Member-specific receiver root of the same table. -/
noncomputable def profiledRawJointLiteralRightBothExactReceiverInitial
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) :
    ProfiledRawJointLiteralRightBothExactReceiverState A strategy hwin
      installed :=
  finiteCrossAnchorReceiverInitial
    (LiteralExactBase A strategy hwin installed)
    (LiteralExactStart A strategy hwin installed)
    (LiteralExactFirstAllowed A strategy hwin installed)
    (LiteralExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed) anchor

/-- One arbitrary-depth graph-blind sender step. -/
noncomputable def profiledRawJointLiteralRightBothExactSenderNoRecv
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (state : ProfiledRawJointLiteralRightBothExactSenderState A strategy hwin
      installed)
    (input : In₂) : Out₂ ×
      ProfiledRawJointLiteralRightBothExactSenderState A strategy hwin
        installed :=
  finiteCrossAnchorSenderNoRecv
    (LiteralExactBase A strategy hwin installed)
    (LiteralExactStart A strategy hwin installed)
    (LiteralExactFirstAllowed A strategy hwin installed)
    (LiteralExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed) state input

/-- One member-threaded receiver step. -/
noncomputable def profiledRawJointLiteralRightBothExactReceiverRecv
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (state : ProfiledRawJointLiteralRightBothExactReceiverState A strategy hwin
      installed)
    (own : In₁) (delivered : In₂) :
    ProfiledRawJointLiteralRightBothExactProductReceiverOutput A strategy hwin
        installed ×
      ProfiledRawJointLiteralRightBothExactReceiverState A strategy hwin
        installed :=
  finiteCrossAnchorReceiverRecv
    (LiteralExactBase A strategy hwin installed)
    (LiteralExactStart A strategy hwin installed)
    (LiteralExactFirstAllowed A strategy hwin installed)
    (LiteralExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed) state own delivered

@[simp] theorem profiledRawJointLiteralRightBothExactReceiverInitial_anchor
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) :
    (profiledRawJointLiteralRightBothExactReceiverInitial A strategy hwin
      installed anchor).1 = anchor :=
  rfl

/-- Both endpoints initially store the same finite table control. -/
theorem profiledRawJointLiteralRightBothExact_initial_controls_eq
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) :
    profiledRawJointLiteralRightBothExactSenderInitial A strategy hwin
        installed =
      (profiledRawJointLiteralRightBothExactReceiverInitial A strategy hwin
        installed anchor).2.1 := by
  exact finiteCrossAnchor_initial_controls_eq
    (LiteralExactBase A strategy hwin installed)
    (LiteralExactStart A strategy hwin installed)
    (LiteralExactFirstAllowed A strategy hwin installed)
    (LiteralExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed) anchor

/-- The sender step is the sender coordinate of either proof-side member. -/
theorem profiledRawJointLiteralRightBothExactSenderNoRecv_output_eq_member
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (state : ProfiledRawJointLiteralRightBothExactSenderState A strategy hwin
      installed)
    (input : In₂) (anchor : Bool) :
    (profiledRawJointLiteralRightBothExactSenderNoRecv A strategy hwin
      installed state input).1 =
      (((profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
        hwin installed).memberController anchor).labelOf state).1 input := by
  exact finiteCrossAnchorSenderNoRecv_output_eq_member
    (LiteralExactBase A strategy hwin installed)
    (LiteralExactStart A strategy hwin installed)
    (LiteralExactFirstAllowed A strategy hwin installed)
    (LiteralExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed) state input anchor

/-- Synchronized sender/receiver table controls stay synchronized after one
physical block letter. -/
theorem profiledRawJointLiteralRightBothExact_step_controls_eq
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (sender : ProfiledRawJointLiteralRightBothExactSenderState A strategy hwin
      installed)
    (receiver : ProfiledRawJointLiteralRightBothExactReceiverState A strategy
      hwin installed)
    (hsync : sender = receiver.2.1)
    (own : In₁) (delivered : In₂) :
    (profiledRawJointLiteralRightBothExactSenderNoRecv A strategy hwin
      installed sender delivered).2 =
      (profiledRawJointLiteralRightBothExactReceiverRecv A strategy hwin
        installed receiver own delivered).2.2.1 := by
  exact finiteCrossAnchor_step_controls_eq
    (LiteralExactBase A strategy hwin installed)
    (LiteralExactStart A strategy hwin installed)
    (LiteralExactFirstAllowed A strategy hwin installed)
    (LiteralExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed) sender receiver hsync own delivered

/-- The unconditional literal seam has one blind no-receive output at every
finite private word. -/
theorem profiledRawJointLiteralRightBothExactHeterogeneousLeftTable_noRecv_output_eq
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (past : List In₂) (input : In₂) :
    let table :=
      profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
        hwin installed
    ((table.memberController false).labeledTree past).1 input =
      ((table.memberController true).labeledTree past).1 input := by
  dsimp only
  exact finiteCrossAnchorFirstTwoTableTwo_pending_sender_step_eq
    (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed) past input

/-- The sender transition of the two unconditional literal projections is
also identical at every shared control. -/
theorem profiledRawJointLiteralRightBothExactHeterogeneousLeftTable_noRecv_step_eq
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (control :
      ((profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
        hwin installed).memberController false).Control)
    (input : In₂) :
    let table :=
      profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
        hwin installed
    (table.memberController false).step control input =
      (table.memberController true).step control input := by
  dsimp only
  exact
    (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      installed).memberController_step_eq_atControl false true control input

/-! ## The active false coordinate still carries the exact child code -/

/-- Although the false heterogeneous member does not constrain the unused
exact `Prod.snd` coordinate, its active target is the incidence code of the
root-pinned literal child at the same first physical record. -/
theorem profiledRawJointLiteralRightBothExactReceiverFirst_false_target_code
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (row : PairedEntryRow) (input : In₁ × In₂) :
    (profiledRawJointLiteralRightBothExactReceiverRecv A strategy hwin
      installed
      (profiledRawJointLiteralRightBothExactReceiverInitial A strategy hwin
        installed false)
      input.1 input.2).1.1.target row =
      (profiledRawJointGuardedFirstLeftTarget A strategy
        (installed.world.oneSidedState A .left)
        (profiledRawJointHybridExactLeftRootPredicate A installed)
        (profiledRawJointHybridExactLeftPolicy A hwin installed)
        row [] input).1 := by
  classical
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      installed
  have hfirst := (table.memberController_records_allowed false input input).1
  change decide (_ = _) = true at hfirst
  have hrecord := of_decide_eq_true hfirst
  exact congrArg (fun record ↦ record.2.1.target row) hrecord

/-! ## Model-facing literal-child wrapper -/

/-- Install the unconditional right/`both` seam at the literal simultaneous
child selected by one guarded-common block input. -/
noncomputable def
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTableAtChild
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (blockInput : In₁ × In₂) :=
  let child := point.step A strategy blockInput
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy child
  profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
    installed

/-- The literal child's two hidden interpretations expose one no-receive
output at every private word. -/
theorem
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTableAtChild_noRecv_output_eq
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (blockInput : In₁ × In₂) (past : List In₂) (input : In₂) :
    let table :=
      profiledRawJointLiteralRightBothExactHeterogeneousLeftTableAtChild A
        strategy hwin point blockInput
    ((table.memberController false).labeledTree past).1 input =
      ((table.memberController true).labeledTree past).1 input := by
  let child := point.step A strategy blockInput
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy child
  simpa [profiledRawJointLiteralRightBothExactHeterogeneousLeftTableAtChild,
    child, installed] using
    (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable_noRecv_output_eq
      A strategy hwin installed past input)

/-- The literal child's two hidden projections also share their sender-state
update at every common table control. -/
theorem
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTableAtChild_noRecv_step_eq
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (blockInput : In₁ × In₂)
    (control :
      ((profiledRawJointLiteralRightBothExactHeterogeneousLeftTableAtChild A
        strategy hwin point blockInput).memberController false).Control)
    (input : In₂) :
    let table :=
      profiledRawJointLiteralRightBothExactHeterogeneousLeftTableAtChild A
        strategy hwin point blockInput
    (table.memberController false).step control input =
      (table.memberController true).step control input := by
  let child := point.step A strategy blockInput
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy child
  simpa [profiledRawJointLiteralRightBothExactHeterogeneousLeftTableAtChild,
    child, installed] using
    (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable_noRecv_step_eq
      A strategy hwin installed control input)

end

end DetParityAutomaton

end DistributedSynthesis
