/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTreeRationalization
import DistributedSynthesis.Formalizations.Lemma.LemPendingBitImmediateAnchors
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointHybridExactRootGuard

/-!
# Uniform finite-target activations at an arbitrary guarded common occurrence

The exact-root construction is semantic-source dependent only because its
receiver returns a subtype of literal children of that source.  The physical
target monitor needs much less: the finite incidence code of each child, its
profiled projection, and a finite allowed-target truth table.

This file erases the dependent subtype at an arbitrary occurrence of the
guarded common semantic tree.  The resulting right and left activations use
the existing globally finite `ProfiledRawJointUnitTarget` alphabet.  Their
blind lambdas are proved equal to the literal common-world strategy lambdas,
which is the equality needed to narrow an old and a fresh cross-anchor
obligation simultaneously before policy canonicalization.
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

/-! ## Literal installed data at every semantic occurrence -/

/-- View an arbitrary guarded-common semantic occurrence through the
policy-free installed-move interface used by the exact-root construction. -/
def profiledRawJointGuardedCommonPointInstalled
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy) :
    ProfiledRawJointHybridCommonMoveData A strategy where
  incidenceCode := point.code A strategy
  rawMove := (profiledRawJointCommonWorldFamily A
    (point.world A strategy)).move A
  world := point.world A strategy
  incidence_eq := rfl
  move_eq := rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- The process-one histories exposed by the literal installed world are the
actual immediate `left`/`both` pending overlap. -/
theorem profiledRawJointGuardedCommonPoint_procOnePendingOverlap
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy) :
    ProcOnePendingOverlap
      ((point.world A strategy).procOne A).leftHistory
      ((point.world A strategy).procOne A).bothHistory := by
  let world := point.world A strategy
  simpa [world] using
    (procOnePendingOverlap_immediate strategy world.base
      (world.inputOne, world.inputTwo))

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Process-two mirror: the literal installed histories are the immediate
`right`/`both` pending overlap. -/
theorem profiledRawJointGuardedCommonPoint_procTwoPendingOverlap
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy) :
    ProcTwoPendingOverlap
      ((point.world A strategy).procTwo A).rightHistory
      ((point.world A strategy).procTwo A).bothHistory := by
  let world := point.world A strategy
  simpa [world] using
    (procTwoPendingOverlap_immediate strategy world.base
      (world.inputOne, world.inputTwo))

/-! ## The selected exact lambda is the literal world lambda -/

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointHybridExactRightActivation_lambda_eq
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    (profiledRawJointHybridExactRightActivation A hwin installed).lambda =
      installed.rightLambda := by
  let package := profiledRawJointHybridExactRightPolicy A hwin installed
  let activation := profiledRawJointHybridExactRightActivation A hwin installed
  have hselected : package.rootMove.rightLambda () =
      some activation.lambda := activation.lambda_selected
  have hliteral : package.rootMove.rightLambda () =
      some installed.rightLambda := by
    rw [profiledRawJointHybridExactRight_rootMove A installed package]
    rfl
  exact Option.some.inj (hselected.symm.trans hliteral)

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointHybridExactLeftActivation_lambda_eq
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    (profiledRawJointHybridExactLeftActivation A hwin installed).lambda =
      installed.leftLambda := by
  let package := profiledRawJointHybridExactLeftPolicy A hwin installed
  let activation := profiledRawJointHybridExactLeftActivation A hwin installed
  have hselected : package.rootMove.leftLambda () =
      some activation.lambda := activation.lambda_selected
  have hliteral : package.rootMove.leftLambda () =
      some installed.leftLambda := by
    rw [profiledRawJointHybridExactLeft_rootMove A installed package]
    rfl
  exact Option.some.inj (hselected.symm.trans hliteral)

/-! ## Finite truth tables of the exact literal children -/

/-- Uniform right descriptor whose allowed targets are precisely the finite
codes emitted by the exact-root activation. -/
noncomputable def profiledRawJointHybridExactRightUniformDescriptor
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ProfiledRawJointRightPhysicalSiblingDescriptor A := by
  classical
  let initial := installed.world.oneSidedState A .right
  let predicate := profiledRawJointHybridExactRightRootPredicate A installed
  let package := profiledRawJointHybridExactRightPolicy A hwin installed
  exact {
    source := installed.world.procOneSlot A
    allowed := fun target ↦ decide (∃ row past input,
      (profiledRawJointGuardedFirstRightTarget A strategy initial predicate
        package row past input).1 = target) }

/-- Left mirror. -/
noncomputable def profiledRawJointHybridExactLeftUniformDescriptor
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ProfiledRawJointLeftPhysicalSiblingDescriptor A := by
  classical
  let initial := installed.world.oneSidedState A .left
  let predicate := profiledRawJointHybridExactLeftRootPredicate A installed
  let package := profiledRawJointHybridExactLeftPolicy A hwin installed
  exact {
    source := installed.world.procTwoSlot A
    allowed := fun target ↦ decide (∃ row past input,
      (profiledRawJointGuardedFirstLeftTarget A strategy initial predicate
        package row past input).1 = target) }

/-! ## Uniform target-parametric activations -/

/-- Erase the exact right activation's source-dependent literal-child subtype
to the globally finite incidence-code target alphabet. -/
noncomputable def profiledRawJointHybridExactRightUniformActivation
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A
        (profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
          installed))
      (profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
        installed).source := by
  classical
  let initial := installed.world.oneSidedState A .right
  let predicate := profiledRawJointHybridExactRightRootPredicate A installed
  let package := profiledRawJointHybridExactRightPolicy A hwin installed
  let exact := profiledRawJointHybridExactRightActivation A hwin installed
  refine {
    lambda := exact.lambda
    initial_profile := exact.initial_profile
    forever := exact.forever
    target := fun row past input ↦
      (profiledRawJointGuardedFirstRightTarget A strategy initial predicate
        package row past input).1
    target_allowed := ?_
    target_state := ?_ }
  · intro row past input
    change decide (∃ row' past' input',
      (profiledRawJointGuardedFirstRightTarget A strategy initial predicate
        package row' past' input').1 =
          (profiledRawJointGuardedFirstRightTarget A strategy initial predicate
            package row past input).1) = true
    exact decide_eq_true ⟨row, past, input, rfl⟩
  · intro row past input
    unfold profiledRawJointUnitRightTargetProjection
    rw [exact.target_active_slot row past input]
    simp [profiledRawJointHybridExactRightUniformDescriptor]

/-- Left mirror. -/
noncomputable def profiledRawJointHybridExactLeftUniformActivation
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A
        (profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
          installed))
      (profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
        installed).source := by
  classical
  let initial := installed.world.oneSidedState A .left
  let predicate := profiledRawJointHybridExactLeftRootPredicate A installed
  let package := profiledRawJointHybridExactLeftPolicy A hwin installed
  let exact := profiledRawJointHybridExactLeftActivation A hwin installed
  refine {
    lambda := exact.lambda
    initial_profile := exact.initial_profile
    forever := exact.forever
    target := fun row past input ↦
      (profiledRawJointGuardedFirstLeftTarget A strategy initial predicate
        package row past input).1
    target_allowed := ?_
    target_state := ?_ }
  · intro row past input
    change decide (∃ row' past' input',
      (profiledRawJointGuardedFirstLeftTarget A strategy initial predicate
        package row' past' input').1 =
          (profiledRawJointGuardedFirstLeftTarget A strategy initial predicate
            package row past input).1) = true
    exact decide_eq_true ⟨row, past, input, rfl⟩
  · intro row past input
    unfold profiledRawJointUnitLeftTargetProjection
    rw [exact.target_active_slot row past input]
    simp [profiledRawJointHybridExactLeftUniformDescriptor]

/-! ## The uniform activations use the two literal pending senders -/

section
omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂]

/-- The right activation's blind sender is definitionally the process-one
sender at the literal strict-left member of the current world. -/
theorem profiledRawJointHybridExactRightUniformSender_eq_leftHistory
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    pairedRightSenderStrategy
        (profiledRawJointHybridExactRightUniformActivation A strategy hwin
          installed).lambda =
      blockSenderOne strategy (installed.world.procOne A).leftHistory := by
  change pairedRightSenderStrategy
      (profiledRawJointHybridExactRightActivation A hwin installed).lambda = _
  rw [profiledRawJointHybridExactRightActivation_lambda_eq A strategy hwin
    installed]
  rfl

/-- The same blind sender is also the literal simultaneous member's sender;
this is the pending-overlap equality, not a leader-dependent branch. -/
theorem profiledRawJointHybridExactRightUniformSender_eq_bothHistory
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    pairedRightSenderStrategy
        (profiledRawJointHybridExactRightUniformActivation A strategy hwin
          installed).lambda =
      blockSenderOne strategy (installed.world.procOne A).bothHistory := by
  calc
    pairedRightSenderStrategy
          (profiledRawJointHybridExactRightUniformActivation A strategy hwin
            installed).lambda =
        blockSenderOne strategy (installed.world.procOne A).leftHistory :=
      profiledRawJointHybridExactRightUniformSender_eq_leftHistory A strategy
        hwin installed
    _ = blockSenderOne strategy (installed.world.procOne A).bothHistory :=
      blockSenderOne_eq_of_view_eq strategy
        (installed.world.procOne A).view_eq

/-- Left-orientation mirror at the literal strict-right member. -/
theorem profiledRawJointHybridExactLeftUniformSender_eq_rightHistory
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    pairedLeftSenderStrategy
        (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
          installed).lambda =
      blockSenderTwo strategy (installed.world.procTwo A).rightHistory := by
  change pairedLeftSenderStrategy
      (profiledRawJointHybridExactLeftActivation A hwin installed).lambda = _
  rw [profiledRawJointHybridExactLeftActivation_lambda_eq A strategy hwin
    installed]
  rfl

/-- The mirror sender is also the literal simultaneous member's sender. -/
theorem profiledRawJointHybridExactLeftUniformSender_eq_bothHistory
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    pairedLeftSenderStrategy
        (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
          installed).lambda =
      blockSenderTwo strategy (installed.world.procTwo A).bothHistory := by
  calc
    pairedLeftSenderStrategy
          (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
            installed).lambda =
        blockSenderTwo strategy (installed.world.procTwo A).rightHistory :=
      profiledRawJointHybridExactLeftUniformSender_eq_rightHistory A strategy
        hwin installed
    _ = blockSenderTwo strategy (installed.world.procTwo A).bothHistory :=
      blockSenderTwo_eq_of_view_eq strategy
        (installed.world.procTwo A).view_eq

end

/-! ## Uniform receiver realizability -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointHybridExactRightUniformMonitor_realizable
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ∀ env : Nat → In₂ × In₁,
      (profiledRawJointRightPhysicalSiblingMonitor A
        (profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
          installed) false).WinsPlay
        (pairPlay
          (profiledRawJointTargetRightReceiverStrategy A
            (profiledRawJointHybridExactRightUniformActivation A strategy hwin
              installed))
          (pairedRightSenderStrategy
            (profiledRawJointHybridExactRightUniformActivation A strategy hwin
              installed).lambda) env) := by
  exact profiledRawJointTargetRightBlockMonitor_realizable A
    (profiledRawJointUnitRightTargetProjection A)
    (profiledRawJointRightPhysicalSiblingAllowed A
      (profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
        installed))
    (profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
      installed).source
    (profiledRawJointHybridExactRightUniformActivation A strategy hwin
      installed)

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointHybridExactLeftUniformMonitor_realizable
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ∀ env : Nat → In₁ × In₂,
      (profiledRawJointLeftPhysicalSiblingMonitor A
        (profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
          installed) false).WinsPlay
        (pairPlay
          (profiledRawJointTargetLeftReceiverStrategy A
            (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
              installed))
          (pairedLeftSenderStrategy
            (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
              installed).lambda) env) := by
  exact profiledRawJointTargetLeftBlockMonitor_realizable A
    (profiledRawJointUnitLeftTargetProjection A)
    (profiledRawJointLeftPhysicalSiblingAllowed A
      (profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
        installed))
    (profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
      installed).source
    (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
      installed)

end

end DetParityAutomaton

end DistributedSynthesis
