/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemBlockRecordMonitorFirstLetterGuard
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonInstalledMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedInitialState
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstRightBlockMonitor
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstLeftBlockMonitor

/-!
# Leader-free simultaneous-output guard at the first strict block

At a common control, a process cannot distinguish an actual simultaneous
receive from the receive side of the first strict block.  The exceptional
one-sided controller must therefore retain the `.both` output of the common
installed move on its first local receive.

The two guards below are finite sticky objective tests.  They inspect only
the first realized local block record, and hence do not tell either process
which strict orientation Nature chose.  The exact semantic block realizes
the guard whenever its root lambda has the common `.both` receive profile;
conversely every narrowed winning controller has that exact root output.
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

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}

/-! ## One-shot semantic root predicates

The rational root is constrained only by the finite simultaneous receive
table.  The complete infinite lambda is not pinned. -/

/-- A right raw move has the process-two simultaneous receive table of the
installed common move. -/
def profiledRawJointHybridRightBothRootPredicate
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit)) : Prop :=
  ∀ lambda, move.rightLambda () = some lambda →
    ∀ input : In₁ × In₂,
      pairedRightInformedForRow .both
          (pairedRightReceiverStrategy lambda [] (input.2, input.1)) =
        installed.bothOutputTwo A input

/-- Left mirror of the finite root predicate. -/
def profiledRawJointHybridLeftBothRootPredicate
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit)) : Prop :=
  ∀ lambda, move.leftLambda () = some lambda →
    ∀ input : In₁ × In₂,
      pairedLeftInformedForRow .both
          (pairedLeftReceiverStrategy lambda [] input) =
        installed.bothOutputOne A input

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The literal right singleton of the common world satisfies the finite
simultaneous receive predicate. -/
theorem profiledRawJointHybridRightBothRootPredicate_literal
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    profiledRawJointHybridRightBothRootPredicate A installed
      ((installed.world.oneSidedState A .right).move A) := by
  intro lambda hlambda input
  have hlambda' : lambda = installed.rightLambda := by
    apply Option.some.inj
    calc
      some lambda =
          ((installed.world.oneSidedState A .right).move A).rightLambda () :=
        hlambda.symm
      _ = some installed.rightLambda := rfl
  subst lambda
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Literal left-singleton mirror. -/
theorem profiledRawJointHybridLeftBothRootPredicate_literal
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    profiledRawJointHybridLeftBothRootPredicate A installed
      ((installed.world.oneSidedState A .left).move A) := by
  intro lambda hlambda input
  have hlambda' : lambda = installed.leftLambda := by
    apply Option.some.inj
    calc
      some lambda =
          ((installed.world.oneSidedState A .left).move A).leftLambda () :=
        hlambda.symm
      _ = some installed.leftLambda := rfl
  subst lambda
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The winning semantic tree admits a root-pinned right policy carrying only
the finite `.both` receive profile. -/
theorem nonempty_profiledRawJointHybridRightBothRootPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    Nonempty (ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridRightBothRootPredicate A installed)) :=
  nonempty_profiledRawJointOneSidedRootPinnedProvenancePolicy A strategy hwin
    (installed.world.oneSidedState A .right)
    (profiledRawJointHybridRightBothRootPredicate A installed)
    (profiledRawJointHybridRightBothRootPredicate_literal A installed)

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left-policy mirror. -/
theorem nonempty_profiledRawJointHybridLeftBothRootPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    Nonempty (ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridLeftBothRootPredicate A installed)) :=
  nonempty_profiledRawJointOneSidedRootPinnedProvenancePolicy A strategy hwin
    (installed.world.oneSidedState A .left)
    (profiledRawJointHybridLeftBothRootPredicate A installed)
    (profiledRawJointHybridLeftBothRootPredicate_literal A installed)

/-! ## Right block: process two is the informed receiver -/

/-- Finite first-record test for the `.both` output of process two. -/
noncomputable def profiledRawJointGuardedFirstRightBothAllowed
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (letter : RealizedBlockRound In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
        RootPred package) Out₁) : Bool := by
  classical
  exact decide
    (pairedRightInformedForRow .both letter.2.1.physical =
      installed.bothOutputTwo A (letter.1.2, letter.1.1))

/-- Exceptional right monitor strengthened by the simultaneous-output test. -/
noncomputable def profiledRawJointGuardedFirstRightBothGuardMonitor
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (source : ProfiledRawRightSlot A) :
    BlockRecordMonitor In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
        RootPred package) Out₁ :=
  (profiledRawJointGuardedFirstRightBlockMonitor A strategy initial RootPred
    package source).firstLetterGuard
      (profiledRawJointGuardedFirstRightBothAllowed A installed)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The literal exceptional right block realizes the strengthened monitor.
The hypothesis is a finite table equality on the first local receive; it is
later supplied by a one-shot root predicate, not by a leader signal. -/
theorem profiledRawJointGuardedFirstRightBothGuardMonitor_realizable
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      initial RootPred package source)
    (hboth : ∀ input : In₁ × In₂,
      pairedRightInformedForRow .both
          (pairedRightReceiverStrategy activation.lambda []
            (input.2, input.1)) =
        installed.bothOutputTwo A input) :
    ∀ env : Nat → In₂ × In₁,
      (profiledRawJointGuardedFirstRightBothGuardMonitor A installed source
        ).WinsPlay
        (pairPlay
          (profiledRawJointGuardedFirstRightReceiverStrategy A activation)
          (pairedRightSenderStrategy activation.lambda) env) := by
  classical
  apply BlockRecordMonitor.firstLetterGuard_realizable
    (profiledRawJointGuardedFirstRightBlockMonitor A strategy initial RootPred
      package source)
    (profiledRawJointGuardedFirstRightBothAllowed A installed)
    (profiledRawJointGuardedFirstRightReceiverStrategy A activation)
    (pairedRightSenderStrategy activation.lambda)
    (profiledRawJointGuardedFirstRightBlockMonitor_realizable A source
      activation)
  intro env
  rw [profiledRawJointGuardedFirstRight_pairPlay_eq_letterAt A activation env 0]
  apply decide_eq_true
  simpa [profiledRawJointGuardedFirstRightBothAllowed, omegaPrefix] using
    hboth ((env 0).2, (env 0).1)

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- A right activation selected under the finite root predicate has the
required simultaneous receive table. -/
theorem profiledRawJointHybridRightBothActivation_profile
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridRightBothRootPredicate A installed))
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridRightBothRootPredicate A installed) package
      (installed.world.procOneSlot A)) :
    ∀ input : In₁ × In₂,
      pairedRightInformedForRow .both
          (pairedRightReceiverStrategy activation.lambda []
            (input.2, input.1)) =
        installed.bothOutputTwo A input :=
  package.rootMove_realizes.2.1 activation.lambda activation.lambda_selected

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Thus the literal right activation realizes the guard with no additional
mathematical hypothesis. -/
theorem profiledRawJointHybridRightBothGuardMonitor_realizable
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridRightBothRootPredicate A installed))
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridRightBothRootPredicate A installed) package
      (installed.world.procOneSlot A)) :
    ∀ env : Nat → In₂ × In₁,
      (profiledRawJointGuardedFirstRightBothGuardMonitor A installed
        (installed.world.procOneSlot A)).WinsPlay
        (pairPlay
          (profiledRawJointGuardedFirstRightReceiverStrategy A activation)
          (pairedRightSenderStrategy activation.lambda) env) :=
  profiledRawJointGuardedFirstRightBothGuardMonitor_realizable A installed
    (installed.world.procOneSlot A) activation
    (profiledRawJointHybridRightBothActivation_profile A installed package
      activation)

/-- Unconditional narrowing of the right activation preserves the exact
common `.both` receiver output at the finite controller root. -/
theorem exists_profiledRawJointHybridRightBothGuardController
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridRightBothRootPredicate A installed))
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridRightBothRootPredicate A installed) package
      (installed.world.procOneSlot A)) :
    ∃ controller : TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
        (NarrowedBlockLabel In₂ In₁
          (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy
            (installed.world.oneSidedState A .right)
            (profiledRawJointHybridRightBothRootPredicate A installed) package)
          Out₁
          (profiledRawJointGuardedFirstRightBothGuardMonitor A installed
            (installed.world.procOneSlot A)).State),
      NarrowedAllThreadsWin
        (profiledRawJointGuardedFirstRightBothGuardMonitor A installed
          (installed.world.procOneSlot A)) controller.labeledTree := by
  apply (block_realizable_iff_implementable_controller_unconditional
    (profiledRawJointGuardedFirstRightBothGuardMonitor A installed
      (installed.world.procOneSlot A))).mp
  exact ⟨profiledRawJointGuardedFirstRightReceiverStrategy A activation,
    pairedRightSenderStrategy activation.lambda,
    profiledRawJointHybridRightBothGuardMonitor_realizable A installed package
      activation⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Any narrowed right controller winning the strengthened monitor emits the
common installed process-two output on its first `.both` receiver row. -/
theorem profiledRawJointGuardedFirstRightBothGuard_root_output
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (source : ProfiledRawRightSlot A)
    (narrowed : LabeledTree In₁
      (NarrowedBlockLabel In₂ In₁
        (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
          RootPred package) Out₁
        (profiledRawJointGuardedFirstRightBothGuardMonitor A installed source
          ).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointGuardedFirstRightBothGuardMonitor A installed source)
      narrowed)
    (move : In₂ × In₁) :
    pairedRightInformedForRow .both
        ((narrowedRecord
          (profiledRawJointGuardedFirstRightBothGuardMonitor A installed source)
          (narrowed [])
          (profiledRawJointGuardedFirstRightBothGuardMonitor A installed source
            ).initial move).2.1.physical) =
      installed.bothOutputTwo A (move.2, move.1) := by
  classical
  have hallowed := BlockRecordMonitor.firstLetterGuard_root_allowed
    (profiledRawJointGuardedFirstRightBlockMonitor A strategy initial RootPred
      package source)
    (profiledRawJointGuardedFirstRightBothAllowed A installed)
    narrowed hthreads move
  exact of_decide_eq_true hallowed

/-! ## Left block: process one is the informed receiver -/

/-- Finite first-record test for the `.both` output of process one. -/
noncomputable def profiledRawJointGuardedFirstLeftBothAllowed
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (letter : RealizedBlockRound In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
        RootPred package) Out₂) : Bool := by
  classical
  exact decide
    (pairedLeftInformedForRow .both letter.2.1.physical =
      installed.bothOutputOne A letter.1)

/-- Exceptional left monitor strengthened by the simultaneous-output test. -/
noncomputable def profiledRawJointGuardedFirstLeftBothGuardMonitor
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (source : ProfiledRawLeftSlot A) :
    BlockRecordMonitor In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
        RootPred package) Out₂ :=
  (profiledRawJointGuardedFirstLeftBlockMonitor A strategy initial RootPred
    package source).firstLetterGuard
      (profiledRawJointGuardedFirstLeftBothAllowed A installed)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Literal semantic realization of the left mirror. -/
theorem profiledRawJointGuardedFirstLeftBothGuardMonitor_realizable
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      initial RootPred package source)
    (hboth : ∀ input : In₁ × In₂,
      pairedLeftInformedForRow .both
          (pairedLeftReceiverStrategy activation.lambda [] input) =
        installed.bothOutputOne A input) :
    ∀ env : Nat → In₁ × In₂,
      (profiledRawJointGuardedFirstLeftBothGuardMonitor A installed source
        ).WinsPlay
        (pairPlay
          (profiledRawJointGuardedFirstLeftReceiverStrategy A activation)
          (pairedLeftSenderStrategy activation.lambda) env) := by
  classical
  apply BlockRecordMonitor.firstLetterGuard_realizable
    (profiledRawJointGuardedFirstLeftBlockMonitor A strategy initial RootPred
      package source)
    (profiledRawJointGuardedFirstLeftBothAllowed A installed)
    (profiledRawJointGuardedFirstLeftReceiverStrategy A activation)
    (pairedLeftSenderStrategy activation.lambda)
    (profiledRawJointGuardedFirstLeftBlockMonitor_realizable A source
      activation)
  intro env
  rw [profiledRawJointGuardedFirstLeft_pairPlay_eq_letterAt A activation env 0]
  apply decide_eq_true
  simpa [profiledRawJointGuardedFirstLeftBothAllowed, omegaPrefix] using
    hboth (env 0)

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- A left activation selected under the finite root predicate has the
required simultaneous receive table. -/
theorem profiledRawJointHybridLeftBothActivation_profile
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridLeftBothRootPredicate A installed))
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridLeftBothRootPredicate A installed) package
      (installed.world.procTwoSlot A)) :
    ∀ input : In₁ × In₂,
      pairedLeftInformedForRow .both
          (pairedLeftReceiverStrategy activation.lambda [] input) =
        installed.bothOutputOne A input :=
  package.rootMove_realizes.2.1 activation.lambda activation.lambda_selected

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Literal left activation realizes the guard unconditionally. -/
theorem profiledRawJointHybridLeftBothGuardMonitor_realizable
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridLeftBothRootPredicate A installed))
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridLeftBothRootPredicate A installed) package
      (installed.world.procTwoSlot A)) :
    ∀ env : Nat → In₁ × In₂,
      (profiledRawJointGuardedFirstLeftBothGuardMonitor A installed
        (installed.world.procTwoSlot A)).WinsPlay
        (pairPlay
          (profiledRawJointGuardedFirstLeftReceiverStrategy A activation)
          (pairedLeftSenderStrategy activation.lambda) env) :=
  profiledRawJointGuardedFirstLeftBothGuardMonitor_realizable A installed
    (installed.world.procTwoSlot A) activation
    (profiledRawJointHybridLeftBothActivation_profile A installed package
      activation)

/-- Unconditional left-controller narrowing with the exact common output
retained at the root. -/
theorem exists_profiledRawJointHybridLeftBothGuardController
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridLeftBothRootPredicate A installed))
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridLeftBothRootPredicate A installed) package
      (installed.world.procTwoSlot A)) :
    ∃ controller : TransitionRationalTree.{v, max u v x y s, max u v x y s} In₂
        (NarrowedBlockLabel In₁ In₂
          (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy
            (installed.world.oneSidedState A .left)
            (profiledRawJointHybridLeftBothRootPredicate A installed) package)
          Out₂
          (profiledRawJointGuardedFirstLeftBothGuardMonitor A installed
            (installed.world.procTwoSlot A)).State),
      NarrowedAllThreadsWin
        (profiledRawJointGuardedFirstLeftBothGuardMonitor A installed
          (installed.world.procTwoSlot A)) controller.labeledTree := by
  apply (block_realizable_iff_implementable_controller_unconditional
    (profiledRawJointGuardedFirstLeftBothGuardMonitor A installed
      (installed.world.procTwoSlot A))).mp
  exact ⟨profiledRawJointGuardedFirstLeftReceiverStrategy A activation,
    pairedLeftSenderStrategy activation.lambda,
    profiledRawJointHybridLeftBothGuardMonitor_realizable A installed package
      activation⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Any narrowed left controller has the exact common process-one output on
its first `.both` receiver row. -/
theorem profiledRawJointGuardedFirstLeftBothGuard_root_output
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (source : ProfiledRawLeftSlot A)
    (narrowed : LabeledTree In₂
      (NarrowedBlockLabel In₁ In₂
        (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
          RootPred package) Out₂
        (profiledRawJointGuardedFirstLeftBothGuardMonitor A installed source
          ).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointGuardedFirstLeftBothGuardMonitor A installed source)
      narrowed)
    (move : In₁ × In₂) :
    pairedLeftInformedForRow .both
        ((narrowedRecord
          (profiledRawJointGuardedFirstLeftBothGuardMonitor A installed source)
          (narrowed [])
          (profiledRawJointGuardedFirstLeftBothGuardMonitor A installed source
            ).initial move).2.1.physical) =
      installed.bothOutputOne A move := by
  classical
  have hallowed := BlockRecordMonitor.firstLetterGuard_root_allowed
    (profiledRawJointGuardedFirstLeftBlockMonitor A strategy initial RootPred
      package source)
    (profiledRawJointGuardedFirstLeftBothAllowed A installed)
    narrowed hthreads move
  exact of_decide_eq_true hallowed

end

end DetParityAutomaton

end DistributedSynthesis
