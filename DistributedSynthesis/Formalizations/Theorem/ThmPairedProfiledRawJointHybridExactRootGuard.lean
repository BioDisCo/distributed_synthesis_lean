/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonOneRoundReplacement
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointHybridBothRootGuard

/-!
# Exact guarded roots at a common/strict fork

The finite `.both` output guard alone does not identify the semantic child:
two raw moves may have the same first physical output and different finite
successor codes.  Here the root predicate pins the complete literal
singleton move.  The opposite lane is absent only in proof data; for the
matching strict direction that erasure leaves the successor code unchanged.

No process observes the selected side or a strict-leader bit.
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

/-! ## Exact singleton root predicates -/

/-- Pin the complete raw root move to the literal right singleton. -/
def profiledRawJointHybridExactRightRootPredicate
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit)) : Prop :=
  move = (installed.world.oneSidedState A .right).move A

/-- Left-singleton mirror. -/
def profiledRawJointHybridExactLeftRootPredicate
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit)) : Prop :=
  move = (installed.world.oneSidedState A .left).move A

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointHybridExactRightRootPredicate_literal
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    profiledRawJointHybridExactRightRootPredicate A installed
      ((installed.world.oneSidedState A .right).move A) :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointHybridExactLeftRootPredicate_literal
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    profiledRawJointHybridExactLeftRootPredicate A installed
      ((installed.world.oneSidedState A .left).move A) :=
  rfl

/-! ## Fail-fast lane-erasure calculation -/

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- A right actual successor depends only on the active right lane and the
right-facing part of the physical direction. -/
theorem profiledRawJointRightActualIncidenceNext_congr_active
    (code code' : ProfiledRawJointFamilyCode A (I := Unit))
    (move move' : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (direction direction' : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (hcode : code.right = code'.right)
    (hpattern : code.rightPattern = code'.rightPattern)
    (hmove : move.rightLambda = move'.rightLambda)
    (hpivot : direction.rightPivot = direction'.rightPivot)
    (hpast : direction.rightPhysicalPast = direction'.rightPhysicalPast)
    (hinput : direction.rightInput = direction'.rightInput) :
    profiledRawJointRightActualIncidenceNext A code move direction =
      profiledRawJointRightActualIncidenceNext A code' move' direction' := by
  have hcandidate :
      A.profiledRawRightCandidateChild code move direction =
        A.profiledRawRightCandidateChild code' move' direction' := by
    funext candidate
    simp only [DetParityAutomaton.profiledRawRightCandidateChild]
    rw [congrFun hcode candidate.1, congrFun hmove candidate.1,
      hpast, hinput]
  have hchildren :
      A.profiledRawRightIndexedChildCode code move direction =
        A.profiledRawRightIndexedChildCode code' move' direction' := by
    simp only [DetParityAutomaton.profiledRawRightIndexedChildCode]
    rw [hpattern, hcandidate, hpivot]
  apply ProfiledRawJointIncidenceCode.eq_of_fields A
  · apply ProfiledRawJointFamilyCode.eq_of_fields A
    · rfl
    · exact congrArg profiledRawOptionalChildSlots hchildren
    · rfl
    · exact congrArg profiledRawActiveCanonicalRowPattern
        (congrArg profiledRawOptionalChildSlots hchildren)
  · rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Left-facing mirror of active-lane congruence. -/
theorem profiledRawJointLeftActualIncidenceNext_congr_active
    (code code' : ProfiledRawJointFamilyCode A (I := Unit))
    (move move' : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (direction direction' : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (hcode : code.left = code'.left)
    (hpattern : code.leftPattern = code'.leftPattern)
    (hmove : move.leftLambda = move'.leftLambda)
    (hpivot : direction.leftPivot = direction'.leftPivot)
    (hpast : direction.leftPhysicalPast = direction'.leftPhysicalPast)
    (hinput : direction.leftInput = direction'.leftInput) :
    profiledRawJointLeftActualIncidenceNext A code move direction =
      profiledRawJointLeftActualIncidenceNext A code' move' direction' := by
  have hcandidate :
      A.profiledRawLeftCandidateChild code move direction =
        A.profiledRawLeftCandidateChild code' move' direction' := by
    funext candidate
    simp only [DetParityAutomaton.profiledRawLeftCandidateChild]
    rw [congrFun hcode candidate.1, congrFun hmove candidate.1,
      hpast, hinput]
  have hchildren :
      A.profiledRawLeftIndexedChildCode code move direction =
        A.profiledRawLeftIndexedChildCode code' move' direction' := by
    simp only [DetParityAutomaton.profiledRawLeftIndexedChildCode]
    rw [hpattern, hcandidate, hpivot]
  apply ProfiledRawJointIncidenceCode.eq_of_fields A
  · apply ProfiledRawJointFamilyCode.eq_of_fields A
    · exact congrArg profiledRawOptionalChildSlots hchildren
    · rfl
    · exact congrArg profiledRawActiveCanonicalRowPattern
        (congrArg profiledRawOptionalChildSlots hchildren)
    · rfl
  · rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Erasing the inactive left lane does not change the strict-right child. -/
theorem profiledRawJointHybridExactRight_literal_strictChild
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (input : In₁ × In₂) :
    profiledRawJointOneSidedNext A
        ((installed.world.oneSidedState A .right).code A)
        ((installed.world.oneSidedState A .right).move A)
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) .both [] (input.2, input.1)) =
      profiledRawJointOneSidedNext A installed.incidenceCode installed.rawMove
        (profiledRawJointCommonOneRoundStrictRight input) := by
  rw [installed.world.rightSingleton_code_eq_leftActual A
    installed.incidenceCode installed.incidence_eq]
  rw [← installed.move_eq]
  apply profiledRawJointRightActualIncidenceNext_congr_active A
  · rfl
  · rfl
  · funext index
    cases index
    rfl
  · rfl
  · rfl
  · rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Left-lane mirror of the strict-child calculation. -/
theorem profiledRawJointHybridExactLeft_literal_strictChild
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (input : In₁ × In₂) :
    profiledRawJointOneSidedNext A
        ((installed.world.oneSidedState A .left).code A)
        ((installed.world.oneSidedState A .left).move A)
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) .both [] input) =
      profiledRawJointOneSidedNext A installed.incidenceCode installed.rawMove
        (profiledRawJointCommonOneRoundStrictLeft input) := by
  rw [installed.world.leftSingleton_code_eq_rightActual A
    installed.incidenceCode installed.incidence_eq]
  rw [← installed.move_eq]
  apply profiledRawJointLeftActualIncidenceNext_congr_active A
  · rfl
  · rfl
  · funext index
    cases index
    rfl
  · rfl
  · rfl
  · rfl

/-! ## Canonical exact right root -/

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact-root rationalization of the literal right singleton. -/
theorem nonempty_profiledRawJointHybridExactRightPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    Nonempty (ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed)) :=
  nonempty_profiledRawJointOneSidedRootPinnedProvenancePolicy A strategy hwin
    (installed.world.oneSidedState A .right)
    (profiledRawJointHybridExactRightRootPredicate A installed) rfl

/-- Select the exact right policy once for the installed common move. -/
noncomputable def profiledRawJointHybridExactRightPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  Classical.choice
    (nonempty_profiledRawJointHybridExactRightPolicy A hwin installed)

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The selected policy's root move is literally the singleton move. -/
theorem profiledRawJointHybridExactRight_rootMove
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed)) :
    package.rootMove = (installed.world.oneSidedState A .right).move A :=
  package.rootMove_realizes.2.1

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Provenance therefore selects a semantic source with exactly that move,
not merely the same first output table. -/
theorem profiledRawJointHybridExactRight_selectedSource_move
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed)) :
    (profiledRawJointRootPinnedSelectedSource A strategy
        (installed.world.oneSidedState A .right)
        (profiledRawJointHybridExactRightRootPredicate A installed)
        package).move A =
      (installed.world.oneSidedState A .right).move A := by
  rw [profiledRawJointRootPinnedSelectedSource_move A strategy]
  exact profiledRawJointHybridExactRight_rootMove A installed package

/-- Canonical activation of the installed literal process-one slot. -/
noncomputable def profiledRawJointHybridExactRightActivation
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  Classical.choice
    (nonempty_profiledRawJointGuardedFirstRightBlockActivation A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed)
      (profiledRawJointHybridExactRightPolicy A hwin installed)
      (installed.world.procOneSlot A) (by rfl))

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The semantic exact activation retains the common process-two output on
the ambiguous `.both` row. -/
theorem profiledRawJointHybridExactRightActivation_bothOutput
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed))
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed) package
      (installed.world.procOneSlot A))
    (input : In₁ × In₂) :
    pairedRightInformedForRow .both
        (pairedRightReceiverStrategy activation.lambda []
          (input.2, input.1)) =
      installed.bothOutputTwo A input := by
  have hweak : profiledRawJointHybridRightBothRootPredicate A installed
      package.rootMove := by
    rw [profiledRawJointHybridExactRight_rootMove A installed package]
    exact profiledRawJointHybridRightBothRootPredicate_literal A installed
  exact hweak activation.lambda activation.lambda_selected input

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The semantic receiver's exact `.both` target is the strict-right child
of the original two-lane installed move. -/
theorem profiledRawJointHybridExactRightActivation_strictChild
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed))
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed) package
      (installed.world.procOneSlot A))
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedFirstRightReceiverStrategy A activation []
        (input.2, input.1)).target .both).1 =
      profiledRawJointOneSidedNext A installed.incidenceCode installed.rawMove
        (profiledRawJointCommonOneRoundStrictRight input) := by
  rw [profiledRawJointGuardedFirstRightReceiverStrategy_target_val]
  dsimp only
  rw [profiledRawJointRootPinnedSelectedSource_code A strategy,
    profiledRawJointHybridExactRight_selectedSource_move A installed package]
  exact profiledRawJointHybridExactRight_literal_strictChild A installed input

/-! ## Exact first-letter guard and narrowed right controller -/

/-- The right first record must carry both the ambiguous common output and
the exact strict-right successor code. -/
noncomputable def profiledRawJointHybridExactRightAllowed
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed))
    (letter : RealizedBlockRound In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy
        (installed.world.oneSidedState A .right)
        (profiledRawJointHybridExactRightRootPredicate A installed) package)
      Out₁) : Bool := by
  classical
  exact decide
    (pairedRightInformedForRow .both letter.2.1.physical =
        installed.bothOutputTwo A (letter.1.2, letter.1.1) ∧
      (letter.2.1.target .both).1 =
        profiledRawJointOneSidedNext A installed.incidenceCode
          installed.rawMove
          (profiledRawJointCommonOneRoundStrictRight
            (letter.1.2, letter.1.1)))

/-- Base exceptional monitor strengthened at its first record by exact root
output and exact strict-child code. -/
noncomputable def profiledRawJointHybridExactRightMonitor
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed)) :=
  (profiledRawJointGuardedFirstRightBlockMonitor A strategy
    (installed.world.oneSidedState A .right)
    (profiledRawJointHybridExactRightRootPredicate A installed) package
    (installed.world.procOneSlot A)).firstLetterGuard
      (profiledRawJointHybridExactRightAllowed A installed package)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The exact semantic right block realizes the strengthened monitor. -/
theorem profiledRawJointHybridExactRightMonitor_realizable
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed))
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed) package
      (installed.world.procOneSlot A)) :
    ∀ env : Nat → In₂ × In₁,
      (profiledRawJointHybridExactRightMonitor A installed package).WinsPlay
        (pairPlay
          (profiledRawJointGuardedFirstRightReceiverStrategy A activation)
          (pairedRightSenderStrategy activation.lambda) env) := by
  classical
  apply BlockRecordMonitor.firstLetterGuard_realizable
    (profiledRawJointGuardedFirstRightBlockMonitor A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed) package
      (installed.world.procOneSlot A))
    (profiledRawJointHybridExactRightAllowed A installed package)
    (profiledRawJointGuardedFirstRightReceiverStrategy A activation)
    (pairedRightSenderStrategy activation.lambda)
    (profiledRawJointGuardedFirstRightBlockMonitor_realizable A
      (installed.world.procOneSlot A) activation)
  intro env
  rw [profiledRawJointGuardedFirstRight_pairPlay_eq_letterAt A activation env 0]
  apply decide_eq_true
  constructor
  · simpa [omegaPrefix] using
      profiledRawJointHybridExactRightActivation_bothOutput A installed package
        activation ((env 0).2, (env 0).1)
  · simpa [omegaPrefix] using
      profiledRawJointHybridExactRightActivation_strictChild A installed
        package activation ((env 0).2, (env 0).1)

/-- Existence of a finite narrowed exact-right controller. -/
theorem exists_profiledRawJointHybridExactRightController
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed))
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed) package
      (installed.world.procOneSlot A)) :
    ∃ controller : TransitionRationalTree.{u, max u v x y s,
        max u v x y s} In₁
        (NarrowedBlockLabel In₂ In₁
          (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy
            (installed.world.oneSidedState A .right)
            (profiledRawJointHybridExactRightRootPredicate A installed) package)
          Out₁ (profiledRawJointHybridExactRightMonitor A installed package
            ).State),
      NarrowedAllThreadsWin
        (profiledRawJointHybridExactRightMonitor A installed package)
        controller.labeledTree := by
  apply (block_realizable_iff_implementable_controller_unconditional
    (profiledRawJointHybridExactRightMonitor A installed package)).mp
  exact ⟨profiledRawJointGuardedFirstRightReceiverStrategy A activation,
    pairedRightSenderStrategy activation.lambda,
    profiledRawJointHybridExactRightMonitor_realizable A installed package
      activation⟩

/-- Canonical finite exact-right controller. -/
noncomputable def profiledRawJointHybridExactRightController
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  Classical.choose
    (exists_profiledRawJointHybridExactRightController A installed
      (profiledRawJointHybridExactRightPolicy A hwin installed)
      (profiledRawJointHybridExactRightActivation A hwin installed))

/-- All threads of the canonical right controller win the exact guard. -/
theorem profiledRawJointHybridExactRightController_wins
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    NarrowedAllThreadsWin
      (profiledRawJointHybridExactRightMonitor A installed
        (profiledRawJointHybridExactRightPolicy A hwin installed))
      (profiledRawJointHybridExactRightController A hwin installed
        ).labeledTree :=
  Classical.choose_spec
    (exists_profiledRawJointHybridExactRightController A installed
      (profiledRawJointHybridExactRightPolicy A hwin installed)
      (profiledRawJointHybridExactRightActivation A hwin installed))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every winning narrowed exact-right controller emits both required root
facts, including the code equation missing from the weaker guard. -/
theorem profiledRawJointHybridExactRight_root
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed))
    (narrowed : LabeledTree In₁
      (NarrowedBlockLabel In₂ In₁
        (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy
          (installed.world.oneSidedState A .right)
          (profiledRawJointHybridExactRightRootPredicate A installed) package)
        Out₁ (profiledRawJointHybridExactRightMonitor A installed package
          ).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointHybridExactRightMonitor A installed package) narrowed)
    (move : In₂ × In₁) :
    let record := narrowedRecord
      (profiledRawJointHybridExactRightMonitor A installed package)
      (narrowed [])
      (profiledRawJointHybridExactRightMonitor A installed package).initial
      move
    pairedRightInformedForRow .both record.2.1.physical =
        installed.bothOutputTwo A (move.2, move.1) ∧
      (record.2.1.target .both).1 =
        profiledRawJointOneSidedNext A installed.incidenceCode
          installed.rawMove
          (profiledRawJointCommonOneRoundStrictRight (move.2, move.1)) := by
  classical
  have hallowed := BlockRecordMonitor.firstLetterGuard_root_allowed
    (profiledRawJointGuardedFirstRightBlockMonitor A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed) package
      (installed.world.procOneSlot A))
    (profiledRawJointHybridExactRightAllowed A installed package)
    narrowed hthreads move
  exact of_decide_eq_true hallowed

/-- Canonical controller root output. -/
theorem profiledRawJointHybridExactRightController_root_output
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (move : In₂ × In₁) :
    pairedRightInformedForRow .both
        ((narrowedRecord
          (profiledRawJointHybridExactRightMonitor A installed
            (profiledRawJointHybridExactRightPolicy A hwin installed))
          (profiledRawJointHybridExactRightController A hwin installed
            |>.labeledTree [])
          (profiledRawJointHybridExactRightMonitor A installed
            (profiledRawJointHybridExactRightPolicy A hwin installed)).initial
          move).2.1.physical) =
      installed.bothOutputTwo A (move.2, move.1) :=
  (profiledRawJointHybridExactRight_root A installed
    (profiledRawJointHybridExactRightPolicy A hwin installed)
    (profiledRawJointHybridExactRightController A hwin installed).labeledTree
    (profiledRawJointHybridExactRightController_wins A hwin installed)
    move).1

/-- Canonical controller's emitted `.both` target is exactly the installed
strict-right raw child. -/
theorem profiledRawJointHybridExactRightController_root_strictChild
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (move : In₂ × In₁) :
    ((narrowedRecord
      (profiledRawJointHybridExactRightMonitor A installed
        (profiledRawJointHybridExactRightPolicy A hwin installed))
      (profiledRawJointHybridExactRightController A hwin installed
        |>.labeledTree [])
      (profiledRawJointHybridExactRightMonitor A installed
        (profiledRawJointHybridExactRightPolicy A hwin installed)).initial
      move).2.1.target .both).1 =
      profiledRawJointOneSidedNext A installed.incidenceCode installed.rawMove
        (profiledRawJointCommonOneRoundStrictRight (move.2, move.1)) :=
  (profiledRawJointHybridExactRight_root A installed
    (profiledRawJointHybridExactRightPolicy A hwin installed)
    (profiledRawJointHybridExactRightController A hwin installed).labeledTree
    (profiledRawJointHybridExactRightController_wins A hwin installed)
    move).2

/-! ## Canonical exact left root -/

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact-root rationalization of the literal left singleton. -/
theorem nonempty_profiledRawJointHybridExactLeftPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    Nonempty (ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed)) :=
  nonempty_profiledRawJointOneSidedRootPinnedProvenancePolicy A strategy hwin
    (installed.world.oneSidedState A .left)
    (profiledRawJointHybridExactLeftRootPredicate A installed) rfl

/-- Select the exact left policy once for the installed common move. -/
noncomputable def profiledRawJointHybridExactLeftPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  Classical.choice
    (nonempty_profiledRawJointHybridExactLeftPolicy A hwin installed)

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The selected left policy's root move is literally the singleton move. -/
theorem profiledRawJointHybridExactLeft_rootMove
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed)) :
    package.rootMove = (installed.world.oneSidedState A .left).move A :=
  package.rootMove_realizes.2.1

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The selected semantic source has the exact left-singleton move. -/
theorem profiledRawJointHybridExactLeft_selectedSource_move
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed)) :
    (profiledRawJointRootPinnedSelectedSource A strategy
        (installed.world.oneSidedState A .left)
        (profiledRawJointHybridExactLeftRootPredicate A installed)
        package).move A =
      (installed.world.oneSidedState A .left).move A := by
  rw [profiledRawJointRootPinnedSelectedSource_move A strategy]
  exact profiledRawJointHybridExactLeft_rootMove A installed package

/-- Canonical activation of the installed literal process-two slot. -/
noncomputable def profiledRawJointHybridExactLeftActivation
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  Classical.choice
    (nonempty_profiledRawJointGuardedFirstLeftBlockActivation A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed)
      (profiledRawJointHybridExactLeftPolicy A hwin installed)
      (installed.world.procTwoSlot A) (by rfl))

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Exact left activation retains the common process-one output. -/
theorem profiledRawJointHybridExactLeftActivation_bothOutput
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed))
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed) package
      (installed.world.procTwoSlot A))
    (input : In₁ × In₂) :
    pairedLeftInformedForRow .both
        (pairedLeftReceiverStrategy activation.lambda [] input) =
      installed.bothOutputOne A input := by
  have hweak : profiledRawJointHybridLeftBothRootPredicate A installed
      package.rootMove := by
    rw [profiledRawJointHybridExactLeft_rootMove A installed package]
    exact profiledRawJointHybridLeftBothRootPredicate_literal A installed
  exact hweak activation.lambda activation.lambda_selected input

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact left semantic target equals the installed strict-left child. -/
theorem profiledRawJointHybridExactLeftActivation_strictChild
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed))
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed) package
      (installed.world.procTwoSlot A))
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedFirstLeftReceiverStrategy A activation [] input
        ).target .both).1 =
      profiledRawJointOneSidedNext A installed.incidenceCode installed.rawMove
        (profiledRawJointCommonOneRoundStrictLeft input) := by
  rw [profiledRawJointGuardedFirstLeftReceiverStrategy_target_val]
  dsimp only
  rw [profiledRawJointRootPinnedSelectedSource_code A strategy,
    profiledRawJointHybridExactLeft_selectedSource_move A installed package]
  exact profiledRawJointHybridExactLeft_literal_strictChild A installed input

/-! ## Exact first-letter guard and narrowed left controller -/

/-- The left first record carries both the common output and exact
strict-left child code. -/
noncomputable def profiledRawJointHybridExactLeftAllowed
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed))
    (letter : RealizedBlockRound In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy
        (installed.world.oneSidedState A .left)
        (profiledRawJointHybridExactLeftRootPredicate A installed) package)
      Out₂) : Bool := by
  classical
  exact decide
    (pairedLeftInformedForRow .both letter.2.1.physical =
        installed.bothOutputOne A letter.1 ∧
      (letter.2.1.target .both).1 =
        profiledRawJointOneSidedNext A installed.incidenceCode
          installed.rawMove
          (profiledRawJointCommonOneRoundStrictLeft letter.1))

/-- Exact-left guarded monitor. -/
noncomputable def profiledRawJointHybridExactLeftMonitor
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed)) :=
  (profiledRawJointGuardedFirstLeftBlockMonitor A strategy
    (installed.world.oneSidedState A .left)
    (profiledRawJointHybridExactLeftRootPredicate A installed) package
    (installed.world.procTwoSlot A)).firstLetterGuard
      (profiledRawJointHybridExactLeftAllowed A installed package)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact left semantic block realizes the strengthened monitor. -/
theorem profiledRawJointHybridExactLeftMonitor_realizable
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed))
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed) package
      (installed.world.procTwoSlot A)) :
    ∀ env : Nat → In₁ × In₂,
      (profiledRawJointHybridExactLeftMonitor A installed package).WinsPlay
        (pairPlay
          (profiledRawJointGuardedFirstLeftReceiverStrategy A activation)
          (pairedLeftSenderStrategy activation.lambda) env) := by
  classical
  apply BlockRecordMonitor.firstLetterGuard_realizable
    (profiledRawJointGuardedFirstLeftBlockMonitor A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed) package
      (installed.world.procTwoSlot A))
    (profiledRawJointHybridExactLeftAllowed A installed package)
    (profiledRawJointGuardedFirstLeftReceiverStrategy A activation)
    (pairedLeftSenderStrategy activation.lambda)
    (profiledRawJointGuardedFirstLeftBlockMonitor_realizable A
      (installed.world.procTwoSlot A) activation)
  intro env
  rw [profiledRawJointGuardedFirstLeft_pairPlay_eq_letterAt A activation env 0]
  apply decide_eq_true
  constructor
  · simpa [omegaPrefix] using
      profiledRawJointHybridExactLeftActivation_bothOutput A installed package
        activation (env 0)
  · simpa [omegaPrefix] using
      profiledRawJointHybridExactLeftActivation_strictChild A installed
        package activation (env 0)

/-- Existence of a finite narrowed exact-left controller. -/
theorem exists_profiledRawJointHybridExactLeftController
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed))
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed) package
      (installed.world.procTwoSlot A)) :
    ∃ controller : TransitionRationalTree.{v, max u v x y s,
        max u v x y s} In₂
        (NarrowedBlockLabel In₁ In₂
          (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy
            (installed.world.oneSidedState A .left)
            (profiledRawJointHybridExactLeftRootPredicate A installed) package)
          Out₂ (profiledRawJointHybridExactLeftMonitor A installed package
            ).State),
      NarrowedAllThreadsWin
        (profiledRawJointHybridExactLeftMonitor A installed package)
        controller.labeledTree := by
  apply (block_realizable_iff_implementable_controller_unconditional
    (profiledRawJointHybridExactLeftMonitor A installed package)).mp
  exact ⟨profiledRawJointGuardedFirstLeftReceiverStrategy A activation,
    pairedLeftSenderStrategy activation.lambda,
    profiledRawJointHybridExactLeftMonitor_realizable A installed package
      activation⟩

/-- Canonical finite exact-left controller. -/
noncomputable def profiledRawJointHybridExactLeftController
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  Classical.choose
    (exists_profiledRawJointHybridExactLeftController A installed
      (profiledRawJointHybridExactLeftPolicy A hwin installed)
      (profiledRawJointHybridExactLeftActivation A hwin installed))

/-- All canonical left controller threads win. -/
theorem profiledRawJointHybridExactLeftController_wins
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    NarrowedAllThreadsWin
      (profiledRawJointHybridExactLeftMonitor A installed
        (profiledRawJointHybridExactLeftPolicy A hwin installed))
      (profiledRawJointHybridExactLeftController A hwin installed
        ).labeledTree :=
  Classical.choose_spec
    (exists_profiledRawJointHybridExactLeftController A installed
      (profiledRawJointHybridExactLeftPolicy A hwin installed)
      (profiledRawJointHybridExactLeftActivation A hwin installed))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Any winning narrowed exact-left controller has the exact two root facts. -/
theorem profiledRawJointHybridExactLeft_root
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed))
    (narrowed : LabeledTree In₂
      (NarrowedBlockLabel In₁ In₂
        (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy
          (installed.world.oneSidedState A .left)
          (profiledRawJointHybridExactLeftRootPredicate A installed) package)
        Out₂ (profiledRawJointHybridExactLeftMonitor A installed package
          ).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointHybridExactLeftMonitor A installed package) narrowed)
    (move : In₁ × In₂) :
    let record := narrowedRecord
      (profiledRawJointHybridExactLeftMonitor A installed package)
      (narrowed [])
      (profiledRawJointHybridExactLeftMonitor A installed package).initial
      move
    pairedLeftInformedForRow .both record.2.1.physical =
        installed.bothOutputOne A move ∧
      (record.2.1.target .both).1 =
        profiledRawJointOneSidedNext A installed.incidenceCode
          installed.rawMove (profiledRawJointCommonOneRoundStrictLeft move) := by
  classical
  have hallowed := BlockRecordMonitor.firstLetterGuard_root_allowed
    (profiledRawJointGuardedFirstLeftBlockMonitor A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed) package
      (installed.world.procTwoSlot A))
    (profiledRawJointHybridExactLeftAllowed A installed package)
    narrowed hthreads move
  exact of_decide_eq_true hallowed

/-- Canonical left controller root output. -/
theorem profiledRawJointHybridExactLeftController_root_output
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (move : In₁ × In₂) :
    pairedLeftInformedForRow .both
        ((narrowedRecord
          (profiledRawJointHybridExactLeftMonitor A installed
            (profiledRawJointHybridExactLeftPolicy A hwin installed))
          (profiledRawJointHybridExactLeftController A hwin installed
            |>.labeledTree [])
          (profiledRawJointHybridExactLeftMonitor A installed
            (profiledRawJointHybridExactLeftPolicy A hwin installed)).initial
          move).2.1.physical) =
      installed.bothOutputOne A move :=
  (profiledRawJointHybridExactLeft_root A installed
    (profiledRawJointHybridExactLeftPolicy A hwin installed)
    (profiledRawJointHybridExactLeftController A hwin installed).labeledTree
    (profiledRawJointHybridExactLeftController_wins A hwin installed)
    move).1

/-- Canonical left controller's `.both` target is the installed strict-left
raw child. -/
theorem profiledRawJointHybridExactLeftController_root_strictChild
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (move : In₁ × In₂) :
    ((narrowedRecord
      (profiledRawJointHybridExactLeftMonitor A installed
        (profiledRawJointHybridExactLeftPolicy A hwin installed))
      (profiledRawJointHybridExactLeftController A hwin installed
        |>.labeledTree [])
      (profiledRawJointHybridExactLeftMonitor A installed
        (profiledRawJointHybridExactLeftPolicy A hwin installed)).initial
      move).2.1.target .both).1 =
      profiledRawJointOneSidedNext A installed.incidenceCode installed.rawMove
        (profiledRawJointCommonOneRoundStrictLeft move) :=
  (profiledRawJointHybridExactLeft_root A installed
    (profiledRawJointHybridExactLeftPolicy A hwin installed)
    (profiledRawJointHybridExactLeftController A hwin installed).labeledTree
    (profiledRawJointHybridExactLeftController_wins A hwin installed)
    move).2

end

end DetParityAutomaton

end DistributedSynthesis
