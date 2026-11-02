/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPersistentPolicyHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitLeftBlockMonitor

/-!
# Target-parametric left blocks in one persistent hybrid policy

The ordinary singleton block monitor used a target whose type was tied to an
ordinary one-sided rational policy.  The monitor itself does not need that
representation.  It only consumes a finite target alphabet, a projection to
the profiled closing state, and a unary allowed-target predicate.

This file factors that exact interface for left blocks and instantiates it
with the complete state of one persistent hybrid policy.  Hence every
physical close remains an edge of the same hybrid policy; no fresh ordinary
policy is selected at the boundary.  The left orientation is proof-side
indexing only and is not exposed to the blind sender.
-/

namespace DistributedSynthesis

universe u v x y s t

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

/-! ## The reusable finite-target interface -/

/-- One physical left lambda together with a finite table of closing
targets.  The monitor sees a target only through `targetState` and `Allowed`.
This is the smallest interface shared by ordinary and hybrid policy states. -/
structure ProfiledRawJointTargetLeftBlockActivation
    (Target : Type t)
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A) where
  lambda : ProcTwoPairedLeftLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  initial_profile : leftInitialFirstProfile lambda = source.2
  forever : PairedLeftForeverAccepts A source.1.1 lambda
  target : PairedEntryRow → List (In₁ × In₂) → In₁ × In₂ → Target
  target_allowed : ∀ row past input, Allowed (target row past input)
  target_state : ∀ row past input,
    targetState (target row past input) =
      .inr (.inl (profiledRawLeftChildSlot A source lambda row past input))

/-- Certificate output for an arbitrary finite left-target alphabet. -/
abbrev ProfiledRawJointTargetLeftReceiverOutput (Target : Type t) :=
  IndexedTargetReceiverOutput
    (PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    PairedEntryRow Target

/-- Forget the target certificate from a target-parametric left letter. -/
def profiledRawJointTargetLeftPhysicalLetter
    {Target : Type t}
    (letter : RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂) :
    PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let _checkerState := A.initial
  indexedTargetPhysicalLetter letter

/-- The complete recurrent left monitor, parameterized only by a finite
target projection and its allowed-edge predicate. -/
noncomputable def profiledRawJointTargetLeftBlockMonitor
    (Target : Type t) [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A) :
    BlockRecordMonitor.{u, v, max x y t, y, max u v y s} In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂ := by
  classical
  let U := (pairedLeftThreadSystem A source.1.1).universalRunDPA
  exact {
    State := ProfiledLeftBlockMonitorState A U.State
    stateFinite := inferInstance
    initial := (U.initial, pairedLeftScanInitial A source.1.1,
      fun _ ↦ none, true, true)
    step := fun monitorState letter ↦
      let physical := profiledRawJointTargetLeftPhysicalLetter A letter
      let rootMatches := !monitorState.2.2.2.1 ||
        decide (pairedLeftInformedForRow .first letter.2.1.physical =
          source.2 letter.1)
      let overlaps := ∀ row expected,
        monitorState.2.2.1 row = some expected →
          pairedLeftClosingForRow row letter.2.1.physical =
            expected (letter.1.2, letter.1.1)
      let targetsSafe := ∀ row,
        erasePairedProfiledState A (targetState (letter.2.1.target row)) =
            pairedLeftCloseTarget A monitorState.2.1 row physical ∧
          Allowed (letter.2.1.target row)
      (U.step monitorState.1 physical,
        pairedLeftScanStep A monitorState.2.1 physical,
        fun row ↦ rightProfileOfProfiledState A
          (targetState (letter.2.1.target row)),
        false,
        monitorState.2.2.2.2 && rootMatches &&
          decide overlaps && decide targetsSafe)
    priority := fun monitorState ↦
      if monitorState.2.2.2.2 then U.priority monitorState.1 + 2 else 1
  }

/-! ## Semantic realization of the target-parametric monitor -/

/-- Full-information receiver induced by a target-parametric activation. -/
def profiledRawJointTargetLeftReceiverStrategy
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source) :
    ReceiverBlockStrategy In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) :=
  fun past input ↦ {
    physical := pairedLeftReceiverStrategy activation.lambda past input
    target := fun row ↦ activation.target row past input }

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

@[simp] theorem profiledRawJointTargetLeftReceiverStrategy_physical
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    (profiledRawJointTargetLeftReceiverStrategy A activation past input).physical =
      pairedLeftReceiverStrategy activation.lambda past input :=
  rfl

theorem profiledRawJointTargetLeftReceiverStrategy_target_profile
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    rightProfileOfProfiledState A
        (targetState
          ((profiledRawJointTargetLeftReceiverStrategy A activation past
            input).target row)) =
      some (leftClosingProfile activation.lambda row past input) := by
  rw [profiledRawJointTargetLeftReceiverStrategy,
    activation.target_state row past input]
  rfl

theorem profiledRawJointTargetLeft_pairPlay_eq_letterAt
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (env : Nat → In₁ × In₂) (n : Nat) :
    pairPlay (profiledRawJointTargetLeftReceiverStrategy A activation)
        (pairedLeftSenderStrategy activation.lambda) env n =
      (env n,
        profiledRawJointTargetLeftReceiverStrategy A activation
          (omegaPrefix env n) (env n),
        activation.lambda.blind (senderWord (omegaPrefix env n)) (env n).2) := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, pairedLeftSenderStrategy, senderWord, omegaPrefix]

theorem profiledRawJointTargetLeft_pairPlay_physical
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (env : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointTargetLeftPhysicalLetter A
        (pairPlay (profiledRawJointTargetLeftReceiverStrategy A activation)
          (pairedLeftSenderStrategy activation.lambda) env n) =
      pairedLeftBlockWord activation.lambda env n := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, profiledRawJointTargetLeftPhysicalLetter,
    indexedTargetPhysicalLetter,
    profiledRawJointTargetLeftReceiverStrategy,
    pairedLeftReceiverStrategy, pairedLeftSenderStrategy,
    pairedLeftBlockWord, pairedLeftBlockLetterAt, senderWord, omegaPrefix]

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
/-- Exact monitor run on the semantic target-parametric stream. -/
theorem profiledRawJointTargetLeftBlockMonitor_run_eq
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (env : Nat → In₁ × In₂) : ∀ n,
    (profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
      source).run
        (pairPlay (profiledRawJointTargetLeftReceiverStrategy A activation)
          (pairedLeftSenderStrategy activation.lambda) env) n =
      ((pairedLeftThreadSystem A source.1.1).universalRunDPA.run
          (pairedLeftBlockWord activation.lambda env) n,
        pairedLeftScanAfter A source.1.1 activation.lambda
          (omegaPrefix env n),
        profiledLeftPendingAfter activation.lambda (omegaPrefix env n),
        decide (n = 0), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih,
        profiledRawJointTargetLeft_pairPlay_eq_letterAt A activation env n,
        omegaPrefix_succ, pairedLeftScanAfter_append,
        profiledLeftPendingAfter_append]
      have hoverlaps : ∀ row expected,
          profiledLeftPendingAfter activation.lambda (omegaPrefix env n) row =
              some expected →
            pairedLeftClosingForRow row
                (profiledRawJointTargetLeftReceiverStrategy A activation
                  (omegaPrefix env n) (env n)).physical =
              expected ((env n).2, (env n).1) := by
        simpa [profiledRawJointTargetLeftReceiverStrategy,
          profiledLeftReceiverStrategy] using
          (profiledLeftPendingAfter_realizes A source.1.1 activation.lambda
            (omegaPrefix env n) (env n))
      have htargets : ∀ row,
          erasePairedProfiledState A
              (targetState
                ((profiledRawJointTargetLeftReceiverStrategy A activation
                  (omegaPrefix env n) (env n)).target row)) =
            pairedLeftCloseTarget A
              (pairedLeftScanAfter A source.1.1 activation.lambda
                (omegaPrefix env n)) row
              (pairedLeftBlockLetterAt activation.lambda
                (omegaPrefix env n) (env n)) ∧
          Allowed
            ((profiledRawJointTargetLeftReceiverStrategy A activation
              (omegaPrefix env n) (env n)).target row) := by
        intro row
        constructor
        · rw [profiledRawJointTargetLeftReceiverStrategy,
            activation.target_state row (omegaPrefix env n) (env n)]
          rw [← pairedProfiledTwoChild_eq_profiledRawLeftChildSlot A source
            activation.lambda row (omegaPrefix env n) (env n),
            erase_pairedProfiledTwoChild,
            pairedLeftCloseTarget_scanAfter]
        · exact activation.target_allowed row (omegaPrefix env n) (env n)
      have hphysicalAt :
          profiledRawJointTargetLeftPhysicalLetter A
              (env n,
                profiledRawJointTargetLeftReceiverStrategy A activation
                  (omegaPrefix env n) (env n),
                activation.lambda.blind
                  (senderWord (omegaPrefix env n)) (env n).2) =
            pairedLeftBlockLetterAt activation.lambda
              (omegaPrefix env n) (env n) := rfl
      simp only [profiledRawJointTargetLeftBlockMonitor]
      rw [hphysicalAt, decide_eq_true hoverlaps, decide_eq_true htargets]
      change
        ((pairedLeftThreadSystem A source.1.1).universalRunDPA.step
            ((pairedLeftThreadSystem A source.1.1).universalRunDPA.run
              (pairedLeftBlockWord activation.lambda env) n)
            (pairedLeftBlockWord activation.lambda env n), _, _, _, _) = _
      by_cases hn : n = 0
      · subst n
        have hroot :
            pairedLeftInformedForRow .first
                (pairedLeftReceiverStrategy activation.lambda [] (env 0)) =
              source.2 (env 0) := by
          simpa [leftInitialFirstProfile] using
            congrFun activation.initial_profile (env 0)
        simp [omegaPrefix, hroot,
          profiledRawJointTargetLeftReceiverStrategy_target_profile]
      · simp [hn,
          profiledRawJointTargetLeftReceiverStrategy_target_profile]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
/-- The target-parametric left block is realizable whenever its activation
supplies the universal physical acceptance and exact finite targets. -/
theorem profiledRawJointTargetLeftBlockMonitor_realizable
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source) :
    ∀ env : Nat → In₁ × In₂,
      (profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
        source).WinsPlay
        (pairPlay (profiledRawJointTargetLeftReceiverStrategy A activation)
          (pairedLeftSenderStrategy activation.lambda) env) := by
  intro env
  have huniversal := pairedLeftUniversalDPA_accepts_of_forever
    A source.1.1 activation.lambda activation.forever env
  have hparity : NatSeqMinEvenParity
      (fun n ↦
        (pairedLeftThreadSystem A source.1.1).universalRunDPA.priority
          ((pairedLeftThreadSystem A source.1.1).universalRunDPA.run
            (pairedLeftBlockWord activation.lambda env) n)) := huniversal
  have hshifted : NatSeqMinEvenParity
      (fun n ↦
        (pairedLeftThreadSystem A source.1.1).universalRunDPA.priority
          ((pairedLeftThreadSystem A source.1.1).universalRunDPA.run
            (pairedLeftBlockWord activation.lambda env) n) + 2) :=
    (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hparity
  unfold BlockRecordMonitor.WinsPlay
  convert hshifted using 1
  funext n
  rw [profiledRawJointTargetLeftBlockMonitor_run_eq A targetState Allowed
    source activation env n]
  simp [profiledRawJointTargetLeftBlockMonitor]
  rfl

/-- Unconditional sender narrowing at the reusable target interface. -/
theorem exists_profiledRawJointTargetLeftController
    {Target : Type t} [Fintype Target] [Inhabited Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source) :
    ∃ controller :
        TransitionRationalTree.{v, max u v x y s t, max u v y s} In₂
        (NarrowedBlockLabel In₁ In₂
          (ProfiledRawJointTargetLeftReceiverOutput
            (Out₁ := Out₁) (Out₂ := Out₂) Target)
          Out₂
          (profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
            source).State),
      NarrowedAllThreadsWin
        (profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
          source) controller.labeledTree := by
  have hrealizable :
      ∃ receiver : ReceiverBlockStrategy In₁ In₂
          (ProfiledRawJointTargetLeftReceiverOutput
            (Out₁ := Out₁) (Out₂ := Out₂) Target),
        ∃ sender : SenderBlockStrategy In₂ Out₂,
          ∀ env : Nat → In₁ × In₂,
            (profiledRawJointTargetLeftBlockMonitor A Target targetState
              Allowed source).WinsPlay (pairPlay receiver sender env) := by
    exact ⟨profiledRawJointTargetLeftReceiverStrategy A activation,
      pairedLeftSenderStrategy activation.lambda,
      profiledRawJointTargetLeftBlockMonitor_realizable A targetState Allowed
        source activation⟩
  simpa only using
    (block_realizable_iff_implementable_controller_unconditional
      (profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
        source)).mp hrealizable

/-! ## Persistent-hybrid activation -/

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The physical-close theorem packages directly as the reusable activation,
with complete hybrid policy states as emitted certificates. -/
theorem nonempty_profiledRawJointHybridPersistentLeftBlockActivation
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {key : ProfiledRawJointHybridOneSidedPolicyKey A strategy initialCode
      policy}
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (source : ProfiledRawLeftSlot A)
    (hsource : key.incidenceCode.family.left () = some source) :
    Nonempty
      (ProfiledRawJointTargetLeftBlockActivation A
        (ProfiledRawJointHybridProvenancePolicyState A strategy initialCode)
        (profiledRawJointHybridPersistentLeftTargetProfiledState A)
        (ProfiledRawJointHybridProvenanceAllowedTarget A strategy initialCode
          policy key.state)
        source) := by
  classical
  have hvalid := installed.move_valid A hwin
  rcases hvalid.2.2.2.2.2.1 () source hsource with
    ⟨lambda, hlambda, hprofile, hforever⟩
  refine ⟨{
    lambda := lambda
    initial_profile := hprofile
    forever := hforever
    target := fun row past input ↦
      (installed.strictSuccessorKey A
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input)).state
    target_allowed := ?_
    target_state := ?_ }⟩
  · intro row past input
    exact installed.strict_allowedTarget A
      (profiledRawJointUnitLeftActualDirection
        (In₁ := In₁) (In₂ := In₂) row past input)
  · intro row past input
    rcases installed.unitLeft_physicalClose A hwin source hsource row past
      input with ⟨lambda', hlambda', _hprofile', _hforever', hslot, _⟩
    have hlambdaEq : lambda' = lambda := by
      exact Option.some.inj (hlambda'.symm.trans hlambda)
    subst lambda'
    let targetKey := installed.strictSuccessorKey A
      (profiledRawJointUnitLeftActualDirection
        (In₁ := In₁) (In₂ := In₂) row past input)
    exact profiledRawJointHybridPersistentLeftTargetProfiledState_eq A
      targetKey.state targetKey.incidenceCode
      (profiledRawLeftChildSlot A source lambda row past input)
      targetKey.state_code hslot

/-- A persistent hybrid left-live key therefore has a finite controller
whose every target remains in the same hybrid rational policy. -/
theorem exists_profiledRawJointHybridPersistentLeftController
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {key : ProfiledRawJointHybridOneSidedPolicyKey A strategy initialCode
      policy}
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (source : ProfiledRawLeftSlot A)
    (hsource : key.incidenceCode.family.left () = some source) :
    let Target := ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode
    let targetState :=
      profiledRawJointHybridPersistentLeftTargetProfiledState A
    let Allowed := ProfiledRawJointHybridProvenanceAllowedTarget A strategy
      initialCode policy key.state
    ∃ controller :
        TransitionRationalTree.{v, max u v x y s, max u v y s} In₂
        (NarrowedBlockLabel In₁ In₂
          (ProfiledRawJointTargetLeftReceiverOutput
            (Out₁ := Out₁) (Out₂ := Out₂) Target)
          Out₂
          (profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
            source).State),
      NarrowedAllThreadsWin
        (profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
          source) controller.labeledTree := by
  dsimp only
  let activation := Classical.choice
    (nonempty_profiledRawJointHybridPersistentLeftBlockActivation A hwin
      installed source hsource)
  exact exists_profiledRawJointTargetLeftController A
    (profiledRawJointHybridPersistentLeftTargetProfiledState A)
    (ProfiledRawJointHybridProvenanceAllowedTarget A strategy initialCode
      policy key.state)
    source activation

end

end DetParityAutomaton

end DistributedSynthesis
