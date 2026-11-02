/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPersistentPolicyHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitRightBlockMonitor

/-!
# Target-parametric right blocks in one persistent hybrid policy

The ordinary singleton block monitor used a target whose type was tied to an
ordinary one-sided rational policy.  The monitor itself does not need that
representation.  It only consumes a finite target alphabet, a projection to
the profiled closing state, and a unary allowed-target predicate.

This file factors that exact interface for right blocks and instantiates it
with the complete state of one persistent hybrid policy.  Hence every
physical close remains an edge of the same hybrid policy; no fresh ordinary
policy is selected at the boundary.  The right orientation is proof-side
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

/-- One physical right lambda together with a finite table of closing
targets.  The monitor sees a target only through `targetState` and `Allowed`.
This is the smallest interface shared by ordinary and hybrid policy states. -/
structure ProfiledRawJointTargetRightBlockActivation
    (Target : Type t)
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A) where
  lambda : ProcOnePairedRightLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  initial_profile : rightInitialFirstProfile lambda = source.2
  forever : PairedRightForeverAccepts A source.1.1 lambda
  target : PairedEntryRow → List (In₂ × In₁) → In₂ × In₁ → Target
  target_allowed : ∀ row past input, Allowed (target row past input)
  target_state : ∀ row past input,
    targetState (target row past input) =
      .inr (.inr (profiledRawRightChildSlot A source lambda row past input))

/-- Certificate output for an arbitrary finite right-target alphabet. -/
abbrev ProfiledRawJointTargetRightReceiverOutput (Target : Type t) :=
  IndexedTargetReceiverOutput
    (PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    PairedEntryRow Target

/-- Forget the target certificate from a target-parametric right letter. -/
def profiledRawJointTargetRightPhysicalLetter
    {Target : Type t}
    (letter : RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁) :
    PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let _checkerState := A.initial
  indexedTargetPhysicalLetter letter

/-- The complete recurrent right monitor, parameterized only by a finite
target projection and its allowed-edge predicate. -/
noncomputable def profiledRawJointTargetRightBlockMonitor
    (Target : Type t) [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A) :
    BlockRecordMonitor.{v, u, max x y t, x, max u v x y s} In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁ := by
  classical
  let U := (pairedRightThreadSystem A source.1.1).universalRunDPA
  exact {
    State := ProfiledRightBlockMonitorState A U.State
    stateFinite := inferInstance
    initial := (U.initial, pairedRightScanInitial A source.1.1,
      fun _ ↦ none, true, true)
    step := fun monitorState letter ↦
      let physical := profiledRawJointTargetRightPhysicalLetter A letter
      let rootMatches := !monitorState.2.2.2.1 ||
        decide (pairedRightInformedForRow .first letter.2.1.physical =
          source.2 letter.1)
      let overlaps := ∀ row expected,
        monitorState.2.2.1 row = some expected →
          pairedRightClosingForRow row letter.2.1.physical =
            expected (letter.1.2, letter.1.1)
      let targetsSafe := ∀ row,
        erasePairedProfiledState A (targetState (letter.2.1.target row)) =
            pairedRightCloseTarget A monitorState.2.1 row physical ∧
          Allowed (letter.2.1.target row)
      (U.step monitorState.1 physical,
        pairedRightScanStep A monitorState.2.1 physical,
        fun row ↦ leftProfileOfProfiledState A
          (targetState (letter.2.1.target row)),
        false,
        monitorState.2.2.2.2 && rootMatches &&
          decide overlaps && decide targetsSafe)
    priority := fun monitorState ↦
      if monitorState.2.2.2.2 then U.priority monitorState.1 + 2 else 1
  }

/-! ## Semantic realization of the target-parametric monitor -/

/-- Full-information receiver induced by a target-parametric activation. -/
def profiledRawJointTargetRightReceiverStrategy
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source) :
    ReceiverBlockStrategy In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) :=
  fun past input ↦ {
    physical := pairedRightReceiverStrategy activation.lambda past input
    target := fun row ↦ activation.target row past input }

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

@[simp] theorem profiledRawJointTargetRightReceiverStrategy_physical
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    (profiledRawJointTargetRightReceiverStrategy A activation past input).physical =
      pairedRightReceiverStrategy activation.lambda past input :=
  rfl

theorem profiledRawJointTargetRightReceiverStrategy_target_profile
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    leftProfileOfProfiledState A
        (targetState
          ((profiledRawJointTargetRightReceiverStrategy A activation past
            input).target row)) =
      some (rightClosingProfile activation.lambda row past input) := by
  rw [profiledRawJointTargetRightReceiverStrategy,
    activation.target_state row past input]
  rfl

theorem profiledRawJointTargetRight_pairPlay_eq_letterAt
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (env : Nat → In₂ × In₁) (n : Nat) :
    pairPlay (profiledRawJointTargetRightReceiverStrategy A activation)
        (pairedRightSenderStrategy activation.lambda) env n =
      (env n,
        profiledRawJointTargetRightReceiverStrategy A activation
          (omegaPrefix env n) (env n),
        activation.lambda.blind (senderWord (omegaPrefix env n)) (env n).2) := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, pairedRightSenderStrategy, senderWord, omegaPrefix]

theorem profiledRawJointTargetRight_pairPlay_physical
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (env : Nat → In₂ × In₁) (n : Nat) :
    profiledRawJointTargetRightPhysicalLetter A
        (pairPlay (profiledRawJointTargetRightReceiverStrategy A activation)
          (pairedRightSenderStrategy activation.lambda) env n) =
      pairedRightBlockWord activation.lambda env n := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, profiledRawJointTargetRightPhysicalLetter,
    indexedTargetPhysicalLetter,
    profiledRawJointTargetRightReceiverStrategy,
    pairedRightReceiverStrategy, pairedRightSenderStrategy,
    pairedRightBlockWord, senderWord, omegaPrefix]

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
/-- Exact monitor run on the semantic target-parametric stream. -/
theorem profiledRawJointTargetRightBlockMonitor_run_eq
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (env : Nat → In₂ × In₁) : ∀ n,
    (profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
      source).run
        (pairPlay (profiledRawJointTargetRightReceiverStrategy A activation)
          (pairedRightSenderStrategy activation.lambda) env) n =
      ((pairedRightThreadSystem A source.1.1).universalRunDPA.run
          (pairedRightBlockWord activation.lambda env) n,
        pairedRightScanAfter A source.1.1 activation.lambda
          (omegaPrefix env n),
        profiledRightPendingAfter activation.lambda (omegaPrefix env n),
        decide (n = 0), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih,
        profiledRawJointTargetRight_pairPlay_eq_letterAt A activation env n,
        omegaPrefix_succ, pairedRightScanAfter_append,
        profiledRightPendingAfter_append]
      have hoverlaps : ∀ row expected,
          profiledRightPendingAfter activation.lambda (omegaPrefix env n) row =
              some expected →
            pairedRightClosingForRow row
                (profiledRawJointTargetRightReceiverStrategy A activation
                  (omegaPrefix env n) (env n)).physical =
              expected ((env n).2, (env n).1) := by
        simpa [profiledRawJointTargetRightReceiverStrategy,
          profiledRightReceiverStrategy] using
          (profiledRightPendingAfter_realizes A source.1.1 activation.lambda
            (omegaPrefix env n) (env n))
      have htargets : ∀ row,
          erasePairedProfiledState A
              (targetState
                ((profiledRawJointTargetRightReceiverStrategy A activation
                  (omegaPrefix env n) (env n)).target row)) =
            pairedRightCloseTarget A
              (pairedRightScanAfter A source.1.1 activation.lambda
                (omegaPrefix env n)) row
              (pairedRightBlockLetterAt activation.lambda
                (omegaPrefix env n) (env n)) ∧
          Allowed
            ((profiledRawJointTargetRightReceiverStrategy A activation
              (omegaPrefix env n) (env n)).target row) := by
        intro row
        constructor
        · rw [profiledRawJointTargetRightReceiverStrategy,
            activation.target_state row (omegaPrefix env n) (env n)]
          rw [← pairedProfiledOneChild_eq_profiledRawRightChildSlot A source
            activation.lambda row (omegaPrefix env n) (env n),
            erase_pairedProfiledOneChild,
            pairedRightCloseTarget_scanAfter]
        · exact activation.target_allowed row (omegaPrefix env n) (env n)
      have hphysicalAt :
          profiledRawJointTargetRightPhysicalLetter A
              (env n,
                profiledRawJointTargetRightReceiverStrategy A activation
                  (omegaPrefix env n) (env n),
                activation.lambda.blind
                  (senderWord (omegaPrefix env n)) (env n).2) =
            pairedRightBlockLetterAt activation.lambda
              (omegaPrefix env n) (env n) := rfl
      simp only [profiledRawJointTargetRightBlockMonitor]
      rw [hphysicalAt, decide_eq_true hoverlaps, decide_eq_true htargets]
      rw [← pairedRightBlockWord_eq_letterAt activation.lambda env n]
      by_cases hn : n = 0
      · subst n
        have hroot :
            pairedRightInformedForRow .first
                (pairedRightReceiverStrategy activation.lambda [] (env 0)) =
              source.2 (env 0) := by
          simpa [rightInitialFirstProfile] using
            congrFun activation.initial_profile (env 0)
        simp [omegaPrefix, hroot,
          profiledRawJointTargetRightReceiverStrategy_target_profile]
      · simp [hn,
          profiledRawJointTargetRightReceiverStrategy_target_profile]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
/-- The target-parametric right block is realizable whenever its activation
supplies the universal physical acceptance and exact finite targets. -/
theorem profiledRawJointTargetRightBlockMonitor_realizable
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source) :
    ∀ env : Nat → In₂ × In₁,
      (profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
        source).WinsPlay
        (pairPlay (profiledRawJointTargetRightReceiverStrategy A activation)
          (pairedRightSenderStrategy activation.lambda) env) := by
  intro env
  have huniversal := pairedRightUniversalDPA_accepts_of_forever
    A source.1.1 activation.lambda activation.forever env
  have hparity : NatSeqMinEvenParity
      (fun n ↦
        (pairedRightThreadSystem A source.1.1).universalRunDPA.priority
          ((pairedRightThreadSystem A source.1.1).universalRunDPA.run
            (pairedRightBlockWord activation.lambda env) n)) := huniversal
  have hshifted : NatSeqMinEvenParity
      (fun n ↦
        (pairedRightThreadSystem A source.1.1).universalRunDPA.priority
          ((pairedRightThreadSystem A source.1.1).universalRunDPA.run
            (pairedRightBlockWord activation.lambda env) n) + 2) :=
    (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hparity
  unfold BlockRecordMonitor.WinsPlay
  convert hshifted using 1
  funext n
  rw [profiledRawJointTargetRightBlockMonitor_run_eq A targetState Allowed
    source activation env n]
  simp [profiledRawJointTargetRightBlockMonitor]
  rfl

/-- Unconditional sender narrowing at the reusable target interface. -/
theorem exists_profiledRawJointTargetRightController
    {Target : Type t} [Fintype Target] [Inhabited Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source) :
    ∃ controller :
        TransitionRationalTree.{u, max u v x y s t, max u v x y s} In₁
        (NarrowedBlockLabel In₂ In₁
          (ProfiledRawJointTargetRightReceiverOutput
            (Out₁ := Out₁) (Out₂ := Out₂) Target)
          Out₁
          (profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
            source).State),
      NarrowedAllThreadsWin
        (profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
          source) controller.labeledTree := by
  have hrealizable :
      ∃ receiver : ReceiverBlockStrategy In₂ In₁
          (ProfiledRawJointTargetRightReceiverOutput
            (Out₁ := Out₁) (Out₂ := Out₂) Target),
        ∃ sender : SenderBlockStrategy In₁ Out₁,
          ∀ env : Nat → In₂ × In₁,
            (profiledRawJointTargetRightBlockMonitor A Target targetState
              Allowed source).WinsPlay (pairPlay receiver sender env) := by
    exact ⟨profiledRawJointTargetRightReceiverStrategy A activation,
      pairedRightSenderStrategy activation.lambda,
      profiledRawJointTargetRightBlockMonitor_realizable A targetState Allowed
        source activation⟩
  simpa only using
    (block_realizable_iff_implementable_controller_unconditional
      (profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
        source)).mp hrealizable

/-! ## Persistent-hybrid activation -/

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The physical-close theorem packages directly as the reusable activation,
with complete hybrid policy states as emitted certificates. -/
theorem nonempty_profiledRawJointHybridPersistentRightBlockActivation
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
    (source : ProfiledRawRightSlot A)
    (hsource : key.incidenceCode.family.right () = some source) :
    Nonempty
      (ProfiledRawJointTargetRightBlockActivation A
        (ProfiledRawJointHybridProvenancePolicyState A strategy initialCode)
        (profiledRawJointHybridPersistentRightTargetProfiledState A)
        (ProfiledRawJointHybridProvenanceAllowedTarget A strategy initialCode
          policy key.state)
        source) := by
  classical
  have hvalid := installed.move_valid A hwin
  rcases hvalid.2.2.2.1 () source hsource with
    ⟨lambda, hlambda, hprofile, hforever⟩
  refine ⟨{
    lambda := lambda
    initial_profile := hprofile
    forever := hforever
    target := fun row past input ↦
      (installed.strictSuccessorKey A
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input)).state
    target_allowed := ?_
    target_state := ?_ }⟩
  · intro row past input
    exact installed.strict_allowedTarget A
      (profiledRawJointUnitRightActualDirection
        (In₁ := In₁) (In₂ := In₂) row past input)
  · intro row past input
    rcases installed.unitRight_physicalClose A hwin source hsource row past
      input with ⟨lambda', hlambda', _hprofile', _hforever', hslot, _⟩
    have hlambdaEq : lambda' = lambda := by
      exact Option.some.inj (hlambda'.symm.trans hlambda)
    subst lambda'
    let targetKey := installed.strictSuccessorKey A
      (profiledRawJointUnitRightActualDirection
        (In₁ := In₁) (In₂ := In₂) row past input)
    exact profiledRawJointHybridPersistentRightTargetProfiledState_eq A
      targetKey.state targetKey.incidenceCode
      (profiledRawRightChildSlot A source lambda row past input)
      targetKey.state_code hslot

/-- A persistent hybrid right-live key therefore has a finite controller
whose every target remains in the same hybrid rational policy. -/
theorem exists_profiledRawJointHybridPersistentRightController
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
    (source : ProfiledRawRightSlot A)
    (hsource : key.incidenceCode.family.right () = some source) :
    let Target := ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode
    let targetState :=
      profiledRawJointHybridPersistentRightTargetProfiledState A
    let Allowed := ProfiledRawJointHybridProvenanceAllowedTarget A strategy
      initialCode policy key.state
    ∃ controller :
        TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
        (NarrowedBlockLabel In₂ In₁
          (ProfiledRawJointTargetRightReceiverOutput
            (Out₁ := Out₁) (Out₂ := Out₂) Target)
          Out₁
          (profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
            source).State),
      NarrowedAllThreadsWin
        (profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
          source) controller.labeledTree := by
  dsimp only
  let activation := Classical.choice
    (nonempty_profiledRawJointHybridPersistentRightBlockActivation A hwin
      installed source hsource)
  exact exists_profiledRawJointTargetRightController A
    (profiledRawJointHybridPersistentRightTargetProfiledState A)
    (ProfiledRawJointHybridProvenanceAllowedTarget A strategy initialCode
      policy key.state)
    source activation

end

end DetParityAutomaton

end DistributedSynthesis
