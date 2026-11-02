/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartFirstThenBothMonitor
import DistributedSynthesis.Formalizations.Theorem.ThmMullerToDPA

/-!
# Conjoining the ordinary and first-then-both block monitors

The old target monitor and the new mixed-lane monitor carry independent
parity conditions.  Taking the pointwise minimum of their priorities would
not express conjunction.  Instead, this file reuses the verified route

`DPA → deterministic Muller → Muller intersection → DPA`.

It first packages that route as a generic conjunction operation on
`BlockRecordMonitor`, then instantiates it on the transported old monitor and
the first-then-both monitor.  The resulting single finite monitor can be fed
directly to unconditional sender narrowing.
-/

namespace DistributedSynthesis

universe u v x y w z s t

namespace BlockRecordMonitor

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}

/-- Regard a record monitor as a DPA over realized block rounds. -/
def toDPA
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut) :
    DetParityAutomaton (RealizedBlockRound RIn SIn ROut SOut) where
  State := M.State
  stateFinite := M.stateFinite
  initial := M.initial
  step := M.step
  priority := M.priority

/-- Regard a DPA over realized block rounds as a block monitor. -/
def ofDPA
    (A : DetParityAutomaton.{max u v x y, w}
      (RealizedBlockRound RIn SIn ROut SOut)) :
    BlockRecordMonitor RIn SIn ROut SOut where
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  step := A.step
  priority := A.priority

theorem toDPA_run
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (play : Nat → RealizedBlockRound RIn SIn ROut SOut) : ∀ n,
    M.toDPA.run play n = M.run play n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change M.step (M.toDPA.run play n) (play n) =
        M.step (M.run play n) (play n)
      rw [ih]

theorem ofDPA_run
    (A : DetParityAutomaton.{max u v x y, w}
      (RealizedBlockRound RIn SIn ROut SOut))
    (play : Nat → RealizedBlockRound RIn SIn ROut SOut) : ∀ n,
    (ofDPA A).run play n = A.run play n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change A.step ((ofDPA A).run play n) (play n) =
        A.step (A.run play n) (play n)
      rw [ih]

theorem toDPA_accepts_iff_wins
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (play : Nat → RealizedBlockRound RIn SIn ROut SOut) :
    M.toDPA.Accepts play ↔ M.WinsPlay play := by
  change NatSeqMinEvenParity (fun n ↦ M.priority (M.toDPA.run play n)) ↔
    NatSeqMinEvenParity (fun n ↦ M.priority (M.run play n))
  rw [show (fun n ↦ M.priority (M.toDPA.run play n)) =
      (fun n ↦ M.priority (M.run play n)) by
    funext n
    rw [toDPA_run M play n]]

theorem ofDPA_wins_iff_accepts
    (A : DetParityAutomaton.{max u v x y, w}
      (RealizedBlockRound RIn SIn ROut SOut))
    (play : Nat → RealizedBlockRound RIn SIn ROut SOut) :
    (ofDPA A).WinsPlay play ↔ A.Accepts play := by
  change NatSeqMinEvenParity (fun n ↦ A.priority ((ofDPA A).run play n)) ↔
    NatSeqMinEvenParity (fun n ↦ A.priority (A.run play n))
  rw [show (fun n ↦ A.priority ((ofDPA A).run play n)) =
      (fun n ↦ A.priority (A.run play n)) by
    funext n
    rw [ofDPA_run A play n]]

/-- Certified parity conjunction of two record monitors over the same
alphabet. -/
noncomputable def conj
    (left : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (right : BlockRecordMonitor.{u, v, x, y, z} RIn SIn ROut SOut) :
    BlockRecordMonitor RIn SIn ROut SOut :=
  ofDPA
    ((DetMullerAutomaton.LAR.eventAutomaton_toDPACompilation
      (A := left.toDPA.toMuller.inter right.toDPA.toMuller)).dpa)

/-- The compiled monitor accepts exactly when both input monitors accept. -/
theorem conj_wins_iff
    (left : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (right : BlockRecordMonitor.{u, v, x, y, z} RIn SIn ROut SOut)
    (play : Nat → RealizedBlockRound RIn SIn ROut SOut) :
    (left.conj right).WinsPlay play ↔
      left.WinsPlay play ∧ right.WinsPlay play := by
  unfold conj
  rw [ofDPA_wins_iff_accepts]
  rw [DetMullerAutomaton.ToDPACompilation.correct]
  rw [DetMullerAutomaton.inter_accepts_iff]
  rw [DetParityAutomaton.toMuller_accepts_iff]
  rw [DetParityAutomaton.toMuller_accepts_iff]
  exact and_congr (toDPA_accepts_iff_wins left play)
    (toDPA_accepts_iff_wins right play)

end BlockRecordMonitor

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

/-- One right monitor enforcing all two constant-row obligations and the
actual first-then-both restart lane. -/
noncomputable def profiledRawJointTargetRightFirstThenBothCombinedMonitor
    (Target : Type t) [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A) :=
  (profiledRawJointTargetRightFirstThenBothBaseMonitor A Target targetState
    Allowed source).conj
      (profiledRawJointRightFirstThenBothMonitor A Target targetState Allowed
        source.1.1)

/-- Left combined monitor. -/
noncomputable def profiledRawJointTargetLeftFirstThenBothCombinedMonitor
    (Target : Type t) [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A) :=
  (profiledRawJointTargetLeftFirstThenBothBaseMonitor A Target targetState
    Allowed source).conj
      (profiledRawJointLeftFirstThenBothMonitor A Target targetState Allowed
        source.1.1)

/-- A source extension realizes the single right combined monitor. -/
theorem profiledRawJointTargetRightFirstThenBothCombinedMonitor_realizable
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetRightFirstThenBothActivationExtension A activation)
    (env : Nat → In₂ × In₁) :
    (profiledRawJointTargetRightFirstThenBothCombinedMonitor A Target
      targetState Allowed source).WinsPlay
        (pairPlay
          (profiledRawJointTargetRightFirstThenBothReceiverStrategyOfExtension
            A activation extension)
          (pairedRightSenderStrategy activation.lambda) env) := by
  apply (BlockRecordMonitor.conj_wins_iff _ _ _).mpr
  constructor
  · exact profiledRawJointTargetRightFirstThenBothBaseMonitor_realizable A
      activation extension.target env
  · exact profiledRawJointRightFirstThenBothMonitor_realizable A targetState
      Allowed source activation extension env

/-- Left combined realization. -/
theorem profiledRawJointTargetLeftFirstThenBothCombinedMonitor_realizable
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetLeftFirstThenBothActivationExtension A activation)
    (env : Nat → In₁ × In₂) :
    (profiledRawJointTargetLeftFirstThenBothCombinedMonitor A Target targetState
      Allowed source).WinsPlay
        (pairPlay
          (profiledRawJointTargetLeftFirstThenBothReceiverStrategyOfExtension A
            activation extension)
          (pairedLeftSenderStrategy activation.lambda) env) := by
  apply (BlockRecordMonitor.conj_wins_iff _ _ _).mpr
  constructor
  · exact profiledRawJointTargetLeftFirstThenBothBaseMonitor_realizable A
      activation extension.target env
  · exact profiledRawJointLeftFirstThenBothMonitor_realizable A targetState
      Allowed source activation extension env

/-- Unconditional finite sender narrowing for the repaired right monitor. -/
theorem exists_profiledRawJointTargetRightFirstThenBothController
    {Target : Type t} [Fintype Target] [Inhabited Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetRightFirstThenBothActivationExtension A activation) :
    ∃ controller :
        TransitionRationalTree.{u, max u v x y s t, max u v x y s} In₁
          (NarrowedBlockLabel In₂ In₁
            (ProfiledRawJointRightFirstThenBothReceiverOutput
              (Out₁ := Out₁) (Out₂ := Out₂) Target)
            Out₁
            (profiledRawJointTargetRightFirstThenBothCombinedMonitor A Target
              targetState Allowed source).State),
      NarrowedAllThreadsWin
        (profiledRawJointTargetRightFirstThenBothCombinedMonitor A Target
          targetState Allowed source) controller.labeledTree := by
  apply (block_realizable_iff_implementable_controller_unconditional
    (profiledRawJointTargetRightFirstThenBothCombinedMonitor A Target
      targetState Allowed source)).mp
  exact ⟨profiledRawJointTargetRightFirstThenBothReceiverStrategyOfExtension A
      activation extension,
    pairedRightSenderStrategy activation.lambda,
    profiledRawJointTargetRightFirstThenBothCombinedMonitor_realizable A
      targetState Allowed source activation extension⟩

/-- Unconditional finite sender narrowing for the repaired left monitor. -/
theorem exists_profiledRawJointTargetLeftFirstThenBothController
    {Target : Type t} [Fintype Target] [Inhabited Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetLeftFirstThenBothActivationExtension A activation) :
    ∃ controller :
        TransitionRationalTree.{v, max u v x y s t, max u v y s} In₂
          (NarrowedBlockLabel In₁ In₂
            (ProfiledRawJointLeftFirstThenBothReceiverOutput
              (Out₁ := Out₁) (Out₂ := Out₂) Target)
            Out₂
            (profiledRawJointTargetLeftFirstThenBothCombinedMonitor A Target
              targetState Allowed source).State),
      NarrowedAllThreadsWin
        (profiledRawJointTargetLeftFirstThenBothCombinedMonitor A Target
          targetState Allowed source) controller.labeledTree := by
  apply (block_realizable_iff_implementable_controller_unconditional
    (profiledRawJointTargetLeftFirstThenBothCombinedMonitor A Target targetState
      Allowed source)).mp
  exact ⟨profiledRawJointTargetLeftFirstThenBothReceiverStrategyOfExtension A
      activation extension,
    pairedLeftSenderStrategy activation.lambda,
    profiledRawJointTargetLeftFirstThenBothCombinedMonitor_realizable A
      targetState Allowed source activation extension⟩

end


end DetParityAutomaton

end DistributedSynthesis
