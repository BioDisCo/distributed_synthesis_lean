/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmReversedBlockThreads
import DistributedSynthesis.Formalizations.Theorem.ThmUniversalThreadDeterminization

/-!
# Per-thread checkers for reversal chains

The universal composed-thread condition of a reversal chain from a
single handoff thread reduces to the ordinary narrowed universal
thread condition through a packing trick: a `BlockRecordMonitor`
steps on an abstract realized round, so the chain's staged outputs
pack into the receiver slot of a narrowed label over the mixed
direction alphabet, with trivial sender slot.  The generic
narrowed-thread determinization then yields a deterministic
per-thread checker monitor over reversed-block labels and mixed
directions.

The chain checker of `ThmReversedBlockThreads.lean` quantifies over
every thread of a handoff set; its instantiation from the per-thread
checkers is the remaining determinization step (a finite conjunction
of parity conditions), recorded as the next unit.
-/

set_option linter.unusedSectionVars false

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-! ### The packed chain thread monitor -/

/-- The composed-thread monitor of a reversal chain from a handoff
thread: the direction sort of a realized round selects the round
type, and the four staged outputs arrive packed in the receiver
slot. -/
def chainThreadMonitor (th₀ : ChainThread A) :
    BlockRecordMonitor.{max u v, max u v, max x y, y, s}
      (In₁ × In₂) (In₂ ⊕ In₁)
      (Bool × Out₁ × Out₁ × Out₂ × Out₂) PUnit where
  State := ChainThread A
  stateFinite := inferInstance
  initial := th₀
  step := fun st round =>
    match round.1.2 with
    | Sum.inl inputTwo =>
        let next :=
          A.step st.2.1
            (leftRoundRecord (round.1.1.1, inputTwo) round.2.1.2.1
              round.2.1.2.2.2.1)
        if round.2.1.1 then
          (st.1, next, A.minPriorityState st.2.2 next)
        else
          ((next, A.minPriorityState st.2.2 next),
            next, A.minPriorityState st.2.2 next)
    | Sum.inr inputOne =>
        let next :=
          A.step st.2.1
            (rightRoundRecord (round.1.1.2, inputOne) round.2.1.2.2.1
              round.2.1.2.2.2.2)
        if round.2.1.1 then
          ((next, A.minPriorityState st.2.2 next),
            next, A.minPriorityState st.2.2 next)
        else
          (st.1, next, A.minPriorityState st.2.2 next)
  priority := fun st => A.priority st.2.1

variable {A}

/-- The full move composed from a chain step: the direction supplies
the sender input, the universal move the receiver input. -/
def composedChainMove (move : (In₁ × In₂) × (In₂ ⊕ In₁)) : In₁ × In₂ :=
  match move.2 with
  | Sum.inl inputTwo => (move.1.1, inputTwo)
  | Sum.inr inputOne => (inputOne, move.1.2)

/-- Pack a reversed-block label into a narrowed label over mixed
directions with trivial sender slot. -/
def packChainLabel
    (label : ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) :
    NarrowedBlockLabel (In₁ × In₂) (In₂ ⊕ In₁)
      (Bool × Out₁ × Out₁ × Out₂ × Out₂) PUnit (ChainThread A) :=
  (fun _ => PUnit.unit, fun th move =>
    match label with
    | Sum.inl labL =>
        (true,
          labL.1 th (composedChainMove move),
          labL.2.1 th (composedChainMove move).1,
          labL.2.2.1 th.1 (composedChainMove move).2,
          labL.2.2.2 th (composedChainMove move))
    | Sum.inr labR =>
        (false,
          labR.1 th (composedChainMove move),
          labR.2.1 th.1 (composedChainMove move).1,
          labR.2.2.1 th (composedChainMove move).2,
          labR.2.2.2 th (composedChainMove move)))

/-- The packed monitor's step on a packed narrowed record is the
composed-thread step. -/
theorem chainThreadMonitor_step_eq (th₀ th : ChainThread A)
    (label : ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (move : (In₁ × In₂) × (In₂ ⊕ In₁)) :
    (A.chainThreadMonitor th₀).step th
        (narrowedRecord (A.chainThreadMonitor th₀)
          (packChainLabel label) th move) =
      chainThreadStep A th label move.2 move.1 := by
  obtain ⟨m, d⟩ := move
  cases d <;> rcases label with labL | labR <;> rfl

/-! ### Fold equivalence -/

theorem chainFold_eq_aux (th₀ : ChainThread A)
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))) :
    ∀ (node : TreeNode ((In₁ × In₂) × (In₂ ⊕ In₁)))
      (word : List (In₂ ⊕ In₁)) (th : ChainThread A),
      chainFold A narrowed word th node =
        narrowedControlAux (A.chainThreadMonitor th₀)
          (fun w => packChainLabel (narrowed w)) word th node
  | [], _, _ => rfl
  | step :: rest, word, qm => by
      show
        chainFold A narrowed (word ++ [step.2])
            (chainThreadStep A qm (narrowed word) step.2 step.1) rest =
          narrowedControlAux (A.chainThreadMonitor th₀)
            (fun w => packChainLabel (narrowed w)) (word ++ [step.2])
            ((A.chainThreadMonitor th₀).step qm
              (narrowedRecord (A.chainThreadMonitor th₀)
                (packChainLabel (narrowed word)) qm step))
            rest
      rw [chainFold_eq_aux th₀ narrowed rest,
        chainThreadMonitor_step_eq th₀ qm (narrowed word) step]

/-- The chain universal condition is the narrowed one of the packed
monitor. -/
theorem chainAllThreadsWin_iff (th₀ : ChainThread A)
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))) :
    ChainAllThreadsWin A narrowed th₀ ↔
      NarrowedAllThreadsWin (A.chainThreadMonitor th₀)
        (fun w => packChainLabel (narrowed w)) := by
  have heq :
      ∀ (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁)) (n : Nat),
        chainFold A narrowed [] th₀ (branchNode env n) =
          narrowedThreadState (A.chainThreadMonitor th₀)
            (fun w => packChainLabel (narrowed w)) env n :=
    fun env n => chainFold_eq_aux th₀ narrowed _ [] th₀
  constructor
  · intro hwin env
    have h := hwin env
    have hfun :
        (fun n =>
            A.priority
              (chainFold A narrowed [] th₀ (branchNode env n)).2.1) =
          fun n =>
            (A.chainThreadMonitor th₀).priority
              (narrowedThreadState (A.chainThreadMonitor th₀)
                (fun w => packChainLabel (narrowed w)) env n) := by
      funext n
      rw [heq env n]
      rfl
    rwa [hfun] at h
  · intro hwin env
    have h := hwin env
    have hfun :
        (fun n =>
            (A.chainThreadMonitor th₀).priority
              (narrowedThreadState (A.chainThreadMonitor th₀)
                (fun w => packChainLabel (narrowed w)) env n)) =
          fun n =>
            A.priority
              (chainFold A narrowed [] th₀ (branchNode env n)).2.1 := by
      funext n
      rw [heq env n]
      rfl
    rwa [hfun] at h

/-! ### The per-thread chain checker monitor -/

section Checker

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
variable (A)

/-- The per-thread chain checker monitor: the narrowed thread
determinization of the packed monitor, reading reversed-block labels
and mixed directions through the packing. -/
noncomputable def chainPerThreadMonitor (th₀ : ChainThread A) :
    DeterministicBlockMonitor.{max u v, max u v x y s, s}
      (In₂ ⊕ In₁)
      (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) where
  branchFinite := inferInstance
  alphabetFinite := by
    classical
    letI :
        Fintype
          ((A.State × A.State) × A.State × A.State ->
            In₁ × In₂ -> Out₁) :=
      inferInstance
    letI :
        Fintype
          ((A.State × A.State) × A.State × A.State -> In₁ -> Out₁) :=
      inferInstance
    letI : Fintype (A.State × A.State -> In₂ -> Out₂) := inferInstance
    letI : Fintype (A.State × A.State -> In₁ -> Out₁) := inferInstance
    letI :
        Fintype
          ((A.State × A.State) × A.State × A.State -> In₂ -> Out₂) :=
      inferInstance
    letI :
        Fintype
          ((A.State × A.State) × A.State × A.State ->
            In₁ × In₂ -> Out₂) :=
      inferInstance
    letI :
        Fintype
          (RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) (A.State × A.State)) :=
      inferInstance
    letI :
        Fintype
          (RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) (A.State × A.State)) :=
      inferInstance
    infer_instance
  State := ((A.chainThreadMonitor th₀).threadBlockMonitor).State
  stateFinite := ((A.chainThreadMonitor th₀).threadBlockMonitor).stateFinite
  initial := ((A.chainThreadMonitor th₀).threadBlockMonitor).initial
  step := fun st label branch =>
    ((A.chainThreadMonitor th₀).threadBlockMonitor).step st
      (packChainLabel label) branch
  priority := fun st =>
    ((A.chainThreadMonitor th₀).threadBlockMonitor).priority st

variable {A}

theorem chainPerThreadMonitor_control (th₀ : ChainThread A)
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))) :
    ∀ node : TreeNode (In₂ ⊕ In₁),
      (chainPerThreadMonitor A th₀).control narrowed node =
        ((A.chainThreadMonitor th₀).threadBlockMonitor).control
          (fun w => packChainLabel (narrowed w)) node := by
  intro node
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node b ih =>
      rw [DeterministicBlockMonitor.control_append,
        DeterministicBlockMonitor.control_append, ih]
      rfl

/-- The per-thread chain checker is sound and complete for the
composed-thread universal condition. -/
theorem chainPerThreadMonitor_winningTree_iff
    (th₀ : ChainThread A)
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))) :
    (chainPerThreadMonitor A th₀).WinningTree narrowed ↔
      ChainAllThreadsWin A narrowed th₀ := by
  rw [chainAllThreadsWin_iff th₀ narrowed,
    ← BlockRecordMonitor.threadBlockMonitor_winningTree_iff
      (A.chainThreadMonitor th₀)
      (fun w => packChainLabel (narrowed w))]
  constructor
  · intro hwin branch
    have h := hwin branch
    have hfun :
        (fun n =>
            (chainPerThreadMonitor A th₀).priority
              ((chainPerThreadMonitor A th₀).control narrowed
                (branchNode branch n))) =
          fun n =>
            ((A.chainThreadMonitor th₀).threadBlockMonitor).priority
              (((A.chainThreadMonitor th₀).threadBlockMonitor).control
                (fun w => packChainLabel (narrowed w))
                (branchNode branch n)) := by
      funext n
      rw [chainPerThreadMonitor_control th₀ narrowed
        (branchNode branch n)]
      rfl
    rwa [hfun] at h
  · intro hwin branch
    have h := hwin branch
    have hfun :
        (fun n =>
            ((A.chainThreadMonitor th₀).threadBlockMonitor).priority
              (((A.chainThreadMonitor th₀).threadBlockMonitor).control
                (fun w => packChainLabel (narrowed w))
                (branchNode branch n))) =
          fun n =>
            (chainPerThreadMonitor A th₀).priority
              ((chainPerThreadMonitor A th₀).control narrowed
                (branchNode branch n)) := by
      funext n
      rw [chainPerThreadMonitor_control th₀ narrowed
        (branchNode branch n)]
      rfl
    rwa [hfun] at h

end Checker

end DetParityAutomaton

end DistributedSynthesis
