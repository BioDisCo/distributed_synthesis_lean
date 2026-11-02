/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmBoundaryGame
import DistributedSynthesis.Formalizations.Theorem.ThmDeterministicBlockAutomaton
import DistributedSynthesis.Formalizations.Theorem.ThmJournalBlockMonitors
import DistributedSynthesis.Formalizations.Theorem.ThmReversedBlockThreads

/-!
# The global journal tree automaton

This file defines the finite tree automaton of step HG-B of the heart
plan.  Its trees are global journal strategies: nodes branch over
atoms at boundary events and over sender inputs within blocks, and
every node carries the four finite tables of a block round (the two
narrowed labels and the two closing tables).  Reading the labels along
a path yields exactly the data of a boundary-game plan, so a regular
accepted tree is a finite-state boundary-game strategy (step HG-C),
while the per-atom family of a positional uniformization winner is an
accepted tree (the completeness step).

The automaton state tracks the play mode.  At an atom the thread is
common knowledge and the state is the atom itself.  Within a block the
receiver inputs are a universal thread dimension that no single state
can follow, so the state carries a per-orientation universal-thread
checker (interface `LeftThreadChecker`/`RightThreadChecker`,
instantiated later from the narrowed-thread determinization) together
with the set of thread atoms realized by some receiver word, which
decides which atom branches a close can reach; unreachable atom
branches and orientation reversals fall into an accepting sink.

Priorities follow design D3 with an even shift: atoms emit the closed
block's minimum, block states emit the checker's priority shifted
evenly above every automaton priority.  On a path that crosses
boundaries forever the shifted block priorities are dominated, so the
value is the min-even parity of the block minima; on a path that stays
in one block forever only checker priorities recur, and their parity
is the checker's verdict on the block's threads.
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

/-- The per-node label of a global journal tree: per normal
orientation the narrowed block label, the shared closing table, and
the staged reversal table; plus the two reversed-block four-value
labels. -/
abbrev GlobalJournalLabel :=
  NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State) ×
    ((A.State × A.State) -> In₁ × In₂ -> Out₂) ×
    ((A.State × A.State) -> In₁ -> Out₁) ×
    NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State) ×
    ((A.State × A.State) -> In₂ × In₁ -> Out₁) ×
    ((A.State × A.State) -> In₂ -> Out₂) ×
    RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State) ×
    RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State)

namespace GlobalJournalLabel

variable {A}

/-- The narrowed label of a left block. -/
def leftNarrowed (l : GlobalJournalLabel (In₁ := In₁) A) :
    NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State) :=
  l.1

/-- The shared closing table of a left block. -/
def leftClose (l : GlobalJournalLabel (In₁ := In₁) A) :
    (A.State × A.State) -> In₁ × In₂ -> Out₂ :=
  l.2.1

/-- The staged reversal table of a left block. -/
def leftRev (l : GlobalJournalLabel (In₁ := In₁) A) :
    (A.State × A.State) -> In₁ -> Out₁ :=
  l.2.2.1

/-- The narrowed label of a right block. -/
def rightNarrowed (l : GlobalJournalLabel (In₁ := In₁) A) :
    NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State) :=
  l.2.2.2.1

/-- The shared closing table of a right block. -/
def rightClose (l : GlobalJournalLabel (In₁ := In₁) A) :
    (A.State × A.State) -> In₂ × In₁ -> Out₁ :=
  l.2.2.2.2.1

/-- The staged reversal table of a right block. -/
def rightRev (l : GlobalJournalLabel (In₁ := In₁) A) :
    (A.State × A.State) -> In₂ -> Out₂ :=
  l.2.2.2.2.2.1

/-- The four-value label of a reversed left block. -/
def revLeft (l : GlobalJournalLabel (In₁ := In₁) A) :
    RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State) :=
  l.2.2.2.2.2.2.1

/-- The four-value label of a reversed right block. -/
def revRight (l : GlobalJournalLabel (In₁ := In₁) A) :
    RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State) :=
  l.2.2.2.2.2.2.2

end GlobalJournalLabel

/-- Tree directions: an atom event, or a sender input of a block. -/
abbrev GlobalJournalBranch :=
  (A.State × A.State) ⊕ In₂ ⊕ In₁

/--
A universal-thread checker for left blocks: a deterministic automaton
over sender inputs and narrowed labels, started per boundary state,
whose branchwise parity decides whether every receiver thread of the
block wins the block monitor.  The `winning_iff` field ties it to the
semantics; it is discharged by the narrowed-thread determinization.
-/
structure LeftThreadChecker where
  monitor :
    DeterministicBlockMonitor.{v, max u v x y s, s}
      In₂ (NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
  start : A.State -> monitor.State
  winning_iff :
    ∀ (boundary : A.State)
      (narrowed :
        LabeledTree In₂
          (NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))),
      DeterministicBlockMonitor.WinningTree
          { monitor with initial := start boundary } narrowed ↔
        NarrowedAllThreadsWin (A.leftBlockMonitor boundary) narrowed

/-- A universal-thread checker for right blocks: the mirror. -/
structure RightThreadChecker where
  monitor :
    DeterministicBlockMonitor.{u, max u v x y s, s}
      In₁ (NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State))
  start : A.State -> monitor.State
  winning_iff :
    ∀ (boundary : A.State)
      (narrowed :
        LabeledTree In₁
          (NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State))),
      DeterministicBlockMonitor.WinningTree
          { monitor with initial := start boundary } narrowed ↔
        NarrowedAllThreadsWin (A.rightBlockMonitor boundary) narrowed

variable {A}

/-! ### Thread steps, mirroring the boundary-game targets -/

/-- The thread atom after a left-block opening round. -/
def leftThreadOpen (atom : A.State × A.State)
    (label : NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (inputOne : In₁) (inputTwo : In₂) : A.State × A.State :=
  let next :=
    A.step atom.1
      (leftRoundRecord (inputOne, inputTwo)
        (label.2 (atom.1, atom.1) (inputOne, inputTwo))
        (label.1 inputTwo))
  (next, A.minPriorityState atom.1 next)

/-- The thread atom after a left-block continuation round. -/
def leftThreadStep (qm : A.State × A.State)
    (label : NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (inputOne : In₁) (inputTwo : In₂) : A.State × A.State :=
  let next :=
    A.step qm.1
      (leftRoundRecord (inputOne, inputTwo)
        (label.2 qm (inputOne, inputTwo))
        (label.1 inputTwo))
  (next, A.minPriorityState qm.2 next)

/-- The boundary atom reached by closing a left block. -/
def leftThreadClose (qm : A.State × A.State)
    (label : NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (close : (A.State × A.State) -> In₁ × In₂ -> Out₂)
    (inputOne : In₁) (inputTwo : In₂) : A.State × A.State :=
  (A.step qm.1
      (bothRoundRecord (inputOne, inputTwo)
        (label.2 qm (inputOne, inputTwo))
        (close qm (inputOne, inputTwo))),
    qm.2)

/-- The thread atom after a right-block opening round. -/
def rightThreadOpen (atom : A.State × A.State)
    (label : NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State))
    (inputTwo : In₂) (inputOne : In₁) : A.State × A.State :=
  let next :=
    A.step atom.1
      (rightRoundRecord (inputTwo, inputOne)
        (label.1 inputOne)
        (label.2 (atom.1, atom.1) (inputTwo, inputOne)))
  (next, A.minPriorityState atom.1 next)

/-- The thread atom after a right-block continuation round. -/
def rightThreadStep (qm : A.State × A.State)
    (label : NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State))
    (inputTwo : In₂) (inputOne : In₁) : A.State × A.State :=
  let next :=
    A.step qm.1
      (rightRoundRecord (inputTwo, inputOne)
        (label.1 inputOne)
        (label.2 qm (inputTwo, inputOne)))
  (next, A.minPriorityState qm.2 next)

/-- The boundary atom reached by closing a right block. -/
def rightThreadClose (qm : A.State × A.State)
    (label : NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State))
    (close : (A.State × A.State) -> In₂ × In₁ -> Out₁)
    (inputTwo : In₂) (inputOne : In₁) : A.State × A.State :=
  (A.step qm.1
      (bothRoundRecord (inputOne, inputTwo)
        (close qm (inputTwo, inputOne))
        (label.2 qm (inputTwo, inputOne))),
    qm.2)

/-- The boundary atom reached by a synchronizing round at an atom. -/
def bothThreadAtom (atom : A.State × A.State)
    (labelL : NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (labelR : NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State))
    (inputOne : In₁) (inputTwo : In₂) : A.State × A.State :=
  (A.step atom.1
      (bothRoundRecord (inputOne, inputTwo)
        (labelL.2 (atom.1, atom.1) (inputOne, inputTwo))
        (labelR.2 (atom.1, atom.1) (inputTwo, inputOne))),
    atom.1)

section Subsets

variable [Fintype In₁] [Fintype In₂] [DecidableEq A.State]

/-- The thread atoms realized after a left-block opening. -/
def leftOpenSubset (atom : A.State × A.State)
    (label : NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (inputTwo : In₂) : Finset (A.State × A.State) :=
  Finset.image (fun inputOne => leftThreadOpen atom label inputOne inputTwo)
    Finset.univ

/-- The thread atoms realized after a left-block continuation. -/
def leftStepSubset (threads : Finset (A.State × A.State))
    (label : NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (inputTwo : In₂) : Finset (A.State × A.State) :=
  threads.biUnion fun qm =>
    Finset.image (fun inputOne => leftThreadStep qm label inputOne inputTwo)
      Finset.univ

/-- The boundary atoms reachable by closing a left block. -/
def leftCloseSubset (threads : Finset (A.State × A.State))
    (label : NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (close : (A.State × A.State) -> In₁ × In₂ -> Out₂) :
    Finset (A.State × A.State) :=
  threads.biUnion fun qm =>
    Finset.image
      (fun move : In₁ × In₂ => leftThreadClose qm label close move.1 move.2)
      Finset.univ

/-- The thread atoms realized after a right-block opening. -/
def rightOpenSubset (atom : A.State × A.State)
    (label : NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State))
    (inputOne : In₁) : Finset (A.State × A.State) :=
  Finset.image (fun inputTwo => rightThreadOpen atom label inputTwo inputOne)
    Finset.univ

/-- The thread atoms realized after a right-block continuation. -/
def rightStepSubset (threads : Finset (A.State × A.State))
    (label : NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State))
    (inputOne : In₁) : Finset (A.State × A.State) :=
  threads.biUnion fun qm =>
    Finset.image (fun inputTwo => rightThreadStep qm label inputTwo inputOne)
      Finset.univ

/-- The boundary atoms reachable by closing a right block. -/
def rightCloseSubset (threads : Finset (A.State × A.State))
    (label : NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State))
    (close : (A.State × A.State) -> In₂ × In₁ -> Out₁) :
    Finset (A.State × A.State) :=
  threads.biUnion fun qm =>
    Finset.image
      (fun move : In₂ × In₁ =>
        rightThreadClose qm label close move.1 move.2)
      Finset.univ

/-- The boundary atoms reachable by a synchronizing round. -/
def bothAtomSubset (atom : A.State × A.State)
    (labelL : NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (labelR : NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)) :
    Finset (A.State × A.State) :=
  Finset.image
    (fun move : In₁ × In₂ => bothThreadAtom atom labelL labelR move.1 move.2)
    Finset.univ

end Subsets

section Automaton

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
variable (CL : LeftThreadChecker (In₁ := In₁) A)
variable (CR : RightThreadChecker (In₁ := In₁) A)
variable (CC : ChainThreadChecker (In₁ := In₁) (A := A))
variable (A)

/-- The explicit finite-label witness required by the finite emptiness-game
extraction.  It used to be stored inside `RunParityTreeAutomaton`; after the
general/finite split it is a reusable fact about the concrete journal label. -/
@[reducible] noncomputable def globalJournalLabelFintype :
    Fintype (GlobalJournalLabel (In₁ := In₁) A) := by
  letI :
      Fintype
        (NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) :=
    inferInstance
  letI :
      Fintype
        (NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)) :=
    inferInstance
  letI : Fintype ((A.State × A.State) -> In₁ × In₂ -> Out₂) :=
    inferInstance
  letI : Fintype ((A.State × A.State) -> In₁ -> Out₁) :=
    inferInstance
  letI : Fintype ((A.State × A.State) -> In₂ × In₁ -> Out₁) :=
    inferInstance
  letI : Fintype ((A.State × A.State) -> In₂ -> Out₂) :=
    inferInstance
  letI :
      Fintype
        ((A.State × A.State) × A.State × A.State ->
          In₁ × In₂ -> Out₁) :=
    inferInstance
  letI :
      Fintype
        ((A.State × A.State) × A.State × A.State -> In₁ -> Out₁) :=
    inferInstance
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

/--
States of the global journal automaton: an atom, a normal or reversed
block mode carrying the checker state and the realized thread atoms,
or the accepting sink of unreachable branches.
-/
abbrev GlobalJournalState :=
  (A.State × A.State) ⊕
    (CL.monitor.State × Finset (A.State × A.State)) ⊕
    (CR.monitor.State × Finset (A.State × A.State)) ⊕
    (CC.monitor.State × Finset (ChainThread A)) ⊕
    (CC.monitor.State × Finset (ChainThread A)) ⊕
    PUnit.{s + 1}

/-- The even priority shift lifting checker priorities above every
automaton priority. -/
noncomputable def globalShift : Nat :=
  2 * ((Finset.univ.sup fun state : A.State => A.priority state) + 1)

/-- The deterministic transition of the global journal automaton:
orientation switches out of block modes are the direct-reversal
handoffs into the reversed modes; reversed modes continue on their
sender's inputs, close into genuine atoms, or reverse again. -/
def globalJournalStep
    (state : GlobalJournalState (In₁ := In₁) A CL CR CC)
    (label : GlobalJournalLabel (In₁ := In₁) A)
    (branch : GlobalJournalBranch (In₁ := In₁) A) :
    GlobalJournalState (In₁ := In₁) A CL CR CC :=
  match state, branch with
  | Sum.inl atom, Sum.inl atom' =>
      if atom' ∈
          bothAtomSubset atom label.leftNarrowed label.rightNarrowed then
        Sum.inl atom'
      else Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))
  | Sum.inl atom, Sum.inr (Sum.inl inputTwo) =>
      Sum.inr (Sum.inl
        (CL.monitor.step (CL.start atom.1) label.leftNarrowed inputTwo,
          leftOpenSubset atom label.leftNarrowed inputTwo))
  | Sum.inl atom, Sum.inr (Sum.inr inputOne) =>
      Sum.inr (Sum.inr (Sum.inl
        (CR.monitor.step (CR.start atom.1) label.rightNarrowed inputOne,
          rightOpenSubset atom label.rightNarrowed inputOne)))
  | Sum.inr (Sum.inl (_checker, threads)), Sum.inl atom' =>
      if atom' ∈
          leftCloseSubset threads label.leftNarrowed label.leftClose then
        Sum.inl atom'
      else Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))
  | Sum.inr (Sum.inl (checker, threads)), Sum.inr (Sum.inl inputTwo) =>
      Sum.inr (Sum.inl
        (CL.monitor.step checker label.leftNarrowed inputTwo,
          leftStepSubset threads label.leftNarrowed inputTwo))
  | Sum.inr (Sum.inl (_checker, threads)), Sum.inr (Sum.inr inputOne) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
        (CC.start
            (leftReverseSubset threads label.leftClose label.leftRev
              inputOne),
          leftReverseSubset threads label.leftClose label.leftRev
            inputOne)))))
  | Sum.inr (Sum.inr (Sum.inl (_checker, threads))), Sum.inl atom' =>
      if atom' ∈
          rightCloseSubset threads label.rightNarrowed
            label.rightClose then
        Sum.inl atom'
      else Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))
  | Sum.inr (Sum.inr (Sum.inl (checker, threads))),
      Sum.inr (Sum.inr inputOne) =>
      Sum.inr (Sum.inr (Sum.inl
        (CR.monitor.step checker label.rightNarrowed inputOne,
          rightStepSubset threads label.rightNarrowed inputOne)))
  | Sum.inr (Sum.inr (Sum.inl (_checker, threads))),
      Sum.inr (Sum.inl inputTwo) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inl
        (CC.start
            (rightReverseSubset threads label.rightClose label.rightRev
              inputTwo),
          rightReverseSubset threads label.rightClose label.rightRev
            inputTwo))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (_checker, threads)))),
      Sum.inl atom' =>
      if atom' ∈ revLeftCloseSubset threads label.revLeft then
        Sum.inl atom'
      else Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, threads)))),
      Sum.inr (Sum.inl inputTwo) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inl
        (CC.monitor.step checker (Sum.inl label.revLeft) (Sum.inl inputTwo),
          revLeftStepSubset threads label.revLeft inputTwo))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, threads)))),
      Sum.inr (Sum.inr inputOne) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
        (CC.monitor.step checker (Sum.inl label.revLeft) (Sum.inr inputOne),
          revLeftReverseSubset threads label.revLeft inputOne)))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (_checker, threads))))),
      Sum.inl atom' =>
      if atom' ∈ revRightCloseSubset threads label.revRight then
        Sum.inl atom'
      else Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, threads))))),
      Sum.inr (Sum.inr inputOne) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
        (CC.monitor.step checker (Sum.inr label.revRight) (Sum.inr inputOne),
          revRightStepSubset threads label.revRight inputOne)))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, threads))))),
      Sum.inr (Sum.inl inputTwo) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inl
        (CC.monitor.step checker (Sum.inr label.revRight) (Sum.inl inputTwo),
          revRightReverseSubset threads label.revRight inputTwo))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))), _ =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))

/-- Design-D3 priorities with the even shift on block modes. -/
noncomputable def globalJournalPriority
    (state : GlobalJournalState (In₁ := In₁) A CL CR CC) : Nat :=
  match state with
  | Sum.inl atom => A.priority atom.2
  | Sum.inr (Sum.inl (checker, _)) =>
      CL.monitor.priority checker + globalShift (In₁ := In₁) A
  | Sum.inr (Sum.inr (Sum.inl (checker, _))) =>
      CR.monitor.priority checker + globalShift (In₁ := In₁) A
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, _)))) =>
      CC.monitor.priority checker + globalShift (In₁ := In₁) A
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, _))))) =>
      CC.monitor.priority checker + globalShift (In₁ := In₁) A
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) =>
      globalShift (In₁ := In₁) A

/--
The global journal tree automaton: accepted trees are global journal
strategies all of whose plays win, with per-branch deterministic
threading.
-/
noncomputable def globalJournalAutomaton :
    RunParityTreeAutomaton.{max u v s, max u v x y s, s}
      (GlobalJournalBranch (In₁ := In₁) A)
      (GlobalJournalLabel (In₁ := In₁) A) where
  State := GlobalJournalState (In₁ := In₁) A CL CR CC
  stateFinite := by
    letI := CL.monitor.stateFinite
    letI := CR.monitor.stateFinite
    letI := CC.monitor.stateFinite
    infer_instance
  initial := Sum.inl (A.initial, A.initial)
  delta := fun state label f =>
    ∀ branch : GlobalJournalBranch (In₁ := In₁) A,
      f branch = globalJournalStep A CL CR CC state label branch
  priority := globalJournalPriority A CL CR CC

/-- Sink states are absorbing. -/
theorem globalJournalStep_sink
    (label : GlobalJournalLabel (In₁ := In₁) A)
    (branch : GlobalJournalBranch (In₁ := In₁) A) :
    globalJournalStep A CL CR CC
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))))
        label branch =
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))) :=
  rfl

/-- Every automaton priority sits strictly below the shift. -/
theorem priority_lt_globalShift (state : A.State) :
    A.priority state < globalShift (In₁ := In₁) A := by
  have hle :
      A.priority state ≤
        Finset.univ.sup fun state : A.State => A.priority state :=
    Finset.le_sup (Finset.mem_univ state)
  unfold globalShift
  omega

/-- The shift is even. -/
theorem globalShift_even : NatEven (globalShift (In₁ := In₁) A) :=
  ⟨(Finset.univ.sup fun state : A.State => A.priority state) + 1, rfl⟩

end Automaton

end DetParityAutomaton

end DistributedSynthesis
