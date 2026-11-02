/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenClassifiedMove

/-!
# Decorating receiver outputs without changing a finite sender controller

An operational table may need to retain a finite certificate together with
its physical receiver output.  This module performs that enrichment on an
already extracted transition-rational narrowed controller.  The finite
control, sender transition, and sender output are copied literally.  Only the
receiver table decorates its output.

If `project (decorate q input output) = output`, the comapped monitor follows
exactly the old narrowed thread.  Hence all-thread acceptance transfers with
no new rationalization.  The construction is objective-generic and contains
no graph, orientation, leader, history, view, or policy state.
-/

namespace DistributedSynthesis

universe u v x x' y w c

variable {RIn : Type u} {SIn : Type v}
variable {ROut : Type x} {ROut' : Type x'} {SOut : Type y}

namespace TransitionRationalTree

/-- Decorate only the receiver half of every narrowed label. -/
def decorateReceiverOutput
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (project : ROut' → ROut)
    (decorate : M.State → RIn × SIn → ROut → ROut')
    (controller : TransitionRationalTree.{v, max u v x y w, c} SIn
      (NarrowedBlockLabel RIn SIn ROut SOut M.State)) :
    TransitionRationalTree.{v, max u v x' y w, c} SIn
      (NarrowedBlockLabel RIn SIn ROut' SOut
        (M.comapReceiverOutput project).State) where
  Control := controller.Control
  controlFinite := controller.controlFinite
  initial := controller.initial
  step := controller.step
  labelOf := fun control ↦
    let label := controller.labelOf control
    (label.1, fun state input ↦
      decorate state input (label.2 state input))

@[simp] theorem decorateReceiverOutput_controlAt
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (project : ROut' → ROut)
    (decorate : M.State → RIn × SIn → ROut → ROut')
    (controller : TransitionRationalTree.{v, max u v x y w, c} SIn
      (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (word : List SIn) :
    (controller.decorateReceiverOutput M project decorate).controlAt word =
      controller.controlAt word :=
  rfl

/-- Sender labels are literally unchanged. -/
@[simp] theorem decorateReceiverOutput_sender
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (project : ROut' → ROut)
    (decorate : M.State → RIn × SIn → ROut → ROut')
    (controller : TransitionRationalTree.{v, max u v x y w, c} SIn
      (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (word : List SIn) :
    ((controller.decorateReceiverOutput M project decorate).labeledTree
      word).1 = (controller.labeledTree word).1 :=
  rfl

/-- Projecting one decorated receiver-table entry returns the old entry. -/
theorem decorateReceiverOutput_receiver_project
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (project : ROut' → ROut)
    (decorate : M.State → RIn × SIn → ROut → ROut')
    (hproject : ∀ state input output,
      project (decorate state input output) = output)
    (controller : TransitionRationalTree.{v, max u v x y w, c} SIn
      (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (word : List SIn) (state : M.State) (input : RIn × SIn) :
    project
        ((controller.decorateReceiverOutput M project decorate).labeledTree
          word |>.2 state input) =
      (controller.labeledTree word).2 state input := by
  exact hproject state input _

/-- The comapped monitor follows the exact old narrowed state at every full
input node. -/
theorem decorateReceiverOutput_narrowedControl
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (project : ROut' → ROut)
    (decorate : M.State → RIn × SIn → ROut → ROut')
    (hproject : ∀ state input output,
      project (decorate state input output) = output)
    (controller : TransitionRationalTree.{v, max u v x y w, c} SIn
      (NarrowedBlockLabel RIn SIn ROut SOut M.State)) :
    ∀ node : TreeNode (RIn × SIn),
      narrowedControl (M.comapReceiverOutput project)
          (controller.decorateReceiverOutput M project decorate).labeledTree
          node =
        narrowedControl M controller.labeledTree node := by
  intro node
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node input ih =>
      rw [narrowedControl_append, narrowedControl_append, ih]
      change M.step _
          (input,
            project (decorate _ input
              ((controller.labeledTree (senderWord node)).2 _ input)),
            (controller.labeledTree (senderWord node)).1 input.2) =
        M.step _
          (input, (controller.labeledTree (senderWord node)).2 _ input,
            (controller.labeledTree (senderWord node)).1 input.2)
      rw [hproject]

/-- Universal narrowed-thread acceptance is invariant under receiver-output
decoration and physical projection. -/
theorem decorateReceiverOutput_allThreadsWin
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (project : ROut' → ROut)
    (decorate : M.State → RIn × SIn → ROut → ROut')
    (hproject : ∀ state input output,
      project (decorate state input output) = output)
    (controller : TransitionRationalTree.{v, max u v x y w, c} SIn
      (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (hwin : NarrowedAllThreadsWin M controller.labeledTree) :
    NarrowedAllThreadsWin (M.comapReceiverOutput project)
      (controller.decorateReceiverOutput M project decorate).labeledTree := by
  intro env
  have heq :
      (fun n ↦ (M.comapReceiverOutput project).priority
        (narrowedThreadState (M.comapReceiverOutput project)
          (controller.decorateReceiverOutput M project decorate).labeledTree
          env n)) =
      (fun n ↦ M.priority
        (narrowedThreadState M controller.labeledTree env n)) := by
    funext n
    exact congrArg M.priority
      (controller.decorateReceiverOutput_narrowedControl M project decorate
        hproject (branchNode env n))
  rw [heq]
  exact hwin env

end TransitionRationalTree

end DistributedSynthesis
