/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteDependentHeterogeneousPinnedPreselection

/-!
# Physical acceptance of a shared dependent pinned table

A member of `FiniteDependentHeterogeneousPinnedTable` runs a root-pinned,
restarted monitor over a dependent tuple of receiver outputs.  Downstream
physical safety theorems consume the original member monitor instead.  This
file provides the exact play-level erasure:

1. forget the root pin;
2. commute restart with receiver-output comapping;
3. project the dependent receiver tuple at the chosen key; and
4. when the selected restart state is the base initial state, forget the
   restart definitionally.

The shared rationalized sender table is never equated with a separately
rationalized member table.
-/

namespace DistributedSynthesis

universe k u v x y w

noncomputable section

variable {Key : Type k} {RIn : Type u} {SIn : Type v}
variable {ROut : Key → Type x} {SOut : Type y}
variable [Inhabited Key] [Fintype Key] [DecidableEq Key]
variable [Inhabited RIn] [Inhabited SIn] [Fintype RIn] [Fintype SIn]
variable [DecidableEq RIn] [DecidableEq SIn]
variable [(key : Key) → Inhabited (ROut key)]
variable [(key : Key) → Fintype (ROut key)] [Fintype SOut]

variable
  (base : (key : Key) →
    BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut)
  (start : (key : Key) → (base key).State)
  (receiver : (key : Key) →
    ReceiverBlockStrategy RIn SIn (ROut key))
  (sender : SenderBlockStrategy SIn SOut)

/-- The physical member play is obtained by projecting the chosen receiver
coordinate out of the one shared dependent-output play. -/
noncomputable def finiteDependentHeterogeneousPinnedMemberPhysicalPlay
    (table : FiniteDependentHeterogeneousPinnedTable base start receiver
      sender)
    (key : Key) (env : Nat → RIn × SIn) :
    Nat → RealizedBlockRound RIn SIn (ROut key) SOut :=
  let pin := finiteDependentHeterogeneousPinnedRestartFamily base start
    receiver sender key
  let controller := table.memberController key
  let productPlay := treePlay
    (narrowedInducedTree pin controller.labeledTree) env
  BlockRecordMonitor.projectReceiverPlay (fun output ↦ output key)
    productPlay

/-- Erasing the pin and dependent receiver coordinate leaves a play winning
the selected member monitor restarted at its prescribed state. -/
theorem finiteDependentHeterogeneousPinnedMemberPhysicalPlay_restart_wins
    (table : FiniteDependentHeterogeneousPinnedTable base start receiver
      sender)
    (key : Key) (env : Nat → RIn × SIn) :
    ((base key).restartAt (start key)).WinsPlay
      (finiteDependentHeterogeneousPinnedMemberPhysicalPlay base start receiver
        sender table key env) := by
  let pin := finiteDependentHeterogeneousPinnedRestartFamily base start
    receiver sender key
  let controller := table.memberController key
  let productPlay := treePlay
    (narrowedInducedTree pin controller.labeledTree) env
  have hthreads : NarrowedAllThreadsWin pin controller.labeledTree := by
    exact table.member_wins key
  have htree : pin.lift.WinningTree
      (narrowedInducedTree pin controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin pin hthreads
  have hpinned : pin.WinsPlay productPlay :=
    (pin.lift_winningTree_iff
      (narrowedInducedTree pin controller.labeledTree)).mp htree env
  have hrestarted :
      (finiteDependentHeterogeneousRestartFamily base start key).WinsPlay
        productPlay := by
    exact
      (finiteDependentHeterogeneousRestartFamily base start key
        ).rootPinned_base_wins_of_wins
          (finiteDependentHeterogeneousSemanticRootRecord receiver sender key)
          productPlay hpinned
  have hcomap :
      ((base key).restartAt (start key) |>.comapReceiverOutput
        (fun output : FiniteDependentReceiverOutput Key ROut ↦ output key)
        ).WinsPlay productPlay := by
    simpa [finiteDependentHeterogeneousRestartFamily,
      finiteDependentHeterogeneousMonitor,
      finiteDependentHeterogeneousStart, BlockRecordMonitor.restartAt,
      BlockRecordMonitor.comapReceiverOutput] using hrestarted
  exact (BlockRecordMonitor.comapReceiverOutput_wins_iff
    ((base key).restartAt (start key))
    (fun output : FiniteDependentReceiverOutput Key ROut ↦ output key)
    productPlay).mp hcomap

/-- When the family was installed at the member monitor's actual initial
state, all three wrappers disappear and the projected play wins `base key`
itself. -/
theorem finiteDependentHeterogeneousPinnedMemberPhysicalPlay_base_wins
    (table : FiniteDependentHeterogeneousPinnedTable base start receiver
      sender)
    (key : Key) (hstart : start key = (base key).initial)
    (env : Nat → RIn × SIn) :
    (base key).WinsPlay
      (finiteDependentHeterogeneousPinnedMemberPhysicalPlay base start receiver
        sender table key env) := by
  have hwins :=
    finiteDependentHeterogeneousPinnedMemberPhysicalPlay_restart_wins base
      start receiver sender table key env
  simpa [hstart, BlockRecordMonitor.restartAt] using hwins

end

end DistributedSynthesis
