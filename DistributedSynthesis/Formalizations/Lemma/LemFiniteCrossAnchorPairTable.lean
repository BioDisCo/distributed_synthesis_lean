/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmCrossAnchorLocalNarrowing
import DistributedSynthesis.Formalizations.Lemma.LemBlockRecordMonitorFirstTwoLetterGuard

/-!
# A finite table for two locally indistinguishable anchors

`FiniteCrossAnchorPairController` proves the simultaneous-narrowing theorem
with an existential finite-state controller.  A local carrier needs a fixed
finite alphabet instead.  This file materializes the same construction in the
state-controlled `FiniteRootFamilyTable` type.

The two members may have different monitors, different restart states, and
different receiver strategies.  They share only the semantic sender.  The
resulting two projected controllers therefore have one literally shared
sender table.  The hidden Boolean occurs only in the proof-side receiver
projection; it is not an input of the sender transition.
-/

namespace DistributedSynthesis

universe u v x y w d

noncomputable section

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

/-- The two restarted obligations which are rationalized simultaneously. -/
noncomputable abbrev finiteCrossAnchorRestartFamily
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut)
    (start : ∀ anchor, (base anchor).State) (anchor : Bool) :=
  (base anchor).restartAt (start anchor)

/-- A fixed finite move alphabet for two hidden anchors.  Unlike
`FiniteCrossAnchorPairController`, the data field has the canonical
state-controlled table type and hence is itself finite. -/
noncomputable abbrev FiniteCrossAnchorPairTable
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut)
    (start : ∀ anchor, (base anchor).State) :=
  { table : FiniteRootFamilyTable
      (finiteCrossAnchorRestartFamily base start) //
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor (finiteCrossAnchorRestartFamily base start))
      table.toTransitionRationalTree.labeledTree }

noncomputable instance finiteCrossAnchorPairTableFintype
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut)
    (start : ∀ anchor, (base anchor).State) :
    Fintype (FiniteCrossAnchorPairTable base start) := by
  classical
  infer_instance

/-- Project the receiver monitor for one hidden anchor from the one shared
finite table. -/
noncomputable def FiniteCrossAnchorPairTable.memberController
    {base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    (table : FiniteCrossAnchorPairTable base start) (anchor : Bool) :=
  finiteRootMemberController
    (finiteCrossAnchorRestartFamily base start)
    table.1.toTransitionRationalTree anchor

section
omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]

/-- Every member projection satisfies its own monitor from its own restart
state. -/
theorem FiniteCrossAnchorPairTable.memberController_wins
    {base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    (table : FiniteCrossAnchorPairTable base start) (anchor : Bool) :
    NarrowedAllThreadsWin (finiteCrossAnchorRestartFamily base start anchor)
      (table.memberController anchor).labeledTree := by
  exact finiteRootMemberController_allThreadsWin
    (finiteCrossAnchorRestartFamily base start)
    table.1.toTransitionRationalTree table.2 anchor

/-- The blind sender label is independent of the hidden anchor at every
future sender word. -/
theorem FiniteCrossAnchorPairTable.memberController_sender_eq
    {base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    (table : FiniteCrossAnchorPairTable base start)
    (left right : Bool) (word : List SIn) :
    ((table.memberController left).labeledTree word).1 =
      ((table.memberController right).labeledTree word).1 := by
  exact finiteRootMemberController_sender_eq
    (finiteCrossAnchorRestartFamily base start)
    table.1.toTransitionRationalTree left right word

/-- Strong local form: both projections use the same sender label even at an
arbitrary finite controller state.  Only the receiver half of the label reads
the anchor index. -/
theorem FiniteCrossAnchorPairTable.memberController_senderLabel_eq
    {base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    (table : FiniteCrossAnchorPairTable base start)
    (left right : Bool) (control : (table.memberController left).Control) :
    ((table.memberController left).labelOf control).1 =
      ((table.memberController right).labelOf control).1 := by
  rfl

/-- The sender-state update is likewise independent of the hidden anchor. -/
theorem FiniteCrossAnchorPairTable.memberController_step_eq
    {base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    (table : FiniteCrossAnchorPairTable base start)
    (left right : Bool) (control : (table.memberController left).Control)
    (input : SIn) :
    (table.memberController left).step control input =
      (table.memberController right).step control input := by
  rfl

end

/-- Simultaneously rationalize two arbitrary monitor/restart obligations
which are realized by one semantic sender. -/
noncomputable def finiteCrossAnchorPairTable
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut)
    (start : ∀ anchor, (base anchor).State)
    (receiver : ∀ anchor, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ anchor env,
      (finiteCrossAnchorRestartFamily base start anchor).WinsPlay
        (pairPlay (receiver anchor) sender env)) :
    FiniteCrossAnchorPairTable base start := by
  let table := finiteRootFamilyTable
    (finiteCrossAnchorRestartFamily base start) receiver sender hwin
  exact ⟨table,
    finiteRootFamilyTable_wins (finiteCrossAnchorRestartFamily base start)
      receiver sender hwin⟩

/-! ## Prefix-pinned preselection

At the charged seam it is not enough to know that each alternative accepts:
the first hard step must still be the literal common-front or staged record
from which the shadow was made.  The following variant inserts both finite
prefix tests *before* the simultaneous rationalization. -/

/-- The two restarted anchor monitors, each enriched with its own two-record
guard. -/
noncomputable abbrev finiteCrossAnchorFirstTwoGuardFamily
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut)
    (start : ∀ anchor, (base anchor).State)
    (firstAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool)
    (anchor : Bool) :=
  (finiteCrossAnchorRestartFamily base start anchor).firstTwoLetterGuard
    (firstAllowed anchor) (secondAllowed anchor)

/-- A finite preselected table whose two hidden members retain their own
first- and second-record laws. -/
noncomputable abbrev FiniteCrossAnchorFirstTwoTable
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut)
    (start : ∀ anchor, (base anchor).State)
    (firstAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool) :=
  { table : FiniteRootFamilyTable
      (finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed
        secondAllowed) //
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed
          secondAllowed))
      table.toTransitionRationalTree.labeledTree }

noncomputable instance finiteCrossAnchorFirstTwoTableFintype
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut)
    (start : ∀ anchor, (base anchor).State)
    (firstAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool) :
    Fintype (FiniteCrossAnchorFirstTwoTable base start firstAllowed
      secondAllowed) := by
  classical
  infer_instance

noncomputable def FiniteCrossAnchorFirstTwoTable.memberController
    {base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    {firstAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (table : FiniteCrossAnchorFirstTwoTable base start firstAllowed
      secondAllowed) (anchor : Bool) :=
  finiteRootMemberController
    (finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed secondAllowed)
    table.1.toTransitionRationalTree anchor

section
omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]

theorem FiniteCrossAnchorFirstTwoTable.memberController_wins
    {base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    {firstAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (table : FiniteCrossAnchorFirstTwoTable base start firstAllowed
      secondAllowed) (anchor : Bool) :
    NarrowedAllThreadsWin
      (finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed secondAllowed
        anchor)
      (table.memberController anchor).labeledTree := by
  exact finiteRootMemberController_allThreadsWin
    (finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed secondAllowed)
    table.1.toTransitionRationalTree table.2 anchor

/-- Forget the finite prefix test after preselection.  Pointwise, the exact
physical play induced by a guarded member still wins its restarted base
monitor.  This is the honest generic handoff: the controller label retains a
guard-state argument, so in general there is no separate base-typed narrowed
tree to manufacture; the physical play is the common object. -/
theorem FiniteCrossAnchorFirstTwoTable.memberController_base_wins
    {base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    {firstAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (table : FiniteCrossAnchorFirstTwoTable base start firstAllowed
      secondAllowed)
    (anchor : Bool) (env : Nat → RIn × SIn) :
    let restarted := finiteCrossAnchorRestartFamily base start anchor
    let guard := finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed
      secondAllowed anchor
    let controller := table.memberController anchor
    let play := treePlay
      (narrowedInducedTree guard controller.labeledTree) env
    restarted.WinsPlay play := by
  let restarted := finiteCrossAnchorRestartFamily base start anchor
  let guard := finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed
    secondAllowed anchor
  let controller := table.memberController anchor
  let play := treePlay
    (narrowedInducedTree guard controller.labeledTree) env
  have htree : guard.lift.WinningTree
      (narrowedInducedTree guard controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin guard
      (table.memberController_wins anchor)
  have hguard : guard.WinsPlay play :=
    (guard.lift_winningTree_iff
      (narrowedInducedTree guard controller.labeledTree)).mp htree env
  exact restarted.firstTwoLetterGuard_base_wins_of_wins
    (firstAllowed anchor) (secondAllowed anchor) play hguard

/-- The two pinned records can be read directly from any preselected table,
not only from the particular constructor call which produced it. -/
theorem FiniteCrossAnchorFirstTwoTable.memberController_records_allowed
    {base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    {firstAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (table : FiniteCrossAnchorFirstTwoTable base start firstAllowed
      secondAllowed)
    (anchor : Bool) (firstMove secondMove : RIn × SIn) :
    let guard := finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed
      secondAllowed anchor
    let controller := table.memberController anchor
    let firstRecord := narrowedRecord guard (controller.labeledTree [])
      guard.initial firstMove
    let secondRecord := narrowedRecord guard
      (controller.labeledTree [firstMove.2])
      (guard.step guard.initial firstRecord) secondMove
    firstAllowed anchor firstRecord = true ∧
      secondAllowed anchor firstRecord secondRecord = true := by
  exact (finiteCrossAnchorRestartFamily base start anchor
    ).firstTwoLetterGuard_narrowed_records_allowed
      (firstAllowed anchor) (secondAllowed anchor)
      (table.memberController anchor).labeledTree
      (table.memberController_wins anchor) firstMove secondMove

theorem FiniteCrossAnchorFirstTwoTable.memberController_sender_eq
    {base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    {firstAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (table : FiniteCrossAnchorFirstTwoTable base start firstAllowed
      secondAllowed) (left right : Bool) (word : List SIn) :
    ((table.memberController left).labeledTree word).1 =
      ((table.memberController right).labeledTree word).1 := by
  exact finiteRootMemberController_sender_eq
    (finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed secondAllowed)
    table.1.toTransitionRationalTree left right word

/-- The first-two guards constrain only the proof-side monitor projection;
the sender label stored in the preselected table is still literally shared
at every controller state. -/
theorem FiniteCrossAnchorFirstTwoTable.memberController_senderLabel_eq
    {base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    {firstAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (table : FiniteCrossAnchorFirstTwoTable base start firstAllowed
      secondAllowed)
    (left right : Bool) (control : (table.memberController left).Control) :
    ((table.memberController left).labelOf control).1 =
      ((table.memberController right).labelOf control).1 := by
  rfl

/-- The shared table control also advances without reading the hidden member
or either prefix guard. -/
theorem FiniteCrossAnchorFirstTwoTable.memberController_step_eq_atControl
    {base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    {firstAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (table : FiniteCrossAnchorFirstTwoTable base start firstAllowed
      secondAllowed)
    (left right : Bool) (control : (table.memberController left).Control)
    (input : SIn) :
    (table.memberController left).step control input =
      (table.memberController right).step control input := by
  rfl

end

/-- Materialize the prefix-pinned table from a single semantic sender. -/
noncomputable def finiteCrossAnchorFirstTwoTable
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut)
    (start : ∀ anchor, (base anchor).State)
    (firstAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool)
    (receiver : ∀ anchor, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hbase : ∀ anchor env,
      (finiteCrossAnchorRestartFamily base start anchor).WinsPlay
        (pairPlay (receiver anchor) sender env))
    (hfirst : ∀ anchor env,
      firstAllowed anchor (pairPlay (receiver anchor) sender env 0) = true)
    (hsecond : ∀ anchor env,
      secondAllowed anchor (pairPlay (receiver anchor) sender env 0)
        (pairPlay (receiver anchor) sender env 1) = true) :
    FiniteCrossAnchorFirstTwoTable base start firstAllowed secondAllowed := by
  let family := finiteCrossAnchorRestartFamily base start
  let guardFamily := finiteCrossAnchorFirstTwoGuardFamily base start
    firstAllowed secondAllowed
  let hguard : ∀ anchor env,
      (guardFamily anchor).WinsPlay
        (pairPlay (receiver anchor) sender env) := by
    intro anchor
    exact (family anchor).firstTwoLetterGuard_realizable
      (firstAllowed anchor) (secondAllowed anchor) (receiver anchor) sender
      (hbase anchor) (hfirst anchor) (hsecond anchor)
  let table := BlockRecordMonitor.firstTwoLetterGuardedFiniteRootFamilyTable
    family firstAllowed secondAllowed receiver sender hbase hfirst hsecond
  exact ⟨table,
    finiteRootFamilyTable_wins guardFamily receiver sender hguard⟩

/-- The two semantic prefix laws survive the finite preselection, for every
pair of concrete receiver/sender inputs. -/
theorem finiteCrossAnchorFirstTwoTable_records_allowed
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut)
    (start : ∀ anchor, (base anchor).State)
    (firstAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool)
    (receiver : ∀ anchor, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hbase : ∀ anchor env,
      (finiteCrossAnchorRestartFamily base start anchor).WinsPlay
        (pairPlay (receiver anchor) sender env))
    (hfirst : ∀ anchor env,
      firstAllowed anchor (pairPlay (receiver anchor) sender env 0) = true)
    (hsecond : ∀ anchor env,
      secondAllowed anchor (pairPlay (receiver anchor) sender env 0)
        (pairPlay (receiver anchor) sender env 1) = true)
    (anchor : Bool) (firstMove secondMove : RIn × SIn) :
    let guard := finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed
      secondAllowed anchor
    let table := finiteCrossAnchorFirstTwoTable base start firstAllowed
      secondAllowed receiver sender hbase hfirst hsecond
    let controller := table.memberController anchor
    let firstRecord := narrowedRecord guard (controller.labeledTree [])
      guard.initial firstMove
    let secondRecord := narrowedRecord guard
      (controller.labeledTree [firstMove.2])
      (guard.step guard.initial firstRecord) secondMove
    firstAllowed anchor firstRecord = true ∧
      secondAllowed anchor firstRecord secondRecord = true := by
  exact BlockRecordMonitor.firstTwoLetterGuardedFiniteRootMemberController_records_allowed
    (finiteCrossAnchorRestartFamily base start) firstAllowed secondAllowed
      receiver sender hbase hfirst hsecond anchor firstMove secondMove

/-! ## A fixed outer move alphabet

The monitor descriptors themselves can differ across the two interpretations.
Packaging the descriptor pair before the table keeps the resulting move type
finite and removes all dependent monitor types from the surrounding local
carrier. -/

section DescriptorPair

variable {Descriptor : Type d} [Fintype Descriptor]
variable (monitor : Descriptor →
  BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

/-- Two finite monitor descriptors and the two monitor states at which their
future obligations begin. -/
structure FiniteCrossAnchorDescriptorPair where
  descriptor : Bool → Descriptor
  start : ∀ anchor, (monitor (descriptor anchor)).State

noncomputable instance finiteCrossAnchorDescriptorPairFintype :
    Fintype (FiniteCrossAnchorDescriptorPair monitor) := by
  classical
  let Rep := Sigma fun descriptor : Bool → Descriptor =>
    ∀ anchor, (monitor (descriptor anchor)).State
  let equiv : FiniteCrossAnchorDescriptorPair monitor ≃ Rep :=
    { toFun := fun pair => ⟨pair.descriptor, pair.start⟩
      invFun := fun pair => ⟨pair.1, pair.2⟩
      left_inv := by intro pair; cases pair; rfl
      right_inv := by intro pair; rcases pair with ⟨descriptor, start⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- One finite preselected move for an arbitrary pair of finite monitor
descriptors. -/
noncomputable abbrev FiniteCrossAnchorDescriptorMove :=
  Sigma fun pair : FiniteCrossAnchorDescriptorPair monitor =>
    FiniteCrossAnchorPairTable
      (fun anchor => monitor (pair.descriptor anchor)) pair.start

noncomputable instance finiteCrossAnchorDescriptorMoveFintype :
    Fintype (FiniteCrossAnchorDescriptorMove monitor) := by
  classical
  infer_instance

noncomputable def FiniteCrossAnchorDescriptorMove.memberController
    (move : FiniteCrossAnchorDescriptorMove monitor) (anchor : Bool) :=
  move.2.memberController anchor

section
omit [Fintype Descriptor] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]

/-- Each projection of a descriptor-indexed move satisfies the monitor at
its stored restart state.  Keeping this theorem at the descriptor layer is
important for readback: a semantic installation can reason about either
member without reopening the finite-table construction. -/
theorem FiniteCrossAnchorDescriptorMove.memberController_wins
    (move : FiniteCrossAnchorDescriptorMove monitor) (anchor : Bool) :
    NarrowedAllThreadsWin
      ((monitor (move.1.descriptor anchor)).restartAt
        (move.1.start anchor))
      (move.memberController monitor anchor).labeledTree := by
  exact move.2.memberController_wins anchor

/-- Even across distinct descriptors, the hidden member cannot change the
blind sender table. -/
theorem FiniteCrossAnchorDescriptorMove.memberController_sender_eq
    (move : FiniteCrossAnchorDescriptorMove monitor)
    (left right : Bool) (word : List SIn) :
    ((move.memberController monitor left).labeledTree word).1 =
      ((move.memberController monitor right).labeledTree word).1 :=
  move.2.memberController_sender_eq left right word

/-- Arbitrary-control sender equality, the local transition-table form used
by a graph-blind carrier. -/
theorem FiniteCrossAnchorDescriptorMove.memberController_senderLabel_eq
    (move : FiniteCrossAnchorDescriptorMove monitor)
    (left right : Bool)
    (control : (move.memberController monitor left).Control) :
    ((move.memberController monitor left).labelOf control).1 =
      ((move.memberController monitor right).labelOf control).1 := by
  exact move.2.memberController_senderLabel_eq left right control

theorem FiniteCrossAnchorDescriptorMove.memberController_step_eq
    (move : FiniteCrossAnchorDescriptorMove monitor)
    (left right : Bool)
    (control : (move.memberController monitor left).Control) (input : SIn) :
    (move.memberController monitor left).step control input =
      (move.memberController monitor right).step control input := by
  exact move.2.memberController_step_eq left right control input

end

/-- Construct one member of the fixed outer alphabet from a concrete pair of
descriptors and one common semantic sender. -/
noncomputable def finiteCrossAnchorDescriptorMove
    (pair : FiniteCrossAnchorDescriptorPair monitor)
    (receiver : ∀ anchor, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ anchor env,
      ((monitor (pair.descriptor anchor)).restartAt (pair.start anchor)
        ).WinsPlay (pairPlay (receiver anchor) sender env)) :
    FiniteCrossAnchorDescriptorMove monitor :=
  ⟨pair,
    finiteCrossAnchorPairTable
      (fun anchor => monitor (pair.descriptor anchor)) pair.start receiver
        sender hwin⟩

/-! ### Prefix-pinned descriptor moves

The charged seam needs the same outer alphabet, but with each descriptor
member retaining its own first-two-record test.  The tests may depend on the
entire descriptor pair; this permits the two members to use unrelated
monitor types and dependent restart states while the table is still chosen
once, before the hidden member is resolved. -/

/-- A finite guarded move over two potentially different descriptors. -/
noncomputable abbrev FiniteCrossAnchorDescriptorFirstTwoMove
    (firstAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool) :=
  Sigma fun pair : FiniteCrossAnchorDescriptorPair monitor =>
    FiniteCrossAnchorFirstTwoTable
      (fun anchor => monitor (pair.descriptor anchor)) pair.start
      (firstAllowed pair) (secondAllowed pair)

noncomputable instance finiteCrossAnchorDescriptorFirstTwoMoveFintype
    (firstAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool) :
    Fintype (FiniteCrossAnchorDescriptorFirstTwoMove monitor firstAllowed
      secondAllowed) := by
  classical
  infer_instance

noncomputable def FiniteCrossAnchorDescriptorFirstTwoMove.memberController
    {firstAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (move : FiniteCrossAnchorDescriptorFirstTwoMove monitor firstAllowed
      secondAllowed)
    (anchor : Bool) :=
  move.2.memberController anchor

section
omit [Fintype Descriptor] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]

theorem FiniteCrossAnchorDescriptorFirstTwoMove.memberController_wins
    {firstAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (move : FiniteCrossAnchorDescriptorFirstTwoMove monitor firstAllowed
      secondAllowed)
    (anchor : Bool) :
    NarrowedAllThreadsWin
      (finiteCrossAnchorFirstTwoGuardFamily
        (fun member => monitor (move.1.descriptor member)) move.1.start
        (firstAllowed move.1) (secondAllowed move.1) anchor)
      (move.memberController monitor anchor).labeledTree := by
  exact move.2.memberController_wins anchor

/-- Descriptor-indexed form of guard erasure.  It supports unrelated member
descriptors and dependent starts; only the induced physical play crosses the
type boundary. -/
theorem
    FiniteCrossAnchorDescriptorFirstTwoMove.memberController_base_wins
    {firstAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (move : FiniteCrossAnchorDescriptorFirstTwoMove monitor firstAllowed
      secondAllowed)
    (anchor : Bool) (env : Nat → RIn × SIn) :
    let restarted :=
      (monitor (move.1.descriptor anchor)).restartAt (move.1.start anchor)
    let guard := finiteCrossAnchorFirstTwoGuardFamily
      (fun member => monitor (move.1.descriptor member)) move.1.start
      (firstAllowed move.1) (secondAllowed move.1) anchor
    let controller := move.memberController monitor anchor
    let play := treePlay
      (narrowedInducedTree guard controller.labeledTree) env
    restarted.WinsPlay play := by
  exact move.2.memberController_base_wins anchor env

/-- Descriptor-indexed prefix preservation, in the concrete two-record form
consumed by automatic-cut alignment proofs. -/
theorem
    FiniteCrossAnchorDescriptorFirstTwoMove.memberController_records_allowed
    {firstAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (move : FiniteCrossAnchorDescriptorFirstTwoMove monitor firstAllowed
      secondAllowed)
    (anchor : Bool) (firstMove secondMove : RIn × SIn) :
    let guard := finiteCrossAnchorFirstTwoGuardFamily
      (fun member => monitor (move.1.descriptor member)) move.1.start
      (firstAllowed move.1) (secondAllowed move.1) anchor
    let controller := move.memberController monitor anchor
    let firstRecord := narrowedRecord guard (controller.labeledTree [])
      guard.initial firstMove
    let secondRecord := narrowedRecord guard
      (controller.labeledTree [firstMove.2])
      (guard.step guard.initial firstRecord) secondMove
    firstAllowed move.1 anchor firstRecord = true ∧
      secondAllowed move.1 anchor firstRecord secondRecord = true := by
  exact move.2.memberController_records_allowed anchor firstMove secondMove

end

section
omit [Fintype Descriptor] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]

theorem
    FiniteCrossAnchorDescriptorFirstTwoMove.memberController_sender_eq
    {firstAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (move : FiniteCrossAnchorDescriptorFirstTwoMove monitor firstAllowed
      secondAllowed)
    (left right : Bool) (word : List SIn) :
    ((move.memberController monitor left).labeledTree word).1 =
      ((move.memberController monitor right).labeledTree word).1 :=
  move.2.memberController_sender_eq left right word

theorem
    FiniteCrossAnchorDescriptorFirstTwoMove.memberController_senderLabel_eq
    {firstAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (move : FiniteCrossAnchorDescriptorFirstTwoMove monitor firstAllowed
      secondAllowed)
    (left right : Bool)
    (control : (move.memberController monitor left).Control) :
    ((move.memberController monitor left).labelOf control).1 =
      ((move.memberController monitor right).labelOf control).1 := by
  exact move.2.memberController_senderLabel_eq left right control

theorem FiniteCrossAnchorDescriptorFirstTwoMove.memberController_step_eq
    {firstAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (move : FiniteCrossAnchorDescriptorFirstTwoMove monitor firstAllowed
      secondAllowed)
    (left right : Bool)
    (control : (move.memberController monitor left).Control) (input : SIn) :
    (move.memberController monitor left).step control input =
      (move.memberController monitor right).step control input := by
  exact move.2.memberController_step_eq_atControl left right control input

end

/-- Construct a guarded descriptor move from the same semantic sender for
both hidden interpretations. -/
noncomputable def finiteCrossAnchorDescriptorFirstTwoMove
    (firstAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool)
    (pair : FiniteCrossAnchorDescriptorPair monitor)
    (receiver : ∀ anchor, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hbase : ∀ anchor env,
      ((monitor (pair.descriptor anchor)).restartAt (pair.start anchor)
        ).WinsPlay (pairPlay (receiver anchor) sender env))
    (hfirst : ∀ anchor env,
      firstAllowed pair anchor
        (pairPlay (receiver anchor) sender env 0) = true)
    (hsecond : ∀ anchor env,
      secondAllowed pair anchor
        (pairPlay (receiver anchor) sender env 0)
        (pairPlay (receiver anchor) sender env 1) = true) :
    FiniteCrossAnchorDescriptorFirstTwoMove monitor firstAllowed
      secondAllowed :=
  ⟨pair,
    finiteCrossAnchorFirstTwoTable
      (fun anchor => monitor (pair.descriptor anchor)) pair.start
      (firstAllowed pair) (secondAllowed pair) receiver sender hbase hfirst
      hsecond⟩

/-! ### The graph-blind sender carrier

Once the move has been preselected, the local sender stores only its one
shared table control.  The proof-side bit is absent from this type and from
its transition. -/

/-- A preselected finite move together with its single shared sender state. -/
noncomputable abbrev FiniteCrossAnchorDescriptorSenderControl :=
  Sigma fun move : FiniteCrossAnchorDescriptorMove monitor =>
    (move.memberController monitor false).Control

noncomputable instance finiteCrossAnchorDescriptorSenderControlFintype :
    Fintype (FiniteCrossAnchorDescriptorSenderControl monitor) := by
  classical
  infer_instance

/-- Install the canonical shared root of a preselected move. -/
noncomputable def finiteCrossAnchorDescriptorSenderInitial
    (move : FiniteCrossAnchorDescriptorMove monitor) :
    FiniteCrossAnchorDescriptorSenderControl monitor :=
  ⟨move, (move.memberController monitor false).initial⟩

/-- One graph-blind local sender transition.  It receives only its own input;
neither the hidden anchor nor a graph/orientation is an argument. -/
noncomputable def finiteCrossAnchorDescriptorSenderStep
    (state : FiniteCrossAnchorDescriptorSenderControl monitor)
    (input : SIn) :
    SOut × FiniteCrossAnchorDescriptorSenderControl monitor :=
  let controller := state.1.memberController monitor false
  let label := controller.labelOf state.2
  (label.1 input, ⟨state.1, controller.step state.2 input⟩)

section
omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] [Fintype Descriptor]

@[simp] theorem finiteCrossAnchorDescriptorSenderStep_move
    (state : FiniteCrossAnchorDescriptorSenderControl monitor)
    (input : SIn) :
    (finiteCrossAnchorDescriptorSenderStep monitor state input).2.1 =
      state.1 :=
  rfl

/-- The emitted output is simultaneously the sender output of either hidden
member. -/
theorem finiteCrossAnchorDescriptorSenderStep_output_eq_member
    (state : FiniteCrossAnchorDescriptorSenderControl monitor)
    (input : SIn) (anchor : Bool) :
    (finiteCrossAnchorDescriptorSenderStep monitor state input).1 =
      ((state.1.memberController monitor anchor).labelOf state.2).1 input := by
  cases anchor <;> rfl

/-- The successor is also the transition of either hidden projection; the
same finite state replaces the ambiguity rather than forking it. -/
theorem finiteCrossAnchorDescriptorSenderStep_control_eq_member
    (state : FiniteCrossAnchorDescriptorSenderControl monitor)
    (input : SIn) (anchor : Bool) :
    (finiteCrossAnchorDescriptorSenderStep monitor state input).2.2 =
      (state.1.memberController monitor anchor).step state.2 input := by
  cases anchor <;> rfl

end

end DescriptorPair

/-! ## Strategy-local constructors

These are the model-facing forms: equality of the blind process's two local
views supplies the common sender required above. -/

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
variable [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Process one is the blind sender.  The anchors may still use unrelated
monitor states and receiver continuations. -/
noncomputable def finiteCrossAnchorPairTableOneOfViewEq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.one (history false) =
      currentView Proc.one (history true))
    (base : Bool → BlockRecordMonitor.{v, u, y, x, w}
      In₂ In₁ Out₂ Out₁)
    (start : ∀ anchor, (base anchor).State)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₂ In₁ Out₂)
    (hwin : ∀ anchor env,
      (finiteCrossAnchorRestartFamily base start anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history anchor)) env)) :
    FiniteCrossAnchorPairTable base start := by
  apply finiteCrossAnchorPairTable base start receiver
    (blockSenderOne strategy (history false))
  intro anchor env
  cases anchor with
  | false => exact hwin false env
  | true =>
      rw [blockSenderOne_eq_of_view_eq strategy hview]
      exact hwin true env

/-- Process-two mirror. -/
noncomputable def finiteCrossAnchorPairTableTwoOfViewEq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.two (history false) =
      currentView Proc.two (history true))
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      In₁ In₂ Out₁ Out₂)
    (start : ∀ anchor, (base anchor).State)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₁ In₂ Out₁)
    (hwin : ∀ anchor env,
      (finiteCrossAnchorRestartFamily base start anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history anchor)) env)) :
    FiniteCrossAnchorPairTable base start := by
  apply finiteCrossAnchorPairTable base start receiver
    (blockSenderTwo strategy (history false))
  intro anchor env
  cases anchor with
  | false => exact hwin false env
  | true =>
      rw [blockSenderTwo_eq_of_view_eq strategy hview]
      exact hwin true env

end DetParityAutomaton

end

end DistributedSynthesis
