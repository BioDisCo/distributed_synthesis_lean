/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyNarrowing
import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyPinnedReindexing
import DistributedSynthesis.Formalizations.Lemma.LemLocallyConsistentStateControlled

/-!
# Common-past finite-root narrowing

This is the fail-fast repair for the dependent member/root pair test.  The
older descriptor-wise provenance predicate says that every projected receiver
row has *some* semantic past; those witnesses need not be the same.  Here the
complete union table is restricted instead to one literal union receiver at
one common past.

The restriction survives the existing state-controlled rationalization.  As
a consequence, any observation that is homogeneous between family members at
one common untagged past remains homogeneous in every table of the resulting
finite controller.  No family member, leader, orientation, or hidden bit is
selected by the sender.
-/

namespace DistributedSynthesis

universe i u v x y w z

section

variable {I : Type i}
variable {RIn : Type u} {SIn : Type v}
variable {ROut : Type x} {SOut : Type y}

/-- A union receiver table has simultaneous provenance when the *whole* table
is one semantic family receiver at one tagged past.  Projecting this equation
to two members therefore uses the same untagged past on both sides. -/
def FiniteRootFamilyCommonPastAllowed
    (receiver : ∀ _ : I, ReceiverBlockStrategy RIn SIn ROut)
    (responses : ((I × RIn) × SIn) → ROut) : Prop :=
  ∃ past : List ((I × RIn) × SIn),
    responses = finiteRootFamilyReceiver receiver past

noncomputable instance finiteRootFamilyCommonPastAllowed_decidable
    (receiver : ∀ _ : I, ReceiverBlockStrategy RIn SIn ROut) :
    DecidablePred (FiniteRootFamilyCommonPastAllowed receiver) :=
  fun _ ↦ Classical.propDecidable _

variable (M : I →
  BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

variable [Fintype I] [DecidableEq I]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]
variable [Inhabited I] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]

/-- The existing finite rationalization can be run under the common-past law.
This is the decisive existence test: the stronger law is not lost merely
because the result is state controlled. -/
noncomputable def finiteRootFamilyCommonPastTableOfStrategies
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ index env, (M index).WinsPlay
      (pairPlay (receiver index) sender env)) :
    LocallyConsistentNarrowedTable
      (finiteRootFamilyMonitor M)
      (FiniteRootFamilyCommonPastAllowed receiver) := by
  let unionReceiver := finiteRootFamilyReceiver receiver
  have hunionWin : ∀ env,
      (finiteRootFamilyMonitor M).WinsPlay
        (pairPlay unionReceiver sender env) :=
    finiteRootFamily_realizable M receiver sender hwin
  exact locallyConsistentTableOfStrategies
    (finiteRootFamilyMonitor M)
    (FiniteRootFamilyCommonPastAllowed receiver)
    (unionReceiver [])
    (⟨[], rfl⟩ :
      FiniteRootFamilyCommonPastAllowed receiver (unionReceiver []))
    unionReceiver sender hunionWin
    (fun past ↦ (⟨past, rfl⟩ :
      FiniteRootFamilyCommonPastAllowed receiver (unionReceiver past)))

omit [Inhabited ROut] in
/-- The common-past restriction does not weaken the universal-thread parity
guarantee. -/
theorem finiteRootFamilyCommonPastTableOfStrategies_wins
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ index env, (M index).WinsPlay
      (pairPlay (receiver index) sender env)) :
    NarrowedAllThreadsWin (finiteRootFamilyMonitor M)
      (finiteRootFamilyCommonPastTableOfStrategies M receiver sender hwin
        ).toTransitionRationalTree.labeledTree := by
  let unionReceiver := finiteRootFamilyReceiver receiver
  have hunionWin : ∀ env,
      (finiteRootFamilyMonitor M).WinsPlay
        (pairPlay unionReceiver sender env) :=
    finiteRootFamily_realizable M receiver sender hwin
  simpa [finiteRootFamilyCommonPastTableOfStrategies] using
    (locallyConsistentTableOfStrategies_wins
      (finiteRootFamilyMonitor M)
      (FiniteRootFamilyCommonPastAllowed receiver)
      (unionReceiver []) (⟨[], rfl⟩ :
        FiniteRootFamilyCommonPastAllowed receiver (unionReceiver []))
      unionReceiver sender hunionWin
      (fun past ↦ (⟨past, rfl⟩ :
        FiniteRootFamilyCommonPastAllowed receiver (unionReceiver past))))

omit [Inhabited ROut] in
/-- Every table of the extracted finite controller still has one common
semantic past. -/
theorem finiteRootFamilyCommonPastTableOfStrategies_allowed
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ index env, (M index).WinsPlay
      (pairPlay (receiver index) sender env)) :
    NarrowedTablesAllowed (finiteRootFamilyMonitor M)
      (FiniteRootFamilyCommonPastAllowed receiver)
      (finiteRootFamilyCommonPastTableOfStrategies M receiver sender hwin
        ).toTransitionRationalTree.labeledTree := by
  let unionReceiver := finiteRootFamilyReceiver receiver
  have hunionWin : ∀ env,
      (finiteRootFamilyMonitor M).WinsPlay
        (pairPlay unionReceiver sender env) :=
    finiteRootFamily_realizable M receiver sender hwin
  simpa [finiteRootFamilyCommonPastTableOfStrategies] using
    (locallyConsistentTableOfStrategies_allowed
      (finiteRootFamilyMonitor M)
      (FiniteRootFamilyCommonPastAllowed receiver)
      (unionReceiver []) (⟨[], rfl⟩ :
        FiniteRootFamilyCommonPastAllowed receiver (unionReceiver []))
      unionReceiver sender hunionWin
      (fun past ↦ (⟨past, rfl⟩ :
        FiniteRootFamilyCommonPastAllowed receiver (unionReceiver past))))

omit [Fintype I] [DecidableEq I] [Fintype RIn] [Fintype SIn] [Fintype ROut] [DecidableEq RIn]
    [DecidableEq SIn] [Inhabited I] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] in
/-- A common-past table preserves every member-independent observable
behavior.  `observe` may forget classified proof data and retain only the
physical output selected by a sticky row. -/
theorem finiteRootFamilyCommonPastAllowed_observe_pair
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    {Observed : Type z} (observe : ROut → Observed)
    (hhomogeneous : ∀ (past : List (RIn × SIn))
      (left right : I) (receiverInput : RIn) (senderInput : SIn),
      observe (receiver left past (receiverInput, senderInput)) =
        observe (receiver right past (receiverInput, senderInput)))
    {responses : ((I × RIn) × SIn) → ROut}
    (hallowed : FiniteRootFamilyCommonPastAllowed receiver responses)
    (left right : I) (receiverInput : RIn) (senderInput : SIn) :
    observe (responses ((left, receiverInput), senderInput)) =
      observe (responses ((right, receiverInput), senderInput)) := by
  rcases hallowed with ⟨past, rfl⟩
  exact hhomogeneous
    (past.map fun old ↦ (old.1.2, old.2)) left right receiverInput
      senderInput

omit [Inhabited ROut] in
/-- End-to-end pair test at an arbitrary finite controller label and monitor
state. -/
theorem finiteRootFamilyCommonPastTable_label_observe_pair
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ index env, (M index).WinsPlay
      (pairPlay (receiver index) sender env))
    {Observed : Type z} (observe : ROut → Observed)
    (hhomogeneous : ∀ (past : List (RIn × SIn))
      (left right : I) (receiverInput : RIn) (senderInput : SIn),
      observe (receiver left past (receiverInput, senderInput)) =
        observe (receiver right past (receiverInput, senderInput)))
    (word : List SIn) (state : (finiteRootFamilyMonitor M).State)
    (left right : I) (receiverInput : RIn) (senderInput : SIn) :
    let table := finiteRootFamilyCommonPastTableOfStrategies M receiver sender
      hwin
    observe ((table.toTransitionRationalTree.labeledTree word).2 state
        ((left, receiverInput), senderInput)) =
      observe ((table.toTransitionRationalTree.labeledTree word).2 state
        ((right, receiverInput), senderInput)) := by
  dsimp only
  apply finiteRootFamilyCommonPastAllowed_observe_pair receiver observe
    hhomogeneous
  exact finiteRootFamilyCommonPastTableOfStrategies_allowed M receiver sender
    hwin word state

end

/-! ## Weakening to the existing descriptor-family runtime alphabet -/

section DescriptorPinned

variable {Descriptor : Type i}
variable (Root : Descriptor → Type i)
variable {RIn : Type u} {SIn : Type v}
variable {ROut : Type x} {SOut : Type y}
variable
  (M : ∀ descriptor, Root descriptor →
    BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
variable
  (Weak : ∀ descriptor,
    (((Root descriptor × RIn) × SIn) → ROut) → Prop)
variable
  (expected : ∀ member : Sigma Root,
    RIn × SIn → RealizedBlockRound RIn SIn ROut SOut)

variable [Fintype Descriptor] [DecidableEq Descriptor]
variable [∀ descriptor, Fintype (Root descriptor)]
variable [∀ descriptor, DecidableEq (Root descriptor)]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

/-- A common-past extraction can be weakened, without changing a single
controller label, to the repository's existing descriptor-wise finite move
alphabet.  The returned proof is carried only on the proof side; the runtime
move remains exactly `FiniteDescriptorFamilyPinnedAllowedMove`.

This theorem is the reusable recut test needed by the profiled-open compiler.
-/
theorem exists_finiteDescriptorFamilyPinnedCommonPastMove
    [Inhabited (Sigma Root)] [Inhabited RIn] [Inhabited SIn]
    [Inhabited ROut]
    (receiver : ∀ member : Sigma Root,
      ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ member env,
      (M member.1 member.2).WinsPlay
        (pairPlay (receiver member) sender env))
    (hroot : ∀ member input,
      pairPlay (receiver member) sender (fun _ ↦ input) 0 =
        expected member input)
    (hweak : ∀ past,
      DescriptorRootUnionAllowed Root Weak
        (finiteRootFamilyReceiver receiver past)) :
    ∃ move : FiniteDescriptorFamilyPinnedAllowedMove Root M Weak expected,
      NarrowedTablesAllowed
        (finiteRootFamilyMonitor
          (descriptorRootUnionMonitor Root
            (descriptorRootPinnedMonitor Root M expected)))
        (FiniteRootFamilyCommonPastAllowed receiver)
        move.1.toTransitionRationalTree.labeledTree := by
  classical
  let pinnedM := descriptorRootUnionMonitor Root
    (descriptorRootPinnedMonitor Root M expected)
  have hpinnedWin : ∀ member env,
      (pinnedM member).WinsPlay (pairPlay (receiver member) sender env) := by
    intro member env
    exact (M member.1 member.2).rootPinned_realizable
      (expected member) (receiver member) sender (hwin member)
      (hroot member) env
  let strongTable := finiteRootFamilyCommonPastTableOfStrategies pinnedM
    receiver sender hpinnedWin
  let Strong := FiniteRootFamilyCommonPastAllowed receiver
  let WeakUnion := DescriptorRootUnionAllowed Root Weak
  have himp : ∀ responses, Strong responses → WeakUnion responses := by
    intro responses hresponses
    rcases hresponses with ⟨past, rfl⟩
    exact hweak past
  let weakTable : LocallyConsistentNarrowedTable
      (finiteRootFamilyMonitor pinnedM) WeakUnion :=
    strongTable.weaken (finiteRootFamilyMonitor pinnedM) Strong WeakUnion
  have hstrongWins : NarrowedAllThreadsWin (finiteRootFamilyMonitor pinnedM)
      strongTable.toTransitionRationalTree.labeledTree :=
    finiteRootFamilyCommonPastTableOfStrategies_wins pinnedM receiver sender
      hpinnedWin
  have hstrongAllowed : NarrowedTablesAllowed
      (finiteRootFamilyMonitor pinnedM) Strong
      strongTable.toTransitionRationalTree.labeledTree :=
    finiteRootFamilyCommonPastTableOfStrategies_allowed pinnedM receiver sender
      hpinnedWin
  have hweakWins : NarrowedAllThreadsWin (finiteRootFamilyMonitor pinnedM)
      weakTable.toTransitionRationalTree.labeledTree :=
    LocallyConsistentNarrowedTable.weaken_wins
      (finiteRootFamilyMonitor pinnedM) Strong WeakUnion strongTable hstrongWins
  have hweakAllowed : NarrowedTablesAllowed
      (finiteRootFamilyMonitor pinnedM) WeakUnion
      weakTable.toTransitionRationalTree.labeledTree :=
    LocallyConsistentNarrowedTable.weaken_allowed
      (finiteRootFamilyMonitor pinnedM) Strong WeakUnion himp strongTable
      hstrongAllowed
  let move : FiniteDescriptorFamilyPinnedAllowedMove Root M Weak expected :=
    ⟨weakTable, hweakWins, hweakAllowed⟩
  refine ⟨move, ?_⟩
  simpa [move, weakTable, Strong, pinnedM] using hstrongAllowed

end DescriptorPinned

end DistributedSynthesis
