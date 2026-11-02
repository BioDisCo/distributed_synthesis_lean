/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorInstalledFixedTailBookkeeping
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOverlayGlobalTraceSlice
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorScheduledPhysicalAlignment

/-!
# Output-only fixed-tail handoff for an installed compatible table

The existing fixed-tail theorem asks for equality of complete physical-word
suffixes.  For a concrete paired controller this is stronger than the local
trace invariant one should prove: the environment already fixes both inputs
and the graph.  The controller must identify only

* the DPA state at the installation cut;
* the suffix of inputs read by the installed table; and
* the two output coordinates produced by that table.

This file proves the generic record-extensionality adapter.  In an eventual
strict-right or strict-left regime the proof-side graph hypothesis supplies
the remaining coordinate, so output-tail bookkeeping yields
`EventuallyInstalledFixedTailBookkeeping` directly.  No runtime map receives
the graph regime, orientation, leader, or strict-leader bit.
-/

namespace DistributedSynthesis

universe u v x y s w

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

private abbrev Controller :=
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂

private abbrev TraceWord
    (controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) :=
  controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
    controller.globalOutputTwo env

/-! ## One installed strict-right output tail -/

/-- The weakest table-specific invariant for an installed strict-right tail.

`table_inputs` identifies the receiver-first input stream at the retained
table cut.  `outputPair` compares only the two controller outputs.  The graph
coordinate is intentionally absent; it is supplied proof-side by the
eventual-regime hypothesis in `toPhysicalTailAligned`. -/
structure ProfiledRawJointHybridPhysicalCompatibleRightInstalledOutputTailAligned
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (row : PairedEntryRow) (tableEnv : Nat → In₂ × In₁)
    (tableCut : Nat)
    (controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) (start : Nat) : Prop where
  state :
    A.run (TraceWord controller env) start =
      A.runFrom (pairedCodeStateForRow A row move.1.source.1.1)
        (profiledRawJointRightPhysicalSiblingWord A move row tableEnv) tableCut
  table_inputs : ∀ n : Nat,
    tableEnv (tableCut + n) =
      ((env (start + n)).inputTwo, (env (start + n)).inputOne)
  outputPair : ∀ n : Nat,
    (TraceWord controller env (start + n)).outputPair =
      (profiledRawJointRightPhysicalSiblingWord A move row tableEnv
        (tableCut + n)).outputPair

namespace
    ProfiledRawJointHybridPhysicalCompatibleRightInstalledOutputTailAligned

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Environment coordinates plus the output-only invariant recover equality
of the complete installed-table suffix. -/
theorem toPhysicalTailAligned
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {row : PairedEntryRow} {tableEnv : Nat → In₂ × In₁}
    {tableCut : Nat}
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂} {start : Nat}
    (aligned :
      ProfiledRawJointHybridPhysicalCompatibleRightInstalledOutputTailAligned
        A move row tableEnv tableCut controller env start)
    (hgraph : ∀ n : Nat, (env (start + n)).graph = .right) :
    ProfiledRawJointHybridPhysicalCompatibleRightInstalledPhysicalTailAligned
      A move row tableEnv tableCut (TraceWord controller env) start where
  state := aligned.state
  word := by
    funext n
    apply RoundRecord.eq_of_environment_eq_of_outputPair_eq
    · apply EnvironmentRound.eq_of_components
      · cases row <;> simpa [OmegaWord.drop_apply,
          profiledRawJointRightPhysicalSiblingWord,
          pairedRightRecordForRow, rightRoundRecord,
          RoundRecord.environment] using
            (congrArg Prod.snd (aligned.table_inputs n)).symm
      · cases row <;> simpa [OmegaWord.drop_apply,
          profiledRawJointRightPhysicalSiblingWord,
          pairedRightRecordForRow, rightRoundRecord,
          RoundRecord.environment] using
            (congrArg Prod.fst (aligned.table_inputs n)).symm
      · cases row <;> simpa [OmegaWord.drop_apply,
          profiledRawJointRightPhysicalSiblingWord,
          pairedRightRecordForRow, rightRoundRecord,
          RoundRecord.environment] using hgraph n
    · simpa only [OmegaWord.drop_apply] using aligned.outputPair n

end
  ProfiledRawJointHybridPhysicalCompatibleRightInstalledOutputTailAligned

/-! ## Strict-left mirror -/

structure ProfiledRawJointHybridPhysicalCompatibleLeftInstalledOutputTailAligned
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (row : PairedEntryRow) (tableEnv : Nat → In₁ × In₂)
    (tableCut : Nat)
    (controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) (start : Nat) : Prop where
  state :
    A.run (TraceWord controller env) start =
      A.runFrom (pairedCodeStateForRow A row move.1.source.1.1)
        (profiledRawJointLeftPhysicalSiblingWord A move row tableEnv) tableCut
  table_inputs : ∀ n : Nat,
    tableEnv (tableCut + n) =
      ((env (start + n)).inputOne, (env (start + n)).inputTwo)
  outputPair : ∀ n : Nat,
    (TraceWord controller env (start + n)).outputPair =
      (profiledRawJointLeftPhysicalSiblingWord A move row tableEnv
        (tableCut + n)).outputPair

namespace
    ProfiledRawJointHybridPhysicalCompatibleLeftInstalledOutputTailAligned

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem toPhysicalTailAligned
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {row : PairedEntryRow} {tableEnv : Nat → In₁ × In₂}
    {tableCut : Nat}
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂} {start : Nat}
    (aligned :
      ProfiledRawJointHybridPhysicalCompatibleLeftInstalledOutputTailAligned A
        move row tableEnv tableCut controller env start)
    (hgraph : ∀ n : Nat, (env (start + n)).graph = .left) :
    ProfiledRawJointHybridPhysicalCompatibleLeftInstalledPhysicalTailAligned A
      move row tableEnv tableCut (TraceWord controller env) start where
  state := aligned.state
  word := by
    funext n
    apply RoundRecord.eq_of_environment_eq_of_outputPair_eq
    · apply EnvironmentRound.eq_of_components
      · cases row <;> simpa [OmegaWord.drop_apply,
          profiledRawJointLeftPhysicalSiblingWord,
          pairedLeftRecordForRow, leftRoundRecord,
          RoundRecord.environment] using
            (congrArg Prod.fst (aligned.table_inputs n)).symm
      · cases row <;> simpa [OmegaWord.drop_apply,
          profiledRawJointLeftPhysicalSiblingWord,
          pairedLeftRecordForRow, leftRoundRecord,
          RoundRecord.environment] using
            (congrArg Prod.snd (aligned.table_inputs n)).symm
      · cases row <;> simpa [OmegaWord.drop_apply,
          profiledRawJointLeftPhysicalSiblingWord,
          pairedLeftRecordForRow, leftRoundRecord,
          RoundRecord.environment] using hgraph n
    · simpa only [OmegaWord.drop_apply] using aligned.outputPair n

end
  ProfiledRawJointHybridPhysicalCompatibleLeftInstalledOutputTailAligned

/-! ## Eventual-regime assembly -/

/-- Output-level fixed-tail obligations for one concrete controller word.

The witnesses may choose a cut after the eventual-regime threshold.  The
explicit `graph_tail` conjunct is proof-side environmental bookkeeping; the
only controller-specific infinite equation is `outputPair`. -/
structure EventuallyInstalledOutputTailBookkeeping
    (controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) : Prop where
  strictRight : EventuallyStrictRight (fun n ↦ (env n).graph) →
    ∃ (move : ProfiledRawJointRightPhysicalSiblingMove A)
      (row : PairedEntryRow) (tableEnv : Nat → In₂ × In₁)
      (tableCut start : Nat),
      (∀ n : Nat, (env (start + n)).graph = .right) ∧
        ProfiledRawJointHybridPhysicalCompatibleRightInstalledOutputTailAligned
          A move row tableEnv tableCut controller env start
  strictLeft : EventuallyStrictLeft (fun n ↦ (env n).graph) →
    ∃ (move : ProfiledRawJointLeftPhysicalSiblingMove A)
      (row : PairedEntryRow) (tableEnv : Nat → In₁ × In₂)
      (tableCut start : Nat),
      (∀ n : Nat, (env (start + n)).graph = .left) ∧
        ProfiledRawJointHybridPhysicalCompatibleLeftInstalledOutputTailAligned
          A move row tableEnv tableCut controller env start

namespace EventuallyInstalledOutputTailBookkeeping

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The output-level obligation is sufficient for the existing fixed-tail
bookkeeping and hence for both fixed-regime parity fields. -/
theorem toEventuallyInstalledFixedTailBookkeeping
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping : EventuallyInstalledOutputTailBookkeeping A controller env) :
    EventuallyInstalledFixedTailBookkeeping A (TraceWord controller env)
      (fun n ↦ (env n).graph) where
  strictRight hstrict := by
    rcases bookkeeping.strictRight hstrict with
      ⟨move, row, tableEnv, tableCut, start, hgraph, aligned⟩
    exact ⟨move, row, tableEnv, tableCut, start,
      aligned.toPhysicalTailAligned A hgraph⟩
  strictLeft hstrict := by
    rcases bookkeeping.strictLeft hstrict with
      ⟨move, row, tableEnv, tableCut, start, hgraph, aligned⟩
    exact ⟨move, row, tableEnv, tableCut, start,
      aligned.toPhysicalTailAligned A hgraph⟩

end EventuallyInstalledOutputTailBookkeeping

end

end DetParityAutomaton

end DistributedSynthesis
