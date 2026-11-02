/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRootFamilyOverlay

/-!
# Winning-table selection for end-to-end restart families

A proof-side restart family is realizable when one simultaneous finite table
wins the combined root-family monitor.  This file packages the corresponding
classical table and move selectors.  It also supplies an arbitrary table for
every source, so selection can be totalized without adding a realizability
proof to runtime control.

The fallback table has no semantic claim.  The total selector is proved
winning whenever the source is realizable.  None of these definitions takes a
history, current orientation, graph value, selected member, or leader bit.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-! ## Realizability predicates -/

/-- Winning predicate for one simultaneous right-family table. -/
def EndToEndRightFamilyRootTableWins
    (source : Bool → EndToEndRightRestartRoot A package)
    (table : EndToEndRightFamilyRootTable A package source) : Prop :=
  NarrowedAllThreadsWin
    (finiteRootFamilyMonitor (endToEndRightFamilyRootMonitors A package source))
    table.toTransitionRationalTree.labeledTree

/-- Winning predicate for one simultaneous left-family table. -/
def EndToEndLeftFamilyRootTableWins
    (source : Bool → EndToEndLeftRestartRoot A package)
    (table : EndToEndLeftFamilyRootTable A package source) : Prop :=
  NarrowedAllThreadsWin
    (finiteRootFamilyMonitor (endToEndLeftFamilyRootMonitors A package source))
    table.toTransitionRationalTree.labeledTree

/-- A right restart-root source is realizable by one shared finite table. -/
def EndToEndRightFamilySourceRealizable
    (source : Bool → EndToEndRightRestartRoot A package) : Prop :=
  ∃ table : EndToEndRightFamilyRootTable A package source,
    EndToEndRightFamilyRootTableWins A package source table

/-- Left restart-root source realizability. -/
def EndToEndLeftFamilySourceRealizable
    (source : Bool → EndToEndLeftRestartRoot A package) : Prop :=
  ∃ table : EndToEndLeftFamilyRootTable A package source,
    EndToEndLeftFamilyRootTableWins A package source table

/-! ## Selectors carrying an explicit realizability proof -/

/-- Classical winning table selected from a realizable right source. -/
noncomputable def endToEndRightWinningFamilyTable
    (source : Bool → EndToEndRightRestartRoot A package)
    (hrealizable : EndToEndRightFamilySourceRealizable A package source) :
    EndToEndRightFamilyRootTable A package source :=
  Classical.choose hrealizable

/-- Left-family mirror. -/
noncomputable def endToEndLeftWinningFamilyTable
    (source : Bool → EndToEndLeftRestartRoot A package)
    (hrealizable : EndToEndLeftFamilySourceRealizable A package source) :
    EndToEndLeftFamilyRootTable A package source :=
  Classical.choose hrealizable

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem endToEndRightWinningFamilyTable_wins
    (source : Bool → EndToEndRightRestartRoot A package)
    (hrealizable : EndToEndRightFamilySourceRealizable A package source) :
    EndToEndRightFamilyRootTableWins A package source
      (endToEndRightWinningFamilyTable A package source hrealizable) :=
  Classical.choose_spec hrealizable

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem endToEndLeftWinningFamilyTable_wins
    (source : Bool → EndToEndLeftRestartRoot A package)
    (hrealizable : EndToEndLeftFamilySourceRealizable A package source) :
    EndToEndLeftFamilyRootTableWins A package source
      (endToEndLeftWinningFamilyTable A package source hrealizable) :=
  Classical.choose_spec hrealizable

/-- Package a realizable right source and its selected table as an actual
finite family move. -/
noncomputable def endToEndRightWinningFamilyMove
    (source : Bool → EndToEndRightRestartRoot A package)
    (hrealizable : EndToEndRightFamilySourceRealizable A package source) :
    EndToEndRightFamilyPairMove A package :=
  ⟨source, endToEndRightWinningFamilyTable A package source hrealizable⟩

/-- Left-family mirror. -/
noncomputable def endToEndLeftWinningFamilyMove
    (source : Bool → EndToEndLeftRestartRoot A package)
    (hrealizable : EndToEndLeftFamilySourceRealizable A package source) :
    EndToEndLeftFamilyPairMove A package :=
  ⟨source, endToEndLeftWinningFamilyTable A package source hrealizable⟩

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndRightWinningFamilyMove_source
    (source : Bool → EndToEndRightRestartRoot A package)
    (hrealizable : EndToEndRightFamilySourceRealizable A package source) :
    (endToEndRightWinningFamilyMove A package source hrealizable).1 = source :=
  rfl

@[simp] theorem endToEndLeftWinningFamilyMove_source
    (source : Bool → EndToEndLeftRestartRoot A package)
    (hrealizable : EndToEndLeftFamilySourceRealizable A package source) :
    (endToEndLeftWinningFamilyMove A package source hrealizable).1 = source :=
  rfl

@[simp] theorem endToEndRightWinningFamilyMove_table
    (source : Bool → EndToEndRightRestartRoot A package)
    (hrealizable : EndToEndRightFamilySourceRealizable A package source) :
    (endToEndRightWinningFamilyMove A package source hrealizable).2 =
      endToEndRightWinningFamilyTable A package source hrealizable :=
  rfl

@[simp] theorem endToEndLeftWinningFamilyMove_table
    (source : Bool → EndToEndLeftRestartRoot A package)
    (hrealizable : EndToEndLeftFamilySourceRealizable A package source) :
    (endToEndLeftWinningFamilyMove A package source hrealizable).2 =
      endToEndLeftWinningFamilyTable A package source hrealizable :=
  rfl

theorem endToEndRightWinningFamilyMove_wins
    (source : Bool → EndToEndRightRestartRoot A package)
    (hrealizable : EndToEndRightFamilySourceRealizable A package source) :
    EndToEndRightFamilyRootTableWins A package source
      (endToEndRightWinningFamilyMove A package source hrealizable).2 :=
  endToEndRightWinningFamilyTable_wins A package source hrealizable

theorem endToEndLeftWinningFamilyMove_wins
    (source : Bool → EndToEndLeftRestartRoot A package)
    (hrealizable : EndToEndLeftFamilySourceRealizable A package source) :
    EndToEndLeftFamilyRootTableWins A package source
      (endToEndLeftWinningFamilyMove A package source hrealizable).2 :=
  endToEndLeftWinningFamilyTable_wins A package source hrealizable

end

/-! ## Arbitrary tables and total selectors -/

/-- A raw right-family table always exists.  The run-automaton initial state
provides a constant transition, while the inhabited output alphabets provide a
constant narrowed label. -/
noncomputable def arbitraryEndToEndRightFamilyRootTable
    (source : Bool → EndToEndRightRestartRoot A package) :
    EndToEndRightFamilyRootTable A package source := by
  classical
  let monitor := finiteRootFamilyMonitor
    (endToEndRightFamilyRootMonitors A package source)
  let run := (BlockRecordMonitor.threadBlockMonitor monitor).toRunAutomaton
  exact
    { step := fun _ _ => run.initial
      label := fun _ => default }

/-- Left-family arbitrary table. -/
noncomputable def arbitraryEndToEndLeftFamilyRootTable
    (source : Bool → EndToEndLeftRestartRoot A package) :
    EndToEndLeftFamilyRootTable A package source := by
  classical
  let monitor := finiteRootFamilyMonitor
    (endToEndLeftFamilyRootMonitors A package source)
  let run := (BlockRecordMonitor.threadBlockMonitor monitor).toRunAutomaton
  exact
    { step := fun _ _ => run.initial
      label := fun _ => default }

omit [Inhabited In₁] [Inhabited In₂] in
theorem nonempty_endToEndRightFamilyRootTable
    (source : Bool → EndToEndRightRestartRoot A package) :
    Nonempty (EndToEndRightFamilyRootTable A package source) :=
  ⟨arbitraryEndToEndRightFamilyRootTable A package source⟩

omit [Inhabited In₁] [Inhabited In₂] in
theorem nonempty_endToEndLeftFamilyRootTable
    (source : Bool → EndToEndLeftRestartRoot A package) :
    Nonempty (EndToEndLeftFamilyRootTable A package source) :=
  ⟨arbitraryEndToEndLeftFamilyRootTable A package source⟩

/-- Total right table selector.  Its fallback is deliberately arbitrary. -/
noncomputable def endToEndRightFamilyTableSelector
    (source : Bool → EndToEndRightRestartRoot A package) :
    EndToEndRightFamilyRootTable A package source := by
  classical
  if hrealizable : EndToEndRightFamilySourceRealizable A package source then
    exact endToEndRightWinningFamilyTable A package source hrealizable
  else
    exact arbitraryEndToEndRightFamilyRootTable A package source

/-- Total left table selector. -/
noncomputable def endToEndLeftFamilyTableSelector
    (source : Bool → EndToEndLeftRestartRoot A package) :
    EndToEndLeftFamilyRootTable A package source := by
  classical
  if hrealizable : EndToEndLeftFamilySourceRealizable A package source then
    exact endToEndLeftWinningFamilyTable A package source hrealizable
  else
    exact arbitraryEndToEndLeftFamilyRootTable A package source

omit [Inhabited In₁] [Inhabited In₂] in
theorem endToEndRightFamilyTableSelector_wins
    (source : Bool → EndToEndRightRestartRoot A package)
    (hrealizable : EndToEndRightFamilySourceRealizable A package source) :
    EndToEndRightFamilyRootTableWins A package source
      (endToEndRightFamilyTableSelector A package source) := by
  classical
  simp only [endToEndRightFamilyTableSelector, dif_pos hrealizable]
  exact endToEndRightWinningFamilyTable_wins A package source hrealizable

omit [Inhabited In₁] [Inhabited In₂] in
theorem endToEndLeftFamilyTableSelector_wins
    (source : Bool → EndToEndLeftRestartRoot A package)
    (hrealizable : EndToEndLeftFamilySourceRealizable A package source) :
    EndToEndLeftFamilyRootTableWins A package source
      (endToEndLeftFamilyTableSelector A package source) := by
  classical
  simp only [endToEndLeftFamilyTableSelector, dif_pos hrealizable]
  exact endToEndLeftWinningFamilyTable_wins A package source hrealizable

/-- Total right move selector. -/
noncomputable def endToEndRightFamilyMoveSelector
    (source : Bool → EndToEndRightRestartRoot A package) :
    EndToEndRightFamilyPairMove A package :=
  ⟨source, endToEndRightFamilyTableSelector A package source⟩

/-- Total left move selector. -/
noncomputable def endToEndLeftFamilyMoveSelector
    (source : Bool → EndToEndLeftRestartRoot A package) :
    EndToEndLeftFamilyPairMove A package :=
  ⟨source, endToEndLeftFamilyTableSelector A package source⟩

section
omit [Inhabited In₁] [Inhabited In₂]

@[simp] theorem endToEndRightFamilyMoveSelector_source
    (source : Bool → EndToEndRightRestartRoot A package) :
    (endToEndRightFamilyMoveSelector A package source).1 = source :=
  rfl

@[simp] theorem endToEndLeftFamilyMoveSelector_source
    (source : Bool → EndToEndLeftRestartRoot A package) :
    (endToEndLeftFamilyMoveSelector A package source).1 = source :=
  rfl

theorem endToEndRightFamilyMoveSelector_wins
    (source : Bool → EndToEndRightRestartRoot A package)
    (hrealizable : EndToEndRightFamilySourceRealizable A package source) :
    EndToEndRightFamilyRootTableWins A package source
      (endToEndRightFamilyMoveSelector A package source).2 :=
  endToEndRightFamilyTableSelector_wins A package source hrealizable

theorem endToEndLeftFamilyMoveSelector_wins
    (source : Bool → EndToEndLeftRestartRoot A package)
    (hrealizable : EndToEndLeftFamilySourceRealizable A package source) :
    EndToEndLeftFamilyRootTableWins A package source
      (endToEndLeftFamilyMoveSelector A package source).2 :=
  endToEndLeftFamilyTableSelector_wins A package source hrealizable

theorem endToEndRightFamilySourceRealizable_iff_selector_wins
    (source : Bool → EndToEndRightRestartRoot A package) :
    EndToEndRightFamilySourceRealizable A package source ↔
      EndToEndRightFamilyRootTableWins A package source
        (endToEndRightFamilyTableSelector A package source) := by
  constructor
  · exact endToEndRightFamilyTableSelector_wins A package source
  · intro hwins
    exact ⟨endToEndRightFamilyTableSelector A package source, hwins⟩

theorem endToEndLeftFamilySourceRealizable_iff_selector_wins
    (source : Bool → EndToEndLeftRestartRoot A package) :
    EndToEndLeftFamilySourceRealizable A package source ↔
      EndToEndLeftFamilyRootTableWins A package source
        (endToEndLeftFamilyTableSelector A package source) := by
  constructor
  · exact endToEndLeftFamilyTableSelector_wins A package source
  · intro hwins
    exact ⟨endToEndLeftFamilyTableSelector A package source, hwins⟩

end

end

end DetParityAutomaton

end DistributedSynthesis
