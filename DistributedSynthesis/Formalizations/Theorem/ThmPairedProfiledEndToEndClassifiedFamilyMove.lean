/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRootFamilyHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenRepresentability

/-!
# Classified labels for end-to-end restart families

The executable end-to-end family carrier currently stores tables whose
receiver label is only `ProfiledRightReceiverOutput` (or its left mirror).
That is enough to advance the restarted monitor and to construct one certified
opposite macro, but it forgets the finite successor view class needed to group
that macro with the continued shadow at the next alternating boundary.

This file records the smallest information-preserving refinement.  The
restarted monitors are merely comapped along the first projection, so their
state, transition, and priority are unchanged.  A table label additionally
advertises the already existing finite open successor root and view class.
The complete-table law checks exact target equality, membership in the
advertised class, and semantic representability of that class.

No selected member, current graph, orientation, or strict-leader bit is added.
The Boolean member remains an input of the proof-side family monitor only.
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

/-! ## The precise information erased by the old receiver alphabet -/

/-- Forget the finite right-to-left successor annotation. -/
def eraseEndToEndRightClassifiedOutput
    (output : ProfiledOpenRightClassifiedOutput A) :
    ProfiledRightReceiverOutput A :=
  output.1

/-- Forget the finite left-to-right successor annotation. -/
def eraseEndToEndLeftClassifiedOutput
    (output : ProfiledOpenLeftClassifiedOutput A) :
    ProfiledLeftReceiverOutput A :=
  output.1

/-- Whenever two annotations differ, the old right receiver alphabet cannot
recover which successor class was advertised.  This is the exact information
loss that prevents a raw winning end-to-end table from supplying a pointed
mixed-pair successor. -/
theorem eraseEndToEndRightClassifiedOutput_not_injective_of_ne
    (physical : ProfiledRightReceiverOutput A)
    (first second :
      PairedEntryRow → ProfiledOpenLeftRoot A × ProfiledOpenLeftViewClass A)
    (hne : first ≠ second) :
    ¬ Function.Injective (eraseEndToEndRightClassifiedOutput A) := by
  intro hinjective
  apply hne
  have hpair : (physical, first) = (physical, second) := hinjective rfl
  exact congrArg Prod.snd hpair

/-- Left mirror of the projection loss. -/
theorem eraseEndToEndLeftClassifiedOutput_not_injective_of_ne
    (physical : ProfiledLeftReceiverOutput A)
    (first second :
      PairedEntryRow → ProfiledOpenRightRoot A × ProfiledOpenRightViewClass A)
    (hne : first ≠ second) :
    ¬ Function.Injective (eraseEndToEndLeftClassifiedOutput A) := by
  intro hinjective
  apply hne
  have hpair : (physical, first) = (physical, second) := hinjective rfl
  exact congrArg Prod.snd hpair

/-! ## Restart monitors with classified output -/

/-- The exact restarted right monitor, with the finite successor annotation
ignored by its transition. -/
noncomputable abbrev endToEndRightClassifiedRestartRootMonitor
    (root : EndToEndRightRestartRoot A package) :=
  (endToEndRightRestartRootMonitor A package root).comapReceiverOutput
    (eraseEndToEndRightClassifiedOutput A)

/-- Left classified restarted monitor. -/
noncomputable abbrev endToEndLeftClassifiedRestartRootMonitor
    (root : EndToEndLeftRestartRoot A package) :=
  (endToEndLeftRestartRootMonitor A package root).comapReceiverOutput
    (eraseEndToEndLeftClassifiedOutput A)

noncomputable abbrev endToEndRightClassifiedFamilyRootMonitors
    (source : Bool → EndToEndRightRestartRoot A package) :=
  fun member => endToEndRightClassifiedRestartRootMonitor A package
    (source member)

noncomputable abbrev endToEndLeftClassifiedFamilyRootMonitors
    (source : Bool → EndToEndLeftRestartRoot A package) :=
  fun member => endToEndLeftClassifiedRestartRootMonitor A package
    (source member)

/-! ## Sticky finite successor law -/

/-- Every response of a right restart-family label names the exact open left
root encoded by its target, places it in one finite view class, and retains a
semantic realization of that class. -/
def EndToEndRightClassifiedTableAllowed
    (responses : (Bool × In₂) × In₁ →
      ProfiledOpenRightClassifiedOutput A) : Prop :=
  ∀ member (move : In₂ × In₁) row,
    let output := responses ((member, move.1), move.2)
    output.1.target row = .inr (.inr (output.2 row).1.1) ∧
      (output.2 row).1 ∈ (output.2 row).2.1 ∧
      (output.2 row).2.SemanticallyRepresentable A

/-- Left sticky successor law. -/
def EndToEndLeftClassifiedTableAllowed
    (responses : (Bool × In₁) × In₂ →
      ProfiledOpenLeftClassifiedOutput A) : Prop :=
  ∀ member (move : In₁ × In₂) row,
    let output := responses ((member, move.1), move.2)
    output.1.target row = .inr (.inl (output.2 row).1.1) ∧
      (output.2 row).1 ∈ (output.2 row).2.1 ∧
      (output.2 row).2.SemanticallyRepresentable A

noncomputable local instance endToEndRightClassifiedAllowedDecidable :
    DecidablePred (EndToEndRightClassifiedTableAllowed A) :=
  fun _ => Classical.propDecidable _

noncomputable local instance endToEndLeftClassifiedAllowedDecidable :
    DecidablePred (EndToEndLeftClassifiedTableAllowed A) :=
  fun _ => Classical.propDecidable _

/-- Fixed finite right-family table retaining the sticky successor law. -/
noncomputable abbrev EndToEndRightClassifiedFamilyRootTable
    (source : Bool → EndToEndRightRestartRoot A package) :=
  LocallyConsistentNarrowedTable
    (finiteRootFamilyMonitor
      (endToEndRightClassifiedFamilyRootMonitors A package source))
    (EndToEndRightClassifiedTableAllowed A)

/-- Fixed finite left-family table retaining the sticky successor law. -/
noncomputable abbrev EndToEndLeftClassifiedFamilyRootTable
    (source : Bool → EndToEndLeftRestartRoot A package) :=
  LocallyConsistentNarrowedTable
    (finiteRootFamilyMonitor
      (endToEndLeftClassifiedFamilyRootMonitors A package source))
    (EndToEndLeftClassifiedTableAllowed A)

noncomputable instance
    (source : Bool → EndToEndRightRestartRoot A package) :
    Fintype (EndToEndRightClassifiedFamilyRootTable A package source) := by
  classical
  infer_instance

noncomputable instance
    (source : Bool → EndToEndLeftRestartRoot A package) :
    Fintype (EndToEndLeftClassifiedFamilyRootTable A package source) := by
  classical
  infer_instance

/-! ## Readback on the genuine family thread -/

noncomputable def endToEndRightClassifiedOutputAt
    (source : Bool → EndToEndRightRestartRoot A package)
    (table : EndToEndRightClassifiedFamilyRootTable A package source)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat) :
    ProfiledOpenRightClassifiedOutput A :=
  (treePlay
    (narrowedInducedTree
      (finiteRootFamilyMonitor
        (endToEndRightClassifiedFamilyRootMonitors A package source))
      table.toTransitionRationalTree.labeledTree)
    (tagFiniteRootEnvironment member env) n).2.1

noncomputable def endToEndLeftClassifiedOutputAt
    (source : Bool → EndToEndLeftRestartRoot A package)
    (table : EndToEndLeftClassifiedFamilyRootTable A package source)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat) :
    ProfiledOpenLeftClassifiedOutput A :=
  (treePlay
    (narrowedInducedTree
      (finiteRootFamilyMonitor
        (endToEndLeftClassifiedFamilyRootMonitors A package source))
      table.toTransitionRationalTree.labeledTree)
    (tagFiniteRootEnvironment member env) n).2.1

/-- The refined right label exposes exactly the three facts required by the
next mixed-pair construction. -/
theorem endToEndRightClassifiedOutputAt_spec
    (source : Bool → EndToEndRightRestartRoot A package)
    (table : EndToEndRightClassifiedFamilyRootTable A package source)
    (hallowed : NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (endToEndRightClassifiedFamilyRootMonitors A package source))
      (EndToEndRightClassifiedTableAllowed A)
      table.toTransitionRationalTree.labeledTree)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let output := endToEndRightClassifiedOutputAt A package source table member
      env n
    output.1.target row = .inr (.inr (output.2 row).1.1) ∧
      (output.2 row).1 ∈ (output.2 row).2.1 ∧
      (output.2 row).2.SemanticallyRepresentable A := by
  let fullEnv := tagFiniteRootEnvironment member env
  let node := branchNode fullEnv n
  have hall := narrowedInducedTree_receiver_allowed
    (finiteRootFamilyMonitor
      (endToEndRightClassifiedFamilyRootMonitors A package source))
    (EndToEndRightClassifiedTableAllowed A)
    table.toTransitionRationalTree.labeledTree hallowed node
  have hentry := hall member (env n) row
  simpa [endToEndRightClassifiedOutputAt, fullEnv, node, treePlay,
    blockLabelApply] using hentry

/-- Left refined-label specification. -/
theorem endToEndLeftClassifiedOutputAt_spec
    (source : Bool → EndToEndLeftRestartRoot A package)
    (table : EndToEndLeftClassifiedFamilyRootTable A package source)
    (hallowed : NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (endToEndLeftClassifiedFamilyRootMonitors A package source))
      (EndToEndLeftClassifiedTableAllowed A)
      table.toTransitionRationalTree.labeledTree)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let output := endToEndLeftClassifiedOutputAt A package source table member
      env n
    output.1.target row = .inr (.inl (output.2 row).1.1) ∧
      (output.2 row).1 ∈ (output.2 row).2.1 ∧
      (output.2 row).2.SemanticallyRepresentable A := by
  let fullEnv := tagFiniteRootEnvironment member env
  let node := branchNode fullEnv n
  have hall := narrowedInducedTree_receiver_allowed
    (finiteRootFamilyMonitor
      (endToEndLeftClassifiedFamilyRootMonitors A package source))
    (EndToEndLeftClassifiedTableAllowed A)
    table.toTransitionRationalTree.labeledTree hallowed node
  have hentry := hall member (env n) row
  simpa [endToEndLeftClassifiedOutputAt, fullEnv, node, treePlay,
    blockLabelApply] using hentry

end

end DetParityAutomaton

end DistributedSynthesis
