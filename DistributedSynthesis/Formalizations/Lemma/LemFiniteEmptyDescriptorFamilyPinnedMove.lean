/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyPinnedReindexing

/-!
# The pinned move of an empty descriptor family

An optional semantic lane which is inactive has no descriptor and no root.
The fixed paired alphabet nevertheless asks for a controller value on that
side.  This file constructs the unique semantically irrelevant kind of such
value directly in the fixed state-controlled table type.

There is no acceptance assumption here.  A narrowed environment for the
union monitor would have to supply a member of `Sigma Root` at time zero;
that is impossible when the descriptor type is empty.  The complete-table
law is equally vacuous because it quantifies over an empty descriptor.
-/

namespace DistributedSynthesis

universe i u v x y w

section

variable {Descriptor : Type i}
variable (Root : Descriptor → Type i)
variable {RIn : Type u} {SIn : Type v}
variable {ROut : Type x} {SOut : Type y}
variable
  (M : ∀ descriptor, Root descriptor →
    BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
variable
  (Allowed : ∀ descriptor,
    (((Root descriptor × RIn) × SIn) → ROut) → Prop)
variable
  (expected : ∀ member : Sigma Root,
    RIn × SIn → RealizedBlockRound RIn SIn ROut SOut)

variable [Fintype Descriptor] [DecidableEq Descriptor] [IsEmpty Descriptor]
variable [∀ descriptor, Fintype (Root descriptor)]
variable [∀ descriptor, DecidableEq (Root descriptor)]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] [Inhabited SOut]

/-- A certified root-pinned union move for an empty descriptor family.

The arbitrary sender/receiver label is never projected to a member, since
there is no member.  Its presence only totalizes the ambient finite move
alphabet used by the opposite active lane. -/
noncomputable def finiteEmptyDescriptorFamilyPinnedAllowedMove :
    FiniteDescriptorFamilyPinnedAllowedMove Root M Allowed expected := by
  classical
  let pinned := descriptorRootPinnedMonitor Root M expected
  let union := finiteRootFamilyMonitor
    (descriptorRootUnionMonitor Root pinned)
  let table : FiniteDescriptorFamilyAllowedTable Root pinned Allowed := {
    step := fun _ _ =>
      (((BlockRecordMonitor.threadBlockMonitor union).restrictLabels
        (NarrowedLabelAllowed union
          (DescriptorRootUnionAllowed Root Allowed))).toRunAutomaton).initial
    label := fun _ =>
      ((fun _ => (default : SOut)), fun _ _ => (default : ROut)) }
  have hthreads : NarrowedAllThreadsWin union
      table.toTransitionRationalTree.labeledTree := by
    intro env
    exact isEmptyElim (env 0).1.1.1
  have hallowed : NarrowedTablesAllowed union
      (DescriptorRootUnionAllowed Root Allowed)
      table.toTransitionRationalTree.labeledTree := by
    intro _ _ descriptor
    exact isEmptyElim descriptor
  exact ⟨table, hthreads, hallowed⟩

end

end DistributedSynthesis
