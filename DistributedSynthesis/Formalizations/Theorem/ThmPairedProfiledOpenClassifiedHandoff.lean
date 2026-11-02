/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenClassifiedRealization

/-!
# Readback of classified finite-table successors

This file reads the successor annotation from the actual induced receiver
play of a fixed classified table.  The monitor state is the coherent thread
state reached by the full history; no artificial restart state is selected.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Full induced tree of a fixed right classified table. -/
noncomputable def profiledOpenRightClassifiedInducedTree
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source) :=
  narrowedInducedTree
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenRightClassifiedRootMonitor A member.1))
    table.toTransitionRationalTree.labeledTree

/-- Actual classified output on one constant-member physical environment. -/
noncomputable def profiledOpenRightClassifiedOutputAt
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (member : {root // root ∈ source.1})
    (env : Nat → In₂ × In₁) (n : Nat) :
    ProfiledOpenRightClassifiedOutput A :=
  (treePlay (profiledOpenRightClassifiedInducedTree A source table)
    (tagFiniteRootEnvironment member env) n).2.1

/-- Opposite-orientation root and complete new blind-view class advertised by
the coherent induced play. -/
noncomputable def profiledOpenRightClassifiedChild
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (member : {root // root ∈ source.1})
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    ProfiledOpenLeftRoot A × ProfiledOpenLeftViewClass A :=
  (profiledOpenRightClassifiedOutputAt A source table member env n).2 row

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Inhabited In₁] in
theorem profiledOpenRightClassifiedChild_spec
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (hallowed : NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A member.1))
      (ProfiledOpenRightClassifiedTableAllowed A source)
      table.toTransitionRationalTree.labeledTree)
    (member : {root // root ∈ source.1})
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let child := profiledOpenRightClassifiedChild A source table member env n row
    (profiledOpenRightClassifiedOutputAt A source table member env n).1.target row =
        .inr (.inr child.1.1) ∧ child.1 ∈ child.2.1 := by
  let fullEnv := tagFiniteRootEnvironment member env
  let node := branchNode fullEnv n
  have hall := narrowedInducedTree_receiver_allowed
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenRightClassifiedRootMonitor A member.1))
    (ProfiledOpenRightClassifiedTableAllowed A source)
    table.toTransitionRationalTree.labeledTree hallowed node
  have hentry := hall member (env n) row
  simpa [profiledOpenRightClassifiedChild,
    profiledOpenRightClassifiedOutputAt,
    profiledOpenRightClassifiedInducedTree, fullEnv, node,
    treePlay, blockLabelApply] using hentry

/-! ## Left mirror -/

noncomputable def profiledOpenLeftClassifiedInducedTree
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source) :=
  narrowedInducedTree
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenLeftClassifiedRootMonitor A member.1))
    table.toTransitionRationalTree.labeledTree

noncomputable def profiledOpenLeftClassifiedOutputAt
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (member : {root // root ∈ source.1})
    (env : Nat → In₁ × In₂) (n : Nat) :
    ProfiledOpenLeftClassifiedOutput A :=
  (treePlay (profiledOpenLeftClassifiedInducedTree A source table)
    (tagFiniteRootEnvironment member env) n).2.1

noncomputable def profiledOpenLeftClassifiedChild
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (member : {root // root ∈ source.1})
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    ProfiledOpenRightRoot A × ProfiledOpenRightViewClass A :=
  (profiledOpenLeftClassifiedOutputAt A source table member env n).2 row

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Inhabited In₂] in
theorem profiledOpenLeftClassifiedChild_spec
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (hallowed : NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A member.1))
      (ProfiledOpenLeftClassifiedTableAllowed A source)
      table.toTransitionRationalTree.labeledTree)
    (member : {root // root ∈ source.1})
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let child := profiledOpenLeftClassifiedChild A source table member env n row
    (profiledOpenLeftClassifiedOutputAt A source table member env n).1.target row =
        .inr (.inl child.1.1) ∧ child.1 ∈ child.2.1 := by
  let fullEnv := tagFiniteRootEnvironment member env
  let node := branchNode fullEnv n
  have hall := narrowedInducedTree_receiver_allowed
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenLeftClassifiedRootMonitor A member.1))
    (ProfiledOpenLeftClassifiedTableAllowed A source)
    table.toTransitionRationalTree.labeledTree hallowed node
  have hentry := hall member (env n) row
  simpa [profiledOpenLeftClassifiedChild,
    profiledOpenLeftClassifiedOutputAt,
    profiledOpenLeftClassifiedInducedTree, fullEnv, node,
    treePlay, blockLabelApply] using hentry

end

end


end DetParityAutomaton

end DistributedSynthesis
