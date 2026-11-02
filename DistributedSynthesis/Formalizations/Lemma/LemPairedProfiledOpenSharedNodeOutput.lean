/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenBiBeliefRealization

/-!
# One shared family-controller node

These operations query every possible current family member in the complete
receiver-response table at one fixed full family-tree node.  Hence the
current member is an argument to one table; it does not select a different
narrowed monitor state.  The indexed belief node uses this distinction to
keep correlated shadows on one semantic block prefix.
-/

namespace DistributedSynthesis

universe u v x y s

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

/-- Shared-node output of a strengthened right table. -/
noncomputable def profiledOpenRightSharedNodeOutput
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightRepresentableTable A source)
    (node : List ((({root // root ∈ source.1} × In₂) × In₁)))
    (member : {root // root ∈ source.1}) (input : In₂ × In₁) :
    ProfiledOpenRightClassifiedOutput A :=
  (narrowedInducedTree
      (finiteRootFamilyMonitor
        (fun candidate : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A candidate.1))
      table.toTransitionRationalTree.labeledTree node).1
    ((member, input.1), input.2)

/-- Shared-node output of a strengthened left table. -/
noncomputable def profiledOpenLeftSharedNodeOutput
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftRepresentableTable A source)
    (node : List ((({root // root ∈ source.1} × In₁) × In₂)))
    (member : {root // root ∈ source.1}) (input : In₁ × In₂) :
    ProfiledOpenLeftClassifiedOutput A :=
  (narrowedInducedTree
      (finiteRootFamilyMonitor
        (fun candidate : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A candidate.1))
      table.toTransitionRationalTree.labeledTree node).1
    ((member, input.1), input.2)

/-- Shared-node operation on the weakened right classified table used by the
finite public move. -/
noncomputable def profiledOpenRightClassifiedSharedNodeOutput
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (node : List ((({root // root ∈ source.1} × In₂) × In₁)))
    (member : {root // root ∈ source.1}) (input : In₂ × In₁) :
    ProfiledOpenRightClassifiedOutput A :=
  (narrowedInducedTree
      (finiteRootFamilyMonitor
        (fun candidate : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A candidate.1))
      table.toTransitionRationalTree.labeledTree node).1
    ((member, input.1), input.2)

/-- Shared-node operation on a left classified table. -/
noncomputable def profiledOpenLeftClassifiedSharedNodeOutput
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (node : List ((({root // root ∈ source.1} × In₁) × In₂)))
    (member : {root // root ∈ source.1}) (input : In₁ × In₂) :
    ProfiledOpenLeftClassifiedOutput A :=
  (narrowedInducedTree
      (finiteRootFamilyMonitor
        (fun candidate : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A candidate.1))
      table.toTransitionRationalTree.labeledTree node).1
    ((member, input.1), input.2)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Weakening a representable right table changes no shared-node output. -/
@[simp] theorem profiledOpenRightClassifiedSharedNodeOutput_toClassified
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightRepresentableTable A source)
    (node : List ((({root // root ∈ source.1} × In₂) × In₁)))
    (member : {root // root ∈ source.1}) (input : In₂ × In₁) :
    profiledOpenRightClassifiedSharedNodeOutput A source
        (table.toClassified A source) node member input =
      profiledOpenRightSharedNodeOutput A source table node member input := by
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left weakening mirror. -/
@[simp] theorem profiledOpenLeftClassifiedSharedNodeOutput_toClassified
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftRepresentableTable A source)
    (node : List ((({root // root ∈ source.1} × In₁) × In₂)))
    (member : {root // root ∈ source.1}) (input : In₁ × In₂) :
    profiledOpenLeftClassifiedSharedNodeOutput A source
        (table.toClassified A source) node member input =
      profiledOpenLeftSharedNodeOutput A source table node member input := by
  rfl

end


end DetParityAutomaton

end DistributedSynthesis
