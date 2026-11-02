/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenViewClassHandoff

/-!
# Canonical finite moves for profiled view classes

Semantic view classes are indexed by concrete histories.  The outer
input-free automaton cannot retain those histories.  This file collapses a
compatible semantic family to the finite set of its open-root descriptors,
choosing one semantic representative for each descriptor.  Compatibility is
preserved by reindexing, so the result is a literal finite move alphabet.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- A canonical right view class is a nonempty finite set of open roots whose
root-indexed family admits one common blind sender. -/
def ProfiledOpenRightViewClass :=
  { roots : Finset (ProfiledOpenRightRoot A) //
    roots.Nonempty ∧
      ProfiledOpenRightFamilyCompatible.{max s u v y, u, v, x, y, s, 0} A
        (fun member : {root // root ∈ roots} => member.1) }

/-- Left-oriented canonical view class. -/
def ProfiledOpenLeftViewClass :=
  { roots : Finset (ProfiledOpenLeftRoot A) //
    roots.Nonempty ∧
      ProfiledOpenLeftFamilyCompatible.{max s u v x, u, v, x, y, s, 0} A
        (fun member : {root // root ∈ roots} => member.1) }

noncomputable instance : Fintype (ProfiledOpenRightViewClass A) := by
  classical
  unfold ProfiledOpenRightViewClass
  infer_instance

noncomputable instance : Fintype (ProfiledOpenLeftViewClass A) := by
  classical
  unfold ProfiledOpenLeftViewClass
  infer_instance

/-- Finite descriptor image of an indexed right family. -/
noncomputable def profiledOpenRightRootImage
    [Fintype I] (source : I → ProfiledOpenRightRoot A) :
    Finset (ProfiledOpenRightRoot A) := by
  classical
  exact Finset.univ.image source

/-- Finite descriptor image of an indexed left family. -/
noncomputable def profiledOpenLeftRootImage
    [Fintype I] (source : I → ProfiledOpenLeftRoot A) :
    Finset (ProfiledOpenLeftRoot A) := by
  classical
  exact Finset.univ.image source

/-- Choose a semantic representative of a descriptor in the right image. -/
noncomputable def profiledOpenRightRootRepresentative
    [Fintype I] (source : I → ProfiledOpenRightRoot A)
    (member : {root // root ∈ profiledOpenRightRootImage A source}) : I := by
  classical
  exact (Finset.mem_image.mp member.2).choose

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
theorem profiledOpenRightRootRepresentative_spec
    [Fintype I] (source : I → ProfiledOpenRightRoot A)
    (member : {root // root ∈ profiledOpenRightRootImage A source}) :
    source (profiledOpenRightRootRepresentative A source member) = member.1 := by
  classical
  exact (Finset.mem_image.mp member.2).choose_spec.2

/-- Left representative. -/
noncomputable def profiledOpenLeftRootRepresentative
    [Fintype I] (source : I → ProfiledOpenLeftRoot A)
    (member : {root // root ∈ profiledOpenLeftRootImage A source}) : I := by
  classical
  exact (Finset.mem_image.mp member.2).choose

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
theorem profiledOpenLeftRootRepresentative_spec
    [Fintype I] (source : I → ProfiledOpenLeftRoot A)
    (member : {root // root ∈ profiledOpenLeftRootImage A source}) :
    source (profiledOpenLeftRootRepresentative A source member) = member.1 := by
  classical
  exact (Finset.mem_image.mp member.2).choose_spec.2

/-- Collapse a nonempty compatible indexed right family to its canonical
finite root set. -/
noncomputable def profiledOpenRightViewClassOfCompatible
    [Inhabited I] [Fintype I]
    (source : I → ProfiledOpenRightRoot A)
    (hcompatible : ProfiledOpenRightFamilyCompatible.{i, u, v, x, y, s, 0}
      A source) :
    ProfiledOpenRightViewClass A := by
  classical
  let roots := profiledOpenRightRootImage A source
  have hnonempty : roots.Nonempty := by
    refine ⟨source default, ?_⟩
    simp [roots, profiledOpenRightRootImage]
  have hreindexed := ProfiledOpenRightFamilyCompatible.reindex A hcompatible
    (profiledOpenRightRootRepresentative A source)
  have hcanonical :
      ProfiledOpenRightFamilyCompatible.{max s u v y, u, v, x, y, s, 0} A
      (fun member : {root // root ∈ roots} => member.1) := by
    convert hreindexed using 1
    funext member
    exact (profiledOpenRightRootRepresentative_spec A source member).symm
  exact ⟨roots, hnonempty, hcanonical⟩

/-- Left collapse. -/
noncomputable def profiledOpenLeftViewClassOfCompatible
    [Inhabited I] [Fintype I]
    (source : I → ProfiledOpenLeftRoot A)
    (hcompatible : ProfiledOpenLeftFamilyCompatible.{i, u, v, x, y, s, 0}
      A source) :
    ProfiledOpenLeftViewClass A := by
  classical
  let roots := profiledOpenLeftRootImage A source
  have hnonempty : roots.Nonempty := by
    refine ⟨source default, ?_⟩
    simp [roots, profiledOpenLeftRootImage]
  have hreindexed := ProfiledOpenLeftFamilyCompatible.reindex A hcompatible
    (profiledOpenLeftRootRepresentative A source)
  have hcanonical :
      ProfiledOpenLeftFamilyCompatible.{max s u v x, u, v, x, y, s, 0} A
      (fun member : {root // root ∈ roots} => member.1) := by
    convert hreindexed using 1
    funext member
    exact (profiledOpenLeftRootRepresentative_spec A source member).symm
  exact ⟨roots, hnonempty, hcanonical⟩

noncomputable instance ProfiledOpenRightViewClass.memberDecidableEq
    (viewClass : ProfiledOpenRightViewClass A) :
    DecidableEq {root // root ∈ viewClass.1} := Classical.decEq _

noncomputable instance ProfiledOpenLeftViewClass.memberDecidableEq
    (viewClass : ProfiledOpenLeftViewClass A) :
    DecidableEq {root // root ∈ viewClass.1} := Classical.decEq _

/-- Every canonical right class has a canonical finite simultaneous table. -/
noncomputable def ProfiledOpenRightViewClass.table
    (viewClass : ProfiledOpenRightViewClass A) :
    FiniteRootFamilyTable (fun member : {root // root ∈ viewClass.1} =>
      profiledOpenRightRootMonitor A member.1) := by
  letI : Inhabited {root // root ∈ viewClass.1} :=
    ⟨⟨viewClass.2.1.choose, viewClass.2.1.choose_spec⟩⟩
  letI : DecidableEq {root // root ∈ viewClass.1} := Classical.decEq _
  exact profiledOpenRightFamilyTableOfCompatible A
    (fun member : {root // root ∈ viewClass.1} => member.1) viewClass.2.2

theorem ProfiledOpenRightViewClass.table_wins
    (viewClass : ProfiledOpenRightViewClass A) :
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ viewClass.1} =>
          profiledOpenRightRootMonitor A member.1))
      viewClass.table.toTransitionRationalTree.labeledTree := by
  letI : Inhabited {root // root ∈ viewClass.1} :=
    ⟨⟨viewClass.2.1.choose, viewClass.2.1.choose_spec⟩⟩
  letI : DecidableEq {root // root ∈ viewClass.1} := Classical.decEq _
  exact profiledOpenRightFamilyTableOfCompatible_wins A
    (fun member : {root // root ∈ viewClass.1} => member.1) viewClass.2.2

/-- Left canonical table and certificate. -/
noncomputable def ProfiledOpenLeftViewClass.table
    (viewClass : ProfiledOpenLeftViewClass A) :
    FiniteRootFamilyTable (fun member : {root // root ∈ viewClass.1} =>
      profiledOpenLeftRootMonitor A member.1) := by
  letI : Inhabited {root // root ∈ viewClass.1} :=
    ⟨⟨viewClass.2.1.choose, viewClass.2.1.choose_spec⟩⟩
  letI : DecidableEq {root // root ∈ viewClass.1} := Classical.decEq _
  exact profiledOpenLeftFamilyTableOfCompatible A
    (fun member : {root // root ∈ viewClass.1} => member.1) viewClass.2.2

theorem ProfiledOpenLeftViewClass.table_wins
    (viewClass : ProfiledOpenLeftViewClass A) :
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ viewClass.1} =>
          profiledOpenLeftRootMonitor A member.1))
      viewClass.table.toTransitionRationalTree.labeledTree := by
  letI : Inhabited {root // root ∈ viewClass.1} :=
    ⟨⟨viewClass.2.1.choose, viewClass.2.1.choose_spec⟩⟩
  letI : DecidableEq {root // root ∈ viewClass.1} := Classical.decEq _
  exact profiledOpenLeftFamilyTableOfCompatible_wins A
    (fun member : {root // root ∈ viewClass.1} => member.1) viewClass.2.2

/-- Literal finite right move alphabet: a canonical information class and one
simultaneous table for all roots in that class. -/
abbrev ProfiledOpenRightViewClassMove :=
  Sigma fun viewClass : ProfiledOpenRightViewClass A =>
    FiniteRootFamilyTable
      (fun member : {root // root ∈ viewClass.1} =>
        profiledOpenRightRootMonitor A member.1)

/-- Left-oriented finite move alphabet. -/
abbrev ProfiledOpenLeftViewClassMove :=
  Sigma fun viewClass : ProfiledOpenLeftViewClass A =>
    FiniteRootFamilyTable
      (fun member : {root // root ∈ viewClass.1} =>
        profiledOpenLeftRootMonitor A member.1)

noncomputable instance : Fintype (ProfiledOpenRightViewClassMove A) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledOpenLeftViewClassMove A) := by
  classical
  infer_instance

/-- Validity of a right class move is the existing simultaneous all-thread
certificate for its selected table. -/
def ProfiledOpenRightViewClassMove.Valid
    (move : ProfiledOpenRightViewClassMove A) : Prop :=
  NarrowedAllThreadsWin
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ move.1.1} =>
        profiledOpenRightRootMonitor A member.1))
    move.2.toTransitionRationalTree.labeledTree

def ProfiledOpenLeftViewClassMove.Valid
    (move : ProfiledOpenLeftViewClassMove A) : Prop :=
  NarrowedAllThreadsWin
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ move.1.1} =>
        profiledOpenLeftRootMonitor A member.1))
    move.2.toTransitionRationalTree.labeledTree

/-- Every canonical right information class contributes a valid move. -/
noncomputable def ProfiledOpenRightViewClass.toMove
    (viewClass : ProfiledOpenRightViewClass A) :
    ProfiledOpenRightViewClassMove A := ⟨viewClass, viewClass.table⟩

theorem ProfiledOpenRightViewClass.toMove_valid
    (viewClass : ProfiledOpenRightViewClass A) :
    viewClass.toMove.Valid := viewClass.table_wins

noncomputable def ProfiledOpenLeftViewClass.toMove
    (viewClass : ProfiledOpenLeftViewClass A) :
    ProfiledOpenLeftViewClassMove A := ⟨viewClass, viewClass.table⟩

theorem ProfiledOpenLeftViewClass.toMove_valid
    (viewClass : ProfiledOpenLeftViewClass A) :
    viewClass.toMove.Valid := viewClass.table_wins

end

end


end DetParityAutomaton

end DistributedSynthesis
