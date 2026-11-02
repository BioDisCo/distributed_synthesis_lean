/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemTwoSortedFamilyRun
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenClassifiedHandoff

/-!
# Two-sorted outer automaton for classified open moves

The family state is now the complete canonical information class of the
currently blind process.  A valid finite table sends each actual root and
environment direction to an actual opposite-orientation child together with
the whole next information class.  No process receives the proof-side root.
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

/-- Finite objective descriptor of a classified open family. -/
inductive ProfiledOpenClassifiedAnchor where
  | sink
  | right (root : ProfiledOpenRightRoot A)
  | left (root : ProfiledOpenLeftRoot A)

noncomputable instance : Fintype (ProfiledOpenClassifiedAnchor A) := by
  classical
  let Rep := Unit ⊕ ProfiledOpenRightRoot A ⊕ ProfiledOpenLeftRoot A
  let e : ProfiledOpenClassifiedAnchor A ≃ Rep :=
    { toFun := fun anchor =>
        match anchor with
        | .sink => .inl ()
        | .right root => .inr (.inl root)
        | .left root => .inr (.inr root)
      invFun := fun anchor =>
        match anchor with
        | .inl _ => .sink
        | .inr (.inl root) => .right root
        | .inr (.inr root) => .left root
      left_inv := by intro anchor; cases anchor <;> rfl
      right_inv := by
        intro anchor
        rcases anchor with empty | (right | left)
        · cases empty; rfl
        · rfl
        · rfl }
  exact Fintype.ofEquiv Rep e.symm

noncomputable instance : DecidableEq (ProfiledOpenClassifiedAnchor A) :=
  Classical.decEq _

instance : Inhabited (ProfiledOpenClassifiedAnchor A) := ⟨.sink⟩

/-- Epoch priority stored in an open root. -/
def profiledOpenClassifiedAnchorPriority :
    ProfiledOpenClassifiedAnchor A → Nat
  | .sink => 0
  | .right root => pairedProfiledEntryPriority A (.inr (.inl root.1))
  | .left root => pairedProfiledEntryPriority A (.inr (.inr root.1))

/-- Proof-side environment directions include the actual current root.  This
root selects a receiver table entry; it is not part of either process's local
observation. -/
inductive ProfiledOpenClassifiedDirection where
  | fromOne (root : ProfiledOpenRightRoot A) (row : PairedEntryRow)
      (past : List (In₂ × In₁)) (input : In₂ × In₁)
  | fromTwo (root : ProfiledOpenLeftRoot A) (row : PairedEntryRow)
      (past : List (In₁ × In₂)) (input : In₁ × In₂)

/-- Literal finite right classified move. -/
abbrev ProfiledOpenRightClassifiedMove :=
  Sigma fun source : ProfiledOpenRightViewClass A =>
    ProfiledOpenRightClassifiedTable.{u, v, x, y, s, 0} A source

/-- Literal finite left classified move. -/
abbrev ProfiledOpenLeftClassifiedMove :=
  Sigma fun source : ProfiledOpenLeftViewClass A =>
    ProfiledOpenLeftClassifiedTable.{u, v, x, y, s, 0} A source

noncomputable instance : Fintype (ProfiledOpenRightClassifiedMove A) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledOpenLeftClassifiedMove A) := by
  classical
  infer_instance

/-- Complete finite move alphabet of the classified outer automaton.  An
inductive wrapper fixes the universes of the two dependent Sigma tables and
keeps later pattern matching definitionally transparent. -/
inductive ProfiledOpenClassifiedMove where
  | sink
  | right (source : ProfiledOpenRightViewClass A)
      (table : ProfiledOpenRightClassifiedTable.{u, v, x, y, s, 0} A source)
  | left (source : ProfiledOpenLeftViewClass A)
      (table : ProfiledOpenLeftClassifiedTable.{u, v, x, y, s, 0} A source)

noncomputable instance : Fintype (ProfiledOpenClassifiedMove A) := by
  classical
  let Rep := Unit ⊕ (ProfiledOpenRightClassifiedMove A ⊕
    ProfiledOpenLeftClassifiedMove A)
  let e : ProfiledOpenClassifiedMove A ≃ Rep :=
    { toFun := fun move =>
        match move with
        | .sink => .inl ()
        | .right source table => .inr (.inl ⟨source, table⟩)
        | .left source table => .inr (.inr ⟨source, table⟩)
      invFun := fun move =>
        match move with
        | .inl _ => .sink
        | .inr (.inl right) => .right right.1 right.2
        | .inr (.inr left) => .left left.1 left.2
      left_inv := by intro move; cases move <;> rfl
      right_inv := by
        intro move
        rcases move with empty | (right | left)
        · cases empty; rfl
        · rcases right with ⟨source, table⟩; rfl
        · rcases left with ⟨source, table⟩; rfl }
  exact Fintype.ofEquiv Rep e.symm

/-- Validity contains both the universal-thread parity certificate and the
complete successor-class table law. -/
def ProfiledOpenClassifiedMove.Valid : ProfiledOpenClassifiedMove A → Prop
  | .sink => True
  | .right source table =>
      NarrowedAllThreadsWin
          (finiteRootFamilyMonitor
            (fun member : {root // root ∈ source.1} =>
              profiledOpenRightClassifiedRootMonitor A member.1))
          table.toTransitionRationalTree.labeledTree ∧
        NarrowedTablesAllowed
          (finiteRootFamilyMonitor
            (fun member : {root // root ∈ source.1} =>
              profiledOpenRightClassifiedRootMonitor A member.1))
          (ProfiledOpenRightClassifiedTableAllowed A source)
          table.toTransitionRationalTree.labeledTree
  | .left source table =>
      NarrowedAllThreadsWin
          (finiteRootFamilyMonitor
            (fun member : {root // root ∈ source.1} =>
              profiledOpenLeftClassifiedRootMonitor A member.1))
          table.toTransitionRationalTree.labeledTree ∧
        NarrowedTablesAllowed
          (finiteRootFamilyMonitor
            (fun member : {root // root ∈ source.1} =>
              profiledOpenLeftClassifiedRootMonitor A member.1))
          (ProfiledOpenLeftClassifiedTableAllowed A source)
          table.toTransitionRationalTree.labeledTree

/-- Family represented by a move. -/
noncomputable def ProfiledOpenClassifiedMove.roots :
    ProfiledOpenClassifiedMove A → Finset (ProfiledOpenClassifiedAnchor A)
  | .sink => {.sink}
  | .right source _ => source.1.image ProfiledOpenClassifiedAnchor.right
  | .left source _ => source.1.image ProfiledOpenClassifiedAnchor.left

/-- Embed a canonical right class as an outer descriptor family. -/
noncomputable def profiledOpenRightClassifiedRoots
    (source : ProfiledOpenRightViewClass A) :
    Finset (ProfiledOpenClassifiedAnchor A) :=
  source.1.image ProfiledOpenClassifiedAnchor.right

/-- Embed a canonical left class as an outer descriptor family. -/
noncomputable def profiledOpenLeftClassifiedRoots
    (source : ProfiledOpenLeftViewClass A) :
    Finset (ProfiledOpenClassifiedAnchor A) :=
  source.1.image ProfiledOpenClassifiedAnchor.left

/-- Successor assignment of one valid finite classified move. -/
noncomputable def ProfiledOpenClassifiedMove.successor
    (move : ProfiledOpenClassifiedMove A) :
    TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
      (ProfiledOpenClassifiedDirection A) := by
  classical
  cases move with
  | sink => exact fun _ => (.sink, {.sink})
  | right source table =>
      by_cases hvalid :
          ProfiledOpenClassifiedMove.Valid A (.right source table)
      · exact fun direction =>
          match direction with
          | .fromOne root row past input =>
              if hmem : root ∈ source.1 then
                let member : {root // root ∈ source.1} := ⟨root, hmem⟩
                let child := profiledOpenRightClassifiedChild A source table
                  member (omegaOfList (past ++ [input])) past.length row
                (.left child.1, profiledOpenLeftClassifiedRoots A child.2)
              else (.sink, {.sink})
          | .fromTwo _ _ _ _ => (.sink, {.sink})
      · exact fun _ => (.sink, {.sink})
  | left source table =>
      by_cases hvalid :
          ProfiledOpenClassifiedMove.Valid A (.left source table)
      · exact fun direction =>
          match direction with
          | .fromTwo root row past input =>
              if hmem : root ∈ source.1 then
                let member : {root // root ∈ source.1} := ⟨root, hmem⟩
                let child := profiledOpenLeftClassifiedChild A source table
                  member (omegaOfList (past ++ [input])) past.length row
                (.right child.1, profiledOpenRightClassifiedRoots A child.2)
              else (.sink, {.sink})
          | .fromOne _ _ _ _ => (.sink, {.sink})
      · exact fun _ => (.sink, {.sink})

/-- Concrete transition law for the generic two-sorted run automaton. -/
def ProfiledOpenClassifiedFamilyAllowed
    (roots : Finset (ProfiledOpenClassifiedAnchor A))
    (next : TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
      (ProfiledOpenClassifiedDirection A)) : Prop :=
  ∃ move : ProfiledOpenClassifiedMove A,
    move.Valid A ∧ move.roots A = roots ∧ move.successor A = next

/-- Fully finite-state classified outer run automaton. -/
noncomputable abbrev profiledOpenClassifiedFamilyRunAutomaton
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A)) :=
  twoSortedFamilyRunAutomaton (profiledOpenClassifiedAnchorPriority A)
    initialRoots (ProfiledOpenClassifiedFamilyAllowed A)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Any finite semantic process-one view class supplies a valid right move of
the concrete classified outer automaton. -/
theorem exists_valid_profiledOpenRightClassifiedMove_of_winning_family
    {I : Type*} [Inhabited I] [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (minimum : I → A.State) (pivot : I)
    (hview : ∀ index,
      currentView Proc.one (entry index).leftHistory =
        currentView Proc.one (entry pivot).leftHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ∃ move : ProfiledOpenClassifiedMove A,
      move.Valid A ∧
        ∃ source : ProfiledOpenRightViewClass A,
          move.roots A = profiledOpenRightClassifiedRoots A source := by
  obtain ⟨source, table, hthreads, hallowed⟩ :=
    exists_profiledOpenRightClassifiedTable_of_winning_family A strategy hwin
      entry minimum pivot hview basis
  refine ⟨.right source table, ⟨hthreads, hallowed⟩, source, ?_⟩
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two/left mirror. -/
theorem exists_valid_profiledOpenLeftClassifiedMove_of_winning_family
    {I : Type*} [Inhabited I] [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (minimum : I → A.State) (pivot : I)
    (hview : ∀ index,
      currentView Proc.two (entry index).rightHistory =
        currentView Proc.two (entry pivot).rightHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ∃ move : ProfiledOpenClassifiedMove A,
      move.Valid A ∧
        ∃ source : ProfiledOpenLeftViewClass A,
          move.roots A = profiledOpenLeftClassifiedRoots A source := by
  obtain ⟨source, table, hthreads, hallowed⟩ :=
    exists_profiledOpenLeftClassifiedTable_of_winning_family A strategy hwin
      entry minimum pivot hview basis
  refine ⟨.left source table, ⟨hthreads, hallowed⟩, source, ?_⟩
  rfl

end

end


end DetParityAutomaton

end DistributedSynthesis
