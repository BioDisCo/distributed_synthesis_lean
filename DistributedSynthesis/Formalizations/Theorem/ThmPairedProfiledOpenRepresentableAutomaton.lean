/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenRepresentability

/-!
# Productive classified outer automaton

This is the corrected finite outer interface.  Its tables preserve semantic
representability of every advertised successor class as a sticky label law.
Consequently every reachable successor family supplies its next move without
a recursive quotient or a hidden strict-leader signal.
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

abbrev ProfiledOpenRightRepresentableMove :=
  Sigma fun source : ProfiledOpenRightViewClass A =>
    ProfiledOpenRightRepresentableTable.{u, v, x, y, s, 0} A source

abbrev ProfiledOpenLeftRepresentableMove :=
  Sigma fun source : ProfiledOpenLeftViewClass A =>
    ProfiledOpenLeftRepresentableTable.{u, v, x, y, s, 0} A source

noncomputable instance : Fintype (ProfiledOpenRightRepresentableMove A) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledOpenLeftRepresentableMove A) := by
  classical
  infer_instance

/-- Finite productive move alphabet. -/
inductive ProfiledOpenRepresentableMove where
  | sink
  | right (source : ProfiledOpenRightViewClass A)
      (table : ProfiledOpenRightRepresentableTable.{u, v, x, y, s, 0} A source)
  | left (source : ProfiledOpenLeftViewClass A)
      (table : ProfiledOpenLeftRepresentableTable.{u, v, x, y, s, 0} A source)

noncomputable instance : Fintype (ProfiledOpenRepresentableMove A) := by
  classical
  let Rep := Unit ⊕ (ProfiledOpenRightRepresentableMove A ⊕
    ProfiledOpenLeftRepresentableMove A)
  let e : ProfiledOpenRepresentableMove A ≃ Rep :=
    { toFun := fun move =>
        match move with
        | .sink => .inl ()
        | .right source table => .inr (.inl ⟨source, table⟩)
        | .left source table => .inr (.inr ⟨source, table⟩)
      invFun := fun move =>
        match move with
        | .inl _ => .sink
        | .inr (.inl move) => .right move.1 move.2
        | .inr (.inr move) => .left move.1 move.2
      left_inv := by intro move; cases move <;> rfl
      right_inv := by
        intro move
        rcases move with empty | (right | left)
        · cases empty; rfl
        · rcases right with ⟨source, table⟩; rfl
        · rcases left with ⟨source, table⟩; rfl }
  exact Fintype.ofEquiv Rep e.symm

/-- A valid move contains the parity certificate and the strengthened sticky
table law. -/
def ProfiledOpenRepresentableMove.Valid :
    ProfiledOpenRepresentableMove A → Prop
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
          (ProfiledOpenRightRepresentableTableAllowed A source)
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
          (ProfiledOpenLeftRepresentableTableAllowed A source)
          table.toTransitionRationalTree.labeledTree

noncomputable def ProfiledOpenRepresentableMove.roots :
    ProfiledOpenRepresentableMove A →
      Finset (ProfiledOpenClassifiedAnchor A)
  | .sink => {.sink}
  | .right source _ => profiledOpenRightClassifiedRoots A source
  | .left source _ => profiledOpenLeftClassifiedRoots A source

/-- Successor assignment read from the genuine induced monitor thread. -/
noncomputable def ProfiledOpenRepresentableMove.successor
    (move : ProfiledOpenRepresentableMove A) :
    TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
      (ProfiledOpenClassifiedDirection A) := by
  classical
  cases move with
  | sink => exact fun _ => (.sink, {.sink})
  | right source table =>
      by_cases hvalid :
          ProfiledOpenRepresentableMove.Valid A (.right source table)
      · exact fun direction =>
          match direction with
          | .fromOne root row past input =>
              if hmem : root ∈ source.1 then
                let member : {root // root ∈ source.1} := ⟨root, hmem⟩
                let output := profiledOpenRightRepresentableOutputAt A source
                  table member (omegaOfList (past ++ [input])) past.length
                (.left (output.2 row).1,
                  profiledOpenLeftClassifiedRoots A (output.2 row).2)
              else (.sink, {.sink})
          | .fromTwo _ _ _ _ => (.sink, {.sink})
      · exact fun _ => (.sink, {.sink})
  | left source table =>
      by_cases hvalid :
          ProfiledOpenRepresentableMove.Valid A (.left source table)
      · exact fun direction =>
          match direction with
          | .fromTwo root row past input =>
              if hmem : root ∈ source.1 then
                let member : {root // root ∈ source.1} := ⟨root, hmem⟩
                let output := profiledOpenLeftRepresentableOutputAt A source
                  table member (omegaOfList (past ++ [input])) past.length
                (.right (output.2 row).1,
                  profiledOpenRightClassifiedRoots A (output.2 row).2)
              else (.sink, {.sink})
          | .fromOne _ _ _ _ => (.sink, {.sink})
      · exact fun _ => (.sink, {.sink})

def ProfiledOpenRepresentableFamilyAllowed
    (roots : Finset (ProfiledOpenClassifiedAnchor A))
    (next : TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
      (ProfiledOpenClassifiedDirection A)) : Prop :=
  ∃ move : ProfiledOpenRepresentableMove A,
    move.Valid A ∧ move.roots A = roots ∧ move.successor A = next

noncomputable abbrev profiledOpenRepresentableFamilyRunAutomaton
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A)) :=
  twoSortedFamilyRunAutomaton (profiledOpenClassifiedAnchorPriority A)
    initialRoots (ProfiledOpenRepresentableFamilyAllowed A)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every represented right class supplies a valid productive move. -/
theorem ProfiledOpenRightViewClass.exists_valid_representableMove
    (source : ProfiledOpenRightViewClass A)
    (hrep : source.SemanticallyRepresentable A) :
    ∃ move : ProfiledOpenRepresentableMove A,
      move.Valid A ∧
        move.roots A = profiledOpenRightClassifiedRoots A source := by
  obtain ⟨table, hwins, hallowed⟩ := source.exists_representableTable A hrep
  exact ⟨.right source table, ⟨hwins, hallowed⟩, rfl⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left represented move. -/
theorem ProfiledOpenLeftViewClass.exists_valid_representableMove
    (source : ProfiledOpenLeftViewClass A)
    (hrep : source.SemanticallyRepresentable A) :
    ∃ move : ProfiledOpenRepresentableMove A,
      move.Valid A ∧
        move.roots A = profiledOpenLeftClassifiedRoots A source := by
  obtain ⟨table, hwins, hallowed⟩ := source.exists_representableTable A hrep
  exact ⟨.left source table, ⟨hwins, hallowed⟩, rfl⟩

/-! ## Recursive productivity closure -/

/-- Finite families that can occur in the productive outer recursion. -/
def ProfiledOpenRepresentableFamily
    (roots : Finset (ProfiledOpenClassifiedAnchor A)) : Prop :=
  roots = {.sink} ∨
    (∃ source : ProfiledOpenRightViewClass A,
      source.SemanticallyRepresentable A ∧
        roots = profiledOpenRightClassifiedRoots A source) ∨
    (∃ source : ProfiledOpenLeftViewClass A,
      source.SemanticallyRepresentable A ∧
        roots = profiledOpenLeftClassifiedRoots A source)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every productive family has a valid finite move with exactly those
roots. -/
theorem exists_valid_representableMove_of_family
    (roots : Finset (ProfiledOpenClassifiedAnchor A))
    (hfamily : ProfiledOpenRepresentableFamily A roots) :
    ∃ move : ProfiledOpenRepresentableMove A,
      move.Valid A ∧ move.roots A = roots := by
  rcases hfamily with hsink | hright | hleft
  · subst roots
    exact ⟨.sink, trivial, rfl⟩
  · rcases hright with ⟨source, hrep, rfl⟩
    exact source.exists_valid_representableMove A hrep
  · rcases hleft with ⟨source, hrep, rfl⟩
    exact source.exists_valid_representableMove A hrep

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every direction of a valid productive move returns another productive
family.  Invalid-root and wrong-orientation directions enter the harmless
sink; real directions use the sticky representability law read at the actual
monitor control. -/
theorem ProfiledOpenRepresentableMove.successor_family
    (move : ProfiledOpenRepresentableMove A)
    (hvalid : move.Valid A)
    (direction : ProfiledOpenClassifiedDirection A) :
    ProfiledOpenRepresentableFamily A (move.successor A direction).2 := by
  classical
  cases move with
  | sink =>
      exact Or.inl rfl
  | right source table =>
      rcases hvalid with ⟨hwins, hallowed⟩
      have hvalid' : ProfiledOpenRepresentableMove.Valid A
          (.right source table) := ⟨hwins, hallowed⟩
      cases direction with
      | fromTwo root row past input =>
          apply Or.inl
          simp [ProfiledOpenRepresentableMove.successor, hvalid']
      | fromOne root row past input =>
          by_cases hmem : root ∈ source.1
          · let member : {root // root ∈ source.1} := ⟨root, hmem⟩
            let env := omegaOfList (past ++ [input])
            let nextClass :=
              ((profiledOpenRightRepresentableOutputAt A source table member
                env past.length).2 row).2
            have hrep : nextClass.SemanticallyRepresentable A :=
              profiledOpenRightRepresentableOutputAt_class A source table
                hallowed member env past.length row
            apply Or.inr; apply Or.inr
            refine ⟨nextClass, hrep, ?_⟩
            simp [ProfiledOpenRepresentableMove.successor, hvalid', hmem,
              member, env, nextClass]
          · apply Or.inl
            simp [ProfiledOpenRepresentableMove.successor, hvalid', hmem]
  | left source table =>
      rcases hvalid with ⟨hwins, hallowed⟩
      have hvalid' : ProfiledOpenRepresentableMove.Valid A
          (.left source table) := ⟨hwins, hallowed⟩
      cases direction with
      | fromOne root row past input =>
          apply Or.inl
          simp [ProfiledOpenRepresentableMove.successor, hvalid']
      | fromTwo root row past input =>
          by_cases hmem : root ∈ source.1
          · let member : {root // root ∈ source.1} := ⟨root, hmem⟩
            let env := omegaOfList (past ++ [input])
            let nextClass :=
              ((profiledOpenLeftRepresentableOutputAt A source table member
                env past.length).2 row).2
            have hrep : nextClass.SemanticallyRepresentable A :=
              profiledOpenLeftRepresentableOutputAt_class A source table
                hallowed member env past.length row
            apply Or.inr; apply Or.inl
            refine ⟨nextClass, hrep, ?_⟩
            simp [ProfiledOpenRepresentableMove.successor, hvalid', hmem,
              member, env, nextClass]
          · apply Or.inl
            simp [ProfiledOpenRepresentableMove.successor, hvalid', hmem]

/-- Canonical total move choice.  Nonproductive families are totalized by
the sink, but the closure theorem below proves they are never encountered
from a productive initial family. -/
noncomputable def profiledOpenRepresentableMoveFor
    (roots : Finset (ProfiledOpenClassifiedAnchor A)) :
    ProfiledOpenRepresentableMove A := by
  classical
  if hfamily : ProfiledOpenRepresentableFamily A roots then
    exact (exists_valid_representableMove_of_family A roots hfamily).choose
  else
    exact .sink

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenRepresentableMoveFor_valid
    (roots : Finset (ProfiledOpenClassifiedAnchor A))
    (hfamily : ProfiledOpenRepresentableFamily A roots) :
    (profiledOpenRepresentableMoveFor A roots).Valid A := by
  classical
  rw [profiledOpenRepresentableMoveFor, dif_pos hfamily]
  exact (exists_valid_representableMove_of_family A roots hfamily).choose_spec.1

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenRepresentableMoveFor_roots
    (roots : Finset (ProfiledOpenClassifiedAnchor A))
    (hfamily : ProfiledOpenRepresentableFamily A roots) :
    (profiledOpenRepresentableMoveFor A roots).roots A = roots := by
  classical
  rw [profiledOpenRepresentableMoveFor, dif_pos hfamily]
  exact (exists_valid_representableMove_of_family A roots hfamily).choose_spec.2

noncomputable def profiledOpenRepresentableSuccessorFor
    (roots : Finset (ProfiledOpenClassifiedAnchor A)) :
    TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
      (ProfiledOpenClassifiedDirection A) :=
  (profiledOpenRepresentableMoveFor A roots).successor A

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Both family and chosen states of the canonical unfolding carry a
productive successor family. -/
theorem profiledOpenRepresentableDeterministicRun_productive
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (hinitial : ProfiledOpenRepresentableFamily A initialRoots) :
    ∀ node,
      match TwoSortedFamilyPolicy.deterministicRun initialRoots
          (profiledOpenRepresentableSuccessorFor A) node with
      | .family roots => ProfiledOpenRepresentableFamily A roots
      | .chosen _ roots => ProfiledOpenRepresentableFamily A roots := by
  intro node
  induction node using List.reverseRecOn with
  | nil => exact hinitial
  | append_singleton node direction ih =>
      rw [TwoSortedFamilyPolicy.deterministicRun_append]
      cases hstate : TwoSortedFamilyPolicy.deterministicRun initialRoots
          (profiledOpenRepresentableSuccessorFor A) node with
      | family roots =>
          rw [hstate] at ih
          exact ProfiledOpenRepresentableMove.successor_family A
            (profiledOpenRepresentableMoveFor A roots)
            (profiledOpenRepresentableMoveFor_valid A roots ih) direction
      | chosen actual roots =>
          rw [hstate] at ih
          exact ih

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Hence the canonical productive assignment satisfies the complete outer
transition law at every family. -/
theorem profiledOpenRepresentableSuccessorFor_allowed
    (roots : Finset (ProfiledOpenClassifiedAnchor A))
    (hfamily : ProfiledOpenRepresentableFamily A roots) :
    ProfiledOpenRepresentableFamilyAllowed A roots
      (profiledOpenRepresentableSuccessorFor A roots) := by
  exact ⟨profiledOpenRepresentableMoveFor A roots,
    profiledOpenRepresentableMoveFor_valid A roots hfamily,
    profiledOpenRepresentableMoveFor_roots A roots hfamily, rfl⟩

end

end


end DetParityAutomaton

end DistributedSynthesis
