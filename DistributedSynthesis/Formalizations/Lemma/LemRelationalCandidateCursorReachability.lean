/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFixedPolicyRelationalCandidateTable

/-!
# Reachability and finite forks of relational-candidate cursors

`RelationalCandidateTreeBranchPackage.Cursor` retains a proof-side live
candidate while following the public candidate-set table.  This file records
the elementary, but frequently needed, fact that a cursor obtained by any
finite query word is still on the same genuine branch.

The final constructor packages the shape used by delayed boundary recutting:
after one common query prefix, one alternative takes a single query while the
other takes two queries.  Selecting either endpoint preserves reachability.
Nothing in these definitions is exposed to a process at runtime; the query
word and the selected fork arm are proof-side witnesses only.
-/

namespace DistributedSynthesis

universe f d m q

section

variable {Family : Type f} {Descriptor : Type d} {Move : Type m}
  {Query : Type q}
variable [Fintype Family] [Fintype Descriptor] [Fintype Move] [Fintype Query]
variable [Inhabited Query]

variable
  (Live : Descriptor → Family → Prop)
  (CandidateValid : Descriptor → Family → Move → Prop)
  (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
  (ControlStep : Descriptor → Descriptor → Prop)

variable
  {initial : Finset (RelationalFamilyCandidate Family Descriptor)}
  {initialActual : RelationalFamilyCandidate Family Descriptor}

namespace RelationalCandidateTreeBranchPackage

variable {Live CandidateValid ExactEdge ControlStep}
variable (package : RelationalCandidateTreeBranchPackage Live CandidateValid
  ExactEdge ControlStep initial initialActual)

/-- Cursor obtained by feeding a finite query word from an arbitrary root
cursor. -/
noncomputable def Cursor.runFrom (root : package.Cursor)
    (queries : List Query) : package.Cursor :=
  queries.foldl (Cursor.step package) root

section
omit [Fintype Move] [Fintype Query]

@[simp] theorem Cursor.runFrom_nil (root : package.Cursor) :
    Cursor.runFrom package root [] = root :=
  rfl

@[simp] theorem Cursor.runFrom_singleton (root : package.Cursor)
    (query : Query) :
    Cursor.runFrom package root [query] = Cursor.step package root query :=
  rfl

theorem Cursor.runFrom_append (root : package.Cursor)
    (head tail : List Query) :
    Cursor.runFrom package root (head ++ tail) =
      Cursor.runFrom package (Cursor.runFrom package root head) tail := by
  simp [Cursor.runFrom, List.foldl_append]

end

/-- Reachability from a cursor means literal finite iteration of the package's
cursor step. -/
def CursorReachableFrom (root cursor : package.Cursor) : Prop :=
  ∃ queries : List Query, cursor = Cursor.runFrom package root queries

section
omit [Fintype Move] [Fintype Query]

theorem cursorReachableFrom_refl (root : package.Cursor) :
    CursorReachableFrom package root root := by
  exact ⟨[], rfl⟩

theorem cursorReachableFrom_step {root cursor : package.Cursor}
    (hcursor : CursorReachableFrom package root cursor) (query : Query) :
    CursorReachableFrom package root (Cursor.step package cursor query) := by
  obtain ⟨queries, rfl⟩ := hcursor
  refine ⟨queries ++ [query], ?_⟩
  rw [Cursor.runFrom_append]
  rfl

theorem cursorReachableFrom_runFrom {root cursor : package.Cursor}
    (hcursor : CursorReachableFrom package root cursor)
    (queries : List Query) :
    CursorReachableFrom package root
      (Cursor.runFrom package cursor queries) := by
  obtain ⟨head, rfl⟩ := hcursor
  refine ⟨head ++ queries, ?_⟩
  rw [Cursor.runFrom_append]

theorem cursorReachableFrom_trans {root middle cursor : package.Cursor}
    (hmiddle : CursorReachableFrom package root middle)
    (hcursor : CursorReachableFrom package middle cursor) :
    CursorReachableFrom package root cursor := by
  obtain ⟨head, rfl⟩ := hmiddle
  obtain ⟨tail, rfl⟩ := hcursor
  refine ⟨head ++ tail, ?_⟩
  rw [Cursor.runFrom_append]

end

/-- A proof-side fork whose two endpoints share one reachable root. -/
structure CursorFork (root : package.Cursor) where
  left : package.Cursor
  right : package.Cursor
  left_reachable : CursorReachableFrom package root left
  right_reachable : CursorReachableFrom package root right

/-- Select one arm of a reachable fork.  `false` selects the left arm and
`true` the right arm. -/
def CursorFork.select {root : package.Cursor} (fork : package.CursorFork root) :
    Bool → package.Cursor
  | false => fork.left
  | true => fork.right

section
omit [Fintype Move] [Fintype Query]

@[simp] theorem CursorFork.select_false {root : package.Cursor}
    (fork : package.CursorFork root) :
    CursorFork.select package fork false = fork.left :=
  rfl

@[simp] theorem CursorFork.select_true {root : package.Cursor}
    (fork : package.CursorFork root) :
    CursorFork.select package fork true = fork.right :=
  rfl

theorem CursorFork.select_reachable {root : package.Cursor}
    (fork : package.CursorFork root) (chooseRight : Bool) :
    CursorReachableFrom package root
      (CursorFork.select package fork chooseRight) := by
  cases chooseRight with
  | false => exact fork.left_reachable
  | true => exact fork.right_reachable

/-- A direct `if`-selection form, convenient when the fork condition is a
proposition rather than a Boolean controller state. -/
theorem cursorReachableFrom_ite {root left right : package.Cursor}
    (condition : Prop) [Decidable condition]
    (hleft : CursorReachableFrom package root left)
    (hright : CursorReachableFrom package root right) :
    CursorReachableFrom package root (if condition then right else left) := by
  by_cases h : condition
  · simp [h, hright]
  · simp [h, hleft]

theorem cursorReachableFrom_commonPrefix_one
    (root : package.Cursor) (head : List Query) (query : Query) :
    CursorReachableFrom package root
      (Cursor.step package (Cursor.runFrom package root head) query) :=
  cursorReachableFrom_step package
    (cursorReachableFrom_runFrom package
      (cursorReachableFrom_refl package root) head) query

theorem cursorReachableFrom_commonPrefix_two
    (root : package.Cursor) (head : List Query)
    (first second : Query) :
    CursorReachableFrom package root
      (Cursor.step package
        (Cursor.step package (Cursor.runFrom package root head) first)
        second) :=
  cursorReachableFrom_step package
    (cursorReachableFrom_commonPrefix_one package root head first) second

end

/-- The reusable delayed-recut fork: both arms first follow `prefix`; the left
arm then consumes `direct`, whereas the right arm consumes `first` and
`second`. -/
noncomputable def commonPrefixOneTwoFork
    (root : package.Cursor) (head : List Query)
    (direct first second : Query) : package.CursorFork root where
  left := Cursor.step package (Cursor.runFrom package root head) direct
  right := Cursor.step package
    (Cursor.step package (Cursor.runFrom package root head) first) second
  left_reachable :=
    cursorReachableFrom_commonPrefix_one package root head direct
  right_reachable :=
    cursorReachableFrom_commonPrefix_two package root head first second

section
omit [Fintype Move] [Fintype Query]

@[simp] theorem commonPrefixOneTwoFork_left
    (root : package.Cursor) (head : List Query)
    (direct first second : Query) :
    (commonPrefixOneTwoFork package root head direct first second).left =
      Cursor.step package (Cursor.runFrom package root head) direct :=
  rfl

@[simp] theorem commonPrefixOneTwoFork_right
    (root : package.Cursor) (head : List Query)
    (direct first second : Query) :
    (commonPrefixOneTwoFork package root head direct first second).right =
      Cursor.step package
        (Cursor.step package (Cursor.runFrom package root head) first)
        second :=
  rfl

theorem commonPrefixOneTwoFork_select_reachable
    (root : package.Cursor) (head : List Query)
    (direct first second : Query) (chooseTwo : Bool) :
    CursorReachableFrom package root
      (CursorFork.select package
        (commonPrefixOneTwoFork package root head direct first second)
        chooseTwo) :=
  CursorFork.select_reachable package _ chooseTwo

end

end RelationalCandidateTreeBranchPackage

end

end DistributedSynthesis
