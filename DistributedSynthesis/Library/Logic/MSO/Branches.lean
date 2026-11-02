/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Tree
import DistributedSynthesis.Library.Automata.TreeNonemptiness

/-! # Defining infinite branches in MSO

A branch contains the root, is closed under ancestors, and contains exactly one
child of each of its nodes. The semantic characterization uses the existing
`branchNode` representation, not a second notion of infinite path.
-/
namespace DistributedSynthesis.MSO.Tree

variable {Branch Alphabet : Type*} {m : Nat}

/-- Rooted, ancestor-closed, with exactly one continuing child at every node. -/
def IsBranchSet (X : Set (TreeNode Branch)) : Prop :=
  [] ∈ X ∧ (∀ x y, y ∈ X → x <+: y → x ∈ X) ∧
    ∀ x, x ∈ X → ∃! y, y ∈ X ∧ ∃ b : Branch, y = x ++ [b]

theorem branchNode_prefix_iff (branch : Nat → Branch) (i j : Nat) :
    branchNode branch i <+: branchNode branch j ↔ i ≤ j := by
  constructor
  · intro h
    simpa only [TreeNonemptiness.branch_length] using h.length_le
  · intro h
    induction j, h using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ j h ih => exact ih.trans (List.prefix_append _ _)

theorem prefix_of_branch_eq (branch : Nat → Branch) (node : TreeNode Branch) (n : Nat)
    (h : node <+: branchNode branch n) : node = branchNode branch node.length := by
  have length : node.length ≤ n := by simpa only [TreeNonemptiness.branch_length] using h.length_le
  have h' := (branchNode_prefix_iff branch node.length n).mpr length
  have eq' := List.prefix_iff_eq_take.mp h'
  simp only [TreeNonemptiness.branch_length] at eq'
  exact (List.prefix_iff_eq_take.mp h).trans eq'.symm

theorem isBranchSet_range (branch : Nat → Branch) : IsBranchSet (Set.range (branchNode branch)) := by
  refine ⟨⟨0,rfl⟩, ?_, ?_⟩
  · rintro x y ⟨n,rfl⟩ h
    exact ⟨x.length, (prefix_of_branch_eq branch x n h).symm⟩
  · rintro x ⟨n,rfl⟩
    refine ⟨branchNode branch (n+1), ⟨⟨n+1,rfl⟩, branch n, rfl⟩, ?_⟩
    rintro y ⟨⟨k,rfl⟩, b, equation⟩
    have length := congrArg List.length equation
    simp only [TreeNonemptiness.branch_length, List.length_append, List.length_singleton] at length
    rw [length]

variable [Nonempty Branch]

theorem isBranchSet_iff (X : Set (TreeNode Branch)) :
    IsBranchSet X ↔ ∃ branch : Nat → Branch, X = Set.range (branchNode branch) := by
  classical
  constructor
  · intro h
    have possible (node : TreeNode Branch) (hn : node ∈ X) : ∃ b, node ++ [b] ∈ X := by
      obtain ⟨next, ⟨member, b, equation⟩, _⟩ := h.2.2 node hn
      exact ⟨b, equation ▸ member⟩
    let select := fun node => if hn : node ∈ X then (possible node hn).choose
      else Classical.arbitrary Branch
    have selected (node : TreeNode Branch) (hn : node ∈ X) : node ++ [select node] ∈ X := by
      simpa only [select, dif_pos hn] using (possible node hn).choose_spec
    have unique (node : TreeNode Branch) (hn : node ∈ X) (b : Branch) (hb : node ++ [b] ∈ X) :
        node ++ [b] = node ++ [select node] := by
      obtain ⟨next, _, unique⟩ := h.2.2 node hn
      exact (unique _ ⟨hb,b,rfl⟩).trans (unique _ ⟨selected node hn,select node,rfl⟩).symm
    have live (n : Nat) : selectorNode select n ∈ X := by
      induction n with
      | zero => exact h.1
      | succ n ih => exact selected _ ih
    have readback (node : TreeNode Branch) : node ∈ X → node = selectorNode select node.length := by
      induction node using List.reverseRecOn with
      | nil => intro _; rfl
      | append_singleton node b ih =>
        intro member
        have parent := h.2.1 node (node ++ [b]) member (List.prefix_append _ _)
        have same := unique node parent b member
        simp only [List.length_append, List.length_singleton, selectorNode]
        rw [← ih parent]
        exact same
    let branch := fun n => select (selectorNode select n)
    refine ⟨branch, Set.ext (fun node => ⟨?_, ?_⟩)⟩
    · intro member
      exact ⟨node.length, (selectorNode_eq_branchNode select _).symm.trans (readback node member).symm⟩
    · rintro ⟨n,rfl⟩
      simpa only [branch, ← selectorNode_eq_branchNode] using live n
  · rintro ⟨branch,rfl⟩
    exact isBranchSet_range branch

omit [Nonempty Branch] in
private def rootIn (X : Fin m) : Formula (language Branch Alphabet) 0 m :=
  ((root 0).and (.mem 0 X)).exNode

omit [Nonempty Branch] in
private def ancestorClosed (X : Fin m) : Formula (language Branch Alphabet) 0 m :=
  .allNode (.allNode ((Formula.mem 1 X).imp ((ancestor 0 1).imp (.mem 0 X))))

omit [Nonempty Branch] in
private def uniqueChild (X : Fin m) : Formula (language Branch Alphabet) 0 m :=
  .allNode ((Formula.mem 0 X).imp
    (((Formula.mem 1 X).and ((child 0 1).and
      (.allNode (((Formula.mem 2 X).and (child 0 2)).imp (Formula.equal 2 1))))).exNode))

/-- The set variable X is one complete infinite branch. -/
def branchFormula (X : Fin m) : Formula (language Branch Alphabet) 0 m :=
  (rootIn X).and ((ancestorClosed X).and (uniqueChild X))

omit [Nonempty Branch] in
theorem branchFormula_correct (tree : LabeledTree Branch Alphabet) (X : Fin m)
    (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (branchFormula X) Fin.elim0 sets ↔ IsBranchSet (sets X) := by
  classical
  simp [branchFormula, rootIn, ancestorClosed, uniqueChild, Realize, IsBranchSet,
    Fin.snoc, ExistsUnique, and_assoc]

end DistributedSynthesis.MSO.Tree
