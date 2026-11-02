/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Reachability
import DistributedSynthesis.Formalizations.Definition.DefTreeAutomata

/-! # MSO on the existing full labelled trees

The domain is the library's `TreeNode Branch`; input trees are the existing
`LabeledTree Branch Alphabet`. The first-order signature names the root,
directional successors, the child relation, and node labels. Set quantifiers
retain the full powerset semantics from `MSO.Semantics`.
-/
namespace DistributedSynthesis.MSO.Tree

universe u v
variable (Branch : Type u) (Alphabet : Type v)

inductive FunctionSymbol : Nat → Type u
  | root : FunctionSymbol 0
  | successor (direction : Branch) : FunctionSymbol 1

inductive RelationSymbol : Nat → Type v
  | child : RelationSymbol 2
  | label (letter : Alphabet) : RelationSymbol 1

def language : FirstOrder.Language.{u, v} where
  Functions := FunctionSymbol Branch
  Relations := RelationSymbol Alphabet

/-- The canonical first-order structure of the full labelled tree. -/
@[implicit_reducible]
def treeStructure (tree : LabeledTree Branch Alphabet) :
    (language Branch Alphabet).Structure (TreeNode Branch) where
  funMap := fun {_} symbol nodes => match symbol with
    | .root => []
    | .successor direction => nodes 0 ++ [direction]
  RelMap := fun {_} symbol nodes => match symbol with
    | .child => ∃ direction : Branch, nodes 1 = nodes 0 ++ [direction]
    | .label letter => tree (nodes 0) = letter

variable {Branch Alphabet} {n m : Nat}

/-- Interpret an MSO formula on a full tree, with its input labelling fixed. -/
def Realize (tree : LabeledTree Branch Alphabet) (φ : Formula (language Branch Alphabet) n m)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch)) : Prop :=
  @Formula.Realize _ _ (treeStructure Branch Alphabet tree) _ _ φ nodes sets

/-- The language defined by a closed MSO sentence. -/
def Satisfies (tree : LabeledTree Branch Alphabet) (φ : Sentence (language Branch Alphabet)) : Prop :=
  Realize tree φ Fin.elim0 Fin.elim0

open FirstOrder.Language

def root (x : Fin n) : Formula (language Branch Alphabet) n m :=
  .firstOrder ((Term.var x).equal (.func .root Fin.elim0))

def successor (direction : Branch) (x y : Fin n) : Formula (language Branch Alphabet) n m :=
  .firstOrder ((Term.var y).equal (.func (.successor direction) ![Term.var x]))

def child (x y : Fin n) : Formula (language Branch Alphabet) n m :=
  Formula.relation .child ![x, y]

def label (letter : Alphabet) (x : Fin n) : Formula (language Branch Alphabet) n m :=
  Formula.relation (.label letter) ![x]

/-- Ancestor, including equality, obtained from the generic MSO reachability formula. -/
def ancestor (x y : Fin n) : Formula (language Branch Alphabet) n m :=
  Formula.reachable .child x y

@[simp] theorem realize_root (tree : LabeledTree Branch Alphabet) (x : Fin n)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (root x) nodes sets ↔ nodes x = [] := by
  rfl

@[simp] theorem realize_successor (tree : LabeledTree Branch Alphabet) (direction : Branch) (x y : Fin n)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (successor direction x y) nodes sets ↔ nodes y = nodes x ++ [direction] := by
  rfl

@[simp] theorem realize_child (tree : LabeledTree Branch Alphabet) (x y : Fin n)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (child x y) nodes sets ↔ ∃ direction : Branch, nodes y = nodes x ++ [direction] := by
  rfl

@[simp] theorem realize_label (tree : LabeledTree Branch Alphabet) (letter : Alphabet) (x : Fin n)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (label letter x) nodes sets ↔ tree (nodes x) = letter := by
  rfl

private theorem child_reaches_iff_prefix (a b : TreeNode Branch) :
    Relation.ReflTransGen (fun a b : TreeNode Branch => ∃ direction, b = a ++ [direction]) a b ↔
      a <+: b := by
  constructor
  · intro reaches
    induction reaches with
    | refl => exact List.prefix_refl _
    | tail _ edge ih =>
      obtain ⟨direction, rfl⟩ := edge
      exact ih.trans (List.prefix_append _ _)
  · rintro ⟨suffix, rfl⟩
    induction suffix using List.reverseRecOn with
    | nil => simpa using (Relation.ReflTransGen.refl (a := a))
    | append_singleton suffix direction ih =>
      exact ih.tail ⟨direction, by simp only [List.append_assoc]⟩

/-- The MSO ancestor formula defines exactly the existing list-prefix relation. -/
theorem realize_ancestor (tree : LabeledTree Branch Alphabet) (x y : Fin n)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (ancestor x y) nodes sets ↔ nodes x <+: nodes y := by
  letI := treeStructure Branch Alphabet tree
  change (Formula.reachable (L := language Branch Alphabet) RelationSymbol.child x y).Realize nodes sets ↔ _
  rw [Formula.realize_reachable]
  exact child_reaches_iff_prefix _ _


/-! The generic `Formula.Realize` forms support simplification under binders. -/
@[simp] theorem formula_realize_root (tree : LabeledTree Branch Alphabet) (x : Fin n)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch)) :
    @Formula.Realize _ _ (treeStructure Branch Alphabet tree) _ _ (root x) nodes sets ↔ nodes x = [] :=
  realize_root tree x nodes sets

@[simp] theorem formula_realize_successor (tree : LabeledTree Branch Alphabet) (b : Branch) (x y : Fin n)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch)) :
    @Formula.Realize _ _ (treeStructure Branch Alphabet tree) _ _ (successor b x y) nodes sets ↔
      nodes y = nodes x ++ [b] := realize_successor tree b x y nodes sets

@[simp] theorem formula_realize_child (tree : LabeledTree Branch Alphabet) (x y : Fin n)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch)) :
    @Formula.Realize _ _ (treeStructure Branch Alphabet tree) _ _ (child x y) nodes sets ↔
      ∃ b : Branch, nodes y = nodes x ++ [b] := realize_child tree x y nodes sets

@[simp] theorem formula_realize_label (tree : LabeledTree Branch Alphabet) (a : Alphabet) (x : Fin n)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch)) :
    @Formula.Realize _ _ (treeStructure Branch Alphabet tree) _ _ (label a x) nodes sets ↔
      tree (nodes x) = a := realize_label tree a x nodes sets

@[simp] theorem formula_realize_ancestor (tree : LabeledTree Branch Alphabet) (x y : Fin n)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch)) :
    @Formula.Realize _ _ (treeStructure Branch Alphabet tree) _ _ (ancestor x y) nodes sets ↔
      nodes x <+: nodes y := realize_ancestor tree x y nodes sets

end DistributedSynthesis.MSO.Tree
