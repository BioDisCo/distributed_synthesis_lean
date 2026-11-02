/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Tree
import DistributedSynthesis.Library.Automata.TreeProjection

/-! # Variable markers and existential set projection

Individual variables mark exactly one tree node; set variables mark arbitrary
sets of nodes. Marker alphabets are ordinary finite function types over `Bool`.
The source alphabet, tree nodes, and finite-set infrastructure are not duplicated.
-/
namespace DistributedSynthesis.MSO.Tree

universe u v w
variable {Branch : Type u} {Alphabet : Type v} {n m : Nat}

/-- Input letters decorated with individual and set membership markers. -/
abbrev ValuationLabel (Alphabet : Type v) (n m : Nat) :=
  Alphabet × (Fin n → Bool) × (Fin m → Bool)

/-- Encode a semantic valuation. Arbitrary sets need not have computable
membership; the compiler operates on the resulting finite marker alphabet. -/
noncomputable def encode (tree : LabeledTree Branch Alphabet)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch)) :
    LabeledTree Branch (ValuationLabel Alphabet n m) := by
  classical
  exact fun node => (tree node, fun i => decide (node = nodes i), fun i => decide (node ∈ sets i))

/-- Forget the newest set variable, preserving every other marker. -/
def dropSet (letter : ValuationLabel Alphabet n (m + 1)) : ValuationLabel Alphabet n m :=
  (letter.1, letter.2.1, fun i => letter.2.2 i.castSucc)

@[simp] theorem dropSet_encode (tree : LabeledTree Branch Alphabet)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch))
    (X : Set (TreeNode Branch)) :
    dropSet ∘ encode tree nodes (Fin.snoc sets X) = encode tree nodes sets := by
  classical
  funext node
  simp [dropSet, encode, Function.comp_def]

/-- Every lift of an encoded valuation adds exactly one arbitrary set of nodes. -/
theorem dropSet_eq_encode_iff (tree : LabeledTree Branch Alphabet)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch))
    (lifted : LabeledTree Branch (ValuationLabel Alphabet n (m + 1))) :
    dropSet ∘ lifted = encode tree nodes sets ↔
      ∃ X : Set (TreeNode Branch), lifted = encode tree nodes (Fin.snoc sets X) := by
  classical
  constructor
  · intro labels
    let X : Set (TreeNode Branch) := {node | (lifted node).2.2 (Fin.last m) = true}
    refine ⟨X, ?_⟩
    funext node
    have atNode := congrFun labels node
    apply Prod.ext
    · simpa only [Function.comp_apply, dropSet, encode] using congrArg Prod.fst atNode
    · apply Prod.ext
      · exact congrArg (fun letter => letter.2.1) atNode
      · funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [encode, X]
        · simpa only [Function.comp_apply, dropSet, encode, Fin.snoc_castSucc] using
            congrFun (congrArg (fun letter => letter.2.2) atNode) j
  · rintro ⟨X, rfl⟩
    exact dropSet_encode tree nodes sets X

/-- The automaton construction for existential set quantification, assuming only
the induction hypothesis that its body automaton recognizes the body formula.
This is one compiler step, not a claim of a completed general MSO compiler. -/
theorem project_exSet_correct
    (φ : Formula (language Branch Alphabet) n (m + 1))
    (A : RunParityTreeAutomaton.{u, v, w} Branch (ValuationLabel Alphabet n (m + 1)))
    (body_correct : ∀ (tree : LabeledTree Branch Alphabet) nodes sets,
      A.acceptsTree (encode tree nodes sets) ↔ Realize tree φ nodes sets)
    (tree : LabeledTree Branch Alphabet) (nodes : Fin n → TreeNode Branch)
    (sets : Fin m → Set (TreeNode Branch)) :
    (A.project dropSet).acceptsTree (encode tree nodes sets) ↔
      Realize tree φ.exSet nodes sets := by
  letI := treeStructure Branch Alphabet tree
  rw [RunParityTreeAutomaton.project_acceptsTree_iff]
  change (∃ lifted, dropSet ∘ lifted = encode tree nodes sets ∧ A.acceptsTree lifted) ↔
    @Formula.Realize _ _ (treeStructure Branch Alphabet tree) _ _ φ.exSet nodes sets
  rw [Formula.realize_exSet]
  constructor
  · rintro ⟨lifted, labels, accepts⟩
    obtain ⟨X, rfl⟩ := (dropSet_eq_encode_iff tree nodes sets lifted).mp labels
    exact ⟨X, (body_correct tree nodes (Fin.snoc sets X)).mp accepts⟩
  · rintro ⟨X, satisfies⟩
    exact ⟨encode tree nodes (Fin.snoc sets X), dropSet_encode tree nodes sets X,
      (body_correct tree nodes (Fin.snoc sets X)).mpr satisfies⟩

end DistributedSynthesis.MSO.Tree
