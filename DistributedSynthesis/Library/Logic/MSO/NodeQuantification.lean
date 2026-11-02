/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Compilation
import DistributedSynthesis.Library.Automata.TreeSingleton

/-! # Individual quantification through singleton markers

The singleton automaton excludes empty and multiple markers before projection.
No validity hypothesis on arbitrary accepted inputs of the body automaton is
needed: its correctness on encoded valuations is sufficient.
-/
namespace DistributedSynthesis.MSO.Tree
variable {Branch Alphabet : Type*} {n m : Nat}

def dropNode (letter : ValuationLabel Alphabet (n+1) m) : ValuationLabel Alphabet n m :=
  (letter.1, (fun i => letter.2.1 i.castSucc), letter.2.2)

@[simp] theorem dropNode_encode (tree : LabeledTree Branch Alphabet)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch))
    (x : TreeNode Branch) :
    dropNode ∘ encode tree (Fin.snoc nodes x) sets = encode tree nodes sets := by
  classical
  funext node
  simp [dropNode, encode]

theorem dropNode_eq_encode_iff (tree : LabeledTree Branch Alphabet)
    (nodes : Fin n → TreeNode Branch) (sets : Fin m → Set (TreeNode Branch))
    (lifted : LabeledTree Branch (ValuationLabel Alphabet (n+1) m)) :
    (dropNode ∘ lifted = encode tree nodes sets ∧
      ∃ x, ∀ node, (lifted node).2.1 (Fin.last n) = true ↔ node = x) ↔
      ∃ x, lifted = encode tree (Fin.snoc nodes x) sets := by
  classical
  constructor
  · rintro ⟨labels, x, singleton⟩
    refine ⟨x, funext (fun node => ?_)⟩
    have atNode := congrFun labels node
    apply Prod.ext
    · simpa only [Function.comp_apply, dropNode, encode] using congrArg Prod.fst atNode
    · apply Prod.ext
      · funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [encode, Fin.snoc_last]
          calc
            _ = decide ((lifted node).2.1 (Fin.last n) = true) := by simp
            _ = decide (node = x) := by simp only [singleton node]
        · simpa only [Function.comp_apply, dropNode, encode, Fin.snoc_castSucc] using
            congrFun (congrArg (fun letter => letter.2.1) atNode) j
      · exact congrArg (fun letter => letter.2.2) atNode
  · rintro ⟨x, rfl⟩
    refine ⟨dropNode_encode tree nodes sets x, x, ?_⟩
    intro node
    simp [encode]

variable [Fintype Branch] [Nonempty Branch]

/-- Individual projection first enforces a singleton for the new node marker. -/
noncomputable def exNodeAutomaton
    (A : RunParityTreeAutomaton Branch (ValuationLabel Alphabet (n+1) m)) :
    RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m) := by
  classical
  exact (TreeBoolean.inter A (TreeSingleton.automaton
    (fun letter : ValuationLabel Alphabet (n+1) m => letter.2.1 (Fin.last n)))).project dropNode

theorem exNodeAutomaton_accepts_iff
    (A : RunParityTreeAutomaton Branch (ValuationLabel Alphabet (n+1) m))
    (tree : LabeledTree Branch Alphabet) (nodes : Fin n → TreeNode Branch)
    (sets : Fin m → Set (TreeNode Branch)) :
    (exNodeAutomaton A).acceptsTree (encode tree nodes sets) ↔
      ∃ x, A.acceptsTree (encode tree (Fin.snoc nodes x) sets) := by
  classical
  rw [exNodeAutomaton, RunParityTreeAutomaton.project_acceptsTree_iff]
  constructor
  · rintro ⟨lifted, labels, accepts⟩
    obtain ⟨body, single⟩ := (TreeBoolean.inter_accepts_iff _ _ lifted).mp accepts
    have marker := TreeSingleton.accepts_iff.mp single
    obtain ⟨x, rfl⟩ := (dropNode_eq_encode_iff tree nodes sets lifted).mp ⟨labels, marker⟩
    exact ⟨x, body⟩
  · rintro ⟨x, body⟩
    refine ⟨encode tree (Fin.snoc nodes x) sets, dropNode_encode tree nodes sets x, ?_⟩
    apply (TreeBoolean.inter_accepts_iff _ _ _).mpr
    refine ⟨body, TreeSingleton.accepts_iff.mpr ?_⟩
    exact ((dropNode_eq_encode_iff tree nodes sets _).mpr ⟨x,rfl⟩).2

theorem exNodeAutomaton_correct
    (A : RunParityTreeAutomaton Branch (ValuationLabel Alphabet (n+1) m))
    (φ : Formula (language Branch Alphabet) (n+1) m) (correct : Represents A φ) :
    Represents (exNodeAutomaton A) φ.exNode := by
  intro tree nodes sets
  rw [exNodeAutomaton_accepts_iff]
  letI := treeStructure Branch Alphabet tree
  change (∃ x, A.acceptsTree (encode tree (Fin.snoc nodes x) sets)) ↔
    Formula.Realize φ.exNode nodes sets
  rw [Formula.realize_exNode]
  exact exists_congr (fun x => correct tree (Fin.snoc nodes x) sets)

variable [Fintype Alphabet]
noncomputable def allNodeAutomaton
    (A : RunParityTreeAutomaton Branch (ValuationLabel Alphabet (n+1) m)) :
    RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m) :=
  TreeComplement.automaton (exNodeAutomaton (TreeComplement.automaton A))

theorem allNodeAutomaton_correct
    (A : RunParityTreeAutomaton Branch (ValuationLabel Alphabet (n+1) m))
    (φ : Formula (language Branch Alphabet) (n+1) m) (correct : Represents A φ) :
    Represents (allNodeAutomaton A) (.allNode φ) := by
  intro tree nodes sets
  rw [allNodeAutomaton, TreeComplement.accepts_iff,
    exNodeAutomaton_correct _ φ.not (complement_represents A φ correct)]
  letI := treeStructure Branch Alphabet tree
  change (¬ Formula.Realize φ.not.exNode nodes sets) ↔ Formula.Realize (.allNode φ) nodes sets
  simp

end DistributedSynthesis.MSO.Tree
