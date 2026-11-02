/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.ExecutableFirstOrder

/-! # Executable MSO compilation and satisfiability

The recursion returns automaton data, not a classical choice from an existence
proof. Both quantifiers use the proved finite constructions. Satisfiability
uses the existing exhaustive finite-policy solver for parity tree automata.
These procedures are deliberately exhaustive; no practical complexity claim
or primitive-recursive numeric encoding theorem is asserted here.
-/
namespace DistributedSynthesis.MSO.Tree.Executable

variable {Branch Alphabet : Type*} [Fintype Branch] [DecidableEq Branch] [Nonempty Branch]
variable [Fintype Alphabet] [DecidableEq Alphabet] {n m : Nat}

/-- Structural compiler with its semantic correctness proof. -/
def recognition {n m : Nat} (φ : Formula (language Branch Alphabet) n m) :
    Recognition (fun tree nodes sets => Realize tree φ nodes sets) :=
  match φ with
  | .firstOrder φ => firstOrder_recognition φ
  | .mem x X => Recognition.membership x X
  | .falsum => Recognition.falsum
  | .imp φ ψ => (recognition φ).impl (recognition ψ)
  | .allNode φ => (recognition φ).forallNode
  | .allSet φ => (recognition φ).forallSet

/-- Executable translation with explicit state equality and transition tests. -/
def compile (φ : Formula (language Branch Alphabet) n m) :
    TreeAutomatonData Branch (ValuationLabel Alphabet n m) := (recognition φ).data

theorem compile_correct (φ : Formula (language Branch Alphabet) n m)
    (tree : LabeledTree Branch Alphabet) (nodes : Fin n → TreeNode Branch)
    (sets : Fin m → Set (TreeNode Branch)) :
    (compile φ).Accepts (encode tree nodes sets) ↔ Realize tree φ nodes sets :=
  (recognition φ).correct tree nodes sets

def sentenceAutomaton (φ : Sentence (language Branch Alphabet)) : TreeAutomatonData Branch Alphabet :=
  (compile φ).comap (fun a => (a,Fin.elim0,Fin.elim0))

theorem sentenceAutomaton_correct (φ : Sentence (language Branch Alphabet))
    (tree : LabeledTree Branch Alphabet) :
    (sentenceAutomaton φ).Accepts tree ↔ Satisfies tree φ := by
  change ((compile φ).toAutomaton.comap _).acceptsTree tree ↔ _
  rw [RunParityTreeAutomaton.comap_acceptsTree_iff]
  have labels : (fun a => (a,Fin.elim0,Fin.elim0)) ∘ tree =
      encode tree (Fin.elim0 : Fin 0 → TreeNode Branch) (Fin.elim0 : Fin 0 → Set (TreeNode Branch)) := by
    funext node
    exact Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))
  rw [labels]
  exact compile_correct φ tree Fin.elim0 Fin.elim0

variable [Inhabited Branch]

/-- An actual decision algorithm; it does not inspect any infinite tree. -/
@[reducible] def satisfiableDecidable (φ : Sentence (language Branch Alphabet)) :
    Decidable (∃ tree, Satisfies tree φ) :=
  letI := TreeAutomatonData.nonemptyDecidable (sentenceAutomaton φ)
  decidable_of_iff (∃ tree, (sentenceAutomaton φ).Accepts tree)
    (exists_congr (sentenceAutomaton_correct φ))

/-- Boolean satisfiability over full infinite labelled trees. -/
def satisfiable (φ : Sentence (language Branch Alphabet)) : Bool :=
  @decide (∃ tree, Satisfies tree φ) (satisfiableDecidable φ)

theorem satisfiable_correct (φ : Sentence (language Branch Alphabet)) :
    satisfiable φ = true ↔ ∃ tree, Satisfies tree φ := by
  exact Iff.of_eq (@decide_eq_true_eq _ (satisfiableDecidable φ))

/-- Validity, by checking that the negated sentence has no model. -/
def valid (φ : Sentence (language Branch Alphabet)) : Bool := !(satisfiable φ.not)

theorem valid_correct (φ : Sentence (language Branch Alphabet)) :
    valid φ = true ↔ ∀ tree, Satisfies tree φ := by
  simp only [valid, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, satisfiable_correct]
  change (¬ ∃ tree, ¬ Satisfies tree φ) ↔ _
  simp

end DistributedSynthesis.MSO.Tree.Executable
