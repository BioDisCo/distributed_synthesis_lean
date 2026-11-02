/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.ExecutableRecognition
import DistributedSynthesis.Library.Logic.MSO.Terms

/-! # Executable compilation of Mathlib terms

The witness-node construction follows `Terms`; its recursion now retains the
finite data instead of proving only existential recognizability.
-/
namespace DistributedSynthesis.MSO.Tree
variable {Branch Alphabet : Type*} {n m k : Nat}
variable [Fintype Branch] [DecidableEq Branch] [Nonempty Branch]
variable [Fintype Alphabet] [DecidableEq Alphabet]

private def function_recognition {arity : Nat} (symbol : FunctionSymbol Branch arity)
    (args : Fin arity → (language Branch Alphabet).Term (Fin n))
    (compiled : ∀ i, Recognition (m := m) (fun tree nodes _ =>
      nodes (Fin.last n) = termValue tree (fun j => nodes j.castSucc) (args i))) :
    Recognition (m := m) (fun tree nodes _ =>
      nodes (Fin.last n) = termValue tree (fun j => nodes j.castSucc) (.func symbol args)) := by
  cases symbol with
  | root => exact Recognition.root (Fin.last n)
  | successor direction =>
    let f : Fin (n+1) → Fin (n+2) := Formula.liftRenaming Fin.castSucc
    have argument := (compiled 0).rename f (id : Fin m → Fin m)
    have edge : Recognition (m := m) (fun (tree : LabeledTree Branch Alphabet) nodes _ =>
        nodes (Fin.last n).castSucc = nodes (Fin.last (n+1)) ++ [direction]) :=
      Recognition.successor direction (Fin.last (n+1)) (Fin.last n).castSucc
    apply (argument.conj edge).existsNode.congr
    intro tree nodes sets
    simp only [f, Function.comp_apply, Formula.liftRenaming_last, Formula.liftRenaming_castSucc,
      Fin.snoc_last, Fin.snoc_castSucc, termValue_successor]
    simp

/-- The newest individual variable denotes the value of the given term.
The recursive calls precede dependent elimination of the function symbol. -/
def term_recognition : (t : (language Branch Alphabet).Term (Fin n)) →
    Recognition (m := m) (fun tree nodes _ =>
      nodes (Fin.last n) = termValue tree (fun i => nodes i.castSucc) t)
  | .var i => Recognition.equal (Fin.last n) i.castSucc
  | .func f args => function_recognition f args (fun i => term_recognition (args i))

/-- Lift a recognizable unary relation from marked nodes to arbitrary terms. -/
def unary_term_recognition (t : (language Branch Alphabet).Term (Fin n))
    (R : LabeledTree Branch Alphabet → TreeNode Branch → Prop)
    (hR : Recognition (m := m) (fun tree nodes _ => R tree (nodes (Fin.last n)))) :
    Recognition (m := m) (fun tree nodes _ => R tree (termValue tree nodes t)) := by
  apply ((term_recognition t).conj hR).existsNode.congr
  intro tree nodes sets
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  simp

/-- Lift a recognizable binary relation using two singleton-marked witnesses. -/
def binary_term_recognition (t s : (language Branch Alphabet).Term (Fin n))
    (R : LabeledTree Branch Alphabet → TreeNode Branch → TreeNode Branch → Prop)
    (hR : Recognition (m := m) (fun tree nodes _ =>
      R tree (nodes (Fin.last n).castSucc) (nodes (Fin.last (n+1))))) :
    Recognition (m := m) (fun tree nodes _ => R tree (termValue tree nodes t) (termValue tree nodes s)) := by
  let f : Fin (n+1) → Fin (n+2) := Formula.liftRenaming Fin.castSucc
  have left := (term_recognition (m := m) t).rename Fin.castSucc (id : Fin m → Fin m)
  have right := (term_recognition (m := m) s).rename f (id : Fin m → Fin m)
  apply ((left.conj right).conj hR).existsNode.existsNode.congr
  intro tree nodes sets
  simp only [f, Function.comp_apply, Formula.liftRenaming_last, Formula.liftRenaming_castSucc,
    Fin.snoc_last, Fin.snoc_castSucc]
  simp

def equal_terms_recognition (t s : (language Branch Alphabet).Term (Fin n)) :
    Recognition (m := m) (fun tree nodes _ => termValue tree nodes t = termValue tree nodes s) := by
  apply binary_term_recognition t s (fun _ x y => x = y)
  exact Recognition.equal (Fin.last n).castSucc (Fin.last (n+1))

def relation_terms_recognition {arity : Nat} (r : RelationSymbol Alphabet arity)
    (args : Fin arity → (language Branch Alphabet).Term (Fin n)) :
    Recognition (m := m) (fun tree nodes _ =>
      relationValue tree r (fun i => termValue tree nodes (args i))) := by
  cases r with
  | label letter =>
    apply unary_term_recognition (args 0) (fun tree x => tree x = letter)
    exact Recognition.label letter (Fin.last n)
  | child =>
    apply binary_term_recognition (args 0) (args 1) (fun _ x y => ∃ b : Branch, y = x ++ [b])
    exact Recognition.child (Fin.last n).castSucc (Fin.last (n+1))

end DistributedSynthesis.MSO.Tree
