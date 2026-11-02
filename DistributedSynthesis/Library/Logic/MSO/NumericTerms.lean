/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.NumericRecognition
import DistributedSynthesis.Library.Logic.MSO.Terms

/-! # Numeric compilation of Mathlib terms

The witness-node construction follows `Terms`; its recursion now retains the
numeric program instead of proving only existential recognizability.
-/
namespace DistributedSynthesis.MSO.Tree.Numeric
variable {b a n m k : Nat}

private def function_recognition {arity : Nat} (symbol : FunctionSymbol (Fin (b+1)) arity)
    (args : Fin arity → (language (Fin (b+1)) (Fin (a+1))).Term (Fin n))
    (compiled : ∀ i, NumericRecognition (m := m) (fun tree nodes _ =>
      nodes (Fin.last n) = termValue tree (fun j => nodes j.castSucc) (args i))) :
    NumericRecognition (m := m) (fun tree nodes _ =>
      nodes (Fin.last n) = termValue tree (fun j => nodes j.castSucc) (.func symbol args)) := by
  cases symbol with
  | root => exact NumericRecognition.root (Fin.last n)
  | successor direction =>
    let f : Fin (n+1) → Fin (n+2) := Formula.liftRenaming Fin.castSucc
    have argument := (compiled 0).rename f (id : Fin m → Fin m)
    have edge : NumericRecognition (m := m) (fun (tree : LabeledTree (Fin (b+1)) (Fin (a+1))) nodes _ =>
        nodes (Fin.last n).castSucc = nodes (Fin.last (n+1)) ++ [direction]) :=
      NumericRecognition.successor direction (Fin.last (n+1)) (Fin.last n).castSucc
    apply (argument.conj edge).existsNode.congr
    intro tree nodes sets
    simp only [f, Function.comp_apply, Formula.liftRenaming_last, Formula.liftRenaming_castSucc,
      Fin.snoc_last, Fin.snoc_castSucc, termValue_successor]
    simp

/-- The newest individual variable denotes the value of the given term.
The recursive calls precede dependent elimination of the function symbol. -/
def term_recognition : (t : (language (Fin (b+1)) (Fin (a+1))).Term (Fin n)) →
    NumericRecognition (m := m) (fun tree nodes _ =>
      nodes (Fin.last n) = termValue tree (fun i => nodes i.castSucc) t)
  | .var i => NumericRecognition.equal (Fin.last n) i.castSucc
  | .func f args => function_recognition f args (fun i => term_recognition (args i))

/-- Lift a recognizable unary relation from marked nodes to arbitrary terms. -/
def unary_term_recognition (t : (language (Fin (b+1)) (Fin (a+1))).Term (Fin n))
    (R : LabeledTree (Fin (b+1)) (Fin (a+1)) → TreeNode (Fin (b+1)) → Prop)
    (hR : NumericRecognition (m := m) (fun tree nodes _ => R tree (nodes (Fin.last n)))) :
    NumericRecognition (m := m) (fun tree nodes _ => R tree (termValue tree nodes t)) := by
  apply ((term_recognition t).conj hR).existsNode.congr
  intro tree nodes sets
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  simp

/-- Lift a recognizable binary relation using two singleton-marked witnesses. -/
def binary_term_recognition (t s : (language (Fin (b+1)) (Fin (a+1))).Term (Fin n))
    (R : LabeledTree (Fin (b+1)) (Fin (a+1)) → TreeNode (Fin (b+1)) → TreeNode (Fin (b+1)) → Prop)
    (hR : NumericRecognition (m := m) (fun tree nodes _ =>
      R tree (nodes (Fin.last n).castSucc) (nodes (Fin.last (n+1))))) :
    NumericRecognition (m := m) (fun tree nodes _ => R tree (termValue tree nodes t) (termValue tree nodes s)) := by
  let f : Fin (n+1) → Fin (n+2) := Formula.liftRenaming Fin.castSucc
  have left := (term_recognition (m := m) t).rename Fin.castSucc (id : Fin m → Fin m)
  have right := (term_recognition (m := m) s).rename f (id : Fin m → Fin m)
  apply ((left.conj right).conj hR).existsNode.existsNode.congr
  intro tree nodes sets
  simp only [f, Function.comp_apply, Formula.liftRenaming_last, Formula.liftRenaming_castSucc,
    Fin.snoc_last, Fin.snoc_castSucc]
  simp

def equal_terms_recognition (t s : (language (Fin (b+1)) (Fin (a+1))).Term (Fin n)) :
    NumericRecognition (m := m) (fun tree nodes _ => termValue tree nodes t = termValue tree nodes s) := by
  apply binary_term_recognition t s (fun _ x y => x = y)
  exact NumericRecognition.equal (Fin.last n).castSucc (Fin.last (n+1))

def relation_terms_recognition {arity : Nat} (r : RelationSymbol (Fin (a+1)) arity)
    (args : Fin arity → (language (Fin (b+1)) (Fin (a+1))).Term (Fin n)) :
    NumericRecognition (m := m) (fun tree nodes _ =>
      relationValue tree r (fun i => termValue tree nodes (args i))) := by
  cases r with
  | label letter =>
    apply unary_term_recognition (args 0) (fun tree x => tree x = letter)
    exact NumericRecognition.label letter (Fin.last n)
  | child =>
    apply binary_term_recognition (args 0) (args 1) (fun _ x y => ∃ b : (Fin (b+1)), y = x ++ [b])
    exact NumericRecognition.child (Fin.last n).castSucc (Fin.last (n+1))

end DistributedSynthesis.MSO.Tree.Numeric
