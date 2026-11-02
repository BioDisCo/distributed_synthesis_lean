/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Recognizability

/-! # Tree terms from Mathlib's first-order syntax

Terms are not replaced by a second syntax. Their graphs are recognized by
introducing singleton-marked witnesses for successive function applications.
-/
namespace DistributedSynthesis.MSO.Tree

variable {Branch Alphabet : Type*} {n m k : Nat}

def termValue (tree : LabeledTree Branch Alphabet) (nodes : Fin n → TreeNode Branch)
    (t : (language Branch Alphabet).Term (Fin n)) : TreeNode Branch :=
  @FirstOrder.Language.Term.realize _ _ (treeStructure Branch Alphabet tree) _ nodes t

@[simp] theorem termValue_var (tree : LabeledTree Branch Alphabet)
    (nodes : Fin n → TreeNode Branch) (i : Fin n) : termValue tree nodes (.var i) = nodes i := rfl

@[simp] theorem termValue_root (tree : LabeledTree Branch Alphabet)
    (nodes : Fin n → TreeNode Branch) (args : Fin 0 → (language Branch Alphabet).Term (Fin n)) :
    termValue tree nodes (.func .root args) = [] := rfl

@[simp] theorem termValue_successor (tree : LabeledTree Branch Alphabet)
    (nodes : Fin n → TreeNode Branch) (direction : Branch)
    (args : Fin 1 → (language Branch Alphabet).Term (Fin n)) :
    termValue tree nodes (.func (.successor direction) args) = termValue tree nodes (args 0) ++ [direction] := rfl

@[simp] theorem termValue_relabel (tree : LabeledTree Branch Alphabet)
    (nodes : Fin k → TreeNode Branch) (t : (language Branch Alphabet).Term (Fin n))
    (f : Fin n → Fin k) : termValue tree nodes (t.relabel f) = termValue tree (nodes ∘ f) t := by
  letI := treeStructure Branch Alphabet tree
  apply FirstOrder.Language.Term.realize_relabel

variable [Fintype Branch] [Nonempty Branch] [Fintype Alphabet]

omit [Fintype Alphabet] in
/-- The newest individual variable denotes the value of the given term. -/
theorem term_recognizable (t : (language Branch Alphabet).Term (Fin n)) :
    Recognizable (m := m) (fun tree nodes _ =>
      nodes (Fin.last n) = termValue tree (fun i => nodes i.castSucc) t) := by
  induction t with
  | var i =>
    exact ⟨equalityAutomaton (Fin.last n) i.castSucc,
      equalityAutomaton_correct (Fin.last n) i.castSucc⟩
  | func f args ih =>
    cases f with
    | root => exact ⟨rootAutomaton (Fin.last n), rootAutomaton_correct (Fin.last n)⟩
    | successor direction =>
      let f : Fin (n+1) → Fin (n+2) := Formula.liftRenaming Fin.castSucc
      have argument := (ih 0).rename f (id : Fin m → Fin m)
      have edge : Recognizable (m := m) (fun (tree : LabeledTree Branch Alphabet) nodes _ =>
          nodes (Fin.last n).castSucc = nodes (Fin.last (n+1)) ++ [direction]) :=
        ⟨successorAutomaton direction (Fin.last (n+1)) (Fin.last n).castSucc,
          successorAutomaton_correct direction (Fin.last (n+1)) (Fin.last n).castSucc⟩
      apply (argument.conj edge).existsNode.congr
      intro tree nodes sets
      simp only [f, Function.comp_apply, Formula.liftRenaming_last, Formula.liftRenaming_castSucc,
        Fin.snoc_last, Fin.snoc_castSucc, termValue_successor]
      simp

omit [Fintype Alphabet] in
/-- Lift a recognizable unary relation from marked nodes to arbitrary terms. -/
theorem unary_term_recognizable (t : (language Branch Alphabet).Term (Fin n))
    (R : LabeledTree Branch Alphabet → TreeNode Branch → Prop)
    (hR : Recognizable (m := m) (fun tree nodes _ => R tree (nodes (Fin.last n)))) :
    Recognizable (m := m) (fun tree nodes _ => R tree (termValue tree nodes t)) := by
  apply ((term_recognizable t).conj hR).existsNode.congr
  intro tree nodes sets
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  simp

omit [Fintype Alphabet] in
/-- Lift a recognizable binary relation using two singleton-marked witnesses. -/
theorem binary_term_recognizable (t s : (language Branch Alphabet).Term (Fin n))
    (R : LabeledTree Branch Alphabet → TreeNode Branch → TreeNode Branch → Prop)
    (hR : Recognizable (m := m) (fun tree nodes _ =>
      R tree (nodes (Fin.last n).castSucc) (nodes (Fin.last (n+1))))) :
    Recognizable (m := m) (fun tree nodes _ => R tree (termValue tree nodes t) (termValue tree nodes s)) := by
  let f : Fin (n+1) → Fin (n+2) := Formula.liftRenaming Fin.castSucc
  have left := (term_recognizable (m := m) t).rename Fin.castSucc (id : Fin m → Fin m)
  have right := (term_recognizable (m := m) s).rename f (id : Fin m → Fin m)
  apply ((left.conj right).conj hR).existsNode.existsNode.congr
  intro tree nodes sets
  simp only [f, Function.comp_apply, Formula.liftRenaming_last, Formula.liftRenaming_castSucc,
    Fin.snoc_last, Fin.snoc_castSucc]
  simp

omit [Fintype Alphabet] in
theorem equal_terms_recognizable (t s : (language Branch Alphabet).Term (Fin n)) :
    Recognizable (m := m) (fun tree nodes _ => termValue tree nodes t = termValue tree nodes s) := by
  apply binary_term_recognizable t s (fun _ x y => x = y)
  exact ⟨equalityAutomaton (Fin.last n).castSucc (Fin.last (n+1)),
    equalityAutomaton_correct (Fin.last n).castSucc (Fin.last (n+1))⟩

def relationValue {arity : Nat} (tree : LabeledTree Branch Alphabet)
    (r : RelationSymbol Alphabet arity) (values : Fin arity → TreeNode Branch) : Prop :=
  @FirstOrder.Language.Structure.RelMap _ _ (treeStructure Branch Alphabet tree) _ r values

theorem relation_terms_recognizable {arity : Nat} (r : RelationSymbol Alphabet arity)
    (args : Fin arity → (language Branch Alphabet).Term (Fin n)) :
    Recognizable (m := m) (fun tree nodes _ =>
      relationValue tree r (fun i => termValue tree nodes (args i))) := by
  cases r with
  | label letter =>
    apply unary_term_recognizable (args 0) (fun tree x => tree x = letter)
    exact ⟨labelAutomaton letter (Fin.last n), labelAutomaton_correct letter (Fin.last n)⟩
  | child =>
    apply binary_term_recognizable (args 0) (args 1) (fun _ x y => ∃ b : Branch, y = x ++ [b])
    exact ⟨childAutomaton (Fin.last n).castSucc (Fin.last (n+1)),
      childAutomaton_correct (Fin.last n).castSucc (Fin.last (n+1))⟩

end DistributedSynthesis.MSO.Tree
