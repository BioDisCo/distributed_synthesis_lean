/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.PrimitiveRecursive

/-! Numeric effectiveness and semantic regressions for full MSO. -/
namespace DistributedSynthesis.Tests.MSOPrimitiveRecursive
open MSO MSO.Tree

example : Nat.Primrec Numeric.compileNat := Numeric.compileNat_primrec
example : Nat.Primrec Numeric.satisfiableNat := Numeric.satisfiableNat_primrec
example : Nat.Primrec Numeric.validNat := Numeric.validNat_primrec

-- Empty alphabets: there is no labelled full tree, independently of the code.
#guard Numeric.satisfiable (1,0,[]) = false
#guard Numeric.valid (1,0,[]) = true

-- A small actual evaluation of the numeric automaton and finite-policy solver.
#guard Numeric.satisfiable (Numeric.sentenceInput
  (.falsum : Sentence (language (Fin 1) (Fin 1)))) = false

-- Check that singleton search cannot stop without a marker and chooses one child.
#guard NumericAtoms.condition (2,(0,1,0),7,0,0,0) 1 0 [1,0]
#guard !decide (NumericAtoms.condition (2,(0,1,0),7,0,0,0) 1 0 [1,1])

private def allNodes : Formula (language (Fin 2) (Fin 1)) 0 1 := .allNode (.mem 0 0)

/-- The witness is the entire infinite tree domain, not a finite set. -/
example : Numeric.satisfiable (Numeric.sentenceInput allNodes.exSet) = true := by
  rw [Numeric.satisfiable_correct]
  refine ⟨fun _ => 0, ?_⟩
  change Realize _ allNodes.exSet Fin.elim0 Fin.elim0
  simp only [Realize, Formula.realize_exSet]
  exact ⟨Set.univ,fun _ => Set.mem_univ _⟩

example : Numeric.validNat (Encodable.encode (Numeric.sentenceInput allNodes.exSet)) =
    Encodable.encode true := by
  rw [Numeric.validNat_correct]
  intro tree
  change Realize tree allNodes.exSet Fin.elim0 Fin.elim0
  simp only [Realize, Formula.realize_exSet]
  exact ⟨Set.univ,fun _ => Set.mem_univ _⟩

private def everySetInhabited : Sentence (language (Fin 2) (Fin 1)) :=
  .allSet ((Formula.mem 0 0).exNode)

/-- Alternating quantifiers must include the empty set. -/
example : Numeric.satisfiable (Numeric.sentenceInput everySetInhabited) = false := by
  rw [Bool.eq_false_iff]
  intro accepted
  obtain ⟨tree,h⟩ := (Numeric.satisfiable_correct everySetInhabited).mp accepted
  change ∀ X : Set (TreeNode (Fin 2)), ¬ ∀ x : TreeNode (Fin 2), ¬ x ∈ X at h
  exact h ∅ (fun _ => id)

private def noParent : Sentence (language (Fin 2) (Fin 1)) :=
  .firstOrder (.all (FirstOrder.Language.BoundedFormula.equal
    (.func (L := language (Fin 2) (Fin 1)) .root Fin.elim0)
    (.func (.successor 0) ![.var (Sum.inr 0)])).not)

/-- Embedded first-order binders and function terms use the same numeric path. -/
example : Numeric.valid (Numeric.sentenceInput noParent) = true := by
  rw [Numeric.valid_correct]
  intro tree
  change ∀ x : TreeNode (Fin 2), ¬ ([] : TreeNode (Fin 2)) = x ++ [0]
  intro x h
  have := congrArg List.length h
  simp at this

example (φ : Sentence (language (Fin 2) (Fin 0))) :
    Numeric.satisfiableNat (Encodable.encode (Numeric.sentenceInput φ)) = Encodable.encode false := by
  rw [Numeric.satisfiableNat_encode]
  rfl

end DistributedSynthesis.Tests.MSOPrimitiveRecursive
