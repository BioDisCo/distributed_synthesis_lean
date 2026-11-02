/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.EffectiveRabin

/-! Executed finite-data checks and semantic regressions for the full compiler. -/
namespace DistributedSynthesis.Tests.MSOExecutable
open MSO MSO.Tree

-- These guards evaluate the procedures; they do not invoke classical deciders.
#guard Executable.satisfiable (Branch := Unit) (Alphabet := Unit) .falsum = false

#guard let A := Executable.compile (Branch := Bool) (Alphabet := Unit)
          (.mem (0 : Fin 1) (0 : Fin 1))
       @decide (A.toAutomaton.delta () ((),![true],![false]) (fun _ => ()))
         (A.deltaDecidable _ _ _) = false

#guard let A := Executable.compile (Branch := Bool) (Alphabet := Unit)
          (.mem (0 : Fin 1) (0 : Fin 1))
       @decide (A.toAutomaton.delta () ((),![true],![true]) (fun _ => ()))
         (A.deltaDecidable _ _ _) = true

-- The child transition must choose one successor, not mark every child.
#guard let A := Recognition.childData (Branch := Bool) (Alphabet := Unit) (m := 0)
          (0 : Fin 2) 1
       @decide (A.toAutomaton.delta false ((),![true,false],Fin.elim0) id)
         (A.deltaDecidable _ _ _) = true

#guard let A := Recognition.childData (Branch := Bool) (Alphabet := Unit) (m := 0)
          (0 : Fin 2) 1
       @decide (A.toAutomaton.delta false ((),![true,false],Fin.elim0) (fun _ => true))
         (A.deltaDecidable _ _ _) = false

private def allNodes : Formula (language Bool Unit) 0 1 := .allNode (.mem 0 0)

/-- Full, not weak, MSO: the satisfying set is the entire infinite domain. -/
example : Executable.satisfiable allNodes.exSet = true := by
  rw [Executable.satisfiable_correct]
  refine ⟨fun _ => (),?_⟩
  change Realize _ allNodes.exSet Fin.elim0 Fin.elim0
  simp only [Realize,Formula.realize_exSet]
  exact ⟨Set.univ,fun _ => Set.mem_univ _⟩

private def everySetInhabited : Sentence (language Bool Unit) :=
  .allSet ((Formula.mem 0 0).exNode)

/-- The decision theorem covers alternating quantifiers and the empty set. -/
example : Executable.satisfiable everySetInhabited = false := by
  rw [Bool.eq_false_iff]
  intro accepted
  obtain ⟨tree,h⟩ := (Executable.satisfiable_correct everySetInhabited).mp accepted
  change ∀ X : Set (TreeNode Bool), ¬ ∀ x : TreeNode Bool, ¬ x ∈ X at h
  exact h ∅ (fun _ => id)

/-- Validity is also decided, using the same full powerset semantics. -/
example : Executable.valid allNodes.exSet = true := by
  rw [Executable.valid_correct]
  intro tree
  change Realize tree allNodes.exSet Fin.elim0 Fin.elim0
  simp only [Realize,Formula.realize_exSet]
  exact ⟨Set.univ,fun _ => Set.mem_univ _⟩

private def noParent : Sentence (language Bool Unit) :=
  .firstOrder (.all (FirstOrder.Language.BoundedFormula.equal
    (.func (L := language Bool Unit) .root Fin.elim0)
    (.func (.successor false) ![.var (Sum.inr 0)])).not)

/-- Arbitrary embedded first-order quantifiers and function terms are compiled. -/
example : Executable.valid noParent = true := by
  rw [Executable.valid_correct]
  intro tree
  change ∀ x : TreeNode Bool, ¬ ([] : TreeNode Bool) = x ++ [false]
  intro x h
  have := congrArg List.length h
  simp at this

private def rejectAll : RunParityTreeAutomaton (Fin 1) (Fin 1) where
  State := Fin 1
  stateFinite := inferInstance
  initial := 0
  delta _ _ _ := False
  priority _ := 0

private instance : LinearOrder rejectAll.State := inferInstanceAs (LinearOrder (Fin 1))
private instance (q a next) : Decidable (rejectAll.delta q a next) := inferInstanceAs (Decidable False)

/-- Ordered finite enumeration in the reverse compiler preserves rejection,
including the case of even priorities but no legal transition. -/
example (tree : LabeledTree (Fin 1) (Fin 1)) :
    ¬ Satisfies tree (Automaton.Ordered.ofAutomaton rejectAll) := by
  rw [Automaton.Ordered.ofAutomaton_correct]
  rintro ⟨run,⟨_,step⟩,_⟩
  exact step []

example (tree : LabeledTree (Fin 1) (Fin 1)) :
    ¬ (Executable.sentenceAutomaton (Automaton.Ordered.ofAutomaton rejectAll)).Accepts tree := by
  rw [Executable.automaton_roundtrip]
  rintro ⟨run,⟨_,step⟩,_⟩
  exact step []

end DistributedSynthesis.Tests.MSOExecutable
