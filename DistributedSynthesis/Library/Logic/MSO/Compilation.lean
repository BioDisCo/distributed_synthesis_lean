/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Encoding
import DistributedSynthesis.Library.Automata.TreeLocal
import DistributedSynthesis.Library.Automata.TreeBoolean

/-! # Proved MSO translation steps

These are actual automaton constructions with correctness proofs, not assumed
closure certificates. They cover local atoms, Boolean connectives, and both set quantifiers.
The complete formula-to-automaton recursion, including individual quantifiers
and arbitrary embedded first-order formulas, is not asserted by this module.
-/
namespace DistributedSynthesis.MSO.Tree

variable {Branch Alphabet : Type*} {n m : Nat}

/-- Correctness on semantic valuations; individual markers are singletons and
set markers describe arbitrary subsets of the full tree. -/
def Represents (A : RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m))
    (φ : Formula (language Branch Alphabet) n m) : Prop :=
  ∀ tree nodes sets, A.acceptsTree (encode tree nodes sets) ↔ Realize tree φ nodes sets

/-- The false formula has no run. -/
def falseAutomaton : RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m) :=
  .localTest (fun _ => False)

theorem falseAutomaton_correct :
    Represents (falseAutomaton : RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m))
      .falsum := by
  intro tree nodes sets
  simp [falseAutomaton, Realize, Formula.Realize]

/-- Test node membership using the corresponding singleton marker. -/
def membershipAutomaton (x : Fin n) (X : Fin m) :
    RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m) :=
  .localTest (fun letter => letter.2.1 x = true → letter.2.2 X = true)

theorem membershipAutomaton_correct (x : Fin n) (X : Fin m) :
    Represents (membershipAutomaton (Branch := Branch) (Alphabet := Alphabet) x X) (.mem x X) := by
  intro tree nodes sets
  classical
  simp [membershipAutomaton, encode, Realize, Formula.Realize]

/-- Equality of individual variables is equality of their singleton markers. -/
def equalityAutomaton (x y : Fin n) :
    RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m) :=
  .localTest (fun letter => letter.2.1 x = letter.2.1 y)

theorem equalityAutomaton_correct (x y : Fin n) :
    Represents (equalityAutomaton (Branch := Branch) (Alphabet := Alphabet) (m := m) x y)
      (Formula.equal x y) := by
  intro tree nodes sets
  classical
  rw [equalityAutomaton, RunParityTreeAutomaton.localTest_accepts_iff]
  change (∀ node, decide (node = nodes x) = decide (node = nodes y)) ↔ nodes x = nodes y
  constructor
  · intro same
    simpa using same (nodes x)
  · intro same node
    rw [same]

/-- Test an input label at the marked node. -/
def labelAutomaton (letter : Alphabet) (x : Fin n) :
    RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m) :=
  .localTest (fun a => a.2.1 x = true → a.1 = letter)

theorem labelAutomaton_correct (letter : Alphabet) (x : Fin n) :
    Represents (labelAutomaton (Branch := Branch) (m := m) letter x) (label letter x) := by
  intro tree nodes sets
  classical
  simp [labelAutomaton, encode]

variable [Fintype Branch] [Nonempty Branch] [Fintype Alphabet]

/-- Negation uses the proved tree-complement construction. -/
theorem complement_represents
    (A : RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m))
    (φ : Formula (language Branch Alphabet) n m) (correct : Represents A φ) :
    Represents (TreeComplement.automaton A) φ.not := by
  intro tree nodes sets
  rw [TreeComplement.accepts_iff, correct]
  rfl

omit [Fintype Branch] [Nonempty Branch] [Fintype Alphabet] in
/-- Existential set quantification is coherent label projection. -/
theorem project_represents_exSet
    (A : RunParityTreeAutomaton Branch (ValuationLabel Alphabet n (m+1)))
    (φ : Formula (language Branch Alphabet) n (m+1)) (correct : Represents A φ) :
    Represents (A.project dropSet) φ.exSet :=
  project_exSet_correct φ A correct

omit [Nonempty Branch] [Fintype Alphabet] in
/-- Conjunction uses a product with a correct parity monitor. -/
theorem inter_represents
    (A B : RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m))
    (φ ψ : Formula (language Branch Alphabet) n m)
    (left : Represents A φ) (right : Represents B ψ) :
    Represents (TreeBoolean.inter A B) (φ.and ψ) := by
  intro tree nodes sets
  rw [TreeBoolean.inter_accepts_iff, left, right]
  letI := treeStructure Branch Alphabet tree
  exact (Formula.realize_and nodes sets φ ψ).symm

/-- Disjunction uses language union, not a branch-dependent choice of formula. -/
theorem union_represents
    (A B : RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m))
    (φ ψ : Formula (language Branch Alphabet) n m)
    (left : Represents A φ) (right : Represents B ψ) :
    Represents (TreeBoolean.union A B) (φ.or ψ) := by
  intro tree nodes sets
  rw [TreeBoolean.union_accepts_iff, left, right]
  letI := treeStructure Branch Alphabet tree
  exact (Formula.realize_or nodes sets φ ψ).symm

noncomputable def impAutomaton
    (A B : RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m)) :
    RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m) :=
  TreeBoolean.union (TreeComplement.automaton A) B

theorem impAutomaton_correct
    (A B : RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m))
    (φ ψ : Formula (language Branch Alphabet) n m)
    (left : Represents A φ) (right : Represents B ψ) :
    Represents (impAutomaton A B) (φ.imp ψ) := by
  intro tree nodes sets
  classical
  rw [impAutomaton, TreeBoolean.union_accepts_iff, TreeComplement.accepts_iff, left, right]
  change (¬ Realize tree φ nodes sets ∨ Realize tree ψ nodes sets) ↔
    (Realize tree φ nodes sets → Realize tree ψ nodes sets)
  tauto

/-- Universal set quantification by complement, projection, complement. -/
noncomputable def allSetAutomaton
    (A : RunParityTreeAutomaton Branch (ValuationLabel Alphabet n (m+1))) :
    RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m) :=
  TreeComplement.automaton ((TreeComplement.automaton A).project dropSet)

theorem allSetAutomaton_correct
    (A : RunParityTreeAutomaton Branch (ValuationLabel Alphabet n (m+1)))
    (φ : Formula (language Branch Alphabet) n (m+1)) (correct : Represents A φ) :
    Represents (allSetAutomaton A) (.allSet φ) := by
  intro tree nodes sets
  rw [allSetAutomaton, TreeComplement.accepts_iff,
    project_exSet_correct φ.not _ (complement_represents A φ correct)]
  letI := treeStructure Branch Alphabet tree
  change (¬ Formula.Realize φ.not.exSet nodes sets) ↔ Formula.Realize (.allSet φ) nodes sets
  simp

end DistributedSynthesis.MSO.Tree
