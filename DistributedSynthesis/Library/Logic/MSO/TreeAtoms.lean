/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Compilation

/-! # Root and directional successor atoms

These finite automata test root membership and the directional parent-child
relation on the existing singleton individual markers.
-/
namespace DistributedSynthesis.MSO.Tree
variable {Branch Alphabet : Type*} {n m : Nat}

def rootAutomaton (x : Fin n) : RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m) :=
  .rootTest (fun letter => letter.2.1 x = true)

theorem rootAutomaton_correct (x : Fin n) :
    Represents (rootAutomaton (Branch := Branch) (Alphabet := Alphabet) (m := m) x) (root x) := by
  intro tree nodes sets
  classical
  rw [rootAutomaton, RunParityTreeAutomaton.rootTest_accepts_iff]
  change decide ([] = nodes x) = true ↔ nodes x = []
  simp only [decide_eq_true_eq]
  exact eq_comm

noncomputable def successorAutomaton (direction : Branch) (x y : Fin n) :
    RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m) := by
  classical
  exact .edgeTest (fun letter => letter.2.1 x) (fun letter => letter.2.1 y) direction

theorem successorAutomaton_correct (direction : Branch) (x y : Fin n) :
    Represents (successorAutomaton (Alphabet := Alphabet) (m := m) direction x y) (successor direction x y) := by
  intro tree nodes sets
  classical
  rw [successorAutomaton, RunParityTreeAutomaton.edgeTest_accepts_iff]
  change (decide ([] = nodes y) = false ∧ ∀ node b,
    decide (node ++ [b] = nodes y) = (decide (node = nodes x) && decide (b = direction))) ↔
    nodes y = nodes x ++ [direction]
  constructor
  · rintro ⟨_, transitions⟩
    have h := transitions (nodes x) direction
    have equal : nodes x ++ [direction] = nodes y := by simpa using h
    exact equal.symm
  · intro equation
    constructor
    · simp [equation]
    · intro node b
      rw [equation]
      have same : (node ++ [b] = nodes x ++ [direction]) ↔ node = nodes x ∧ b = direction := by
        simpa only [List.concat_eq_append] using (List.concat_inj (l := node) (l' := nodes x) (a := b) (b := direction))
      simp [same]
variable [Fintype Branch] [Nonempty Branch] [Fintype Alphabet]

/-- The child relation is the finite disjunction of directional successors. -/
noncomputable def childAutomaton (x y : Fin n) :
    RunParityTreeAutomaton Branch (ValuationLabel Alphabet n m) := by
  classical
  exact TreeBoolean.finiteUnion (Finset.univ.toList.map
    (fun direction : Branch => successorAutomaton direction x y))

theorem childAutomaton_correct (x y : Fin n) :
    Represents (childAutomaton (Branch := Branch) (Alphabet := Alphabet) (m := m) x y) (child x y) := by
  intro tree nodes sets
  classical
  simp [childAutomaton, TreeBoolean.finiteUnion_accepts_iff]
  exact exists_congr (fun direction => successorAutomaton_correct direction x y tree nodes sets)

end DistributedSynthesis.MSO.Tree
