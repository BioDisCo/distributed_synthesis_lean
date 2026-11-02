/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.Tree

/-! # Local label tests on full trees -/
namespace DistributedSynthesis.RunParityTreeAutomaton

variable {Branch Alphabet : Type*}

/-- Require a predicate at every node. Local failure forbids a transition. -/
def localTest (predicate : Alphabet → Prop) : RunParityTreeAutomaton Branch Alphabet where
  State := Unit
  stateFinite := inferInstance
  initial := ()
  delta _ label _ := predicate label
  priority _ := 0

@[simp] theorem localTest_accepts_iff (predicate : Alphabet → Prop)
    (tree : LabeledTree Branch Alphabet) :
    (localTest predicate : RunParityTreeAutomaton Branch Alphabet).acceptsTree tree ↔
      ∀ node, predicate (tree node) := by
  constructor
  · rintro ⟨_, ⟨_, transition⟩, _⟩
    exact transition
  · intro allNodes
    refine ⟨fun _ => (), ⟨rfl, allNodes⟩, fun _ => ?_⟩
    exact ⟨0, ⟨0, rfl⟩, fun n => ⟨n, le_rfl, rfl⟩, fun _ _ => Nat.zero_le _⟩

instance localTestDeltaDecidable (predicate : Alphabet → Prop) [DecidablePred predicate]
    (q : (localTest predicate : RunParityTreeAutomaton Branch Alphabet).State)
    (label : Alphabet) (next : Branch → Unit) :
    Decidable ((localTest predicate : RunParityTreeAutomaton Branch Alphabet).delta q label next) :=
  inferInstanceAs (Decidable (predicate label))


/-- A label predicate checked only at the root. -/
def rootTest (predicate : Alphabet → Prop) : RunParityTreeAutomaton Branch Alphabet where
  State := Bool
  stateFinite := inferInstance
  initial := true
  delta q a next := (q = true → predicate a) ∧ ∀ b, next b = false
  priority _ := 0

theorem rootTest_accepts_iff (predicate : Alphabet → Prop)
    (tree : LabeledTree Branch Alphabet) :
    (rootTest predicate).acceptsTree tree ↔ predicate (tree []) := by
  classical
  constructor
  · rintro ⟨run, ⟨initial, transitions⟩, _⟩
    exact (transitions []).1 initial
  · intro root
    refine ⟨fun node => decide (node = []), ⟨by simp [rootTest], ?_⟩, fun _ => ?_⟩
    · intro node
      refine ⟨?_, fun b => ?_⟩
      · intro h
        have hn : node = [] := of_decide_eq_true h
        simpa only [hn] using root
      · simp
    · exact ⟨0, ⟨0,rfl⟩, fun n => ⟨n,le_rfl,rfl⟩, fun _ _ => Nat.zero_le _⟩

/-- The target marker at a child equals the source marker at its designated parent. -/
def edgeTest [DecidableEq Branch] (source target : Alphabet → Bool) (direction : Branch) :
    RunParityTreeAutomaton Branch Alphabet where
  State := Bool
  stateFinite := inferInstance
  initial := false
  delta q a next := target a = q ∧ ∀ b, next b = (source a && decide (b = direction))
  priority _ := 0

theorem edgeTest_accepts_iff [DecidableEq Branch] (source target : Alphabet → Bool)
    (direction : Branch) (tree : LabeledTree Branch Alphabet) :
    (edgeTest source target direction).acceptsTree tree ↔
      target (tree []) = false ∧ ∀ node b,
        target (tree (node ++ [b])) = (source (tree node) && decide (b = direction)) := by
  constructor
  · rintro ⟨run, ⟨initial, transitions⟩, _⟩
    exact ⟨(transitions []).1.trans initial,
      fun node b => (transitions (node ++ [b])).1.trans ((transitions node).2 b)⟩
  · rintro ⟨initial, transitions⟩
    refine ⟨fun node => target (tree node), ⟨initial, fun node => ⟨rfl, transitions node⟩⟩, fun _ => ?_⟩
    exact ⟨0, ⟨0,rfl⟩, fun n => ⟨n,le_rfl,rfl⟩, fun _ _ => Nat.zero_le _⟩
end DistributedSynthesis.RunParityTreeAutomaton
