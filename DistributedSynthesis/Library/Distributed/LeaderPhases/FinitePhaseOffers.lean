/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Computability.DFA
import Mathlib.Data.Finset.Union
import Mathlib.Tactic

/-! Exact finite offers of a fixed finite phase controller. The search bound
concerns reachability of its full state, not the duration of physical phases.
In particular, this file does not identify histories at different depths. -/
namespace Characterisation

section Reachability
variable {State Input : Type} [Fintype State]

/-- Every reachable state has a short witness. We remove a repeated-state
loop using Mathlib's DFA splitting lemma; no strategy is changed. -/
theorem finitePhase_short_witness (step : State → Input → State) (initial : State)
    (word : List Input) :
    ∃ short : List Input, short.length < Fintype.card State ∧
      short.foldl step initial = word.foldl step initial := by
  let machine : DFA Input State := ⟨step, initial, Set.univ⟩
  have aux : ∀ n, ∀ w : List Input, w.length = n →
      ∃ short : List Input, short.length < Fintype.card State ∧
        short.foldl step initial = w.foldl step initial := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw
      by_cases small : w.length < Fintype.card State
      · exact ⟨w, small, rfl⟩
      obtain ⟨q, a, b, c, split, _, nonempty, ha, _, hc⟩ :=
        machine.evalFrom_split (s := initial) (Nat.le_of_not_gt small) rfl
      have shorter : (a ++ c).length < n := by
        have positive : 0 < b.length := List.length_pos_iff.mpr nonempty
        simp only [split, List.length_append] at hw
        simp only [List.length_append]
        omega
      obtain ⟨short, bound, same⟩ := ih (a ++ c).length shorter (a ++ c) rfl
      refine ⟨short, bound, same.trans ?_⟩
      change machine.evalFrom initial (a ++ c) = machine.evalFrom initial w
      rw [machine.evalFrom_of_append, ha]
      exact hc
  exact aux word.length word rfl

end Reachability

section Offers
variable {State Input Outcome : Type}
variable [Fintype State] [Fintype Input] [DecidableEq Outcome]

/-- Enumerate complete outcomes at all reachable states and current inputs.
The outcome type may itself encode a whole jointly compatible handover. -/
def finitePhaseOffers (step : State → Input → State) (initial : State)
    (collect : State → Input → Finset Outcome) : Finset Outcome :=
  Finset.univ.biUnion fun n : Fin (Fintype.card State) =>
    Finset.univ.biUnion fun word : Fin n.val → Input =>
      Finset.univ.biUnion fun input : Input =>
        collect ((List.ofFn word).foldl step initial) input

/-- Soundness and completeness use one common word for each whole outcome,
not separate witnesses for its target slots. -/
theorem mem_finitePhaseOffers_iff (step : State → Input → State) (initial : State)
    (collect : State → Input → Finset Outcome) (outcome : Outcome) :
    outcome ∈ finitePhaseOffers step initial collect ↔
      ∃ word : List Input, ∃ input, outcome ∈ collect (word.foldl step initial) input := by
  simp only [finitePhaseOffers, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, word, input, offered⟩
    exact ⟨List.ofFn word, input, offered⟩
  · rintro ⟨word, input, offered⟩
    obtain ⟨short, bound, same⟩ := finitePhase_short_witness step initial word
    refine ⟨⟨short.length, bound⟩, short.get, input, ?_⟩
    simpa only [List.ofFn_get, same] using offered

/-- An executable offer test, relative to the supplied finite state table
and collector. No choice of a winning strategy is used in this definition. -/
def finitePhaseOffersTest (step : State → Input → State) (initial : State)
    (collect : State → Input → Finset Outcome) (outcome : Outcome) : Bool :=
  decide (outcome ∈ finitePhaseOffers step initial collect)

theorem finitePhaseOffersTest_correct (step : State → Input → State) (initial : State)
    (collect : State → Input → Finset Outcome) (outcome : Outcome) :
    finitePhaseOffersTest step initial collect outcome = true ↔
      ∃ word : List Input, ∃ input, outcome ∈ collect (word.foldl step initial) input := by
  simp only [finitePhaseOffersTest, decide_eq_true_eq, mem_finitePhaseOffers_iff]

end Offers
end Characterisation
