/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmUniversalThreadDeterminization

/-! # Executable finite data for the universal-thread Büchi automaton

All receiver-input and priority-threshold searches are finite. The construction
has the same state type, transitions, and acceptance as the semantic thread
automaton; explicit decision procedures make it suitable for determinization.
No predicate on infinite runs is tested by this constructor.
-/

namespace DistributedSynthesis.ThreadComputable

variable {RIn SIn ROut SOut : Type*}
variable (M : BlockRecordMonitor RIn SIn ROut SOut)

def priorityRange : Finset Nat := Finset.image M.priority Finset.univ

abbrev GuessState := M.State × Option {p : Nat // p ∈ priorityRange M}

def natEvenDecidable (p : Nat) : Decidable (DetParityAutomaton.NatEven p) :=
  decidable_of_iff (p % 2 = 0) (by
    unfold DetParityAutomaton.NatEven
    constructor
    · intro h
      exact ⟨p / 2, by omega⟩
    · rintro ⟨k, rfl⟩
      omega)

variable [Fintype RIn] [DecidableEq M.State]

def buchi : NondetBuchiAutomaton (BlockRecordMonitor.ThreadLetter M) where
  State := GuessState M
  stateFinite := inferInstance
  initial := (M.initial, none)
  step := fun source letter target =>
    (∃ r : RIn,
      target.1 = M.step source.1
        (narrowedRecord M letter.1 source.1 (r, letter.2))) ∧
      ((source.2 = none ∧
          (target.2 = none ∨
            ∃ t : {p : Nat // p ∈ priorityRange M},
              target.2 = some t ∧
                ¬ DetParityAutomaton.NatEven t.1 ∧
                  t.1 ≤ M.priority target.1)) ∨
        (∃ t : {p : Nat // p ∈ priorityRange M},
          source.2 = some t ∧ target.2 = some t ∧
            t.1 ≤ M.priority target.1))
  accepting := fun state =>
    ∃ t : {p : Nat // p ∈ priorityRange M},
      state.2 = some t ∧ M.priority state.1 = t.1

instance stateDecidableEq : DecidableEq (buchi M).State :=
  inferInstanceAs (DecidableEq (GuessState M))

def stepDecidable : ∀ q a q', Decidable ((buchi M).step q a q') := by
  intro q a q'
  letI : ∀ p, Decidable (DetParityAutomaton.NatEven p) := natEvenDecidable
  change Decidable ((_ ∧ _) : Prop)
  infer_instance

@[reducible] def acceptingDecidable : DecidablePred (buchi M).accepting := by
  intro q
  change Decidable (∃ t : {p : Nat // p ∈ priorityRange M}, _)
  infer_instance

omit [Fintype RIn] [DecidableEq M.State] in
/-- Only the implementation of finite enumeration and decision procedures changes. -/
theorem buchi_eq : buchi M = M.threadBuchi := rfl

omit [Fintype RIn] [DecidableEq M.State] in
theorem accepts_iff (word : OmegaWord (BlockRecordMonitor.ThreadLetter M)) :
    (buchi M).Accepts word ↔ M.threadBuchi.Accepts word := Iff.rfl

end DistributedSynthesis.ThreadComputable
