/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.UniversalThreads
import DistributedSynthesis.Library.Automata.PitermanComputable

/-! # Executable universal-thread determinization

The existing violation Büchi construction with explicit finite enumeration and
deciders, followed by the existing executable Piterman compiler.
-/
namespace DistributedSynthesis.FiniteThreadSystem.Computable

variable {L : Type*} (S : FiniteThreadSystem L)

def priorityRange : Finset Nat := Finset.image S.priority Finset.univ
abbrev GuessState := S.State × Option {p : Nat // p ∈ priorityRange S}

def natEvenDecidable (p : Nat) : Decidable (DetParityAutomaton.NatEven p) :=
  decidable_of_iff (p % 2 = 0) (by
    unfold DetParityAutomaton.NatEven
    constructor
    · intro h; exact ⟨p / 2, by omega⟩
    · rintro ⟨k,rfl⟩; omega)

/-- Executable data adapter for the existing violation automaton. The following
`buchi_eq` theorem identifies the complete record with the semantic construction. -/
def buchi : NondetBuchiAutomaton L where
  State := GuessState S
  stateFinite := inferInstance
  initial := (S.initial, none)
  step := fun source letter target =>
    (∃ r : S.Resolution, target.1 = S.step source.1 letter r) ∧
      ((source.2 = none ∧
        (target.2 = none ∨ ∃ t : {p : Nat // p ∈ priorityRange S},
          target.2 = some t ∧ ¬ DetParityAutomaton.NatEven t.1 ∧ t.1 ≤ S.priority target.1)) ∨
       (∃ t : {p : Nat // p ∈ priorityRange S},
         source.2 = some t ∧ target.2 = some t ∧ t.1 ≤ S.priority target.1))
  accepting := fun state => ∃ t : {p : Nat // p ∈ priorityRange S},
    state.2 = some t ∧ S.priority state.1 = t.1

theorem buchi_eq : buchi S = S.violationBuchi := rfl

variable [Fintype S.Resolution] [DecidableEq S.State]

instance stateDecidableEq : DecidableEq (buchi S).State :=
  inferInstanceAs (DecidableEq (GuessState S))

def stepDecidable : ∀ q a r, Decidable ((buchi S).step q a r) := by
  intro q a r
  letI := natEvenDecidable
  change Decidable (_ ∧ _)
  infer_instance

@[reducible] def acceptingDecidable : DecidablePred (buchi S).accepting := by
  intro q
  change Decidable (∃ t : {p : Nat // p ∈ priorityRange S}, _)
  infer_instance

def universalDPA : DetParityAutomaton L :=
  (NondetBuchiAutomaton.Piterman.Computable.automatonData (buchi S)
    (stepDecidable S) (acceptingDecidable S)).shiftPriority 1

instance universalStateDecidableEq : DecidableEq (universalDPA S).State :=
  NondetBuchiAutomaton.Piterman.Computable.stateDecidableEq (buchi S)

theorem universalDPA_eq : universalDPA S = S.universalRunDPA := by
  unfold universalDPA FiniteThreadSystem.universalRunDPA
  rw [NondetBuchiAutomaton.Piterman.Computable.automatonData_eq]
  simp only [NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler,
    NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompilation,
    NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompilationOfCompleteness]
  congr 2

theorem universalDPA_correct (word : OmegaWord L) :
    (universalDPA S).Accepts word ↔
      ∀ q, S.IsRun word q → NatSeqMinEvenParity (fun n => S.priority (q n)) := by
  rw [universalDPA_eq]
  exact S.universalRunDPA_accepts_iff word

end DistributedSynthesis.FiniteThreadSystem.Computable
