/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.MiyanoHayashiComputable

namespace DistributedSynthesis.Tests.MiyanoHayashiComputable
open AlternatingParityAutomaton.MiyanoHayashi

def objective : AlternatingParityAutomaton (Fin 5) where
  State := Bool
  stateFinite := inferInstance
  initial := false
  step := fun q letter => match letter.val with
    | 0 => .falsum
    | 1 => .verum
    | 2 => .atom q
    | 3 => .conj (.atom false) (.atom true)
    | _ => .disj (.atom false) (.atom true)
  priority := fun q => if q then 0 else 1

local instance : DecidableEq objective.State := inferInstanceAs (DecidableEq Bool)

def testStep (frontier pending : Finset Bool) (letter : Fin 5)
    (frontier' pending' : Finset Bool) : Bool :=
  @decide _ (Computable.stepDecidable objective ⟨frontier, pending⟩ letter ⟨frontier', pending'⟩)

-- False rejects; true permits the empty support but forbids extraneous states.
#guard !testStep {false} ∅ 0 ∅ ∅
#guard testStep {false} ∅ 1 ∅ ∅
#guard !testStep {false} ∅ 1 {true} ∅

-- Atoms and conjunction retain all mandatory nonaccepting obligations.
#guard testStep {false} ∅ 2 {false} {false}
#guard !testStep {false} ∅ 2 {true} ∅
#guard testStep {false} ∅ 3 {false, true} {false}
#guard !testStep {false} ∅ 3 {false} {false}

-- Disjunction permits either singleton and their union, but not the empty set.
#guard testStep {false} ∅ 4 {false} {false}
#guard testStep {false} ∅ 4 {true} ∅
#guard testStep {false} ∅ 4 {false, true} {false}
#guard !testStep {false} ∅ 4 ∅ ∅

-- The pending update MUST use the same support as the frontier update.
#guard !testStep {false} {false} 4 {false} ∅
#guard testStep {false} {false} 4 {true} ∅
#guard testStep {false, true} {true} 2 {false, true} ∅

-- Empty frontiers and out-of-frontier pending states are handled literally.
#guard testStep ∅ ∅ 0 ∅ ∅
#guard testStep ∅ {false} 0 ∅ ∅

def stateCount : Nat :=
  letI := Computable.stateFintype objective
  Fintype.card (BuchiState objective)
#guard stateCount = 16

example (word : OmegaWord (Fin 5)) :
    (Computable.buchi objective).Accepts word ↔ objective.Accepts word :=
  Computable.accepts_iff objective (by intro q; cases q <;> simp [objective]) word

end DistributedSynthesis.Tests.MiyanoHayashiComputable
