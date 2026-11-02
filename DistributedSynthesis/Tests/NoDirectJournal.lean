/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.NoDirectJournal
import DistributedSynthesis.Library.Automata.PitermanComputable

/-! Public semantic boundary and actual evaluation of the executable operations. -/
namespace DistributedSynthesis.Tests.NoDirectJournal

example {In₁ In₂ Out₁ Out₂ : Type}
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    (A : DetParityAutomaton.{0, 0} (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    [DecidableEq A.State] :
    (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        NoDirectReversalSequence env → A.Accepts (execution σ env)) ↔
      ∃ tree, (DistributedSynthesis.NoDirectJournal.journal A).acceptsTree tree :=
  DistributedSynthesis.NoDirectJournal.realizable_iff_nonempty A

def objective : DetParityAutomaton.{0, 0} (RoundRecord Unit Unit Graph Bool Bool) where
  State := Bool
  stateFinite := inferInstance
  initial := false
  step q _ := !q
  priority q := if q then 3 else 0

/-- info: 8 -/
#guard_msgs in
#eval JournalCompilation.shift objective

def toggle : NondetBuchiAutomaton.{0, 0} Bool where
  State := Bool
  stateFinite := inferInstance
  initial := false
  step q a q' := q' = if a then !q else q
  accepting q := q = true

instance : DecidableEq toggle.State := inferInstanceAs (DecidableEq Bool)

def toggleDec : ∀ q a q', Decidable (toggle.step q a q') :=
  fun _ _ _ => inferInstanceAs (Decidable (_ = _))

open NondetBuchiAutomaton.Piterman

example : Computable.stepImage toggle toggleDec true {false} = {true} := by decide
example : Computable.stepImage toggle toggleDec false {false} = {false} := by decide
example : Computable.stepImage toggle toggleDec true ∅ = ∅ := by decide
example : Computable.stepImage toggle toggleDec true {false, true} = {false, true} := by decide

def seed : CompactTreeData toggle where
  active n := n == root toggle
  name _ := root toggle
  parent _ := root toggle
  label _ := {false}
  e := sentinel toggle
  f := sentinel toggle

/-- info: true -/
#guard_msgs in
#eval decide (true ∈ (Computable.stage1 toggle toggleDec seed true).label (root toggle))

/-- info: false -/
#guard_msgs in
#eval decide (false ∈ (Computable.stage1 toggle toggleDec seed true).label (root toggle))

end DistributedSynthesis.Tests.NoDirectJournal
