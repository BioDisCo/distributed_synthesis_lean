/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Tests.NoDirectJournal
import DistributedSynthesis.Library.Distributed.ThreadComputable

/-! Evaluation regressions for finite thread tests and deterministic allocation. -/
namespace DistributedSynthesis.Tests.PitermanAllocation
open NondetBuchiAutomaton.Piterman
open DistributedSynthesis.Tests.NoDirectJournal

@[reducible] def toggleAccept : DecidablePred toggle.accepting :=
  fun _ => inferInstanceAs (Decidable (_ = true))

def noTriggers := Computable.stage2Plan toggle toggleAccept
  (CompactTreeData.initial toggle) (CompactTreeData.initial_wellFormed toggle)

/-- info: 0 -/
#guard_msgs in
#eval (Computable.stage2Triggers toggle toggleAccept (CompactTreeData.initial toggle)).card

/-- info: true -/
#guard_msgs in
#eval (Computable.ownerOf toggle toggleAccept noTriggers (root toggle)).isNone

def twoTriggers : CompactTreeData toggle where
  active node := decide (node.val < 2)
  name node := node
  parent _ := root toggle
  label _ := {true}
  e := sentinel toggle
  f := sentinel toggle

def twoPlan : CompactTreeData.Stage2Plan toggle twoTriggers :=
  Computable.stage2PlanOfBounds toggle toggleAccept twoTriggers
    (by
      intro node hn
      change node.val < 2
      exact of_decide_eq_true hn)
    (by intro left right _ _ heq; exact heq)
    (by
      intro k hk _ j hj
      have hk' : k < 2 := hk
      refine ⟨⟨j, by omega⟩, ?_, rfl⟩
      simp [twoTriggers]
      omega)

/-- info: [(2, 2), (3, 3)] -/
#guard_msgs in
#eval (List.finRange 2).map fun i =>
  let node : Node toggle := ⟨i.val, by have := i.isLt; change _ < 4; omega⟩
  ((twoPlan.freshChild node).val, (twoPlan.freshName node).val)

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval (List.finRange 4).map fun node =>
  (Computable.stage2 toggle toggleAccept twoTriggers twoPlan).active node

/-- info: [0, 1] -/
#guard_msgs in
#eval [((Computable.stage2 toggle toggleAccept twoTriggers twoPlan).parent ⟨2, by decide⟩).val,
  ((Computable.stage2 toggle toggleAccept twoTriggers twoPlan).parent ⟨3, by decide⟩).val]

def allocatedTransition := Computable.transitionPlan toggle toggleDec toggleAccept
  (CompactTreeData.initial toggle) (CompactTreeData.initial_wellFormed toggle) true

/-- info: (1, 1) -/
#guard_msgs in
#eval ((allocatedTransition.stage2Plan.freshChild (root toggle)).val,
  (allocatedTransition.stage2Plan.freshName (root toggle)).val)

def threadMonitor : BlockRecordMonitor.{0, 0, 0, 0, 0} Bool Unit Unit Unit where
  State := Bool
  stateFinite := inferInstance
  initial := false
  step _ record := record.1.1
  priority q := if q then 1 else 0

instance : DecidableEq threadMonitor.State := inferInstanceAs (DecidableEq Bool)

def threadLetter : BlockRecordMonitor.ThreadLetter threadMonitor :=
  ((fun _ => (), fun _ _ => ()), ())

def oddTag : {p : Nat // p ∈ ThreadComputable.priorityRange threadMonitor} := ⟨1, by decide⟩
def evenTag : {p : Nat // p ∈ ThreadComputable.priorityRange threadMonitor} := ⟨0, by decide⟩

def stepTest (q q' : ThreadComputable.GuessState threadMonitor) : Bool :=
  @decide _ (ThreadComputable.stepDecidable threadMonitor q threadLetter q')

/-- info: [true, false, false, true] -/
#guard_msgs in
#eval [stepTest (false, none) (true, some oddTag),
  stepTest (false, none) (false, some evenTag),
  stepTest (true, some oddTag) (false, some oddTag),
  stepTest (true, some oddTag) (true, some oddTag)]

/-- info: [false, true, false] -/
#guard_msgs in
#eval [@decide _ (ThreadComputable.acceptingDecidable threadMonitor (true, none)),
  @decide _ (ThreadComputable.acceptingDecidable threadMonitor (true, some oddTag)),
  @decide _ (ThreadComputable.acceptingDecidable threadMonitor (false, some oddTag))]

end DistributedSynthesis.Tests.PitermanAllocation
