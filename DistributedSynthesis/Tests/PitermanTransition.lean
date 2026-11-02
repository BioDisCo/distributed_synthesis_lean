/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Tests.PitermanAllocation

/-! Exercise stages 3--6 and complete transitions without enumerating the enormous
raw-state carrier. These are runtime checks, not language-equivalence assertions. -/
namespace DistributedSynthesis.Tests.PitermanTransition
open NondetBuchiAutomaton.Piterman
open DistributedSynthesis.Tests.NoDirectJournal DistributedSynthesis.Tests.PitermanAllocation

/-- info: [true, false] -/
#guard_msgs in
#eval [@decide _ (FiniteOrbits.reachableDecidable (fun b : Bool => !b) false true),
  @decide _ (FiniteOrbits.reachableDecidable (fun _ : Fin 3 => 0) 0 2)]

def duplicates : CompactTreeData toggle where
  active _ := true
  name node := node
  parent node := if node.val = 3 then ⟨2, by decide⟩ else root toggle
  label node := if node.val = 1 then {true} else {false, true}
  e := sentinel toggle
  f := sentinel toggle

def pruned := Computable.stage3 toggle duplicates

/-- info: [(true, true), (false, true), (true, false), (true, false)] -/
#guard_msgs in
#eval (List.finRange 4).map fun node =>
  (decide (false ∈ pruned.label node), decide (true ∈ pruned.label node))

def green := Computable.stage4 toggle pruned

/-- info: ([true, false, false, false], 0) -/
#guard_msgs in
#eval ((List.finRange 4).map green.active, green.f.val)

/-- info: 3 -/
#guard_msgs in
#eval (Computable.greenRemovedNodes toggle pruned).card

/-- info: 1 -/
#guard_msgs in
#eval (Computable.stage5 toggle green (Computable.greenRemovedNodes toggle pruned)).e.val

def sparseNames : CompactTreeData toggle where
  active node := decide (node.val = 0 ∨ node.val = 3)
  name node := node
  parent _ := root toggle
  label node := if node.val = 0 ∨ node.val = 3 then {false} else ∅
  e := sentinel toggle
  f := sentinel toggle

/-- info: 1 -/
#guard_msgs in
#eval ((Computable.stage6 toggle sparseNames {⟨1, by decide⟩, ⟨2, by decide⟩}).name
  ⟨3, by decide⟩).val

/-- info: [2, 2] -/
#guard_msgs in
#eval [(Computable.minBoundedNameOf toggle sparseNames ∅).val,
  (Computable.minBoundedNameOf toggle sparseNames {⟨3, by decide⟩}).val]

def next := Computable.liveTransition toggle toggleDec toggleAccept
  ⟨CompactTreeData.initial toggle, CompactTreeData.initial_wellFormed toggle⟩ true

/-- info: some (true, 1, 0) -/
#guard_msgs in
#eval next.map fun state =>
  (@decide _ (Computable.wellFormedDecidable toggle state.val), state.val.e.val, state.val.f.val)

/-- info: false -/
#guard_msgs in
#eval @decide _ (Computable.wellFormedDecidable toggle duplicates)

def dead : NondetBuchiAutomaton.{0, 0} Bool where
  State := Bool
  stateFinite := inferInstance
  initial := false
  step _ _ _ := False
  accepting _ := False

instance : DecidableEq dead.State := inferInstanceAs (DecidableEq Bool)

def deadStep : ∀ q a q', Decidable (dead.step q a q') := fun _ _ _ => isFalse id
@[reducible] def deadAccept : DecidablePred dead.accepting := fun _ => isFalse id

/-- info: true -/
#guard_msgs in
#eval (Computable.liveTransition dead deadStep deadAccept
  ⟨CompactTreeData.initial dead, CompactTreeData.initial_wellFormed dead⟩ true).isNone

end DistributedSynthesis.Tests.PitermanTransition
