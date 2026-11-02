/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.PitermanTransition
import Mathlib.Data.Finset.Sort

/-! # Executable finite allocation and the first two Piterman stages -/

namespace DistributedSynthesis.NondetBuchiAutomaton.Piterman.Computable
open CompactTreeData
variable {Alphabet : Type*} (A : NondetBuchiAutomaton Alphabet)
variable [DecidableEq A.State]

/-- Finite successor search using the supplied transition decision procedure. -/
def stepImage (decStep : ∀ q a q', Decidable (A.step q a q'))
    (letter : Alphabet) (states : Finset A.State) : Finset A.State :=
  letI := decStep
  Finset.univ.filter fun next => ∃ state, state ∈ states ∧ A.step state letter next

theorem stepImage_eq (decStep : ∀ q a q', Decidable (A.step q a q'))
    (letter : Alphabet) (states : Finset A.State) :
    stepImage A decStep letter states = CompactTreeData.stepImage A letter states := by
  classical
  ext next
  simp [stepImage, CompactTreeData.mem_stepImage]

/-- Piterman's first transition stage, now executable from decidable NBW data. -/
def stage1 (decStep : ∀ q a q', Decidable (A.step q a q'))
    (tree : CompactTreeData A) (letter : Alphabet) : CompactTreeData A where
  active := tree.active
  name := tree.name
  parent := tree.parent
  label node := stepImage A decStep letter (tree.label node)
  e := sentinel A
  f := sentinel A

theorem stage1_eq (decStep : ∀ q a q', Decidable (A.step q a q'))
    (tree : CompactTreeData A) (letter : Alphabet) :
    stage1 A decStep tree letter = CompactTreeData.stage1 A tree letter := by
  simp only [stage1, CompactTreeData.stage1, stepImage_eq]

/-- The accepting part of a label, using the supplied acceptance test. -/
def acceptingPart (decAccept : DecidablePred A.accepting)
    (tree : CompactTreeData A) (node : Node A) : Finset A.State :=
  letI := decAccept
  (tree.label node).filter A.accepting

theorem acceptingPart_eq (decAccept : DecidablePred A.accepting)
    (tree : CompactTreeData A) (node : Node A) :
    acceptingPart A decAccept tree node = tree.acceptingPart A node := by
  classical
  ext q
  simp [acceptingPart, CompactTreeData.mem_acceptingPart]

/-- Compute exactly which active nodes need a fresh child. -/
def stage2Triggers (decAccept : DecidablePred A.accepting)
    (tree : CompactTreeData A) : Finset (Node A) :=
  (tree.activeNodes A).filter fun node => (acceptingPart A decAccept tree node).Nonempty

theorem stage2Triggers_eq (decAccept : DecidablePred A.accepting)
    (tree : CompactTreeData A) :
    stage2Triggers A decAccept tree = tree.stage2Triggers A := by
  classical
  simp only [stage2Triggers, CompactTreeData.stage2Triggers, acceptingPart_eq]

/-- Allocate the j-th trigger to the j-th inactive node, both in increasing
node order, and give it name `active.card + j`. All sorting is on finite nodes;
there is no choice of an embedding or test of an infinite-run property. -/
def stage2PlanOfBounds (decAccept : DecidablePred A.accepting)
    (tree : CompactTreeData A)
    (hbound : ∀ node, tree.active node = true → (tree.name node).val < Fintype.card A.State)
    (hinjective : ∀ left right, tree.active left = true → tree.active right = true →
      tree.name left = tree.name right → left = right)
    (hconsecutive : ∀ k : Nat, k < Fintype.card A.State →
      (∃ node, tree.active node ∧ (tree.name node).val = k) →
      ∀ j : Nat, j < k → ∃ node, tree.active node ∧ (tree.name node).val = j) :
    Stage2Plan A tree := by
  let triggers := stage2Triggers A decAccept tree
  have htriggers : triggers = tree.stage2Triggers A := stage2Triggers_eq A decAccept tree
  have hactive : (tree.activeNodes A).card ≤ Fintype.card A.State :=
    activeNodes_card_le_of_name_bound_injective A tree hbound hinjective
  have hspace : triggers.card ≤ (tree.inactiveNodes A).card := by
    rw [htriggers]
    exact stage2Triggers_card_le_inactiveNodes_of_active_card_le A tree hactive
  have hsmall : triggers.card ≤ Fintype.card A.State := by
    rw [htriggers]
    exact (stage2Triggers_card_le_activeNodes A tree).trans hactive
  let rank : triggers ≃o Fin triggers.card := (triggers.orderIsoOfFin rfl).symm
  let available := (tree.inactiveNodes A).orderIsoOfFin rfl
  let child : Node A → Node A := fun node =>
    if hn : node ∈ triggers then
      (available ⟨(rank ⟨node, hn⟩).val,
        lt_of_lt_of_le (rank ⟨node, hn⟩).isLt hspace⟩).val
    else root A
  let name : Node A → TempName A := fun node =>
    if hn : node ∈ triggers then
      ⟨(tree.activeNodes A).card + (rank ⟨node, hn⟩).val, by
        have := (rank ⟨node, hn⟩).isLt
        change _ < 2 * Fintype.card A.State
        omega⟩
    else root A
  refine {
    freshChild := child
    freshName := name
    fresh_inactive := ?_
    fresh_injective := ?_
    fresh_name_gt_used := ?_
    fresh_name_ge_active_card := ?_
    fresh_name_lt_active_plus_triggers := ?_
    fresh_name_covers_interval := ?_
    fresh_name_injective := ?_
  }
  · intro node hn
    have ht : node ∈ triggers := htriggers.symm ▸ hn
    apply (mem_inactiveNodes A tree).mp
    dsimp [child]
    rw [dif_pos ht]
    exact (available _).property
  · intro left right hl hr heq
    have hl' : left ∈ triggers := htriggers.symm ▸ hl
    have hr' : right ∈ triggers := htriggers.symm ▸ hr
    dsimp [child] at heq
    simp only [dif_pos hl', dif_pos hr'] at heq
    have hrank := congrArg Fin.val (available.injective (Subtype.ext heq))
    exact congrArg Subtype.val (rank.injective (Fin.ext hrank))
  · intro node old hn ho
    have ht : node ∈ triggers := htriggers.symm ▸ hn
    have hold := active_name_lt_activeNodes_card_of_consecutive A tree
      hbound hinjective hconsecutive old ((mem_activeNodes A tree).mp ho)
    dsimp [name]
    rw [dif_pos ht]
    dsimp
    omega
  · intro node hn
    have ht : node ∈ triggers := htriggers.symm ▸ hn
    simp [name, ht]
  · intro node hn
    have ht : node ∈ triggers := htriggers.symm ▸ hn
    have hi := (rank ⟨node, ht⟩).isLt
    have hc := congrArg Finset.card htriggers
    have hi' : (rank ⟨node, ht⟩).val < (tree.stage2Triggers A).card := by omega
    simp only [name, dif_pos ht]
    exact Nat.add_lt_add_left hi' _
  · intro idx hi
    have hi' : idx < triggers.card := htriggers.symm ▸ hi
    let node := rank.symm ⟨idx, hi'⟩
    refine ⟨node.val, htriggers ▸ node.property, ?_⟩
    simp only [name, dif_pos node.property]
    have hrank : rank node = ⟨idx, hi'⟩ := rank.apply_symm_apply _
    exact congrArg (fun j : Fin triggers.card => (tree.activeNodes A).card + j.val) hrank
  · intro left right hl hr heq
    have hl' : left ∈ triggers := htriggers.symm ▸ hl
    have hr' : right ∈ triggers := htriggers.symm ▸ hr
    have hval := congrArg Fin.val heq
    simp only [name, dif_pos hl', dif_pos hr'] at hval
    exact congrArg Subtype.val (rank.injective (Fin.ext (Nat.add_left_cancel hval)))

/-- The executable allocation is total on well-formed compact trees. -/
def stage2Plan (decAccept : DecidablePred A.accepting)
    (tree : CompactTreeData A) (htree : tree.WellFormed A) : Stage2Plan A tree := by
  obtain ⟨_, _, _, _, _, hbound, hinjective, hconsecutive, _, _, _⟩ := htree
  exact stage2PlanOfBounds A decAccept tree hbound hinjective hconsecutive

/-- Find a fresh child's unique parent by searching the finite trigger list. -/
def ownerOf (decAccept : DecidablePred A.accepting)
    {tree : CompactTreeData A} (plan : Stage2Plan A tree) (node : Node A) :
    Option (Node A) :=
  ((stage2Triggers A decAccept tree).sort (· ≤ ·)).find?
    fun parent => decide (plan.freshChild parent = node)

theorem ownerOf_eq (decAccept : DecidablePred A.accepting)
    {tree : CompactTreeData A} (plan : Stage2Plan A tree) (node : Node A) :
    ownerOf A decAccept plan node = plan.ownerOf A node := by
  cases h : ownerOf A decAccept plan node with
  | none =>
      symm
      apply (Stage2Plan.ownerOf_eq_none_iff A plan).mpr
      intro parent hp hc
      have hp' : parent ∈ (stage2Triggers A decAccept tree).sort (· ≤ ·) := by
        simpa [stage2Triggers_eq] using hp
      have hn := (List.find?_eq_none.mp h) parent hp'
      exact hn (by simp [hc])
  | some parent =>
      have hp : parent ∈ tree.stage2Triggers A := by
        have hm := List.mem_of_find?_eq_some h
        simpa [stage2Triggers_eq] using hm
      have ht := List.find?_some h
      have hc : plan.freshChild parent = node := of_decide_eq_true ht
      have ho := Stage2Plan.ownerOf_eq_some_of_freshChild A plan hp
      rw [hc] at ho
      exact ho.symm

/-- Create all fresh children using the certified finite allocation. -/
def stage2 (decAccept : DecidablePred A.accepting)
    (tree : CompactTreeData A) (plan : Stage2Plan A tree) : CompactTreeData A where
  active node := if (ownerOf A decAccept plan node).isSome then true else tree.active node
  name node := match ownerOf A decAccept plan node with
    | some parent => plan.freshName parent
    | none => tree.name node
  parent node := match ownerOf A decAccept plan node with
    | some parent => parent
    | none => tree.parent node
  label node := match ownerOf A decAccept plan node with
    | some parent => acceptingPart A decAccept tree parent
    | none => tree.label node
  e := sentinel A
  f := sentinel A

/-- For any fixed valid plan the executable and semantic second stages agree. -/
theorem stage2_eq (decAccept : DecidablePred A.accepting)
    (tree : CompactTreeData A) (plan : Stage2Plan A tree) :
    stage2 A decAccept tree plan = tree.stage2 A plan := by
  simp only [stage2, CompactTreeData.stage2, ownerOf_eq, acceptingPart_eq]
  rfl

/-- The shared sorted allocation used by both the executable compiler and the
canonical correctness proof. It supplies the existing transition certificate. -/
def transitionPlan (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting)
    (tree : CompactTreeData A) (htree : tree.WellFormed A) (letter : Alphabet) :
    TransitionPlan A tree letter := by
  obtain ⟨_, _, _, _, _, hbound, hinjective, hconsecutive, _, _, _⟩ := htree
  let plan := stage2PlanOfBounds A decAccept (stage1 A decStep tree letter)
    hbound hinjective hconsecutive
  exact ⟨(stage1_eq A decStep tree letter) ▸ plan⟩

end DistributedSynthesis.NondetBuchiAutomaton.Piterman.Computable
