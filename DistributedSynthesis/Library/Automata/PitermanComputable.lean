/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.Piterman
import DistributedSynthesis.Library.Combinatorics.FiniteOrbits

/-! # Executable operations for the existing Piterman construction

The NBW interface allows arbitrary proposition-valued transitions.
An executable determinizer must instead receive their decision procedures.
Together with `PitermanAllocation`, this module implements all six transition
stages, the live-state transition, and exhaustive finite-state enumeration.
The canonical correctness proof now uses the same sorted allocation. Exact
automaton agreement transfers language correctness to the executable compiler;
no allocation-independence hypothesis is required.
-/

namespace DistributedSynthesis.NondetBuchiAutomaton.Piterman.Computable
open CompactTreeData

variable {Alphabet : Type*} (A : NondetBuchiAutomaton Alphabet)
variable [DecidableEq A.State]

/-- Equality of compact trees is equality of their six finite data fields. -/
@[reducible] def rawDecidableEq : DecidableEq (CompactTreeData A) := by
  intro x y
  exact decidable_of_iff
    (x.active = y.active ∧ x.name = y.name ∧ x.parent = y.parent ∧
      x.label = y.label ∧ x.e = y.e ∧ x.f = y.f)
    (by cases x; cases y; simp only [CompactTreeData.mk.injEq])

/-- Equality of optional well-formed trees does not enumerate the state carrier. -/
@[reducible] def stateDecidableEq : DecidableEq (DPWState A) :=
  letI := rawDecidableEq A
  inferInstance

/-- The canonical proof and executable construction now use the same sorted
allocation. The supplied deciders affect evaluation, not the resulting data. -/
theorem transitionPlan_eq_livePlan (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting) (state : LiveState A) (letter : Alphabet) :
    transitionPlan A decStep decAccept state.val state.property letter =
      CompactTreeData.livePlan A state letter := by
  unfold CompactTreeData.livePlan
  congr 1 <;> apply Subsingleton.elim

/-- Parent-chain reachability is a finite search even for malformed cyclic trees. -/
def ancestorDecidable (tree : CompactTreeData A) (ancestor node : Node A) :
    Decidable (tree.IsAncestorOrSelf A ancestor node) :=
  FiniteOrbits.reachableDecidable tree.parent node ancestor

def blockedDecidable (tree : CompactTreeData A) (node : Node A) (q : A.State) :
    Decidable (tree.BlockedByOlderSibling A node q) := by
  letI := ancestorDecidable A tree
  unfold BlockedByOlderSibling OlderSibling
  infer_instance

/-- Remove states blocked by an older sibling of an ancestor. -/
def stage3 (tree : CompactTreeData A) : CompactTreeData A :=
  letI := blockedDecidable A tree
  { active := tree.active
    name := tree.name
    parent := tree.parent
    label := fun node => (tree.label node).filter fun q => ¬ tree.BlockedByOlderSibling A node q
    e := sentinel A
    f := sentinel A }

theorem stage3_eq (tree : CompactTreeData A) : stage3 A tree = tree.stage3 A := by
  unfold stage3 CompactTreeData.stage3
  congr 1
  funext node
  ext q
  simp

/-- Bounded minimum, with the sentinel when no bounded name is present. -/
def minBoundedNameOf (tree : CompactTreeData A) (nodes : Finset (Node A)) : Name A := by
  let bounded := (nodes.filter fun node => (tree.name node).val < Fintype.card A.State).image
    fun node => (tree.name node).val
  if h : bounded.Nonempty then
    refine ⟨bounded.min' h, ?_⟩
    have hm := Finset.min'_mem bounded h
    obtain ⟨node, hn, heq⟩ := Finset.mem_image.mp hm
    have hlt := (Finset.mem_filter.mp hn).2
    omega
  else exact sentinel A

theorem minBoundedNameOf_eq (tree : CompactTreeData A) (nodes : Finset (Node A)) :
    minBoundedNameOf A tree nodes = tree.minBoundedNameOf A nodes := rfl

def removedByGreenDecidable (tree : CompactTreeData A) (node : Node A) :
    Decidable (tree.RemovedByGreen A node) := by
  letI := ancestorDecidable A tree
  unfold RemovedByGreen
  infer_instance

/-- Delete descendants of green nodes and record the minimum green name. -/
def stage4 (tree : CompactTreeData A) : CompactTreeData A :=
  letI := removedByGreenDecidable A tree
  { active := fun node => if tree.RemovedByGreen A node then false else tree.active node
    name := tree.name
    parent := tree.parent
    label := fun node => if tree.RemovedByGreen A node then ∅ else tree.label node
    e := sentinel A
    f := minBoundedNameOf A tree (tree.greenNodes A) }

theorem stage4_eq (tree : CompactTreeData A) : stage4 A tree = tree.stage4 A := by
  simp only [stage4, CompactTreeData.stage4, minBoundedNameOf_eq]
  congr 1 <;> funext node <;> split_ifs <;> rfl

def greenRemovedNodes (tree : CompactTreeData A) : Finset (Node A) :=
  letI := removedByGreenDecidable A tree
  Finset.univ.filter fun node => tree.RemovedByGreen A node

theorem greenRemovedNodes_eq (tree : CompactTreeData A) :
    greenRemovedNodes A tree = tree.greenRemovedNodes A := by
  ext node
  simp [greenRemovedNodes, CompactTreeData.greenRemovedNodes]

/-- Remove empty labels, accounting also for nodes deleted during stage 4. -/
def stage5 (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A)) :
    CompactTreeData A :=
  letI : DecidablePred (tree.RemovedByStage5 A previouslyRemoved) := fun node => by
    unfold RemovedByStage5
    infer_instance
  { active := fun node =>
      if tree.RemovedByStage5 A previouslyRemoved node then false else tree.active node
    name := tree.name
    parent := tree.parent
    label := fun node =>
      if tree.RemovedByStage5 A previouslyRemoved node then ∅ else tree.label node
    e := minBoundedNameOf A tree (previouslyRemoved ∪ tree.emptyActiveNodes A)
    f := tree.f }

theorem stage5_eq (tree : CompactTreeData A) (removed : Finset (Node A)) :
    stage5 A tree removed = tree.stage5 A removed := by
  simp only [stage5, CompactTreeData.stage5, minBoundedNameOf_eq]
  congr 1 <;> funext node <;> split_ifs <;> rfl

/-- Compact surviving names by counting smaller deleted names. -/
def stage6 (tree : CompactTreeData A) (removed : Finset (Node A)) : CompactTreeData A where
  active := tree.active
  name node := if tree.label node = ∅ then tree.name node else tree.compactedName A removed node
  parent := tree.parent
  label := tree.label
  e := tree.e
  f := tree.f

theorem stage6_eq (tree : CompactTreeData A) (removed : Finset (Node A)) :
    stage6 A tree removed = tree.stage6 A removed := rfl

/-- The first two stages with a supplied certificate, transported only in its type. -/
def afterStage2 (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting) (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter) : CompactTreeData A :=
  stage2 A decAccept (stage1 A decStep tree letter)
    ((stage1_eq A decStep tree letter).symm ▸ plan.stage2Plan)

theorem afterStage2_eq (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting) (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter) :
    afterStage2 A decStep decAccept tree letter plan =
      (tree.stage1 A letter).stage2 A plan.stage2Plan := by
  simp only [afterStage2, stage2_eq]
  have transport (t₁ t₂ : CompactTreeData A) (h : t₁ = t₂) (p : Stage2Plan A t₂) :
      t₁.stage2 A (h.symm ▸ p) = t₂.stage2 A p := by cases h; rfl
  exact transport _ _ (stage1_eq A decStep tree letter) plan.stage2Plan

/-- The stage-4 tree used to decide whether the transition enters the rejecting sink. -/
def afterStage4 (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting) (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter) : CompactTreeData A :=
  stage4 A (stage3 A (afterStage2 A decStep decAccept tree letter plan))

theorem afterStage4_eq (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting) (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter) :
    afterStage4 A decStep decAccept tree letter plan =
      (((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).stage4 A := by
  simp only [afterStage4, stage4_eq, stage3_eq, afterStage2_eq]

/-- The complete six-stage transition, given a valid finite allocation. -/
def transitionWithPlan (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting) (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter) : CompactTreeData A :=
  let t3 := stage3 A (afterStage2 A decStep decAccept tree letter plan)
  let t4 := stage4 A t3
  let removed4 := greenRemovedNodes A t3
  let t5 := stage5 A t4 removed4
  stage6 A t5 (removed4 ∪ t4.emptyActiveNodes A)

theorem transitionWithPlan_eq (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting) (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter) :
    transitionWithPlan A decStep decAccept tree letter plan =
      tree.transitionWithPlan A letter plan := by
  simp only [transitionWithPlan, stage6_eq, stage5_eq, stage4_eq, stage3_eq,
    greenRemovedNodes_eq, afterStage2_eq, CompactTreeData.transitionWithPlan]

/-- Reuse the existing full transition invariant, with no extra certificate premise. -/
theorem transitionWithPlan_wellFormed (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting) (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter) (htree : tree.WellFormed A)
    (hroot : (afterStage4 A decStep decAccept tree letter plan).label (root A) ≠ ∅) :
    (transitionWithPlan A decStep decAccept tree letter plan).WellFormed A := by
  rw [transitionWithPlan_eq]
  apply transitionWithPlan_preserves_wellFormed_of_stage4_root_label_nonempty
    A tree letter plan htree
  simpa only [afterStage4_eq] using hroot

/-- A total executable transition on live compact trees; an empty root goes to `none`.
This uses our deterministic allocation, not the arbitrary choice. -/
def liveTransition (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting) (state : LiveState A) (letter : Alphabet) :
    DPWState A :=
  let plan := transitionPlan A decStep decAccept state.val state.property letter
  if hroot : (afterStage4 A decStep decAccept state.val letter plan).label (root A) ≠ ∅ then
    some ⟨transitionWithPlan A decStep decAccept state.val letter plan,
      transitionWithPlan_wellFormed A decStep decAccept state.val letter plan state.property hroot⟩
  else none

/-- Explicit enumeration of raw tree records. This is finite but intentionally
exhaustive; it is not an efficient reachable-state construction. -/
@[reducible] def rawFintype : Fintype (CompactTreeData A) := by
  let Repr := (((((Node A → Bool) × (Node A → TempName A)) ×
    (Node A → Node A)) × (Node A → Finset A.State)) × Name A) × Name A
  exact Fintype.ofEquiv Repr
    { toFun := fun data =>
        { active := data.1.1.1.1.1
          name := data.1.1.1.1.2
          parent := data.1.1.1.2
          label := data.1.1.2
          e := data.1.2
          f := data.2 }
      invFun := fun tree =>
        (((((tree.active, tree.name), tree.parent), tree.label), tree.e), tree.f)
      left_inv := by
        intro data
        rcases data with ⟨⟨⟨⟨⟨active, name⟩, parent⟩, label⟩, e⟩, f⟩
        rfl
      right_inv := by intro tree; cases tree; rfl }

set_option synthInstance.maxSize 2048 in
/-- Every invariant check ranges over finite nodes/states or bounded natural names. -/
def wellFormedDecidable (tree : CompactTreeData A) : Decidable (tree.WellFormed A) := by
  letI (k : Nat) : Decidable (∀ j : Nat, j < k →
      ∃ node, tree.active node ∧ (tree.name node).val = j) :=
    decidable_of_iff (∀ j : Fin k, ∃ node, tree.active node ∧ (tree.name node).val = j.val)
      ⟨fun h j hj => h ⟨j, hj⟩, fun h j => h j.val j.isLt⟩
  letI : Decidable (∀ k : Nat, k < Fintype.card A.State →
      (∃ node, tree.active node ∧ (tree.name node).val = k) →
      ∀ j : Nat, j < k → ∃ node, tree.active node ∧ (tree.name node).val = j) :=
    decidable_of_iff (∀ k : Fin (Fintype.card A.State),
      (∃ node, tree.active node ∧ (tree.name node).val = k.val) →
      ∀ j : Nat, j < k.val → ∃ node, tree.active node ∧ (tree.name node).val = j)
      ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k.val k.isLt⟩
  unfold WellFormed
  infer_instance

/-- Enumerate well-formed live states using the executable invariant test. -/
@[reducible] def liveFintype : Fintype (LiveState A) :=
  letI := rawFintype A
  letI := wellFormedDecidable A
  inferInstanceAs (Fintype {tree : CompactTreeData A // tree.WellFormed A})

/-- Complete executable automaton data. `accepts_iff` below proves language
equivalence via the canonical proof with the shared sorted allocation. -/
def automatonData (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting) : DetParityAutomaton Alphabet where
  State := DPWState A
  stateFinite := by
    letI := liveFintype A
    infer_instance
  initial := some ⟨CompactTreeData.initial A, initial_wellFormed A⟩
  step state letter := match state with
    | none => none
    | some live => liveTransition A decStep decAccept live letter
  priority state := match state with
    | none => 1
    | some live => priority A live.val

/-- Exact transition agreement after fixing the shared canonical allocation. -/
theorem liveTransition_eq (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting) (state : LiveState A) (letter : Alphabet) :
    liveTransition A decStep decAccept state letter =
      CompactTreeData.liveTransition A state letter := by
  unfold liveTransition
  simp only [afterStage4_eq, transitionWithPlan_eq, transitionPlan_eq_livePlan]
  unfold CompactTreeData.liveTransition liveRootLabelNonempty liveStage4RootLabel liveNextTree
  split_ifs <;> rfl

/-- Finite enumerations and decision proofs do not change the automaton record. -/
theorem automatonData_eq (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting) :
    automatonData A decStep decAccept = CompactTreeData.automaton A := by
  unfold automatonData CompactTreeData.automaton
  congr 1
  · exact Subsingleton.elim _ _
  · funext state letter
    cases state with
    | none => rfl
    | some live => exact liveTransition_eq A decStep decAccept live letter

/-- Language correctness, with no allocation-independence or completeness premise. -/
theorem accepts_iff (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting) (word : OmegaWord Alphabet) :
    (automatonData A decStep decAccept).Accepts word ↔ A.Accepts word := by
  rw [automatonData_eq]
  exact ⟨accepts_of_automaton_accepts A word, automaton_accepts_of_accepts A⟩

/-- An executable certified NBW-to-DPA compilation from finite decidable data. -/
def compilation (decStep : ∀ q a q', Decidable (A.step q a q'))
    (decAccept : DecidablePred A.accepting) : NondetBuchiToDPACompilation A where
  dpa := automatonData A decStep decAccept
  correct := accepts_iff A decStep decAccept

end DistributedSynthesis.NondetBuchiAutomaton.Piterman.Computable
