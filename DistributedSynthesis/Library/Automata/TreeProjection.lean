/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.Tree

/-! # Relabelling and projection for parity tree automata

These constructions reuse `RunParityTreeAutomaton` and its existing run/parity
semantics. Projection chooses one complete label per node, shared by all
successors; it does not choose a different witness separately on each branch.
-/
namespace DistributedSynthesis.RunParityTreeAutomaton

universe u v w z
variable {Branch : Type u} {Alphabet : Type v} {Label : Type w}

/-- Inverse image under a letter map. -/
def comap (A : RunParityTreeAutomaton.{u, w, z} Branch Label) (f : Alphabet → Label) :
    RunParityTreeAutomaton.{u, v, z} Branch Alphabet where
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  delta q a next := A.delta q (f a) next
  priority := A.priority

@[simp] theorem comap_acceptsTree_iff
    (A : RunParityTreeAutomaton.{u, w, z} Branch Label) (f : Alphabet → Label)
    (tree : LabeledTree Branch Alphabet) :
    (A.comap f).acceptsTree tree ↔ A.acceptsTree (f ∘ tree) := Iff.rfl

/-- Existential letter projection. With a finite source alphabet and decidable
transition data, this is a finite search at each transition. -/
def project (A : RunParityTreeAutomaton.{u, v, z} Branch Alphabet) (f : Alphabet → Label) :
    RunParityTreeAutomaton.{u, w, z} Branch Label where
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  delta q b next := ∃ a, f a = b ∧ A.delta q a next
  priority := A.priority

instance projectDeltaDecidable [Fintype Alphabet] [DecidableEq Label]
    (A : RunParityTreeAutomaton.{u, v, z} Branch Alphabet)
    [∀ q a next, Decidable (A.delta q a next)] (f : Alphabet → Label)
    (q : A.State) (b : Label) (next : Branch → A.State) :
    Decidable ((A.project f).delta q b next) :=
  inferInstanceAs (Decidable (∃ a, f a = b ∧ A.delta q a next))

/-- Projection quantifies over a single coherent labelling of the whole tree. -/
theorem project_acceptsTree_iff
    (A : RunParityTreeAutomaton.{u, v, z} Branch Alphabet) (f : Alphabet → Label)
    (tree : LabeledTree Branch Label) :
    (A.project f).acceptsTree tree ↔
      ∃ original : LabeledTree Branch Alphabet, f ∘ original = tree ∧ A.acceptsTree original := by
  constructor
  · rintro ⟨run, ⟨initial, step⟩, parity⟩
    choose original label transition using step
    refine ⟨original, funext label, run, ⟨initial, transition⟩, parity⟩
  · rintro ⟨original, labels, run, ⟨initial, step⟩, parity⟩
    refine ⟨run, ⟨initial, fun node => ?_⟩, parity⟩
    exact ⟨original node, congrFun labels node, step node⟩

/-- Dropping an annotation is the operation used for existential set variables. -/
theorem project_fst_acceptsTree_iff
    (A : RunParityTreeAutomaton.{u, max v w, z} Branch (Alphabet × Label))
    (tree : LabeledTree Branch Alphabet) :
    (A.project Prod.fst).acceptsTree tree ↔
      ∃ annotation : LabeledTree Branch Label,
        A.acceptsTree (fun node => (tree node, annotation node)) := by
  rw [project_acceptsTree_iff]
  constructor
  · rintro ⟨original, labels, accepts⟩
    refine ⟨fun node => (original node).2, ?_⟩
    have same : (fun node => (tree node, (original node).2)) = original := by
      funext node
      rw [← congrFun labels node]
      rfl
    rwa [same]
  · rintro ⟨annotation, accepts⟩
    exact ⟨fun node => (tree node, annotation node), rfl, accepts⟩

end DistributedSynthesis.RunParityTreeAutomaton
