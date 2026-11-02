/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefEpochAbstractions
import DistributedSynthesis.Formalizations.Theorem.ThmBerardfinitememory
import Mathlib.Data.Fintype.Prod

/-!
# Parametric journal construction

This file formalizes the product-state step used by
`prop:parametricjournal`: finite one-directional summaries remain finite and
uniform after adding finitely many synchronized-block regular monitors.
-/

namespace DistributedSynthesis

universe u v w x y z

/-- A finite monitor family for synchronized blocks, separately for each real side. -/
structure SynchronizedBlockRegularMonitor
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type w) (Out₂ : Type x) where
  State : Proc -> Type y
  stateFinite : (d : Proc) -> Fintype (State d)
  initial : (d : Proc) -> State d
  update : (d : Proc) -> State d -> In₁ -> In₂ -> Out₁ -> Out₂ -> State d
  close : (d : Proc) -> State d -> ClosingLetter In₁ In₂ Out₁ Out₂ -> State d
  recognizesPrescribedRegularTests : Prop

attribute [instance] SynchronizedBlockRegularMonitor.stateFinite

/-- Product of a one-directional summary with synchronized-block regular monitors. -/
def parametricJournalProduct
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (base : UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z} Alphabet In₁ In₂ Out₁ Out₂)
    (monitor : SynchronizedBlockRegularMonitor.{v, w, x, y, max u v w x y z} In₁ In₂ Out₁ Out₂)
    (continuationInvariant : Prop)
    (regularRepresentation : Prop) :
    UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z} Alphabet In₁ In₂ Out₁ Out₂ where
  automaton := base.automaton
  boundary := base.boundary
  boundaryFinite := base.boundaryFinite
  summary := fun d => base.summary d × monitor.State d
  summaryFinite := by
    intro d
    letI := base.summaryFinite d
    letI := monitor.stateFinite d
    exact instFintypeProd (base.summary d) (monitor.State d)
  sideData := fun d =>
    let baseData := base.sideData d
    {
      init := fun boundary =>
        (baseData.init boundary, monitor.initial d)
      update := fun state inputOne inputTwo outputOne outputTwo =>
        ( baseData.update state.1 inputOne inputTwo outputOne outputTwo,
          monitor.update d state.2 inputOne inputTwo outputOne outputTwo )
      close := fun state letter =>
        baseData.close state.1 letter
    }
  continuationInvariant := continuationInvariant
  regularRepresentation := regularRepresentation

/--
Proposition `prop:parametricjournal`: adding a finite family of regular tests
to the sampled one-directional construction is implemented by a finite product
with deterministic monitors.
-/
theorem parametric_journal
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (base : UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z} Alphabet In₁ In₂ Out₁ Out₂)
    (monitor : SynchronizedBlockRegularMonitor.{v, w, x, y, max u v w x y z} In₁ In₂ Out₁ Out₂)
    (continuationInvariant : Prop)
    (regularRepresentation : Prop) :
    ∃ enriched : UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z} Alphabet In₁ In₂ Out₁ Out₂,
      (∀ d, enriched.summary d = (base.summary d × monitor.State d)) ∧
      enriched.continuationInvariant = continuationInvariant ∧
      enriched.regularRepresentation = regularRepresentation := by
  refine ⟨parametricJournalProduct base monitor continuationInvariant regularRepresentation, ?_, ?_, ?_⟩
  · intro d
    rfl
  · rfl
  · rfl

end DistributedSynthesis
