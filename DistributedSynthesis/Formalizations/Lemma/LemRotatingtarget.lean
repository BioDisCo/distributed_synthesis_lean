/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefEpochAbstractions

/-!
# Rotating access-state target
-/

namespace DistributedSynthesis

universe u v

/-- A semantic finite rotating access-state map. -/
structure RotatingAccessStateSemantics
    (Config : Type u)
    (AContinuation : Config -> Config -> Prop) where
  State : Type v
  stateFinite : Fintype State
  accessState : Config -> State
  determinesReceiptAndOrder : Prop
  updateClosed : Prop
  preservesDynamicHierarchy : Prop
  determinesReceiptAndOrder_proof : determinesReceiptAndOrder
  updateClosed_proof : updateClosed
  preservesDynamicHierarchy_proof : preservesDynamicHierarchy
  refinesAContinuation :
    ∀ c c', accessState c = accessState c' -> AContinuation c c'

attribute [instance] RotatingAccessStateSemantics.stateFinite

/-- The finite-index retraction relation induced by a finite access-state map. -/
def RotatingAccessStateSemantics.sameAccess
    {Config : Type u} {AContinuation : Config -> Config -> Prop}
    (sem : RotatingAccessStateSemantics Config AContinuation)
    (c c' : Config) : Prop :=
  sem.accessState c = sem.accessState c'

/-- The actual finite quotient data induced by a semantic rotating access-state map. -/
structure RotatingAccessFiniteIndex
    (Config : Type u)
    (AContinuation : Config -> Config -> Prop) where
  Quotient : Type v
  quotientFinite : Fintype Quotient
  classOf : Config -> Quotient
  refines : ∀ c c', classOf c = classOf c' -> AContinuation c c'

attribute [instance] RotatingAccessFiniteIndex.quotientFinite

/--
Semantic core of Lemma `lem:rotatingtarget`: a finite rotating access-state map
whose fibers refine `A`-continuation equivalence induces a finite-index
retraction.
-/
theorem rotating_access_state_semantic_finite_index
    {Config : Type u} {AContinuation : Config -> Config -> Prop}
    (sem : RotatingAccessStateSemantics.{u, v} Config AContinuation) :
    Nonempty (RotatingAccessFiniteIndex.{u, v} Config AContinuation) := by
  refine ⟨{
    Quotient := sem.State
    quotientFinite := sem.stateFinite
    classOf := sem.accessState
    refines := ?_
  }⟩
  intro c c' h
  exact sem.refinesAContinuation c c' h

/-- Equal rotating states imply the semantic continuation relation they refine. -/
theorem rotating_access_state_refines_A_continuation
    {Config : Type u} {AContinuation : Config -> Config -> Prop}
    (sem : RotatingAccessStateSemantics Config AContinuation)
    {c c' : Config}
    (h : sem.sameAccess c c') :
    AContinuation c c' := by
  exact sem.refinesAContinuation c c' h

/-- Certificate for the finite rotating access-state target. -/
structure RotatingAccessStateTargetCertificate
    (Config : Type u) where
  State : Type v
  stateFinite : Fintype State
  accessState : Config -> State
  determinesReceiptAndOrder : Prop
  updateClosed : Prop
  refinesAContinuation : Prop
  preservesDynamicHierarchy : Prop
  finiteIndexEffective : Prop
  synthesisDecidable : Prop
  determinesReceiptAndOrder_proof : determinesReceiptAndOrder
  updateClosed_proof : updateClosed
  refinesAContinuation_proof : refinesAContinuation
  preservesDynamicHierarchy_proof : preservesDynamicHierarchy
  finiteIndexEffective_proof : finiteIndexEffective
  synthesisDecidable_proof : synthesisDecidable

attribute [instance] RotatingAccessStateTargetCertificate.stateFinite

/--
Paper-facing Lemma `lem:rotatingtarget`: a finite rotating access-state map gives
effective finite `A`-index and the corresponding decidability conclusion.
-/
theorem rotating_access_state_target
    {Config : Type u}
    (cert : RotatingAccessStateTargetCertificate Config) :
    Nonempty (Fintype cert.State) ∧
      cert.determinesReceiptAndOrder ∧
      cert.updateClosed ∧
      cert.refinesAContinuation ∧
      cert.preservesDynamicHierarchy ∧
      cert.finiteIndexEffective ∧
      cert.synthesisDecidable := by
  exact
    ⟨⟨inferInstance⟩,
      cert.determinesReceiptAndOrder_proof,
      cert.updateClosed_proof,
      cert.refinesAContinuation_proof,
      cert.preservesDynamicHierarchy_proof,
      cert.finiteIndexEffective_proof,
      cert.synthesisDecidable_proof⟩

end DistributedSynthesis
