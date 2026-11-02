/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefEpochAbstractions

/-!
# Sufficient finite-congruence repair
-/

namespace DistributedSynthesis

universe u v w x y z

/-- Certificate for the four quotient properties in Proposition `prop:finitecongruencerepair`. -/
structure FiniteCongruenceRepairCertificate
    (Boundary : Type u)
    (EdgeType : Type v)
    (SummaryData : PathSummarySemigroup EdgeType)
    (In₁ : Type w) (In₂ : Type x) (Out₁ : Type y) (Out₂ : Type z) where
  summaries : EpochCongruentPathSummaries Boundary EdgeType SummaryData In₁ In₂ Out₁ Out₂
  preservesPathData : Prop
  privateInputUpdateClosed : Prop
  closingMapWellDefined : Prop
  rightCongruenceForContinuations : Prop
  preservesPathData_proof : preservesPathData
  privateInputUpdateClosed_proof : privateInputUpdateClosed
  closingMapWellDefined_proof : closingMapWellDefined
  rightCongruenceForContinuations_proof : rightCongruenceForContinuations

/--
Paper-facing Proposition `prop:finitecongruencerepair`: the finite congruence data
packages finite epoch-congruent path summaries.
-/
theorem sufficient_finite_congruence_repair
    {Boundary : Type u}
    {EdgeType : Type v}
    {SummaryData : PathSummarySemigroup EdgeType}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    (cert :
      FiniteCongruenceRepairCertificate
        Boundary EdgeType SummaryData In₁ In₂ Out₁ Out₂) :
    Nonempty (EpochCongruentPathSummaries Boundary EdgeType SummaryData In₁ In₂ Out₁ Out₂) ∧
      cert.preservesPathData ∧
      cert.privateInputUpdateClosed ∧
      cert.closingMapWellDefined ∧
      cert.rightCongruenceForContinuations := by
  exact
    ⟨⟨cert.summaries⟩,
      cert.preservesPathData_proof,
      cert.privateInputUpdateClosed_proof,
      cert.closingMapWellDefined_proof,
      cert.rightCongruenceForContinuations_proof⟩

end DistributedSynthesis
