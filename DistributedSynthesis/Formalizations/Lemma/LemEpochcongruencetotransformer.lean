/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefEpochAbstractions

/-!
# Epoch congruences instantiate the transformer
-/

namespace DistributedSynthesis

universe u v w x y z q r

/-- Certificate carrying finite epoch-congruent summaries for both sides and the resulting transformer. -/
structure EpochCongruenceTransformerCertificate
    (Alphabet : Type u)
    (Boundary : Type v)
    (EdgeType : Type w)
    (SummaryData : PathSummarySemigroup EdgeType)
    (In₁ : Type x) (In₂ : Type y) (Out₁ : Type z) (Out₂ : Type q) where
  boundaryFinite : Fintype Boundary
  sideCongruence :
    (d : Proc) -> EpochCongruentPathSummaries Boundary EdgeType SummaryData In₁ In₂ Out₁ Out₂
  transformer : FiniteEpochTransformer.{u, x, y, z, q, r} Alphabet In₁ In₂ Out₁ Out₂
  transformerSound : Prop
  transformerSound_proof : transformerSound

attribute [instance] EpochCongruenceTransformerCertificate.boundaryFinite

/-- Lemma `lem:epochcongruencetotransformer`: the certificate yields a finite epoch transformer. -/
theorem epoch_congruences_instantiate_transformer
    {Alphabet : Type u}
    {Boundary : Type v}
    {EdgeType : Type w}
    {SummaryData : PathSummarySemigroup EdgeType}
    {In₁ : Type x} {In₂ : Type y} {Out₁ : Type z} {Out₂ : Type q}
    (cert :
      EpochCongruenceTransformerCertificate.{u, v, w, x, y, z, q, r}
        Alphabet Boundary EdgeType SummaryData In₁ In₂ Out₁ Out₂) :
    ∃ transformer : FiniteEpochTransformer.{u, x, y, z, q, r} Alphabet In₁ In₂ Out₁ Out₂,
      cert.transformerSound := by
  exact ⟨cert.transformer, cert.transformerSound_proof⟩

end DistributedSynthesis
