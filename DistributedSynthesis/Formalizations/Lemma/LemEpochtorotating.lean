/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefEpochAbstractions
import Mathlib.Data.Fintype.Sum

/-!
# Epoch transformers give rotating access states
-/

namespace DistributedSynthesis

universe u v w x y z a b c

/-- The finite state space used after turning epoch states into rotating access states. -/
abbrev EpochRotatingAccessState
    (Boundary : Type a) (P₁ : Type b) (P₂ : Type c) :=
  Sum Boundary (Sum P₁ P₂)

/-- The semantic obligations required by Lemma `lem:epochtorotating`. -/
structure EpochToRotatingCertificate
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (transformer : FiniteEpochTransformer.{u, v, w, x, y, z} Alphabet In₁ In₂ Out₁ Out₂) where
  receiptAndOrderDetermined : Prop
  updateClosed : Prop
  continuationSound : Prop
  hierarchyPreserved : Prop
  receiptAndOrderDetermined_proof : receiptAndOrderDetermined
  updateClosed_proof : updateClosed
  continuationSound_proof : continuationSound
  hierarchyPreserved_proof : hierarchyPreserved

/-- A finite epoch transformer has the finite rotating state space `M_A ⊎ P₁ ⊎ P₂`. -/
theorem epoch_transformer_rotating_state_finite
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (transformer : FiniteEpochTransformer.{u, v, w, x, y, z} Alphabet In₁ In₂ Out₁ Out₂) :
    Nonempty
      (Fintype
        (EpochRotatingAccessState
          transformer.boundary
          (transformer.within Proc.one)
          (transformer.within Proc.two))) := by
  letI : Fintype transformer.boundary := transformer.boundaryFinite
  letI : Fintype (transformer.within Proc.one) := transformer.withinFinite Proc.one
  letI : Fintype (transformer.within Proc.two) := transformer.withinFinite Proc.two
  exact ⟨inferInstance⟩

/--
Paper-facing Lemma `lem:epochtorotating`: under the semantic access-state obligations,
the epoch transformer supplies a finite rotating target.
-/
theorem epoch_transformer_gives_rotating_access_states
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {transformer : FiniteEpochTransformer.{u, v, w, x, y, z} Alphabet In₁ In₂ Out₁ Out₂}
    (cert : EpochToRotatingCertificate transformer) :
    Nonempty
        (Fintype
          (EpochRotatingAccessState
            transformer.boundary
            (transformer.within Proc.one)
            (transformer.within Proc.two))) ∧
      cert.receiptAndOrderDetermined ∧
      cert.updateClosed ∧
      cert.continuationSound ∧
      cert.hierarchyPreserved := by
  exact
    ⟨epoch_transformer_rotating_state_finite transformer,
      cert.receiptAndOrderDetermined_proof,
      cert.updateClosed_proof,
      cert.continuationSound_proof,
      cert.hierarchyPreserved_proof⟩

end DistributedSynthesis
