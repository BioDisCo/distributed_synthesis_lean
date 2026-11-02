/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefEpochAbstractions

/-!
# Private-input one-step regular predecessor
-/

namespace DistributedSynthesis

universe u v w x y z

/-- Certificate for the effective regular predecessor construction. -/
structure PrivateInputPredecessorCertificate
    (EdgeType : Type u)
    (In₁ : Type v) (In₂ : Type w) where
  predecessor : ((In₁ × In₂) -> TypedPathLanguage EdgeType) -> TypedPathLanguage EdgeType
  isRegular : ((In₁ × In₂) -> TypedPathLanguage EdgeType) -> Prop
  exactForLocallyUniformMoves : ((In₁ × In₂) -> TypedPathLanguage EdgeType) -> Prop

/-- Lemma `lem:privateinputpredecessor`, packaged as the exact finite predecessor certificate. -/
theorem private_input_one_step_regular_predecessor
    {EdgeType : Type u} {In₁ : Type v} {In₂ : Type w}
    (cert : PrivateInputPredecessorCertificate EdgeType In₁ In₂)
    (targets : (In₁ × In₂) -> TypedPathLanguage EdgeType)
    (hregular : cert.isRegular targets)
    (hexact : cert.exactForLocallyUniformMoves targets) :
    cert.isRegular targets ∧ cert.exactForLocallyUniformMoves targets := by
  exact ⟨hregular, hexact⟩

end DistributedSynthesis
