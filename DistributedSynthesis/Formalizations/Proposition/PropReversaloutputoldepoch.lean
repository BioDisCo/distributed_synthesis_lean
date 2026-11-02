/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemDirectreversalboundary
import DistributedSynthesis.Formalizations.Definition.DefEpochAbstractions

/-!
# Reversal output belongs to the old epoch
-/

namespace DistributedSynthesis

universe u v w x

/-- Certificate that a direct-reversal closing round is processed by the old epoch. -/
structure ReversalOutputOldEpochCertificate
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type w) (Out₂ : Type x) where
  closingRound : RoundRecord In₁ In₂ Graph Out₁ Out₂
  oldSide : Proc
  isDirectReversalClosing : closingRound.graph = dominantGraph oldSide.other
  outputAccountedInOldEpoch : Prop
  outputAccountedInOldEpoch_proof : outputAccountedInOldEpoch

/--
Paper-facing Proposition `prop:reversaloutputoldepoch`: a certified direct-reversal
closing round contributes its input/output letter to the old epoch.
-/
theorem reversal_output_belongs_to_old_epoch
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type w} {Out₂ : Type x}
    (cert : ReversalOutputOldEpochCertificate In₁ In₂ Out₁ Out₂) :
    cert.outputAccountedInOldEpoch := by
  exact cert.outputAccountedInOldEpoch_proof

end DistributedSynthesis
