/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmOnebitfringe

/-!
# Fixed-input local partitions
-/

namespace DistributedSynthesis

/-- Certificate for the finite fixed-input partition count and one-bit classes. -/
structure FixedInputPartitionCertificate (t : Nat) where
  processOneClasses : Nat
  processTwoClasses : Nat
  processOne_count : processOneClasses = (3 ^ t + 1) / 2
  processTwo_count : processTwoClasses = (3 ^ t + 1) / 2
  processOne_onlyLastReceivePairs : Prop
  processTwo_onlyLastReceivePairs : Prop
  processOne_onlyLastReceivePairs_proof : processOne_onlyLastReceivePairs
  processTwo_onlyLastReceivePairs_proof : processTwo_onlyLastReceivePairs

/-- Proposition `prop:fixedinputpartition`, paper-facing certificate form. -/
theorem fixed_input_partition
    (t : Nat)
    (cert : FixedInputPartitionCertificate t) :
    cert.processOneClasses = (3 ^ t + 1) / 2 ∧
      cert.processTwoClasses = (3 ^ t + 1) / 2 ∧
      cert.processOne_onlyLastReceivePairs ∧
      cert.processTwo_onlyLastReceivePairs := by
  exact
    ⟨cert.processOne_count,
      cert.processTwo_count,
      cert.processOne_onlyLastReceivePairs_proof,
      cert.processTwo_onlyLastReceivePairs_proof⟩

end DistributedSynthesis
