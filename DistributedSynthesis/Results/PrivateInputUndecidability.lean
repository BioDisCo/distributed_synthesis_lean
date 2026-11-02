/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.PrivateInputs.Binary
import DistributedSynthesis.Results.UnconditionalUndecidability

/-! # Undecidability with private binary inputs and no communication

The communication model and the classical private-input architecture
support the same refining paths. The compiler first selects those paths by an
ordinary LTL input assumption and then uses two rounds for each ternary input.
The target is the separate no-communication model, with a Boolean input at
each process, four outputs at process 1, and two at process 2. Strategies have
unrestricted perfect recall.
-/

namespace DistributedSynthesis.PrivateInputUndecidability
open PrivateInputs

/-- Translate a binary-output communication specification to a specification
with private Boolean inputs and no communication. Process one has four output
symbols and process two has two. -/
noncomputable def compile (c : EncodedBinaryReduction.Instance) : Binary.Instance :=
  Binary.compile (Ternary.compile c)

/-- The translation is primitive recursive in the encoded source formula. -/
theorem compile_primrec : Primrec compile := Binary.compile_primrec.comp Ternary.compile_primrec

/-- A translated specification is realizable without communication exactly
when the original specification is realizable in the communication model. -/
theorem compile_realizable_iff (c : EncodedBinaryReduction.Instance) :
    Binary.Realizable (compile c) ↔ EncodedBinaryReduction.Realizable c :=
  (Binary.realizable_iff (Ternary.compile c)).trans (Ternary.realizable_iff c)

/-- The translation is a computable many-one reduction from communication
synthesis to synthesis with independent private inputs and no communication. -/
theorem communication_manyOneReducible :
    EncodedBinaryReduction.Realizable ≤₀ Binary.Realizable :=
  ⟨compile, compile_primrec.to_comp, fun c ↦ (compile_realizable_iff c).symm⟩

/-- No algorithm decides ordinary LTL realizability for two noncommunicating
processes with independent private Boolean inputs, four outputs at process one,
and two at process two. Each output may depend on the complete local input
history, including the input of the current round. -/
theorem binary_input_ltl_synthesis_undecidable : ¬ ComputablePred Binary.Realizable := by
  intro h
  exact CounterMachine.Unconditional.binary_ltl_synthesis_undecidable
    (ComputablePred.computable_of_manyOneReducible communication_manyOneReducible h)

end DistributedSynthesis.PrivateInputUndecidability
