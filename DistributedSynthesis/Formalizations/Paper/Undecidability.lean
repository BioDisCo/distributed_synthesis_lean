/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Results.UnconditionalUndecidability

/-!
# Undecidability of lossy-link synthesis

Manuscript source label: `thm:undecidability`.

## Paper statement

The \textsc{LL-Synthesis} problem is undecidable.

## Correspondence

The unconditional source theorem is used here: no source-undecidability premise is
assumed. Singleton inputs already give the negative result.

## Reading the proof

See the [proof locations](PROOFS.md#undecidability-of-lossy-link-synthesis-of-lossy-link-synthesis-of-lossy-link-synthesis) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.Undecidability

/-- Reuses `DistributedSynthesis.CounterMachine.Unconditional.encoded_ltl_synthesis_undecidable`. -/
theorem encoded_ltl_synthesis_undecidable :
    ¬ComputablePred
        CounterMachine.Compiler.EncodedRealizable :=
  @_root_.DistributedSynthesis.CounterMachine.Unconditional.encoded_ltl_synthesis_undecidable

end DistributedSynthesis.Paper.Undecidability
