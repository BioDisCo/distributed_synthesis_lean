/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.CounterMachines.Source
import DistributedSynthesis.Results.Undecidability
import DistributedSynthesis.Results.BinaryUndecidability

/-! # Unconditional encoded LTL synthesis undecidability

These endpoints discharge the existing explicit source parameter with the
proved Mathlib/Rocq source port. The original conditional APIs remain unchanged.
-/
namespace DistributedSynthesis.CounterMachine.Unconditional

/-- No algorithm decides whether a finite-output LTL specification has a pair
of perfect-recall strategies winning against every sequence of the three
communication graphs. Inputs are singletons; the instance encodes a finite
output alphabet and a formula whose atoms test graph and output letters. -/
theorem encoded_ltl_synthesis_undecidable : ¬ ComputablePred Compiler.EncodedRealizable :=
  Compiler.encoded_ltl_synthesis_undecidable SourcePort.source

/-- LTL synthesis remains undecidable when each process outputs a single Boolean
value per round. Inputs are singletons, all three communication graphs are
allowed, and strategies may use their entire local views. -/
theorem binary_ltl_synthesis_undecidable : ¬ ComputablePred EncodedBinaryReduction.Realizable :=
  BinaryCompiler.binary_ltl_synthesis_undecidable SourcePort.source

end DistributedSynthesis.CounterMachine.Unconditional
