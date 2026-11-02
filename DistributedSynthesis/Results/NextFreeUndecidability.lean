/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Library.Distributed.EncodedNextFreeReduction
import DistributedSynthesis.Results.UnconditionalUndecidability

/-! # Unconditional next-free LTL synthesis undecidability

Each process has the fixed four-symbol output alphabet `Bool × Bool` (a data
bit and a clock bit). External input alphabets remain singletons. The graph
sequence is unrestricted and strategies have the original full-view perfect
recall. This is a reduction from the established binary-output theorem, not a
change to it. The target syntax contains no next operator, including its clock
constraints. No source interface or additional mathematical axiom is assumed.
-/
namespace DistributedSynthesis.NextFreeUndecidability

/-- No algorithm decides realizability of next-free LTL specifications in the
full-view communication model with singleton inputs and four output symbols
per process. Strategies have unrestricted perfect recall, and the environment
may choose any infinite sequence of the three communication graphs. -/
theorem four_symbol_nextFree_ltl_synthesis_undecidable :
    ¬ ComputablePred EncodedNextFreeReduction.Realizable := by
  intro h
  exact CounterMachine.Unconditional.binary_ltl_synthesis_undecidable
    (ComputablePred.computable_of_manyOneReducible
      EncodedNextFreeReduction.binary_manyOneReducible h)

end DistributedSynthesis.NextFreeUndecidability
