/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Results.PrivateInputUndecidability

namespace DistributedSynthesis.Tests.PrivateInputUndecidability
open PrivateInputs

example (h k : List Graph) :
    word (FullViewPath.evaluate h).one = word (FullViewPath.evaluate k).one ↔
      (FullViewPath.evaluate h).one = (FullViewPath.evaluate k).one := word_one_eq_iff h k

example (h k : List Graph) :
    word (FullViewPath.evaluate h).two = word (FullViewPath.evaluate k).two ↔
      (FullViewPath.evaluate h).two = (FullViewPath.evaluate k).two := word_two_eq_iff h k

example : Primrec DistributedSynthesis.PrivateInputUndecidability.compile :=
  DistributedSynthesis.PrivateInputUndecidability.compile_primrec

example (c : EncodedBinaryReduction.Instance) :
    Binary.Realizable (DistributedSynthesis.PrivateInputUndecidability.compile c) ↔
      EncodedBinaryReduction.Realizable c :=
  DistributedSynthesis.PrivateInputUndecidability.compile_realizable_iff c

example : ¬ ComputablePred Binary.Realizable :=
  DistributedSynthesis.PrivateInputUndecidability.binary_input_ltl_synthesis_undecidable

-- The original endpoints retain their original types.
example : ¬ ComputablePred CounterMachine.Compiler.EncodedRealizable :=
  CounterMachine.Unconditional.encoded_ltl_synthesis_undecidable

example : ¬ ComputablePred EncodedBinaryReduction.Realizable :=
  CounterMachine.Unconditional.binary_ltl_synthesis_undecidable

end DistributedSynthesis.Tests.PrivateInputUndecidability
