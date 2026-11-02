/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Undecidability.OneCounterSoundness
import DistributedSynthesis.Formalizations.Undecidability.RowConditions
import DistributedSynthesis.Results.UnconditionalUndecidability

namespace DistributedSynthesis.Tests.UnconditionalUndecidability
open CounterMachine

example : Primrec SourcePort.reduce := SourcePort.reduce_primrec
example (p : Nat.Partrec.Code) : MM2.ZeroHalts (SourcePort.reduce p) ↔ (p.eval 0).Dom := SourcePort.reduce_correct p
example : MM2.SourceUndecidability := SourcePort.source
example : ¬ ComputablePred MM2.ZeroHalts := SourcePort.zeroHalting_not_computable
example : ¬ ComputablePred (@MMA.Halts 2) := MMA2Source.halting_not_computable
example : ¬ ComputablePred Compiler.EncodedRealizable := Unconditional.encoded_ltl_synthesis_undecidable
example : ¬ ComputablePred EncodedBinaryReduction.Realizable := Unconditional.binary_ltl_synthesis_undecidable

-- The current payload contains one right plan per counter, with no left plan.
example {Q : Type*} (q : Q) (z : Fin 2 → Bool) (c : Fin 2 → Fin 9)
    (r : Fin 2 → Plan) (pos : Fin 3) : ResidueLTL.Output Q :=
  ⟨⟨q,z,c,r⟩,pos⟩

-- The manuscript clauses quantify over all actual executions and need no
-- extra row certificate, plan agreement, or source-undecidability premise.
example {Q : Type*} [DecidableEq Q] [Fintype Q] (M : Machine Q) :
    (∃ σ : StrategyPair Unit Unit (ResidueLTL.Output Q) (ResidueLTL.Output Q),
      ∀ env, Paper.Checks M (execution σ env)) ↔ M.Nonhalting :=
  Paper.checks_realizable_iff_nonhalting M

end DistributedSynthesis.Tests.UnconditionalUndecidability
