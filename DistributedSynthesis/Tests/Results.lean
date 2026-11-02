/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Results

/-! Preserve all four result families through their public entry points. -/
open DistributedSynthesis

example (P : CounterMachine.MM2.Program) :
    CounterMachine.Compiler.EncodedRealizable (CounterMachine.Compiler.compileInstance P) ↔
      ¬ CounterMachine.MM2.ZeroHalts P :=
  CounterMachine.Compiler.compiled_realizable_iff P

example (source : CounterMachine.MM2.SourceUndecidability) :
    ¬ ComputablePred CounterMachine.Compiler.EncodedRealizable :=
  CounterMachine.Compiler.encoded_ltl_synthesis_undecidable source

#guard_msgs (drop info) in
#check ScalingSafety.ResidueLTL.ltl_realizable_not_finite
#guard_msgs (drop info) in
#check DetParityAutomaton.summaryGameDelayOneViewHierarchy_holds
#guard_msgs (drop info) in
#check main_result_for_ltl_noDirect_fragment_synthesis_finiteAlphabets
