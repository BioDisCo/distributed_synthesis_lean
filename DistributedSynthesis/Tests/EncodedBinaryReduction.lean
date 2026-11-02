/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Results.BinaryUndecidability

/-! Public clients and executable small-alphabet postfix regression tests.
The machine payload alphabet is intentionally not enumerated by these tests.
-/
open DistributedSynthesis EncodedFiniteLTL

private def source : Code Bool := binary 7 (atom true) (unary 5 (atom false))
private def run (c : Code Bool) : Code Bool :=
  EncodedBlockTranslation.translate 3 (EncodedBinarySyntax.marker true) atom c

#guard decode (run source) = LTL.BlockTranslation.translate 3 (LTL.BinaryClock.marker true)
  LTL.atom (.release (.atom true) (.next (.atom false)))
#guard decode (run []) = .falsum
#guard decode (run [.inr 7]) = .falsum
#guard decode (run [.inl true, .inl false]) = .falsum
#guard decode (run [.inr 3, .inr 0, .inr 3]) = .conj .falsum .verum

-- All eight operators are included, not only the constructors used above.
example (c : Code Bool) :
    Represents (run c) (LTL.BlockTranslation.translate 3 (LTL.BinaryClock.marker true) LTL.atom (decode c)) :=
  EncodedBlockTranslation.translate_rep 3 _ _ (EncodedBinarySyntax.marker_rep true) atom LTL.atom atom_rep c

example : Primrec run :=
  EncodedBlockTranslation.translate_primrec (Primrec.const 3) (Primrec.const _)
    (atom_primrec.comp Primrec.snd).to₂ Primrec.id

#guard decode (EncodedBinarySyntax.frame true false 1) = LTL.BinaryClock.frame true false 1
#guard decode (EncodedBinarySyntax.word 2 true 1) =
  BinaryWords.wordTest true (fun j : Fin 2 ↦ decide (1 = j.val))

example (I : CounterMachine.Compiler.Instance) :
    EncodedBinaryReduction.Realizable (CounterMachine.BinaryCompiler.compileInstance I) ↔
      CounterMachine.Compiler.EncodedRealizable I :=
  CounterMachine.BinaryCompiler.compiled_realizable_iff I

example : Primrec CounterMachine.BinaryCompiler.compileProgram :=
  CounterMachine.BinaryCompiler.compileProgram_primrec

example (P : CounterMachine.MM2.Program) :
    EncodedBinaryReduction.Realizable (CounterMachine.BinaryCompiler.compileProgram P) ↔
      ¬ CounterMachine.MM2.ZeroHalts P :=
  CounterMachine.BinaryCompiler.compileProgram_realizable_iff P

-- The public endpoint takes exactly the agreed source interface.
example (source : CounterMachine.MM2.SourceUndecidability) :
    ¬ ComputablePred EncodedBinaryReduction.Realizable :=
  CounterMachine.BinaryCompiler.binary_ltl_synthesis_undecidable source
