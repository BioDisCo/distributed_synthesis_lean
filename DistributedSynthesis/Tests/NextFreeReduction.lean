/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Results.NextFreeUndecidability

/-! Public API and executable syntax tests for the next-free extension. -/
open DistributedSynthesis EncodedFiniteLTL

private def translate (c : Code Bool) : Code (Bool ⊕ Unit) :=
  EncodedNextFree.translate (.inr ()) Sum.inl c

private def sample : Code Bool :=
  binary 7 (binary 6 (atom true) (unary 2 (atom false)))
    (unary 5 (unary 5 (binary 4 truth falsity)))

#guard decode (translate sample) =
  LTL.NextFreeTranslation.translate (.inr ()) Sum.inl (decode sample)
#guard decode (translate []) = .falsum
#guard decode (translate [.inr 5]) = .falsum
#guard decode (translate [.inl true, .inl false]) = .falsum
#guard decode (translate [.inr 3, .inr 0, .inr 3]) = .conj .falsum .verum
#guard (translate sample).all (fun token ↦ token != .inr 5)

example : Fintype.card NextFreeClock.Output = 4 := by decide
example : Fintype.card NextFreeClock.Atom = 7 := by decide
example : LTL.NextFree NextFreeClock.protocol := NextFreeClock.protocol_nextFree

example (τ : NextFreeClock.Strategies)
    (win : ∀ env, LTL.Satisfies NextFreeClock.interp (execution τ env) NextFreeClock.protocol)
    (env : EnvironmentSequence Unit Unit) (t : Nat) :
    (execution τ env (t+1)).outputOne.2 ≠ (execution τ env t).outputOne.2 :=
  NextFreeClock.winning_alternates τ win env t

example (p : LTL BinaryAgreement.Atom) :
    NextFreeReduction.Realizable (NextFreeReduction.formula p) ↔
      NextFreeReduction.BinaryRealizable p := NextFreeReduction.realizable_iff p

example : Primrec EncodedNextFreeReduction.compile := EncodedNextFreeReduction.compile_primrec

example (c : EncodedBinaryReduction.Instance) :
    LTL.NextFree (decode (EncodedNextFreeReduction.compile c)) :=
  EncodedNextFreeReduction.compile_nextFree c

example (c : EncodedBinaryReduction.Instance) :
    EncodedNextFreeReduction.Realizable (EncodedNextFreeReduction.compile c) ↔
      EncodedBinaryReduction.Realizable c := EncodedNextFreeReduction.compile_correct c

example : ¬ ComputablePred EncodedNextFreeReduction.Realizable :=
  NextFreeUndecidability.four_symbol_nextFree_ltl_synthesis_undecidable
