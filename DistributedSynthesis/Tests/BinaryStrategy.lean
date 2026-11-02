/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.BinaryStrategy

/-! Public clients of actual strategy construction and finite word tests. -/
open DistributedSynthesis

private def code := BinaryWords.finCode 2 2 (by omega)

example : code.bits 0 0 = true := by decide
example : code.bits 0 1 = false := by decide
example : code.bits 1 0 = false := by decide
example : code.bits 1 1 = true := by decide

example (K : Nat) (data : BinaryStrategy.Payload) :
    BinaryAgreement.Winning K (BinaryStrategy.strategy K data) :=
  BinaryStrategy.strategy_winning K data

example (σ : StrategyPair Unit Unit (Fin 2) (Fin 2)) :
    ∀ env, LTL.Satisfies BinaryAgreement.interp
      (execution (BinaryStrategy.encode code code σ) env)
      (.conj (BinaryAgreement.protocol 2) (BinaryStrategy.validOnCore code code [0,1] [0,1])) := by
  apply BinaryStrategy.encode_protocol_and_validity
  all_goals intro a; fin_cases a <;> simp

example {K : Nat} {O : Type*} (c : BinaryWords.Code O K) (w : OmegaWord Bool)
    (t : Nat) {a b : O}
    (ha : LTL.Satisfies (fun (_ : Unit) bit ↦ bit = true) (w.drop t) (BinaryWords.wordTest () (c.bits a)))
    (hb : LTL.Satisfies (fun (_ : Unit) bit ↦ bit = true) (w.drop t) (BinaryWords.wordTest () (c.bits b))) : a = b :=
  BinaryWords.wordTest_unique _ w () c t ha hb

#guard_msgs (drop info) in
#check BinaryStrategy.encode_stream_data
#guard_msgs (drop info) in
#check BinaryWords.exists_common_codes
