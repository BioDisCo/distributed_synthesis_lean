/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.CounterMachines.MathlibBridge.UniversalStackMachine

/-! Independent public clients for the Mathlib starting point. No MM2 model,
source-undecidability premise, or synthesis result is imported here. -/
namespace DistributedSynthesis.Tests.MathlibHaltingBridge
open CounterMachine.MathlibBridge Turing Turing.PartrecToTM2

example : Primrec InputEncoding.inputWord := InputEncoding.inputWord_primrec
example : (fun p : Nat.Partrec.Code => (p.eval 0).Dom) ≤₀ WordHalts universalCode :=
  halting_manyOneReducible
example : ¬ ComputablePred (WordHalts universalCode) := wordHalting_not_computable
example : Finite (support universalCode) := finite_control _
example : Fintype.card K' = 4 := four_stacks
example : Fintype.card Γ' = 4 := four_symbols
example : Fintype.card (Option Γ') = 5 := five_store_values

example (p : Nat.Partrec.Code) :
    WordHalts universalCode (InputEncoding.inputWord p) ↔ (p.eval 0).Dom :=
  inputWord_correct p

-- Zero has no bits; every encoded input nevertheless has a number separator.
#guard InputEncoding.numberWord 0 == []
#guard InputEncoding.numberWord 1 == [3]
#guard InputEncoding.numberWord 2 == [2,3]
#guard InputEncoding.numberWord 3 == [3,3]
#guard InputEncoding.numberWord 4 == [2,2,3]
#guard InputEncoding.numberWord 7 == [3,3,3]
#guard InputEncoding.numberWord 8 == [2,2,2,3]
#guard InputEncoding.numberWord 13 == [3,2,3,3]
#guard InputEncoding.carry [true,true,true] == [false,false,false,true]
#guard InputEncoding.decodeWord [0,1,2,3] == [Γ'.consₗ,Γ'.cons,Γ'.bit0,Γ'.bit1]

example (c : ToPartrec.Code) (v : List Nat) :
    (StateTransition.eval (TM2.step (program c)) (initial c (trList v))).Dom ↔
      (c.eval v).Dom := halts_encoded_list c v

-- The halting predicate has an operational, finite-reachability characterization.
example (c : ToPartrec.Code) (w : List (Fin 4)) :
    WordHalts c w ↔ ∃ y,
      TM2.Reaches (program c) (initial c (InputEncoding.decodeWord w)) y ∧ y.l = none :=
  wordHalts_iff_reaches_halt c w

end DistributedSynthesis.Tests.MathlibHaltingBridge
