/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.CounterMachines.FRACTRANSource

/-! Fraction cancellation, priority, self-jumps, and public source regressions. -/
namespace DistributedSynthesis.Tests.MMToFRACTRAN
open CounterMachine

-- Applicability tests the product, not just the input. Fractions need not be reduced.
#guard FRACTRAN.step [(6,4)] 2 == some 3
#guard FRACTRAN.step [(6,4)] 1 == none
#guard FRACTRAN.step [(7,7)] 2 == some 2
#guard FRACTRAN.step [(3,2),(5,2)] 2 == some 3
#guard FRACTRAN.step [(3,2),(5,3)] 3 == some 5
#guard FRACTRAN.step [] 9 == none
-- Unsupported zero denominators are skipped; regularity excludes this case.
#guard FRACTRAN.step [(3,0),(2,1)] 4 == some 8

private theorem entry_one : MMToFRACTRAN.entry 1 = 7 := Nat.nth_prime_three_eq_seven
private theorem active_one : MMToFRACTRAN.active 1 = 11 := Nat.nth_prime_four_eq_eleven
private theorem entry_two : MMToFRACTRAN.entry 2 = 17 := by
  change Nat.nth Nat.Prime 6 = 17
  have hc : Nat.count Nat.Prime 17 = 6 := by decide
  rw [← hc]
  exact Nat.nth_count (by decide : Nat.Prime 17)
private theorem reg_zero : MMToFRACTRAN.reg (0 : Fin 1) = 5 := Nat.nth_prime_two_eq_five

example : MMToFRACTRAN.compile ([MM.inc 0] : MM.Program 1) = [(11,7),(85,11)] := by
  simp [MMToFRACTRAN.compile,MMToFRACTRAN.code,MMToFRACTRAN.block,MMToFRACTRAN.enter,
    MMToFRACTRAN.actions,MM.inc,entry_one,active_one,entry_two,reg_zero]

def selfJump : MM.Program 1 := [MM.dec 0 1]
def selfFractions : FRACTRAN.Program := [(11,7),(17,55),(7,11)]
theorem selfJump_compile : MMToFRACTRAN.compile selfJump = selfFractions := by
  simp [MMToFRACTRAN.compile,MMToFRACTRAN.code,MMToFRACTRAN.block,MMToFRACTRAN.enter,
    MMToFRACTRAN.actions,MM.dec,selfJump,selfFractions,entry_one,active_one,entry_two,reg_zero]

-- The zero-counter self-jump really loops in two steps.
#guard FRACTRAN.runSteps selfFractions 1 7 == some 11
#guard FRACTRAN.runSteps selfFractions 2 7 == some 7
#guard FRACTRAN.runSteps selfFractions 8 7 == some 7
-- A positive counter selects decrement before the zero branch, then halts.
#guard FRACTRAN.runSteps selfFractions 2 35 == some 17
#guard FRACTRAN.step selfFractions 17 == none
-- Entry/active control primes for other addresses do not activate this block.
#guard FRACTRAN.step selfFractions 2 == none
#guard FRACTRAN.step selfFractions 3 == none
#guard FRACTRAN.step selfFractions 19 == none
#guard FRACTRAN.runSteps [(11,7),(85,11)] 2 7 == some 85
#guard FRACTRAN.step [(11,7),(85,11)] 85 == none

example : ¬ FRACTRAN.Halts (MMToFRACTRAN.compile selfJump,MMToFRACTRAN.state (1,fun _ : Fin 1 => 0)) := by
  rw [MMToFRACTRAN.compile_correct]
  intro h
  obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp h
  obtain ⟨hr,hs⟩ := StateTransition.mem_eval.mp hy
  have he : y = (1,fun _ => 0) := by
    clear hy hs
    induction hr with
    | refl => rfl
    | @tail b c hab hbc ih =>
      subst b
      simpa [MM.step,MM.lookup,MM.next,MM.dec,selfJump] using hbc.symm
  rw [he] at hs
  simp [MM.step,MM.lookup,MM.next,MM.dec,selfJump] at hs

example {n : Nat} (P : MM.Program n) (v : MM.Registers n) :
    FRACTRAN.RegularHalts (MMToFRACTRAN.compile P,MMToFRACTRAN.state (1,v)) ↔ MM.Halts (P,v) :=
  MMToFRACTRAN.compile_regular_correct P v
example : Primrec FRACTRANSource.reduce := FRACTRANSource.reduce_primrec
example : FRACTRAN.Regular FRACTRANSource.program := FRACTRANSource.program_regular
example : ¬ ComputablePred FRACTRAN.RegularHalts := FRACTRANSource.regularHalting_not_computable
example : ¬ ComputablePred FRACTRANSource.WordHalts := FRACTRANSource.wordHalting_not_computable
example (P : FRACTRAN.Program) (hP : FRACTRAN.Regular P) (x y : Nat) :
    FRACTRAN.step P x = some y ↔ FRACTRAN.RelStep P x y := FRACTRAN.step_eq_some_iff hP x y

end DistributedSynthesis.Tests.MMToFRACTRAN
