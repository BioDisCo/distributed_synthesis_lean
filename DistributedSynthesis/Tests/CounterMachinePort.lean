/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.CounterMachines

/-! Public clients and finite execution regressions for the credited source port.
No source-undecidability hypothesis is needed for these compiler theorems. -/
namespace DistributedSynthesis.Tests.CounterMachinePort
open CounterMachine MM2

example : Primrec ZeroInitialization.reduce := ZeroInitialization.reduce_primrec
example : Halts ≤₀ ZeroHalts := ZeroInitialization.halting_manyOneReducible_zeroHalting
example : @MMA.Halts 2 ≤₀ ZeroHalts := MMA2ToMM2.halting_manyOneReducible_zeroHalting

example (P : Program) (a b : Nat) :
    ZeroHalts (ZeroInitialization.compile P a b) ↔ Halts (P,a,b) :=
  ZeroInitialization.compile_correct P a b

#guard ZeroInitialization.compile [.decA 0, .decB 99] 2 3 ==
  [.incA, .incA, .incB, .incB, .incB, .decA 0, .decB 104]
#guard ZeroInitialization.compile [.incA, .decA 1] 0 0 == [.incA, .decA 1]

-- Loading an empty source program still terminates, after exactly five rounds.
#guard run (ZeroInitialization.compile [] 2 3) 5 == (6,(2,3))
#guard lookup (ZeroInitialization.compile [] 2 3) 6 == none

-- A relocated jump to zero really halts; it does not jump into the loading prefix.
#guard run (ZeroInitialization.compile [.decA 0] 2 3) 6 == (0,(1,3))
#guard lookup (ZeroInitialization.compile [.decA 0] 2 3) 0 == none

-- An out-of-range positive address remains out of range after relocation.
#guard run (ZeroInitialization.compile [.decB 99] 2 3) 6 == (104,(2,2))
#guard lookup (ZeroInitialization.compile [.decB 99] 2 3) 104 == none

-- Zero decrement falls through, positive decrement jumps, in both models.
#guard run [.decA 0] 1 == (2,(0,0))
#guard MMA2ToMM2.compile [(0,none),(1,none),(0,some 0),(1,some 99)] ==
  [.incA,.incB,.decA 0,.decB 99]
#guard MMA2ToMM2.stateEquiv (MMA.next (0,some 9) (1,![0,7])) == (2,(0,7))
#guard MMA2ToMM2.stateEquiv (MMA.next (0,some 9) (1,![3,7])) == (9,(2,7))
#guard MMA2ToMM2.stateEquiv (MMA.next (1,some 9) (1,![7,0])) == (2,(7,0))
#guard MMA2ToMM2.stateEquiv (MMA.next (1,some 9) (1,![7,3])) == (9,(7,2))

example : ZeroHalts (ZeroInitialization.compile [] 2 3) :=
  (zeroHalts_iff_run _).mpr ⟨5,by decide⟩

example (d : MMA.HaltingInput 2) :
    ZeroHalts (MMA2ToMM2.toZero d) ↔ MMA.Halts d := MMA2ToMM2.toZero_correct d

-- This is deliberately a conditional client: the universality premise is open.
example (h : (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom) ≤₀ Halts) :
    SourceUndecidability := ZeroInitialization.source_of_halting_reduction h

end DistributedSynthesis.Tests.CounterMachinePort
