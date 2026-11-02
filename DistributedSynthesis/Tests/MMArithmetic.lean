/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.CounterMachines.MM.StackMacros

/-! Executable checks of the credited MM arithmetic and sentinel-stack macros. -/
namespace DistributedSynthesis.Tests.MMArithmetic
open CounterMachine

def F : MM.Frame 4 := ⟨0,1,2,by decide,by decide,by decide⟩
def v : MM.Registers 4 := fun _ => 42
def values (x : MM.Cfg 4) := (x.1,List.ofFn x.2)
def outcome (x : Option (MM.Cfg 4)) := x.map values

-- MM jumps on zero; positive decrement falls through (unlike MMA).
#guard values (MM.next (MM.dec 0 99) (10,F.regs v 0 5 0)) == (99,[0,5,0,42])
#guard values (MM.next (MM.dec 0 99) (10,F.regs v 3 5 0)) == (11,[2,5,0,42])

#guard MM.StackEncoding.encode [] == 1
#guard MM.StackEncoding.encode [false] == 2
#guard MM.StackEncoding.encode [true] == 3
#guard MM.StackEncoding.encode [true,false] == 5
#guard MM.StackEncoding.encode [false,true] == 6

#guard outcome (MM.runSteps (MM.Arithmetic.transfer F 10) 10 1 (10,F.regs v 0 5 0)) ==
  some (13,[0,5,0,42])
#guard outcome (MM.runSteps (MM.Arithmetic.transfer F 10) 10 10 (10,F.regs v 3 5 0)) ==
  some (13,[0,8,0,42])
#guard outcome (MM.runSteps (MM.Arithmetic.double F 10) 10 13 (10,F.regs v 3 5 0)) ==
  some (14,[0,11,0,42])
#guard outcome (MM.runSteps (MM.Arithmetic.divide F 10) 10 1 (10,F.regs v 0 5 0)) ==
  some (16,[0,5,0,42])
#guard outcome (MM.runSteps (MM.Arithmetic.divide F 10) 10 3 (10,F.regs v 1 5 0)) ==
  some (16,[0,5,1,42])
#guard outcome (MM.runSteps (MM.Arithmetic.divide F 10) 10 25 (10,F.regs v 8 5 0)) ==
  some (16,[0,9,0,42])
#guard outcome (MM.runSteps (MM.Arithmetic.divide F 10) 10 27 (10,F.regs v 9 5 0)) ==
  some (16,[0,9,1,42])

#guard outcome (MM.runSteps (MM.StackMacros.pushZero F 10) 10 9 (10,F.regs v 1 0 0)) ==
  some (17,[2,0,0,42])
#guard outcome (MM.runSteps (MM.StackMacros.pushOne F 10) 10 17 (10,F.regs v 2 0 0)) ==
  some (18,[5,0,0,42])
#guard outcome (MM.runSteps (MM.StackMacros.pop F 10 77 88 99) 10 11 (10,F.regs v 1 0 0)) ==
  some (99,[1,0,0,42])
#guard outcome (MM.runSteps (MM.StackMacros.pop F 10 77 88 99) 10 17 (10,F.regs v 2 0 0)) ==
  some (77,[1,0,0,42])
#guard outcome (MM.runSteps (MM.StackMacros.pop F 10 77 88 99) 10 23 (10,F.regs v 3 0 0)) ==
  some (88,[1,0,0,42])
#guard outcome (MM.runSteps (MM.StackMacros.pop F 10 77 88 99) 10 35 (10,F.regs v 5 0 0)) ==
  some (88,[2,0,0,42])

example : Primrec MM.StackEncoding.encode := MM.StackEncoding.encode_primrec
example (s : List Bool) : 0 < MM.StackEncoding.encode s := MM.StackEncoding.positive s
example (P : MM.Program 4) (base i : Nat) (h : MM.Placed P base i (MM.Arithmetic.divide F i))
    (a b : Nat) (bit : Bool) :
    MM.Reaches₁ P base (i,F.regs v (2*a+(bif bit then 1 else 0)) b 0)
      (i+6,F.regs v 0 (a+b) (bif bit then 1 else 0)) :=
  MM.Arithmetic.divide_correct F P base i h v a b bit

end DistributedSynthesis.Tests.MMArithmetic
