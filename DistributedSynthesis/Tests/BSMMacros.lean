/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.CounterMachines.BSMMacros

/-! Independent clients for the Rocq BSM convention and local control blocks. -/
namespace DistributedSynthesis.Tests.BSMMacros
open CounterMachine.BSM

example : Primcodable (HaltingInput 2) := inferInstance

example (P : Program 2) (base i : Nat) :
    lookup P base i = none ↔ i < base ∨ base + P.length ≤ i := lookup_eq_none P base i

example (P : Program 2) (base : Nat) (x : Cfg 2) :
    Terminates P base x ↔ ∃ y, Eval P base x y := terminates_iff_eval P base x

def sampleStacks (l : List Bool) : Stacks 2 := fun k => if k = 0 then l else [true,false,true]
def outcome (o : Option (Cfg 2)) := o.map (fun x => (x.1,x.2 0,x.2 1))

-- Arbitrary bases are allowed, including zero. Halting is outside the code interval.
#guard lookup ([push 0 true] : Program 2) 10 9 == none
#guard lookup ([push 0 true] : Program 2) 10 10 == some (push 0 true)
#guard lookup ([push 0 true] : Program 2) 10 11 == none
#guard lookup ([push 0 true] : Program 2) 0 0 == some (push 0 true)

-- A jump uses no empty-stack hypothesis, even when jumping to its own entry.
#guard outcome (runSteps (jump 0 99) 10 2 (10,sampleStacks [true,false])) ==
  some (99,[true,false],[true,false,true])
#guard outcome (runSteps (jump 0 10) 10 2 (10,sampleStacks [])) ==
  some (10,[],[true,false,true])

-- Peek restores both possible bits; empty takes exactly one step.
#guard outcome (runSteps (peek 0 10 101 102 103) 10 4 (10,sampleStacks [true,false])) ==
  some (101,[true,false],[true,false,true])
#guard outcome (runSteps (peek 0 10 101 102 103) 10 4 (10,sampleStacks [false,true])) ==
  some (102,[false,true],[true,false,true])
#guard outcome (runSteps (peek 0 10 101 102 103) 10 1 (10,sampleStacks [])) ==
  some (103,[],[true,false,true])

-- Push/pop dispatches use the true-fall-through convention correctly.
#guard outcome (runSteps (pushTo 0 true 99) 10 3 (10,sampleStacks [false])) ==
  some (99,[true,false],[true,false,true])
#guard outcome (runSteps (popTo 0 101 102 103) 10 3 (10,sampleStacks [true,false])) ==
  some (101,[false],[true,false,true])
#guard outcome (runSteps (popTo 0 101 102 103) 10 1 (10,sampleStacks [false,true])) ==
  some (102,[true],[true,false,true])
#guard outcome (runSteps (popTo 0 101 102 103) 10 1 (10,sampleStacks [])) ==
  some (103,[],[true,false,true])

example (s : Stacks 2) : Reaches₁ (jump 0 10) 10 (10,s) (10,s) :=
  jump_progress _ _ _ _ _ _ (placed_self _ _)

example (s : Stacks 2) : Reaches₁ (peek 0 10 101 102 103) 10
    (10,s) (peekTarget 101 102 103 (s 0).head?,s) :=
  peek_progress _ _ _ _ _ _ _ _ (placed_self _ _)

end DistributedSynthesis.Tests.BSMMacros
