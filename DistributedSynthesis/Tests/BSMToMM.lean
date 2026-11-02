/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.CounterMachines.MMSource

/-! Whole-program and public-interface regressions for BSM-to-MM compilation. -/
namespace DistributedSynthesis.Tests.BSMToMM
open CounterMachine

def sourceStacks (l : List Bool) : BSM.Stacks 2 := fun k => if k = 0 then l else [true]
def outcome (x : Option (MM.Cfg 4)) := x.map (fun c => (c.1,List.ofFn c.2))
def run (P : BSM.Program 2) (t : Nat) (l : List Bool) :=
  outcome (MM.runSteps (BSMToMM.compile P) 1 t (1,BSMToMM.state (sourceStacks l)))

#guard (BSMToMM.compile ([] : BSM.Program 2)).length == 1
#guard (BSMToMM.compile ([BSM.push 0 true] : BSM.Program 2)).length == 17
#guard run [] 1 [] == some (0,[0,0,1,3])
#guard run [BSM.push 0 false] 11 [] == some (0,[0,0,2,3])
#guard run [BSM.push 0 true] 12 [] == some (0,[0,0,3,3])
#guard run [BSM.pop 0 0 0] 12 [] == some (0,[0,0,1,3])
#guard run [BSM.pop 0 0 0] 18 [false] == some (0,[0,0,1,3])
#guard run [BSM.pop 0 0 0] 24 [true] == some (0,[0,0,1,3])
#guard run [BSM.push 0 true,BSM.pop 0 0 0] 35 [] == some (0,[0,0,1,3])
#guard run [BSM.push 0 true,BSM.pop 0 0 0] 54 [false] == some (0,[0,0,2,3])
-- A branch to source address one lands on its block, not the bootstrap.
#guard run [BSM.pop 0 1 0] 18 [false] == some (2,[0,0,1,3])
#guard run [BSM.pop 0 1 0] 29 [false] == some (0,[0,0,1,3])
#guard run [BSM.pop 0 99 99] 12 [] == some (0,[0,0,1,3])

def loopProgram : BSM.Program 2 := [BSM.pop 0 0 1]
#guard run loopProgram 12 [] == some (2,[0,0,1,3])

example : ¬ MM.Halts (BSMToMM.compile loopProgram,BSMToMM.state (sourceStacks [])) := by
  rw [BSMToMM.compile_correct]
  intro h
  obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp h
  obtain ⟨hr,hs⟩ := StateTransition.mem_eval.mp hy
  have he : y = (1,sourceStacks []) := by
    clear hy hs
    induction hr with
    | refl => rfl
    | @tail b c hab hbc ih =>
      subst b
      simpa [BSM.step,BSM.lookup,BSM.next,BSM.pop,loopProgram,sourceStacks] using hbc.symm
  rw [he] at hs
  simp [BSM.step,BSM.lookup,BSM.next,BSM.pop,loopProgram,sourceStacks] at hs

example (P : BSM.Program 2) (s : BSM.Stacks 2) :
    MM.Halts (BSMToMM.compile P,BSMToMM.state s) ↔ BSM.Halts (1,P,s) :=
  BSMToMM.compile_correct P s

example : Primrec MMSource.reduce := MMSource.reduce_primrec
example : (fun p : Nat.Partrec.Code => (p.eval 0).Dom) ≤₀ @MM.Halts 6 := MMSource.halting_manyOneReducible
example : ¬ ComputablePred (@MM.Halts 6) := MMSource.halting_not_computable
example : ¬ ComputablePred MMSource.WordHalts := MMSource.wordHalting_not_computable

#guard List.ofFn (MMSource.inputRegisters [true,false]) == [0,0,5,1,1,1]
#guard List.ofFn (MMSource.inputRegisters []) == [0,0,1,1,1,1]

end DistributedSynthesis.Tests.BSMToMM
