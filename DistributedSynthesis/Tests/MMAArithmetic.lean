/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.CounterMachines.MMA.Division

namespace DistributedSynthesis.Tests.MMAArithmetic
open CounterMachine MMA MMA.Arithmetic
def frame : MMA.Frame 3 := ⟨0,1,by decide⟩
def registers (a b : Nat) : MMA.Registers 3 := ![a,b,42]
theorem frame_regs (a b : Nat) : frame.regs (registers 0 0) a b = registers a b := by
  funext r; fin_cases r <;> rfl
def run (code : MMA.Program 3) (i t a b : Nat) :=
  (MMA.runSteps (List.replicate (i-1) (MMA.inc 2) ++ code) t (i,registers a b)).map
    (fun x => (x.1,List.ofFn x.2))

#guard run (jump 0 99) 10 2 0 5 == some (99,[0,5,42])
#guard run (jump 0 99) 10 2 7 5 == some (99,[7,5,42])
#guard run (transfer frame 10) 10 3 0 5 == some (13,[0,5,42])
#guard run (transfer frame 10) 10 9 3 5 == some (13,[0,8,42])
#guard run (mult frame 4 10) 10 24 3 5 == some (19,[0,17,42])
#guard run (mult frame 0 10) 10 12 3 5 == some (15,[0,5,42])
#guard run (incs frame.y 0) 10 0 3 5 == some (10,[3,5,42])
#guard run (subtract frame false 99 88 3 10) 10 5 7 5 == some (99,[4,5,42])
#guard run (subtract frame false 99 88 3 10) 10 5 2 5 == some (88,[0,5,42])
#guard run (subtract frame true 99 88 3 10) 10 8 7 5 == some (99,[4,8,42])
#guard run (subtract frame true 99 88 3 10) 10 7 2 5 == some (88,[0,7,42])
#guard run (subtract frame true 99 88 0 10) 10 2 2 5 == some (99,[2,5,42])
#guard run (empty frame 99 10) 10 3 0 5 == some (99,[0,5,42])
#guard run (empty frame 99 10) 10 2 7 5 == some (14,[7,5,42])
#guard run (modulo frame 3 10 99 88) 10 29 8 5 == some (88,[0,13,42])
#guard run (modulo frame 3 10 99 88) 10 33 9 5 == some (99,[0,14,42])
#guard run (modulo frame 3 10 99 88) 10 3 0 5 == some (99,[0,5,42])
#guard run (modulo frame 1 10 99 88) 10 21 3 5 == some (99,[0,8,42])
#guard run (divide frame 3 10) 10 21 8 5 == some (24,[0,7,42])
#guard run (divide frame 3 10) 10 27 9 5 == some (24,[0,8,42])
#guard run (divide frame 3 10) 10 3 0 5 == some (24,[0,5,42])

example (P : MMA.Program 3) (h : MMA.Placed P 10 (modulo frame 3 10 99 88)) :
    MMA.Progress P (10,registers 8 5) (88,registers 0 13) := by
  simpa [frame_regs] using modulo_correct frame P 3 10 99 88 h (registers 0 0) 2 2 5 (by decide)
end DistributedSynthesis.Tests.MMAArithmetic
