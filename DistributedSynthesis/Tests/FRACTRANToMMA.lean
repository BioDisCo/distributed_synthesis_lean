/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.CounterMachines.FRACTRANToMMA.Compiler

namespace DistributedSynthesis.Tests.FRACTRANToMMA
open CounterMachine
def run (Q : FRACTRAN.Program) (t x : Nat) :=
  (MMA.runSteps (FRACTRANToMMA.compile Q) t (1,FRACTRANToMMA.initial x)).map
    (fun c => (c.1,List.ofFn c.2))

#guard run [] 2 7 == some (0,[7,0])
#guard run [(2,3)] 69 3 == some (1,[2,0])
#guard run [(2,3)] 56 2 == some (0,[2,0])
#guard run [(2,3)] 125 3 == some (0,[2,0])
-- Cancellation is allowed: applicability is 4 | 2*x, not 4 | x.
#guard run [(2,4)] 47 2 == some (1,[1,0])
-- A rejected fraction restores the input before the next fraction is tried.
#guard run [(2,3),(2,4)] 101 2 == some (1,[1,0])
-- First applicable fraction wins, even if another one applies too.
#guard run [(2,3),(7,3)] 69 3 == some (1,[2,0])
#guard run [(0,3)] 41 9 == some (1,[0,0])
#guard run [(0,3)] 14 0 == some (1,[0,0])

example : ¬ MMA.Halts (FRACTRANToMMA.compile [(1,1)],FRACTRANToMMA.initial 3) := by
  rw [FRACTRANToMMA.compile_correct _ (by simp [FRACTRAN.Regular])]
  intro h
  obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp h
  obtain ⟨hr,hs⟩ := StateTransition.mem_eval.mp hy
  have he : y = 3 := by
    clear hy hs
    induction hr with
    | refl => rfl
    | @tail b c hab hbc ih =>
      subst b
      simpa [FRACTRAN.step,FRACTRAN.applyFraction] using hbc.symm
  rw [he] at hs
  simp [FRACTRAN.step,FRACTRAN.applyFraction] at hs

example (Q : FRACTRAN.Program) (hQ : FRACTRAN.Regular Q) (x : Nat) :
    MMA.Halts (FRACTRANToMMA.compile Q,FRACTRANToMMA.initial x) ↔ FRACTRAN.Halts (Q,x) :=
  FRACTRANToMMA.compile_correct Q hQ x
example : Primrec FRACTRANToMMA.initial := FRACTRANToMMA.initial_primrec
end DistributedSynthesis.Tests.FRACTRANToMMA
