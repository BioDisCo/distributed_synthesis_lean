/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.CounterMachines.BSMSource

/-! Public clients for the whole-program compiler and unconditional BSM source.
Execution regressions inspect actual laid-out instruction lists, not only blocks.
-/
namespace DistributedSynthesis.Tests.BSMCompiler
open CounterMachine

def emptyStacks : BSM.Stacks 1 := fun _ => []
def sampleStacks (l : List Bool) : BSM.Stacks 1 := fun _ => l
def result (x : Option (BSM.Cfg 1)) := x.map (fun c => (c.1,c.2 0))

def stopGraph : Fin 1 → BSMGraph.Op 1 1 := fun _ => .jump none
def loopGraph : Fin 1 → BSMGraph.Op 1 1 := fun _ => .jump (some 0)
def peekGraph : Fin 1 → BSMGraph.Op 1 1 := fun _ => .peek 0 (fun _ => none)
def pushPopGraph (q : Fin 2) : BSMGraph.Op 1 2 :=
  if q = 0 then .push 0 true (some 1) else .pop 0 (fun _ => none)

#guard (BSMGraph.compile 0 0 stopGraph).length == 9
#guard (BSMGraph.compile 0 0 pushPopGraph).length == 16
-- Entry takes two steps; the terminating jump takes another two.
#guard result (BSM.runSteps (BSMGraph.compile 0 0 stopGraph) 1 4 (1,emptyStacks)) == some (0,[])
-- Padding exists, but the terminal address is zero, never a padding location.
#guard BSM.lookup (BSMGraph.compile 0 0 stopGraph) 1 0 == none
#guard (BSM.lookup (BSMGraph.compile 0 0 stopGraph) 1 6).isSome
-- A nonzero selected entry really starts at its own block, not node zero.
#guard result (BSM.runSteps (BSMGraph.compile 0 1 pushPopGraph) 1 2 (1,emptyStacks)) == some (10,[])
#guard result (BSM.runSteps (BSMGraph.compile 0 1 pushPopGraph) 1 3 (1,emptyStacks)) == some (0,[])
-- Cross-block push/pop execution returns to the original stack.
#guard result (BSM.runSteps (BSMGraph.compile 0 0 pushPopGraph) 1 8 (1,sampleStacks [false])) ==
  some (0,[false])
-- Both nonempty peek branches restore data; empty peek takes the shorter path.
#guard result (BSM.runSteps (BSMGraph.compile 0 0 peekGraph) 1 6 (1,sampleStacks [true,false])) ==
  some (0,[true,false])
#guard result (BSM.runSteps (BSMGraph.compile 0 0 peekGraph) 1 6 (1,sampleStacks [false,true])) ==
  some (0,[false,true])
#guard result (BSM.runSteps (BSMGraph.compile 0 0 peekGraph) 1 3 (1,emptyStacks)) == some (0,[])
-- Cycles remain at the node entry; they do not fall through into padding.
#guard result (BSM.runSteps (BSMGraph.compile 0 0 loopGraph) 1 20 (1,sampleStacks [true])) ==
  some (3,[true])

example : BSM.Halts (1,BSMGraph.compile 0 0 stopGraph,emptyStacks) := by
  rw [BSM.Halts,BSM.Terminates,Part.dom_iff_mem]
  refine ⟨(0,emptyStacks),StateTransition.mem_eval.mpr ⟨?_,?_⟩⟩
  · exact BSM.runSteps_reaches _ _ 4 _ _ (by decide)
  · simp [BSM.step,BSM.lookup]

example (M : Fin 2 → BSMGraph.Op 1 2) (entry : Fin 2) (s : BSM.Stacks 1) :
    BSM.Halts (1,BSMGraph.compile 0 entry M,s) ↔
      (StateTransition.eval (BSMGraph.step M) (some entry,s)).Dom :=
  BSMGraph.initial_halts_iff _ _ _ _

-- Halting reflection also rules out accidental termination through padding.
example : ¬ BSM.Halts (1,BSMGraph.compile 0 0 loopGraph,emptyStacks) := by
  rw [BSMGraph.initial_halts_iff]
  intro h
  obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp h
  obtain ⟨hr,hs⟩ := StateTransition.mem_eval.mp hy
  have he : y = (some 0,emptyStacks) := by
    clear hy hs
    induction hr with
    | refl => rfl
    | @tail b c hab hbc ih =>
      subst b
      simpa [BSMGraph.step,loopGraph,BSMGraph.next] using hbc.symm
  rw [he] at hs
  simp [BSMGraph.step,loopGraph,BSMGraph.next] at hs

example (M : Unit → Turing.TM2.Stmt (fun _ : Fin 1 => Bool) Unit Bool)
    (v : Bool) (s : BSM.Stacks 1) :
    BSM.Halts (1,TM2ToBSM.compile M (Equiv.refl _) 0 () v,s) ↔
      (StateTransition.eval (Turing.TM2.step M) ⟨some (),v,s⟩).Dom :=
  TM2ToBSM.compile_correct M (Equiv.refl _) 0 () v s

example : Primrec BSMSource.reduce := BSMSource.reduce_primrec
example : (fun p : Nat.Partrec.Code => (p.eval 0).Dom) ≤₀ @BSM.Halts 4 :=
  BSMSource.halting_manyOneReducible
example : ¬ ComputablePred (@BSM.Halts 4) := BSMSource.halting_not_computable
example : ¬ ComputablePred BSMSource.WordHalts := BSMSource.wordHalting_not_computable

#guard BSMSource.stackEquiv Turing.PartrecToTM2.K'.main == 0
#guard BSMSource.stackEquiv Turing.PartrecToTM2.K'.stack == 3
#guard BSMSource.inputStacks [true,false] 0 == [true,false]
#guard BSMSource.inputStacks [true,false] 1 == []

end DistributedSynthesis.Tests.BSMCompiler
