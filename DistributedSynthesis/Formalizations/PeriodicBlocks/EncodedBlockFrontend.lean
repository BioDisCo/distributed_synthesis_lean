/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.PeriodicBlocks.EncodedBlockSolver
import DistributedSynthesis.Formalizations.PeriodicBlocks.ComputableBounds
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedPhysicalObjective
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGuardedFrontend

/-! Uniform generation of every numeric table from a fixed graph recognizer,
a block length, and an encoded finite-input LTL objective. -/
namespace Characterisation.PeriodicBlocks.EncodedBlock
open DistributedSynthesis
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

/-- State count, initial state, three transition rows, and live-state bits. -/
abbrev GraphData := Nat × Nat × List (List Nat) × List Bool
abbrev Question := Nat × GraphData × EncodedRoundObjectives.Data

def instanceBound (x : Question) := numericCompressionBound x.2.1.1
  (EncodedRoundObjectives.stateCount x.2.2) (EncodedPhysicalObjective.environments x.2.2)
  (EncodedPhysicalObjective.outputs x.2.2) x.1

def instanceContext (x : Question) : Context :=
  (instanceBound x,x.1,x.2.1.1,EncodedRoundObjectives.stateCount x.2.2,
    EncodedPhysicalObjective.environments x.2.2,EncodedPhysicalObjective.outputs x.2.2,
    (List.range (EncodedPhysicalObjective.environments x.2.2)).map (fun e =>
      (e/(EncodedRoundObjectives.inputTwo x.2.2*3),e%(EncodedRoundObjectives.inputTwo x.2.2*3)/3,([2,0,1] : List Nat).getD (e%3) 1)),
    (List.range (EncodedPhysicalObjective.outputs x.2.2)).map (fun y =>
      (y/EncodedRoundObjectives.outputTwo x.2.2,y%EncodedRoundObjectives.outputTwo x.2.2)))
def instanceData (x : Question) : Data :=
  (instanceContext x,
    (List.range (EncodedPhysicalObjective.environments x.2.2)).map (fun e => x.2.1.2.2.1.getD (e%3) []),
    x.2.1.2.2.2,EncodedPhysicalObjective.compile x.2.2)
def instanceInitial (x : Question) : Outcome :=
  ((List.range (endCount (instanceContext x))).map (fun _ => false),
    (List.range ((instanceBound x+1)*(instanceBound x+1))).map (fun _ => (true,true)),
    (List.range (instanceBound x+1)).map (fun _ => x.2.1.2.1),
    (List.range (instanceBound x+1)).map (fun _ =>
      EncodedParityTables.initial x.2.2.2 % EncodedRoundObjectives.stateCount x.2.2))
def instanceInput (x : Question) : Input :=
  (instanceData x,EncodedLeaderObjective.priorityBound x.2.2,instanceInitial x,(0,0))
def solveObjective (x : Question) : Bool := solve (instanceInput x)

attribute [local fun_prop] EncodedRoundObjectives.stateCount_primrec
attribute [local fun_prop] EncodedRoundObjectives.inputTwo_primrec EncodedRoundObjectives.outputTwo_primrec
attribute [local fun_prop] EncodedPhysicalObjective.environments_primrec EncodedPhysicalObjective.outputs_primrec
attribute [local fun_prop] EncodedPhysicalObjective.compile_primrec EncodedParityTables.initial_primrec
attribute [local fun_prop] EncodedLeaderObjective.priorityBound_primrec
@[fun_prop] theorem instanceBound_primrec : Primrec instanceBound := by unfold instanceBound; fun_prop
@[fun_prop] theorem instanceContext_primrec : Primrec instanceContext := by unfold instanceContext; fun_prop
@[fun_prop] theorem instanceData_primrec : Primrec instanceData := by unfold instanceData; fun_prop
@[fun_prop] theorem instanceInitial_primrec : Primrec instanceInitial := by unfold instanceInitial; fun_prop
@[fun_prop] theorem instanceInput_primrec : Primrec instanceInput := by unfold instanceInput; fun_prop

theorem solveObjective_primrec : Primrec solveObjective := solve_primrec.comp instanceInput_primrec

/-- This function compiles LTL by the supplied fixed adversary presentation,
then runs the new block solver. No old distributed-synthesis solver is called. -/
def solveLTL (D : Nat) (g : GraphData) (adversary : EncodedParityTables.Data)
    (i : WithInputs.Instance) : Bool :=
  solveObjective (D,g,EncodedGuardedObjective.roundData (adversary,i))

theorem solveLTL_primrec (D : Nat) (g : GraphData) (adversary : EncodedParityTables.Data) :
    Primrec (solveLTL D g adversary) :=
  solveObjective_primrec.comp ((Primrec.const D).pair ((Primrec.const g).pair
    (EncodedGuardedObjective.roundData_primrec.comp ((Primrec.const adversary).pair Primrec.id))))

end Characterisation.PeriodicBlocks.EncodedBlock
