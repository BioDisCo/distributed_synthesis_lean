/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.PeriodicBlocks.EncodedBlockComputable
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderProgress
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedSupportedGameCorrect

/-! A uniform numeric solver for the block arena. The thread determinizer
and parity-tree solver are the existing generic algorithms. -/
namespace Characterisation.PeriodicBlocks.EncodedBlock
open DistributedSynthesis
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
attribute [local irreducible] Primrec PrimrecPred

abbrev Input := Data × Nat × Outcome × (Nat × Nat)
def progressContext (x : Input) : EncodedLeaderAlphabet.Context := (x.1.1.1,0,x.2.1)
def threadStates (x : Input) := EncodedLeaderProgress.states (progressContext x)
def resolutions (x : Input) := EncodedLeaderProgress.resolutions (progressContext x)
def stateName (x : Input) (q : EncodedLeaderProgress.State) := EncodedLeaderProgress.name (progressContext x) q

def threadStep (d : Data) (q : EncodedLeaderProgress.State) (a : Move × Outcome)
    (r : Nat × Nat) : EncodedLeaderProgress.State := q.bind fun old =>
  if Edge d (old.1,old.2.1) a.1 a.2 r then some (r.1,r.2,r.2) else none

def edgeRow (x : Input) (a : Move × Outcome) : EncodedThreadBuchi.Edges :=
  (threadStates x).flatMap (fun q => (resolutions x).map (fun r =>
    (stateName x q,stateName x (threadStep x.1 q a r))))
def edgeRows (x : Input) :=
  ((moves x.1.1).product (outcomes x.1.1)).map (edgeRow x)
def threadData (x : Input) : EncodedThreadBuchi.Input :=
  ((threadStates x).length,
    stateName x (EncodedLeaderProgress.initial (progressContext x,x.2.2.2)),
    (threadStates x).map EncodedLeaderProgress.priority,edgeRows x)
def offersTable (x : Input) := (moves x.1.1).flatMap (fun m =>
  (outcomes x.1.1).map (offered x.1 m))
def legalTable (x : Input) := (outcomes x.1.1).flatMap (fun b =>
  (moves x.1.1).map (legal x.1 b.2))
def compile (x : Input) : EncodedSupportedGame.Data :=
  ((outcomes x.1.1).length-1,(moves x.1.1).length,
    EncodedThreadCompiler.compile (threadData x),(@List.idxOf Outcome instBEqOfDecidableEq x.2.2.1 (outcomes x.1.1)),
    offersTable x,legalTable x)
def solve (x : Input) := EncodedSupportedGame.solve (compile x)

attribute [local fun_prop] EncodedLeaderProgress.states_primrec EncodedLeaderProgress.resolutions_primrec
attribute [local fun_prop] EncodedLeaderProgress.initial_primrec EncodedLeaderProgress.priority_primrec
attribute [local fun_prop] EncodedThreadCompiler.compile_primrec EncodedSupportedGame.solve_primrec
@[local fun_prop] theorem name_pr : Primrec (fun x : EncodedLeaderAlphabet.Context ×
    EncodedLeaderProgress.State => EncodedLeaderProgress.name x.1 x.2) := EncodedLeaderProgress.name_primrec
@[local fun_prop] theorem some_pr {X : Type*} [Primcodable X] : Primrec (@some X) := Primrec.option_some

@[fun_prop] theorem progressContext_primrec : Primrec progressContext := by unfold progressContext; fun_prop
@[fun_prop] theorem threadStates_primrec : Primrec threadStates := by unfold threadStates; fun_prop
@[fun_prop] theorem resolutions_primrec : Primrec resolutions := by unfold resolutions; fun_prop
@[fun_prop] theorem stateName_primrec : Primrec (fun x : Input × EncodedLeaderProgress.State => stateName x.1 x.2) := by
  unfold stateName; fun_prop
@[fun_prop] theorem threadStep_primrec : Primrec (fun x : Data × EncodedLeaderProgress.State ×
    (Move × Outcome) × (Nat × Nat) => threadStep x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold threadStep
  apply Primrec.option_bind (by fun_prop)
  change Primrec (fun x : (Data × EncodedLeaderProgress.State × (Move × Outcome) × (Nat × Nat)) ×
      (Nat × Nat × Nat) =>
    if Edge x.1.1 (x.2.1,x.2.2.1) x.1.2.2.1.1 x.1.2.2.1.2 x.1.2.2.2
    then some (x.1.2.2.2.1,x.1.2.2.2.2,x.1.2.2.2.2) else none)
  apply Primrec.ite
  · fun_prop
  · fun_prop
  · fun_prop
@[fun_prop] theorem edgeRow_primrec : Primrec (fun x : Input × (Move × Outcome) => edgeRow x.1 x.2) := by
  unfold edgeRow; fun_prop
@[fun_prop] theorem edgeRows_primrec : Primrec edgeRows := by unfold edgeRows; fun_prop
@[fun_prop] theorem threadData_primrec : Primrec threadData := by unfold threadData; fun_prop
@[fun_prop] theorem offersTable_primrec : Primrec offersTable := by unfold offersTable; fun_prop
@[fun_prop] theorem legalTable_primrec : Primrec legalTable := by unfold legalTable; fun_prop
@[fun_prop] theorem compile_primrec : Primrec compile := by
  unfold compile
  fun_prop
/-- Primitive recursiveness is uniform in every finite table and bound. -/
theorem solve_primrec : Primrec solve := EncodedSupportedGame.solve_primrec.comp compile_primrec

end Characterisation.PeriodicBlocks.EncodedBlock
