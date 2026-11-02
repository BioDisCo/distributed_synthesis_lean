/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedPublicLeaderInitial
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedBoundaryWidth

/-! Uniform instance-dependent assembly. The finite graph data, leader table,
component bound, and initial graph index are fixed. The private-input family
width and physical objective vary with the instance. -/
namespace Characterisation.EncodedHolesSolver
open DistributedSynthesis
attribute [local irreducible] Primrec
set_option maxHeartbeats 1200000
local instance holesSolverGraphCode : Primcodable EncodedHeaderCompiler.GraphData := inferInstance
local instance holesSolverInitialCode : Primcodable (EncodedHeaderCompiler.GraphData × List Bool × EncodedRoundObjectives.Data × Nat) := inferInstance

/-- Replace only the family-width field of the original graph context. -/
def withWidth (g : EncodedHeaderCompiler.GraphData) (width : Nat) : EncodedHeaderCompiler.GraphData :=
  (g.1,g.2.1,g.2.2.1,g.2.2.2.1,g.2.2.2.2.1,width)

def width (componentBound delay : Nat) (i : EncodedNoDirect.Instance) :=
  EncodedBoundaryWidth.bound componentBound delay
    (i.inputOneSizeMinusOne+1) (i.inputTwoSizeMinusOne+1)

def solve (g : EncodedHeaderCompiler.GraphData) (leaders : List Bool)
    (componentBound initialGraph : Nat) (tables : EncodedNoDirect.Instance → EncodedParityTables.Data)
    (i : EncodedNoDirect.Instance) : Bool :=
  EncodedPublicLeaderGame.solveInitial (withWidth g (width componentBound g.2.2.2.2.1 i))
    leaders (i,tables i) initialGraph

theorem withWidth_primrec : Primrec₂ withWidth :=
  (Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).pair Primrec.snd))))

theorem width_primrec (componentBound delay : Nat) : Primrec (width componentBound delay) := by
  have one : Primrec (fun i : EncodedNoDirect.Instance => i.inputOneSizeMinusOne+1) :=
    Primrec.succ.comp (Primrec.fst.comp EncodedNoDirect.instanceEquiv_primrec)
  have two : Primrec (fun i : EncodedNoDirect.Instance => i.inputTwoSizeMinusOne+1) :=
    Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp EncodedNoDirect.instanceEquiv_primrec))
  exact EncodedBoundaryWidth.bound_primrec.comp ((Primrec.const componentBound).pair
    ((Primrec.const delay).pair (one.pair two)))

theorem width_pos (componentBound delay : Nat) (i : EncodedNoDirect.Instance) :
    0 < width componentBound delay i := Nat.zero_lt_succ _

theorem solve_primrec (g : EncodedHeaderCompiler.GraphData) (leaders : List Bool)
    (componentBound initialGraph : Nat) (tables : EncodedNoDirect.Instance → EncodedParityTables.Data)
    (effective : Primrec tables) : Primrec (solve g leaders componentBound initialGraph tables) := by
  have context := withWidth_primrec.comp (Primrec.const g) (width_primrec componentBound g.2.2.2.2.1)
  have assembled := context.pair
    ((Primrec.const leaders).pair ((Primrec.id.pair effective).pair (Primrec.const initialGraph)))
  have result := EncodedPublicLeaderGame.solveInitial_primrec.comp assembled
  exact result.of_eq (fun _ => rfl)

end Characterisation.EncodedHolesSolver
