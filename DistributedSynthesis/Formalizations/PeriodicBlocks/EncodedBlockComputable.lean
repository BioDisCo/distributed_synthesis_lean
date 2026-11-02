/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.PeriodicBlocks.EncodedBlockData
import DistributedSynthesis.Formalizations.PeriodicBlocks.PrimitiveRecursive

namespace Characterisation.PeriodicBlocks.EncodedBlock
open DistributedSynthesis
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
attribute [local irreducible] Primrec PrimrecPred

attribute [local fun_prop] FiniteCodeNumbering.unique_primrec
attribute [local fun_prop] EncodedClosingLayers.slots_primrec
attribute [local fun_prop] EncodedClosingReplay.replay_primrec
attribute [local fun_prop] EncodedClosingComponents.mask_primrec
@[local fun_prop] theorem plans_pr : Primrec (fun x : (Nat × Nat) × Nat =>
    EncodedClosingPlans.plans x.1 x.2) := EncodedClosingPlans.plans_primrec
@[local fun_prop] theorem observed_pr : Primrec (fun x : EncodedClosingBanks.Data ×
    EncodedClosingBanks.Slot × EncodedClosingBanks.Slot =>
    EncodedClosingBanks.observed x.1 x.2.1 x.2.2) := EncodedClosingBanks.observed_primrec
@[local fun_prop] theorem coherent_pr : Primrec (fun x : EncodedClosingBanks.Data ×
    EncodedClosingBanks.Bank => EncodedClosingBanks.coherent x.1 x.2) := EncodedClosingBanks.coherent_primrec
@[local fun_prop] theorem priority_pr : Primrec (fun x : EncodedParityTables.Data × Nat =>
    EncodedParityTables.priority x.1 x.2) := EncodedParityTables.priority_primrec

@[fun_prop] theorem width_primrec : Primrec width := by
  unfold width
  fun_prop
@[fun_prop] theorem depth_primrec : Primrec depth := by
  unfold depth
  fun_prop
@[fun_prop] theorem graphs_primrec : Primrec graphs := by
  unfold graphs
  fun_prop
@[fun_prop] theorem objectives_primrec : Primrec objectives := by
  unfold objectives
  fun_prop
@[fun_prop] theorem environments_primrec : Primrec environments := by
  unfold environments
  fun_prop
@[fun_prop] theorem outputs_primrec : Primrec outputs := by
  unfold outputs
  fun_prop
@[fun_prop] theorem rounds_primrec : Primrec rounds := by
  unfold rounds
  fun_prop
@[fun_prop] theorem outputPairs_primrec : Primrec outputPairs := by
  unfold outputPairs
  fun_prop
@[fun_prop] theorem layerContext_primrec : Primrec layerContext := by
  unfold layerContext
  fun_prop
@[fun_prop] theorem endpoints_primrec : Primrec endpoints := by
  unfold endpoints
  fun_prop
@[fun_prop] theorem endCount_primrec : Primrec endCount := by
  unfold endCount
  fun_prop
@[fun_prop] theorem boundaries_primrec : Primrec boundaries := by
  unfold boundaries
  fun_prop
@[fun_prop] theorem masks_primrec : Primrec masks := by
  unfold masks
  fun_prop
@[fun_prop] theorem responses_primrec : Primrec responses := by
  unfold responses
  fun_prop
@[fun_prop] theorem banks_primrec : Primrec banks := by
  unfold banks
  fun_prop
@[fun_prop] theorem moves_primrec : Primrec moves := by
  unfold moves
  fun_prop
@[fun_prop] theorem outcomes_primrec : Primrec outcomes := by
  unfold outcomes
  fun_prop
@[fun_prop] theorem bankData_primrec : Primrec (fun x : Context × Boundary => bankData x.1 x.2) := by
  unfold bankData
  fun_prop
@[fun_prop] theorem endpoint_primrec : Primrec (fun x : Context × Nat => endpoint x.1 x.2) := by
  unfold endpoint
  fun_prop
@[fun_prop] theorem observed_primrec : Primrec (fun x : Context × Boundary × Nat × Nat => observed x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold observed
  fun_prop
@[fun_prop] theorem graphAt_primrec : Primrec (fun x : Data × Boundary × EncodedClosingLayers.Slot => graphAt x.1 x.2.1 x.2.2) := by
  unfold graphAt
  fun_prop
@[fun_prop] theorem objectiveAt_primrec : Primrec (fun x : Data × Move × EncodedClosingLayers.Slot => objectiveAt x.1 x.2.1 x.2.2) := by
  unfold objectiveAt
  fun_prop
@[fun_prop] theorem graphEnd_primrec : Primrec (fun x : Data × Move × Nat => graphEnd x.1 x.2.1 x.2.2) := by
  unfold graphEnd
  fun_prop
@[fun_prop] theorem objectiveEnd_primrec : Primrec (fun x : Data × Move × Nat => objectiveEnd x.1 x.2.1 x.2.2) := by
  unfold objectiveEnd
  fun_prop
@[fun_prop] theorem live_primrec : Primrec (fun x : Data × Move × Nat => live x.1 x.2.1 x.2.2) := by
  unfold live
  fun_prop
@[fun_prop] theorem components_primrec : Primrec (fun x : Data × Move => components x.1 x.2) := by
  unfold components
  fun_prop
@[fun_prop] theorem component_primrec : Primrec (fun x : Data × Move × Nat => component x.1 x.2.1 x.2.2) := by
  unfold component
  fun_prop
@[fun_prop] theorem response_primrec : Primrec (fun x : Context × Move × List Bool => response x.1 x.2.1 x.2.2) := by
  unfold response
  exact (Primrec.list_getD ([],[])).comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
    (Primrec.list_idxOf.comp (Primrec.snd.comp Primrec.snd) (masks_primrec.comp Primrec.fst))
@[fun_prop] theorem folded_primrec : Primrec (fun x : Response × Nat => folded x.1 x.2) := by
  unfold folded
  fun_prop
@[fun_prop] theorem target_primrec : Primrec (fun x : Data × Move × List Bool => target x.1 x.2.1 x.2.2) := by
  unfold target
  fun_prop
@[fun_prop] theorem ResponseValid_primrec : PrimrecPred (fun x : Data × Move × List Bool => ResponseValid x.1 x.2.1 x.2.2) := by
  unfold ResponseValid
  fun_prop
@[fun_prop] theorem Legal_primrec : PrimrecPred (fun x : Data × Boundary × Move => Legal x.1 x.2.1 x.2.2) := by
  unfold Legal
  fun_prop
@[fun_prop] theorem offered_primrec : Primrec (fun x : Data × Move × Outcome => offered x.1 x.2.1 x.2.2) := by
  unfold offered
  apply PrimrecPred.decide
  fun_prop
@[fun_prop] theorem legal_primrec : Primrec (fun x : Data × Boundary × Move => legal x.1 x.2.1 x.2.2) := by
  unfold legal
  apply PrimrecPred.decide
  fun_prop
@[fun_prop] theorem color_primrec : Primrec (fun x : Data × Move × Nat => color x.1 x.2.1 x.2.2) := by
  unfold color
  fun_prop
@[fun_prop] theorem Edge_primrec : PrimrecPred (fun x : Data × (Nat × Nat) × Move × Outcome × (Nat × Nat) => Edge x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  unfold Edge
  fun_prop

end Characterisation.PeriodicBlocks.EncodedBlock
