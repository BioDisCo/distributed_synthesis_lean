/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedHeaderTables
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderAnnotations
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedRoleExchange
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedInitialLeftLeaderBanks

/-! Assemble local solver inputs from raw header codes. Graph-rule data are
fixed with the adversary; every specification-dependent table is generated. -/
namespace Characterisation.EncodedHeaderCompiler
open DistributedSynthesis
attribute [local irreducible] Primrec

/-- Original graph rules, chosen steps, right/left stopping flags, closing
depth, and maximum header width. -/
abbrev GraphData := EncodedClosingScans.Rules × List Nat × List Bool × List Bool × Nat × Nat
abbrev Data := GraphData × EncodedRoundObjectives.Data × EncodedLeaderAlphabet.Header × EncodedClosingBanks.Bank × List EncodedLeaderAlphabet.Outcome
local instance headerCompilerMemoryCode : Primcodable EncodedGraphMemory.Data := inferInstance
local instance headerCompilerPhysicalCode : Primcodable EncodedLeaderPhysical.Data := inferInstance
local instance headerCompilerDataCode : Primcodable Data := inferInstance

def graphData (d : Data) := d.1
def objective (d : Data) := d.2.1
def header (d : Data) := d.2.2.1
def bank (d : Data) := d.2.2.2.1
def permitted (d : Data) := d.2.2.2.2
def rules (d : Data) := (graphData d).1
def graphSteps (d : Data) := (graphData d).2.1
def rightStops (d : Data) := (graphData d).2.2.1
def leftStops (d : Data) := (graphData d).2.2.2.1
def horizon (d : Data) := (graphData d).2.2.2.2.1+1
def width (d : Data) := (graphData d).2.2.2.2.2
def environmentGraphs (d : Data) := (EncodedHeaderTables.environments (objective d)).map (fun r => r.2.2)
def annotations (d : Data) : EncodedLeaderAnnotations.Data :=
  ((rules d).1,EncodedRoundObjectives.stateCount (objective d),EncodedLeaderObjective.priorityBound (objective d),
    graphSteps d,environmentGraphs d,EncodedPhysicalObjective.outputs (objective d),EncodedPhysicalObjective.compile (objective d))
def source (d : Data) := (header d).2.2.2.map (EncodedLeaderAnnotations.graphState (annotations d))
def initial (d : Data) := (header d).2.2.2.map (EncodedLeaderAnnotations.reset (annotations d))
def residuals (d : Data) := (header d).2.2.2.map (EncodedLeaderAnnotations.objectiveState (annotations d))
def advance (d : Data) (one : Bool) := (List.range (rules d).1).map
  (fun q => (graphSteps d).getD (q*3 + bif one then 0 else 2) 0)
def stops (d : Data) (one : Bool) := bif one then rightStops d else leftStops d

def scheduled (d : Data) : EncodedScheduledCollector.Data :=
  ((EncodedHeaderTables.bankData (objective d) (header d) (horizon d),bank d,
      EncodedPhysicalObjective.outputs (objective d),
      EncodedLeaderAnnotations.compile (annotations d) (EncodedPhysicalObjective.alphabet (objective d)),initial d),
    List.range (header d).1,EncodedLeaderAnnotations.minima (annotations d),
    (((header d).1,EncodedPhysicalObjective.environments (objective d),horizon d),rules d,environmentGraphs d,source d),
    [],true,width d)
def originalMemory (d : Data) (one : Bool) : EncodedGraphMemory.Data :=
  (scheduled d,advance d one,stops d one,EncodedLeaderObjective.priorityBound (objective d))
def memory (d : Data) (one : Bool) :=
  bif one then originalMemory d one else EncodedLeftGraphMemory.prepare (originalMemory d one) (stops d one)
def phase (d : Data) (one : Bool) : EncodedLeaderPhase.Data :=
  ((bif one then objective d else EncodedRoleExchange.swap (objective d)),
    EncodedLeaderPhase.headerGroups (header d) one,residuals d)
def compile (d : Data) (one : Bool) : EncodedLeaderPhysical.Data :=
  (phase d one,memory d one,permitted d)
def solve (d : Data) (one : Bool) :=
  bif one then EncodedInitialLeaderBanks.solve (compile d one)
    else EncodedInitialLeftLeaderBanks.solve (compile d one)

theorem graphData_primrec : Primrec graphData := Primrec.fst
theorem objective_primrec : Primrec objective := Primrec.fst.comp Primrec.snd
theorem header_primrec : Primrec header := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem bank_primrec : Primrec bank := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem permitted_primrec : Primrec permitted := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem rules_primrec : Primrec rules := Primrec.fst.comp graphData_primrec
theorem graphSteps_primrec : Primrec graphSteps := Primrec.fst.comp (Primrec.snd.comp graphData_primrec)
theorem rightStops_primrec : Primrec rightStops := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp graphData_primrec))
theorem leftStops_primrec : Primrec leftStops := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp graphData_primrec)))
theorem horizon_primrec : Primrec horizon := Primrec.succ.comp
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp graphData_primrec)))))
theorem width_primrec : Primrec width := Primrec.snd.comp
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp graphData_primrec))))
theorem environmentGraphs_primrec : Primrec environmentGraphs :=
  Primrec.list_map (EncodedHeaderTables.environments_primrec.comp objective_primrec)
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).to₂
theorem annotations_primrec : Primrec annotations := (Primrec.fst.comp rules_primrec).pair
  ((EncodedRoundObjectives.stateCount_primrec.comp objective_primrec).pair
    ((EncodedLeaderObjective.priorityBound_primrec.comp objective_primrec).pair
      (graphSteps_primrec.pair (environmentGraphs_primrec.pair
        ((EncodedPhysicalObjective.outputs_primrec.comp objective_primrec).pair
          (EncodedPhysicalObjective.compile_primrec.comp objective_primrec))))))
theorem source_primrec : Primrec source := Primrec.list_map
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp header_primrec)))
  (EncodedLeaderAnnotations.graphState_primrec.comp (annotations_primrec.comp Primrec.fst) Primrec.snd).to₂
theorem initial_primrec : Primrec initial := Primrec.list_map
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp header_primrec)))
  (EncodedLeaderAnnotations.reset_primrec.comp (annotations_primrec.comp Primrec.fst) Primrec.snd).to₂
theorem residuals_primrec : Primrec residuals := Primrec.list_map
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp header_primrec)))
  (EncodedLeaderAnnotations.objectiveState_primrec.comp (annotations_primrec.comp Primrec.fst) Primrec.snd).to₂
theorem advance_primrec : Primrec₂ advance := Primrec.list_map
  (Primrec.list_range.comp (Primrec.fst.comp (rules_primrec.comp Primrec.fst)))
  ((Primrec.list_getD 0).comp (graphSteps_primrec.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp Primrec.snd (Primrec.const 3))
      (Primrec.cond (Primrec.snd.comp Primrec.fst) (Primrec.const 0) (Primrec.const 2)))).to₂
theorem stops_primrec : Primrec₂ stops := Primrec.cond Primrec.snd
  (rightStops_primrec.comp Primrec.fst) (leftStops_primrec.comp Primrec.fst)
theorem scheduled_primrec : Primrec scheduled :=
  ((EncodedHeaderTables.bankData_primrec.comp (objective_primrec.pair (header_primrec.pair horizon_primrec))).pair
    (bank_primrec.pair ((EncodedPhysicalObjective.outputs_primrec.comp objective_primrec).pair
      ((EncodedLeaderAnnotations.compile_primrec.comp annotations_primrec
        (EncodedPhysicalObjective.alphabet_primrec.comp objective_primrec)).pair initial_primrec)))).pair
    ((Primrec.list_range.comp (Primrec.fst.comp header_primrec)).pair
      ((EncodedLeaderAnnotations.minima_primrec.comp annotations_primrec).pair
        ((((Primrec.fst.comp header_primrec).pair
          ((EncodedPhysicalObjective.environments_primrec.comp objective_primrec).pair horizon_primrec)).pair
          (rules_primrec.pair (environmentGraphs_primrec.pair source_primrec))).pair
          ((Primrec.const []).pair ((Primrec.const true).pair width_primrec)))))
theorem originalMemory_primrec : Primrec₂ originalMemory := (scheduled_primrec.comp Primrec.fst).pair
  (Primrec.pair advance_primrec (Primrec.pair stops_primrec
    (EncodedLeaderObjective.priorityBound_primrec.comp (objective_primrec.comp Primrec.fst))))
theorem memory_primrec : Primrec₂ memory := Primrec.cond Primrec.snd originalMemory_primrec
  (EncodedLeftGraphMemory.prepare_primrec.comp originalMemory_primrec stops_primrec)
theorem phase_primrec : Primrec₂ phase :=
  (Primrec.cond Primrec.snd (objective_primrec.comp Primrec.fst)
    (EncodedRoleExchange.swap_primrec.comp (objective_primrec.comp Primrec.fst))).pair
    ((EncodedLeaderPhase.headerGroups_primrec.comp (header_primrec.comp Primrec.fst) Primrec.snd).pair
      (residuals_primrec.comp Primrec.fst))
theorem compile_primrec : Primrec₂ compile := Primrec.pair phase_primrec (Primrec.pair memory_primrec (permitted_primrec.comp Primrec.fst))
theorem solve_primrec : Primrec₂ solve := Primrec.cond Primrec.snd
  (EncodedInitialLeaderBanks.solve_primrec.comp compile_primrec)
  (EncodedInitialLeftLeaderBanks.solve_primrec.comp compile_primrec)

end Characterisation.EncodedHeaderCompiler
