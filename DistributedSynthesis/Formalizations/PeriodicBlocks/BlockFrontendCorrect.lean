/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockSolverCorrect
import DistributedSynthesis.Formalizations.PeriodicBlocks.EncodedBlockFrontend

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
attribute [local instance] Classical.propDecidable

variable {G : Type} {S : Nat} (M : Recognizer Graph G)
  [DecidablePred (· ∈ M.accept)] (graph : G ≃ Fin S)
  (D : Nat) (o : EncodedRoundObjectives.Data)

/-- The fixed prefix recognizer, in the graph order of the LTL frontend. -/
def blockGraphData : EncodedBlock.GraphData :=
  (S,(graph M.start).val,
    List.ofFn (fun g : Fin 3 => List.ofFn (fun q : Fin S =>
      (graph (M.step (graph.symm q) (EncodedParityPresentation.graphNumber.symm g))).val)),
    List.ofFn (fun q : Fin S => decide (graph.symm q ∈ M.accept)))

local notation "question" => (D,blockGraphData M graph,o)
local notation "width" => EncodedBlock.instanceBound question
local notation "env" => EncodedPhysicalObjective.environmentNumber o
local notation "output" => EncodedPhysicalObjective.outputNumber o
local notation "objective" => EncodedLeaderObjective.automaton o
local notation "ctx" => blockContext (B:=width) (D:=D) (S:=S)
  (N:=EncodedRoundObjectives.stateCount o) env output (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
local notation "first" => initialBlockOutcome M (DetParityAutomaton.initial objective) width D
local notation "code" => ((0,0) : HandoverCode width (EncodedLeaderObjective.priorityBound o))

lemma graph_observation_code (g : Fin 3) :
    ([2,0,1] : List Nat).getD g.val 1 = (graphCode (EncodedParityPresentation.graphNumber.symm g)).val := by
  fin_cases g <;> rfl

lemma block_instanceContext : EncodedBlock.instanceContext question = ctx := by
  unfold EncodedBlock.instanceContext blockContext
  repeat' first | apply Prod.ext | rfl
  · apply FiniteSearch.tabulate_eq_ofFn
    intro e
    change (_,_,_) = (_,_,(graphCode (EncodedParityPresentation.graphNumber.symm
      ⟨e.val % (EncodedRoundObjectives.inputTwo o*3) % 3,_⟩)).val)
    have h : e.val % (EncodedRoundObjectives.inputTwo o*3) % 3 = e.val % 3 :=
      Nat.mod_mod_of_dvd _ (dvd_mul_left _ _)
    rw [← graph_observation_code]
    simp only [h]
    rfl
  · apply FiniteSearch.tabulate_eq_ofFn
    intro y
    rfl

lemma block_instanceData : EncodedBlock.instanceData question =
    blockData (B:=width) (D:=D) (N:=EncodedRoundObjectives.stateCount o)
      env output (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) graph M (EncodedPhysicalObjective.compile o) := by
  unfold EncodedBlock.instanceData blockData
  rw [block_instanceContext]
  repeat' first | apply Prod.ext | rfl
  apply FiniteSearch.tabulate_eq_ofFn
  intro e
  change (List.ofFn (fun g : Fin 3 => List.ofFn (fun q : Fin S =>
      (graph (M.step (graph.symm q) (EncodedParityPresentation.graphNumber.symm g))).val))).getD
        (e.val%3) [] = _
  rw [List.getD_eq_getElem _ _ (by simp; omega),List.getElem_ofFn]
  apply congrArg List.ofFn
  funext q
  congr 3
  apply congrArg EncodedParityPresentation.graphNumber.symm
  apply Fin.ext
  exact (Nat.mod_mod_of_dvd _ (dvd_mul_left 3 (EncodedRoundObjectives.inputTwo o))).symm

lemma block_instanceInitial : EncodedBlock.instanceInitial question =
    (outcomePresentation (B:=width) (D:=D) env graph (Equiv.refl (objective).State)).encode first := by
  change ((List.range (EncodedBlock.endCount (EncodedBlock.instanceContext question))).map (fun _ => false),
    (List.range ((width+1)*(width+1))).map (fun _ => (true,true)),
    (List.range (width+1)).map (fun _ => (graph M.start).val),
    (List.range (width+1)).map (fun _ => (objective).initial.val)) =
      (List.ofFn (fun _ : Fin (EncodedClosingLayers.count (width+1,EncodedPhysicalObjective.environments o,D)) => false),
       List.ofFn (fun _ : Fin ((width+1)*(width+1)) => (true,true)),
       List.ofFn (fun _ : Fin (width+1) => (graph M.start).val),
       List.ofFn (fun _ : Fin (width+1) => (objective).initial.val))
  rw [block_instanceContext]
  exact Prod.ext (FiniteSearch.tabulate_eq_ofFn _ _ (fun _ => rfl))
    (Prod.ext (FiniteSearch.tabulate_eq_ofFn _ _ (fun _ => rfl))
      (Prod.ext (FiniteSearch.tabulate_eq_ofFn _ _ (fun _ => rfl))
        (FiniteSearch.tabulate_eq_ofFn _ _ (fun _ => rfl))))

lemma block_instanceInput : EncodedBlock.instanceInput question =
    blockInput env output (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
      graph (Equiv.refl (objective).State) M (EncodedPhysicalObjective.compile o) first code := by
  unfold EncodedBlock.instanceInput blockInput
  rw [block_instanceData,block_instanceInitial]
  simp

variable [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
/-- The arithmetic width used by the compiler suffices for semantic compression. -/
lemma block_instanceBound :
    compressionBound (Fin (EncodedRoundObjectives.inputOne o)) (Fin (EncodedRoundObjectives.inputTwo o))
      (Fin (EncodedRoundObjectives.outputOne o)) (Fin (EncodedRoundObjectives.outputTwo o))
      G (objective).State D ≤ width+1 := by
  letI : Nonempty (Fin (EncodedRoundObjectives.outputOne o)) := ⟨⟨0,by unfold EncodedRoundObjectives.outputOne; omega⟩⟩
  letI : Nonempty (Fin (EncodedRoundObjectives.outputTwo o)) := ⟨⟨0,by unfold EncodedRoundObjectives.outputTwo; omega⟩⟩
  have h := compressionBound_le_numeric
    (Fin (EncodedRoundObjectives.inputOne o)) (Fin (EncodedRoundObjectives.inputTwo o))
    (Fin (EncodedRoundObjectives.outputOne o)) (Fin (EncodedRoundObjectives.outputTwo o))
    G (objective).State D
  have gcard : Nat.card G = S := (Nat.card_congr graph).trans (by simp)
  have ecard : Nat.card (Fin (EncodedRoundObjectives.inputOne o) ×
      Fin (EncodedRoundObjectives.inputTwo o) × Graph) = EncodedPhysicalObjective.environments o :=
    (Nat.card_congr env).trans (by simp)
  have ycard : Nat.card (Fin (EncodedRoundObjectives.outputOne o) ×
      Fin (EncodedRoundObjectives.outputTwo o)) = EncodedPhysicalObjective.outputs o :=
    (Nat.card_congr output).trans (by simp)
  have qcard : Nat.card (objective).State = EncodedRoundObjectives.stateCount o := by
    change Nat.card (Fin (EncodedRoundObjectives.stateCount o)) = _
    simp
  rw [gcard,ecard,ycard,qcard] at h
  exact h.trans (Nat.le_succ width)

/-- The uniform numeric frontend constructs precisely the semantic block game. -/
theorem solveObjective_correct (positive : 0 < D) :
    EncodedBlock.solveObjective question = true ↔
      ∃ tree, (blockGame M (fun q e y => (objective).step q (e,y)) (objective).priority first code).WinningTree tree := by
  unfold EncodedBlock.solveObjective
  rw [block_instanceInput]
  exact encoded_block_solve_correct env output (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
    graph (Equiv.refl (objective).State) M (EncodedPhysicalObjective.compile o)
    (fun q e y => (objective).step q (e,y)) (objective).priority
    (EncodedPhysicalObjective.transition o) (EncodedPhysicalObjective.priority o) positive first code

end
end Characterisation.PeriodicBlocks
