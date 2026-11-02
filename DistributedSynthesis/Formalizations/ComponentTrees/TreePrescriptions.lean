/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.TreeCoverage

/-! Consistent local output prescriptions, following the English readback
proof and reusing the library's view, policy, and local-strategy machinery.
-/
namespace Characterisation.ComponentTrees.UncompressedTree
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames.HistoryGame
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable {B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D)}
variable {M : Recognizer Graph G} [DecidablePred (· ∈ M.accept)]
variable (tree : UncompressedTree B M) (valid : tree.Valid)

/-- Exactly the output prescriptions in the English proof, restricted to
live histories reached along supported finite plays. -/
structure Prescription where
  node : List (Position I₁ I₂ B.State D)
  supported : publicSupport UncompressedNode.offers tree node = true
  time : Fin D
  scenario : ClosingLayer (tree node).position.Root I₁ I₂ (time.val+1)
  live : M.eval (History.graphSequence
    (closingLayerHistory (tree node).position.past (time.val+1) scenario)) ∈ M.accept

def prescribedHistory (x : Prescription tree) : EnvHistory I₁ I₂ :=
  closingLayerHistory (tree x.node).position.past (x.time.val+1) x.scenario

def prescribedOutput (x : Prescription tree) : O₁ × O₂ :=
  (tree x.node).rule x.time x.scenario

include valid in
theorem prescribed_length (x : Prescription tree) :
    List.length (prescribedHistory tree x) = x.node.length * D + (x.time.val+1) := by
  have len := closingLayerHistory_length (tree x.node).position.past ((tree x.node).position.phase*D)
    (fun h => (tree x.node).position.lengths h.val h.property) (x.time.val+1) x.scenario
  simpa only [position_phase tree valid x.node x.supported] using len

include valid in
theorem prescription_times (x y : Prescription tree) (p : Proc)
    (same : currentView p (prescribedHistory tree x) = currentView p (prescribedHistory tree y)) :
    x.node.length = y.node.length ∧ x.time = y.time := by
  have adjacent : InputAdjacent (prescribedHistory tree x) (prescribedHistory tree y) := by
    cases p <;> [exact Or.inl same; exact Or.inr same]
  have lengths := adjacent_same_depth (inputAdjacent_projects adjacent)
  simp only [History.graphSequence,List.length_map] at lengths
  rw [prescribed_length tree valid x,prescribed_length tree valid y] at lengths
  have tx := x.time.isLt
  have ty := y.time.isLt
  have nodes : x.node.length = y.node.length := by
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt | gt
    · have bound := Nat.mul_le_mul_right D (Nat.succ_le_of_lt lt)
      simp only [Nat.succ_mul] at bound
      omega
    · have bound := Nat.mul_le_mul_right D (Nat.succ_le_of_lt gt)
      simp only [Nat.succ_mul] at bound
      omega
  refine ⟨nodes,Fin.ext ?_⟩
  rw [nodes] at lengths
  omega

include valid in
theorem prescription_nodes (x y : Prescription tree) (p : Proc)
    (same : currentView p (prescribedHistory tree x) = currentView p (prescribedHistory tree y)) :
    x.node = y.node := by
  obtain ⟨lengths,times⟩ := prescription_times tree valid x y p same
  have old : currentView p (closingLayerRoot (x.time.val+1) x.scenario).val =
      currentView p (closingLayerRoot (y.time.val+1) y.scenario).val := by
    have left := lagView_suffix p (closingLayerRoot (x.time.val+1) x.scenario).val
      (scenarioWord (x.time.val+1) x.scenario).val
    have right := lagView_suffix p (closingLayerRoot (y.time.val+1) y.scenario).val
      (scenarioWord (y.time.val+1) y.scenario).val
    rw [(scenarioWord (x.time.val+1) x.scenario).property] at left
    rw [(scenarioWord (y.time.val+1) y.scenario).property] at right
    have lx : lagView (x.time.val+1) (currentView p (prescribedHistory tree x)) =
        currentView p (closingLayerRoot (x.time.val+1) x.scenario).val := by
      simpa only [prescribedHistory,scenarioWord_history,Position.past] using left
    have ly : lagView (y.time.val+1) (currentView p (prescribedHistory tree y)) =
        currentView p (closingLayerRoot (y.time.val+1) y.scenario).val := by
      simpa only [prescribedHistory,scenarioWord_history,Position.past] using right
    have shift := congrArg (fun t : Fin D => lagView (t.val+1)
      (currentView p (prescribedHistory tree y))) times
    exact lx.symm.trans ((congrArg (lagView (x.time.val+1)) same).trans (shift.trans ly))

  exact nodes_equal_of_view tree valid x.node y.node lengths x.supported y.supported _ _ p old

include valid in
theorem prescriptions_consistent (x y : Prescription tree) (p : Proc)
    (same : currentView p (prescribedHistory tree x) = currentView p (prescribedHistory tree y)) :
    match p with
    | .one => (prescribedOutput tree x).1 = (prescribedOutput tree y).1
    | .two => (prescribedOutput tree x).2 = (prescribedOutput tree y).2 := by
  have nodes := prescription_nodes tree valid x y p same
  have times := (prescription_times tree valid x y p same).2
  rcases x with ⟨node,support,t,e,live⟩
  rcases y with ⟨other,otherSupport,u,f,otherLive⟩
  dsimp only at nodes times
  subst other
  subst u
  have shape := (closingLayerShape_exact (tree node).position.past _
    (extractInputShape_exact (tree node).position.past) (t.val+1) p e f).mpr same
  have distributed := (tree node).distributed t
  cases p
  · exact distributed.1 e f shape
  · exact distributed.2 e f shape

include valid in
/-- Assign arbitrary values elsewhere using the existing local-table lemma.
This is the paper's global f, agreeing with ALL live prescriptions at once. -/
theorem component_controller_strategy [Nonempty O₁] [Nonempty O₂] :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ x : Prescription tree,
      (σ.one (currentView .one (prescribedHistory tree x)),
       σ.two (currentView .two (prescribedHistory tree x))) = prescribedOutput tree x := by
  let history := prescribedHistory tree
  let out := prescribedOutput tree
  have coherent : ShapeCoherent (extractInputShape history) out := by
    constructor
    · intro x y same
      exact prescriptions_consistent tree valid x y .one
        ((extractInputShape_exact history .one x y).mp same)
    · intro x y same
      exact prescriptions_consistent tree valid x y .two
        ((extractInputShape_exact history .two x y).mp same)
  obtain ⟨σ,correct⟩ := (shapeCoherent_iff_local history _ (extractInputShape_exact history) out).mp coherent
  exact ⟨σ,fun x => Prod.ext (correct x).1 (correct x).2⟩


end
end Characterisation.ComponentTrees.UncompressedTree
