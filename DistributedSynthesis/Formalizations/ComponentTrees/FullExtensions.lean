/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.ComponentRetraction

/-! Full-source and reduced-source indexing describe the same children.
This is a representation equivalence, with the full component retained.
-/
namespace Characterisation.ComponentTrees.FullExtensions
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (P : Position I₁ I₂ B.State D) (r : Reduction P.past P.state)
variable (out : ClosingPolicy P.Root I₁ I₂ O₁ O₂ D)

def full : Move I₁ I₂ O₁ O₂ B.State D := ⟨P,out,r.map.edge⟩
def reduced : Move I₁ I₂ O₁ O₂ B.State D :=
  ⟨r.imagePosition P,restrictClosingPolicy (r.imageInclusion P) out,id⟩
def includeEnd := mapClosingLayer (I₁:=I₁) (I₂:=I₂) (r.imageInclusion P) D
def projectEnd := mapClosingLayer (I₁:=I₁) (I₂:=I₂) (r.imageProjection P) D

theorem layer_left (e : (r.imagePosition P).End) :
    projectEnd B P r (includeEnd B P r e) = e := by
  rw [projectEnd,includeEnd,mapClosingLayer_comp]
  have inverse : r.imageProjection P ∘ r.imageInclusion P = id := funext (r.imageProjection_fixed P)
  rw [inverse,Representation.mapLayer_id]

theorem history_include (e : (r.imagePosition P).End) :
    P.history (includeEnd B P r e) = (r.imagePosition P).history e := by
  rw [Position.history,includeEnd,← closingLayerHistory_map]
  rfl

theorem live_include (e : (r.imagePosition P).End) :
    extensionLive M (full B P r out) (includeEnd B P r e) =
      extensionLive M (reduced B P r out) e := by
  have kept : closingLayerRoot D (includeEnd B P r e) ∈ retained (full B P r out) := by
    change closingLayerRoot D (mapClosingLayer (r.imageInclusion P) D e) ∈ Finset.univ.image r.map.edge
    rw [closingLayerRoot_map]
    have fixed := congrArg (r.imageInclusion P) (r.imageProjection_fixed P (closingLayerRoot D e))
    exact Finset.mem_image.mpr ⟨r.imageInclusion P (closingLayerRoot D e),Finset.mem_univ _,fixed⟩
  have all : closingLayerRoot D e ∈ retained (reduced B P r out) := by
    change closingLayerRoot D e ∈ Finset.univ.image id
    simp
  change decide (_ ∧ _) = decide (_ ∧ _)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨all, (congrArg (fun h => M.eval (History.graphSequence h) ∈ M.accept)
      (history_include B P r e)) ▸ h.2⟩
  · intro h
    exact ⟨kept, (congrArg (fun h => M.eval (History.graphSequence h) ∈ M.accept)
      (history_include B P r e)).symm ▸ h.2⟩

theorem layer_right (e : P.End) (alive : extensionLive M (full B P r out) e = true) :
    includeEnd B P r (projectEnd B P r e) = e := by
  have kept := (of_decide_eq_true alive).1
  obtain ⟨h,_,eq⟩ := Finset.mem_image.mp kept
  change r.map.edge h = closingLayerRoot D e at eq
  have fixed : r.map.edge (closingLayerRoot D e) = closingLayerRoot D e := by
    rw [← eq]
    exact r.idempotent h
  rw [includeEnd,projectEnd,mapClosingLayer_comp]
  exact mapClosingLayer_fixed_root r.map.edge D e fixed

theorem shape_include (p : Proc) (e f : (r.imagePosition P).End) :
    closingLayerShape P.shape D p (includeEnd B P r e) (includeEnd B P r f) =
      closingLayerShape (r.imagePosition P).shape D p e f := by
  apply Bool.eq_iff_iff.mpr
  rw [closingLayerShape_exact P.past P.shape (extractInputShape_exact P.past),
    closingLayerShape_exact (r.imagePosition P).past (r.imagePosition P).shape
      (extractInputShape_exact (r.imagePosition P).past)]
  change currentView p (P.history (includeEnd B P r e)) = currentView p (P.history (includeEnd B P r f)) ↔ _
  rw [history_include,history_include]
  rfl

theorem component_forward (C : Finset (r.imagePosition P).End)
    (component : IsComponent M (reduced B P r out) C) :
    IsComponent M (full B P r out) (C.image (includeEnd B P r)) :=
  component_image_retract _ _ _ _ _ _ (layer_left B P r) (layer_right B M P r out)
    (shape_include B P r) (live_include B M P r out) C component

theorem component_backward (K : Finset P.End) (component : IsComponent M (full B P r out) K) :
    IsComponent M (reduced B P r out) (K.image (projectEnd B P r)) ∧
      (K.image (projectEnd B P r)).image (includeEnd B P r) = K :=
  component_pullback_retract _ _ _ _ _ _ (layer_left B P r) (layer_right B M P r out)
    (shape_include B P r) (live_include B M P r out) K component

theorem state_include (e : (r.imagePosition P).End) :
    blockSuccessor B P.state out (includeEnd B P r e) =
      blockSuccessor B (r.imagePosition P).state (reduced B P r out).rule e :=
  (blockSuccessor_restrict B (r.imageInclusion P) P.state out e).symm

/-- The child keeps every history and its exact block-successor state. -/
theorem successor_iff (Q : Position I₁ I₂ B.State D) :
    ComponentSuccessor B M (full B P r out) Q ↔ ComponentSuccessor B M (reduced B P r out) Q := by
  constructor
  · rintro ⟨K,component,phase,histories,states⟩
    obtain ⟨back,inverse⟩ := component_backward B M P r out K component
    refine ⟨K.image (projectEnd B P r),back,phase,?_,?_⟩
    · calc
        Q.histories = K.image P.history := histories
        _ = ((K.image (projectEnd B P r)).image (includeEnd B P r)).image P.history :=
          congrArg (Finset.image P.history) inverse.symm
        _ = (K.image (projectEnd B P r)).image (r.imagePosition P).history := by
          simp only [Finset.image_image,Function.comp_def,history_include]
    · intro h e eq
      have inside : includeEnd B P r e.val ∈ K :=
        (Finset.ext_iff.mp inverse _).mp (Finset.mem_image.mpr ⟨e.val,e.property,rfl⟩)
      exact (states h ⟨includeEnd B P r e.val,inside⟩
        (eq.trans (history_include B P r e.val).symm)).trans (state_include B P r out e.val)
  · rintro ⟨C,component,phase,histories,states⟩
    refine ⟨C.image (includeEnd B P r),component_forward B M P r out C component,phase,?_,?_⟩
    · calc
        Q.histories = C.image (r.imagePosition P).history := histories
        _ = (C.image (includeEnd B P r)).image P.history := by
          simp only [Finset.image_image,Function.comp_def,history_include]
    · intro h e eq
      obtain ⟨s,mem,hs⟩ := Finset.mem_image.mp e.property
      have history : h.val = (r.imagePosition P).history s :=
        eq.trans ((congrArg P.history hs).symm.trans (history_include B P r s))
      exact (states h ⟨s,mem⟩ history).trans
        ((state_include B P r out s).symm.trans (congrArg (blockSuccessor B P.state out) hs))


/-- Restrict the full-source rule to r(K); no condition is imposed on its
values outside that image. -/
def node {bound : Nat} (valid : PositionValid B M P)
    (small : (Finset.univ.image r.map.edge).card ≤ bound)
    (coherent : ClosingPolicyCoherent P.shape out) : CompressedNode B M bound where
  position := P
  valid := valid
  reduction := r
  small := by rwa [r.imagePosition_card P]
  rule := (reduced B P r out).rule
  distributed := simulation_rule_coherent (r.imagePosition P).past P.past (r.imageInclusion P)
    (fun _ _ _ same => same) out coherent

theorem node_successor_iff {bound : Nat} (valid : PositionValid B M P)
    (small : (Finset.univ.image r.map.edge).card ≤ bound)
    (coherent : ClosingPolicyCoherent P.shape out) (Q : Position I₁ I₂ B.State D) :
    (node B M P r out valid small coherent).Successor Q ↔
      ComponentSuccessor B M (full B P r out) Q :=
  (successor_iff B M P r out Q).symm

/-- Pulling a reduced rule back to K and restricting it again is identity. -/
theorem original_rule {bound : Nat} (N : CompressedNode B M bound) :
    restrictClosingPolicy (N.reduction.imageInclusion N.position) N.runMove.rule = N.rule := by
  funext t s
  change N.rule t (mapClosingLayer (N.reduction.imageProjection N.position) _
    (mapClosingLayer (N.reduction.imageInclusion N.position) _ s)) = N.rule t s
  rw [mapClosingLayer_comp]
  have inverse : N.reduction.imageProjection N.position ∘ N.reduction.imageInclusion N.position = id :=
    funext (N.reduction.imageProjection_fixed N.position)
  rw [inverse,Representation.mapLayer_id]

theorem original_successor_iff {bound : Nat} (N : CompressedNode B M bound)
    (Q : Position I₁ I₂ B.State D) :
    N.Successor Q ↔ ComponentSuccessor B M N.runMove Q := by
  have same : reduced B N.position N.reduction N.runMove.rule = N.extensionMove := by
    have rule := original_rule B M N
    unfold reduced CompressedNode.extensionMove
    rw [rule]
  change ComponentSuccessor B M N.extensionMove Q ↔ _
  rw [← same]
  exact (successor_iff B M N.position N.reduction N.runMove.rule Q).symm

end
end Characterisation.ComponentTrees.FullExtensions
