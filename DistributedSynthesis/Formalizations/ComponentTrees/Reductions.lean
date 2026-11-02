/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.ViewMaps
import DistributedSynthesis.Formalizations.ComponentTrees.Compression

/-! The reductions of `main.tex`: arbitrary state-preserving idempotent maps
of view complexes. No representative-table condition is part of this type.
-/

namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section

variable {H I₁ I₂ Q : Type}

structure Reduction (past : H → EnvHistory I₁ I₂) (state : H → Q) where
  map : ViewComplexMap past past
  idempotent : ∀ e, map.edge (map.edge e) = map.edge e
  states : ∀ e, state (map.edge e) = state e

namespace Reduction
variable {past : H → EnvHistory I₁ I₂} {state : H → Q}

/-- Edge idempotence implies vertex idempotence because every vertex occurs
on an edge. This is the last vertex-map step in `lem:tree-compression`. -/
theorem vertex_idempotent (r : Reduction past state) (p : Proc) (v : ViewVertex past p) :
    r.map.vertex p (r.map.vertex p v) = r.map.vertex p v := by
  obtain ⟨e, he⟩ := v.property
  have eq : viewEndpoint past p e = v := Subtype.ext he
  rw [← eq, r.map.incident, r.map.incident, r.idempotent]

theorem map_idempotent (r : Reduction past state) : r.map.comp r.map = r.map := by
  apply ViewComplexMap.ext
  funext e
  exact r.idempotent e

def identity (past : H → EnvHistory I₁ I₂) (state : H → Q) : Reduction past state where
  map := ViewComplexMap.identity past
  idempotent _ := rfl
  states _ := rfl

/-- Reuses `Set.range`: these are exactly the edges of r(K). -/
abbrev Image (r : Reduction past state) := Set.range r.map.edge

def project (r : Reduction past state) (e : H) : r.Image := ⟨r.map.edge e, e, rfl⟩

theorem fixes_image (r : Reduction past state) (e : r.Image) : r.map.edge e.val = e.val := by
  obtain ⟨f, eq⟩ := e.property
  rw [← eq, r.idempotent]

def toImage (r : Reduction past state) :
    ViewComplexMap past (fun e : r.Image => past e.val) :=
  ViewComplexMap.ofEdge r.project (fun p e f same => r.map.preserves_views p e f same)

theorem image_nonempty (r : Reduction past state) [Nonempty H] : Nonempty r.Image :=
  ⟨r.project (Classical.arbitrary H)⟩

/-- Connectivity stays internal to the image; no extra ambient vertices
are used to connect its edges. -/
theorem image_connected (r : Reduction past state)
    (connected : ∀ e f : H, Relation.ReflTransGen
      (fun x y => ∃ p, currentView p (past x) = currentView p (past y)) e f)
    (e f : r.Image) : Relation.ReflTransGen
      (fun x y : r.Image => ∃ p, currentView p (past x.val) = currentView p (past y.val)) e f := by
  obtain ⟨a, ha⟩ := e.property
  obtain ⟨b, hb⟩ := f.property
  have ea : r.project a = e := Subtype.ext ha
  have fb : r.project b = f := Subtype.ext hb
  rw [← ea, ← fb]
  exact Relation.ReflTransGen.lift r.project (fun x y edge => by
    obtain ⟨p, same⟩ := edge
    exact ⟨p, r.map.preserves_views p x y same⟩) (connected a b)

theorem priority_preserved (r : Reduction past state) (χ : Q → Nat) (e : H) :
    χ (state (r.map.edge e)) = χ (state e) := congrArg χ (r.states e)

/-- Renaming edge indices transports the same concrete reduction. This is
used to pass from endpoint scenarios to the existing `Position` container. -/
def reindex {K : Type} (r : Reduction past state) (e : H ≃ K)
    (other : K → EnvHistory I₁ I₂) (label : K → Q)
    (histories : ∀ h, other (e h) = past h)
    (labels : ∀ h, label (e h) = state h) : Reduction other label where
  map := ViewComplexMap.ofEdge (fun k => e (r.map.edge (e.symm k))) (by
    intro p h k same
    have back z : other z = past (e.symm z) := by
      simpa only [e.apply_symm_apply] using histories (e.symm z)
    rw [histories, histories]
    apply r.map.preserves_views
    simpa only [back] using same)
  idempotent k := by
    change e (r.map.edge (e.symm (e (r.map.edge (e.symm k)))) ) = e (r.map.edge (e.symm k))
    rw [e.symm_apply_apply, r.idempotent]
  states k := by
    change label (e (r.map.edge (e.symm k))) = label k
    rw [labels, r.states]
    simpa only [e.apply_symm_apply] using (labels (e.symm k)).symm

theorem reindex_image_card {K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K]
    (r : Reduction past state) (e : H ≃ K)
    (other : K → EnvHistory I₁ I₂) (label : K → Q)
    (histories : ∀ h, other (e h) = past h)
    (labels : ∀ h, label (e h) = state h) :
    (Finset.univ.image (r.reindex e other label histories labels).map.edge).card =
      (Finset.univ.image r.map.edge).card := conjugate_image_card e r.map.edge

end Reduction

/-- The compression construction supplies a reduction of the FULL selected
component C. Its image is a separate object; C is not replaced by that image.
The common-view premise is explicit here so the new broadcaster proof can
supply it without using the older missing-extension argument. -/
def endpointReduction
    {O₁ O₂ S : Type} {D : Nat}
    [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
    (m : Move I₁ I₂ O₁ O₂ S D) (C : Finset m.source.End)
    (label : m.source.End → Q)
    (rep : participatingRoots m C → participatingRoots m C)
    (preserves : ∀ h, endpointTable m C label (rep h) = endpointTable m C label h)
    (constant : ∀ h k, endpointTable m C label h = endpointTable m C label k → rep h = rep k)
    (p : Proc)
    (common : ∀ h k : participatingRoots m C, currentView p h.val.val = currentView p k.val.val) :
    Reduction (fun e : C => m.source.history e.val) (fun e : C => label e.val) where
  map := ViewComplexMap.ofEdge (endpointFold m C label rep preserves) (by
    intro q e f same
    rw [endpointFold_history, endpointFold_history]
    apply append_preserves_views _ _ _ _
      (fun i eq => common_view_root_map (fun h : participatingRoots m C => h.val.val)
        (fun _ _ eq => Subtype.ext (Subtype.ext eq)) p common rep i _ _ eq)
      _ _ ((scenarioWord D e.val).property.trans (scenarioWord D f.val).property.symm) q
    simpa only [Position.history, scenarioWord_history, Position.past, rootOf] using same)
  idempotent := endpointFold_idempotent m C label rep preserves constant
  states := endpointFold_label m C label rep preserves

end
end Characterisation.ComponentTrees
