/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.Trees
import DistributedSynthesis.Formalizations.ComponentGames.RepresentationComponents
import DistributedSynthesis.Formalizations.ComponentGames.SimulationRuns

/-! Restricting a finite observation graph to all its live vertices preserves
its full components. This is used to compare r(K)-indexed extensions with
K-indexed extensions whose roots are fixed by r.
-/
namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

section Graph
variable {H J : Type} [Fintype H] [Fintype J] [DecidableEq H] [DecidableEq J]
variable (shape : InputShape H) (other : InputShape J) (live : H → Bool) (alive : J → Bool)
variable (f : H → J) (g : J → H)
variable (left : ∀ h, g (f h) = h)
variable (right : ∀ j, alive j = true → f (g j) = j)
variable (views : ∀ p h k, other p (f h) (f k) = shape p h k)
variable (liveness : ∀ h, alive (f h) = live h)

include left right views liveness in
theorem componentMask_retract (h k : H) :
    closingComponentMask other alive (f h) (f k) = closingComponentMask shape live h k := by
  let forward : closingObservationGraph shape live →g closingObservationGraph other alive := {
    toFun := f
    map_rel' := by
      intro x y edge
      exact ⟨fun eq => edge.1 (by simpa only [left] using congrArg g eq),
        (liveness x).trans edge.2.1,(liveness y).trans edge.2.2.1,
        edge.2.2.2.imp (fun p same => by simpa only [views] using same)⟩ }
  let backward : closingObservationGraph other alive →g closingObservationGraph shape live := {
    toFun := g
    map_rel' := by
      intro x y edge
      have ex := right x edge.2.1
      have ey := right y edge.2.2.1
      refine ⟨fun eq => edge.1 (ex.symm.trans ((congrArg f eq).trans ey)),?_,?_,?_⟩
      · simpa only [← liveness,ex] using edge.2.1
      · simpa only [← liveness,ey] using edge.2.2.1
      · obtain ⟨p,same⟩ := edge.2.2.2
        exact ⟨p,by simpa only [← views,ex,ey] using same⟩ }
  have reach : (closingObservationGraph other alive).Reachable (f h) (f k) ↔
      (closingObservationGraph shape live).Reachable h k := by
    constructor
    · intro path
      have mapped := path.map backward
      change (closingObservationGraph shape live).Reachable (g (f h)) (g (f k)) at mapped
      simpa only [left] using mapped
    · intro path
      exact path.map forward
  simp only [closingComponentMask,liveness,reach]


include left right views liveness in
theorem component_image_retract (K : Finset H)
    (component : ∃ anchor, live anchor = true ∧ ∀ h,
      h ∈ K ↔ closingComponentMask shape live anchor h = true) :
    ∃ anchor, alive anchor = true ∧ ∀ j,
      j ∈ K.image f ↔ closingComponentMask other alive anchor j = true := by
  obtain ⟨anchor,anchorLive,members⟩ := component
  have injective : Function.Injective f := fun h k eq => by simpa only [left] using congrArg g eq
  refine ⟨f anchor,(liveness anchor).trans anchorLive,fun j => ?_⟩
  by_cases active : alive j = true
  · rw [← right j active, componentMask_retract shape other live alive f g left right views liveness]
    simpa only [Finset.mem_image,injective.eq_iff,exists_eq_right] using members (g j)
  · constructor
    · intro mem
      obtain ⟨h,inside,rfl⟩ := Finset.mem_image.mp mem
      have mask := (members h).mp inside
      simp only [closingComponentMask,Bool.and_eq_true] at mask
      exact False.elim (active ((liveness h).trans mask.1))
    · intro mask
      simp only [closingComponentMask,Bool.and_eq_true] at mask
      exact False.elim (active mask.1)

include left right views liveness in
theorem component_pullback_retract (L : Finset J)
    (component : ∃ anchor, alive anchor = true ∧ ∀ j,
      j ∈ L ↔ closingComponentMask other alive anchor j = true) :
    (∃ anchor, live anchor = true ∧ ∀ h,
      h ∈ L.image g ↔ closingComponentMask shape live anchor h = true) ∧
    (L.image g).image f = L := by
  obtain ⟨anchor,anchorLive,members⟩ := component
  have allLive j (mem : j ∈ L) : alive j = true := by
    have mask := (members j).mp mem
    simp only [closingComponentMask,Bool.and_eq_true] at mask
    exact mask.1
  have inverse j (mem : j ∈ L) := right j (allLive j mem)
  have membership h : h ∈ L.image g ↔ f h ∈ L := by
    constructor
    · rintro mem
      obtain ⟨j,inside,rfl⟩ := Finset.mem_image.mp mem
      rwa [inverse j inside]
    · intro mem
      exact Finset.mem_image.mpr ⟨f h,mem,left h⟩
  constructor
  · refine ⟨g anchor,?_,fun h => ?_⟩
    · rw [← liveness,right anchor anchorLive]
      exact anchorLive
    · rw [membership,members,← right anchor anchorLive,
        componentMask_retract shape other live alive f g left right views liveness,left]
  · ext j
    constructor
    · intro mem
      obtain ⟨h,inside,rfl⟩ := Finset.mem_image.mp mem
      exact (membership h).mp inside
    · intro mem
      exact Finset.mem_image.mpr ⟨g j,Finset.mem_image.mpr ⟨j,mem,rfl⟩,inverse j mem⟩

end Graph

/-- A scenario is fixed by a root map exactly when its old root is fixed;
all new signals remain unchanged. -/
theorem mapClosingLayer_fixed_root {H I₁ I₂ : Type} (f : H → H)
    (D : Nat) (s : ClosingLayer H I₁ I₂ D)
    (fixed : f (closingLayerRoot D s) = closingLayerRoot D s) :
    mapClosingLayer f D s = s := by
  induction D with
  | zero => exact fixed
  | succ n ih => exact Prod.ext (ih s.1 fixed) rfl

end Characterisation.ComponentTrees
