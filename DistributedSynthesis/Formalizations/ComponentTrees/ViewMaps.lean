/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.BlockRules

/-! Maps of the view complexes in `main.tex`, `lem:view-extension`.

Edges are indexed by an existing history family. Vertices are precisely its
occurring local views, so there are no isolated vertices. No equality of
source and target rounds, injectivity of a map, or finiteness is required.
-/

namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section

variable {H K L I₁ I₂ : Type}

/-- The vertices owned by `p` that occur in the given history family. -/
def ViewVertex (past : H → EnvHistory I₁ I₂) (p : Proc) :=
  {v : View I₁ I₂ p // ∃ e, currentView p (past e) = v}

def viewEndpoint (past : H → EnvHistory I₁ I₂) (p : Proc) (e : H) :
    ViewVertex past p := ⟨currentView p (past e), e, rfl⟩

/-- An owner-preserving vertex map with its induced map on edges. -/
structure ViewComplexMap (past : H → EnvHistory I₁ I₂)
    (other : K → EnvHistory I₁ I₂) where
  edge : H → K
  vertex : (p : Proc) → ViewVertex past p → ViewVertex other p
  incident : ∀ p e, vertex p (viewEndpoint past p e) = viewEndpoint other p (edge e)

namespace ViewComplexMap
variable {past : H → EnvHistory I₁ I₂} {other : K → EnvHistory I₁ I₂}
variable {third : L → EnvHistory I₁ I₂}

theorem preserves_views (T : ViewComplexMap past other) (p : Proc) (e f : H)
    (same : currentView p (past e) = currentView p (past f)) :
    currentView p (other (T.edge e)) = currentView p (other (T.edge f)) := by
  have eq : viewEndpoint past p e = viewEndpoint past p f := Subtype.ext same
  exact congrArg Subtype.val ((T.incident p e).symm.trans
    ((congrArg (T.vertex p) eq).trans (T.incident p f)))

/-- Every view-preserving edge map induces an actual vertex map. -/
def ofEdge (f : H → K)
    (preserves : ∀ p e e', currentView p (past e) = currentView p (past e') →
      currentView p (other (f e)) = currentView p (other (f e'))) :
    ViewComplexMap past other where
  edge := f
  vertex p v := viewEndpoint other p (f v.property.choose)
  incident p e := by
    apply Subtype.ext
    exact preserves p _ e (viewEndpoint past p e).property.choose_spec

/-- Conversely every owner-preserving vertex map sending edges to edges
has an edge map. Thus `ofEdge` does not restrict the manuscript's maps. -/
def ofVertices (f : (p : Proc) → ViewVertex past p → ViewVertex other p)
    (edges : ∀ e, ∃ k, ∀ p, f p (viewEndpoint past p e) = viewEndpoint other p k) :
    ViewComplexMap past other where
  edge e := (edges e).choose
  vertex := f
  incident p e := (edges e).choose_spec p

/-- There are no isolated vertices: the edge action determines the vertex action. -/
@[ext] theorem ext {T U : ViewComplexMap past other} (edges : T.edge = U.edge) : T = U := by
  have vertices : T.vertex = U.vertex := by
    funext p v
    obtain ⟨e, he⟩ := v.property
    have eq : viewEndpoint past p e = v := Subtype.ext he
    rw [← eq, T.incident, U.incident, edges]
  cases T
  cases U
  simp_all

/-- For actual history edges, the vertex action also determines the edge
map: the two process views uniquely determine the target history. -/
theorem ext_vertices (injective : Function.Injective other)
    {T U : ViewComplexMap past other} (vertices : T.vertex = U.vertex) : T = U := by
  apply ext
  funext e
  apply injective
  apply joint_env_history
  · exact congrArg Subtype.val ((T.incident .one e).symm.trans
      ((congrFun (congrFun vertices .one) (viewEndpoint past .one e)).trans (U.incident .one e)))
  · exact congrArg Subtype.val ((T.incident .two e).symm.trans
      ((congrFun (congrFun vertices .two) (viewEndpoint past .two e)).trans (U.incident .two e)))

def identity (past : H → EnvHistory I₁ I₂) : ViewComplexMap past past where
  edge := id
  vertex _ := id
  incident _ _ := rfl

def comp (U : ViewComplexMap other third) (T : ViewComplexMap past other) :
    ViewComplexMap past third where
  edge := U.edge ∘ T.edge
  vertex p := U.vertex p ∘ T.vertex p
  incident p e := by simp only [Function.comp_apply, T.incident, U.incident]

/-- Constructor recursion from the English proof, on all length-`t`
extensions, including nonlive ones. The existing `append_preserves_views`
proves the one-round `recv`/`noRecv` constructor step. -/
def extend (T : ViewComplexMap past other) (t : Nat) :
    ViewComplexMap (closingLayerHistory past t) (closingLayerHistory other t) :=
  ofEdge (mapClosingLayer T.edge t) (by
    intro p s u same
    rw [← closingLayerHistory_map, ← closingLayerHistory_map,
      scenarioWord_history, scenarioWord_history]
    apply append_preserves_views _ _ _ _ (fun q eq => T.preserves_views q _ _ eq)
      _ _ ((scenarioWord t s).property.trans (scenarioWord t u).property.symm) p
    simpa only [scenarioWord_history] using same)

theorem extend_history (T : ViewComplexMap past other) (t : Nat)
    (s : ClosingLayer H I₁ I₂ t) :
    closingLayerHistory other t ((T.extend t).edge s) =
      other (T.edge (closingLayerRoot t s)) ++ (scenarioWord t s).val := by
  change closingLayerHistory other t (mapClosingLayer T.edge t s) = _
  rw [← closingLayerHistory_map, scenarioWord_history]
  rfl

theorem extend_identity (past : H → EnvHistory I₁ I₂) (t : Nat) :
    (identity past).extend t = identity (closingLayerHistory past t) := by
  apply ext
  funext s
  exact mapClosingLayer_identity t s

theorem extend_comp (U : ViewComplexMap other third) (T : ViewComplexMap past other) (t : Nat) :
    (U.comp T).extend t = (U.extend t).comp (T.extend t) := by
  apply ext
  funext s
  exact (mapClosingLayer_comp T.edge U.edge t s).symm

theorem extend_zero (T : ViewComplexMap past other) : T.extend 0 = T := by
  apply ext
  rfl

/-- Inverses extend to inverses, as used in the finite MSO alphabet proof. -/
theorem extend_inverse (T : ViewComplexMap past other) (U : ViewComplexMap other past)
    (inverse : U.comp T = identity past) (t : Nat) :
    (U.extend t).comp (T.extend t) = identity (closingLayerHistory past t) := by
  rw [← extend_comp, inverse, extend_identity]

end ViewComplexMap
end
end Characterisation.ComponentTrees
