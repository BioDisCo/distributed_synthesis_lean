/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.ViewMaps

/-!
# Extending maps of view complexes

Manuscript source label: `lem:view-extension`.

## Paper statement

Let $T:K\to L$ be a map of view complexes as above.
For every $t\geq0$, there is a map $T^{(t)}:K^{(t)}\to L^{(t)}$ such that
\[
  T^{(t)}(ew)=T(e)w
  \qquad(e\in E(K),\ w\in\Sigma^t) \enspace.
\]
These extensions preserve identities and composition.

## Reading the proof

See the [proof locations](PROOFS.md#extending-maps-of-view-complexes) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.ViewExtension

/-- Reuses `Characterisation.ComponentTrees.ViewComplexMap.extend_history`. -/
theorem extend_history :
    ∀ {H K I₁ I₂ : Type} {past : H → EnvHistory I₁ I₂}
      {other : K → EnvHistory I₁ I₂} (T : ComponentTrees.ViewComplexMap past other) (t : ℕ) (s : ClosingLayer H I₁ I₂ t),
      closingLayerHistory other t ((T.extend t).edge s) =
        other (T.edge (closingLayerRoot t s)) ++ ↑(PeriodicBlocks.scenarioWord t s) :=
  @_root_.Characterisation.ComponentTrees.ViewComplexMap.extend_history

/-- Reuses `Characterisation.ComponentTrees.ViewComplexMap.extend_zero`. -/
theorem extend_zero :
    ∀ {H K I₁ I₂ : Type} {past : H → EnvHistory I₁ I₂}
      {other : K → EnvHistory I₁ I₂} (T : ComponentTrees.ViewComplexMap past other), T.extend 0 = T :=
  @_root_.Characterisation.ComponentTrees.ViewComplexMap.extend_zero

/-- Reuses `Characterisation.ComponentTrees.ViewComplexMap.extend_identity`. -/
theorem extend_identity :
    ∀ {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂) (t : ℕ),
      (ComponentTrees.ViewComplexMap.identity past).extend t =
        ComponentTrees.ViewComplexMap.identity (closingLayerHistory past t) :=
  @_root_.Characterisation.ComponentTrees.ViewComplexMap.extend_identity

/-- Reuses `Characterisation.ComponentTrees.ViewComplexMap.extend_comp`. -/
theorem extend_comp :
    ∀ {H K L I₁ I₂ : Type} {past : H → EnvHistory I₁ I₂}
      {other : K → EnvHistory I₁ I₂} {third : L → EnvHistory I₁ I₂} (U : ComponentTrees.ViewComplexMap other third)
      (T : ComponentTrees.ViewComplexMap past other) (t : ℕ), (U.comp T).extend t = (U.extend t).comp (T.extend t) :=
  @_root_.Characterisation.ComponentTrees.ViewComplexMap.extend_comp

/-- Reuses `Characterisation.ComponentTrees.ViewComplexMap.extend_inverse`. -/
theorem extend_inverse :
    ∀ {H K I₁ I₂ : Type} {past : H → EnvHistory I₁ I₂}
      {other : K → EnvHistory I₁ I₂} (T : ComponentTrees.ViewComplexMap past other)
      (U : ComponentTrees.ViewComplexMap other past),
      U.comp T = ComponentTrees.ViewComplexMap.identity past →
        ∀ (t : ℕ), (U.extend t).comp (T.extend t) = ComponentTrees.ViewComplexMap.identity (closingLayerHistory past t) :=
  @_root_.Characterisation.ComponentTrees.ViewComplexMap.extend_inverse

end DistributedSynthesis.Paper.ViewExtension
