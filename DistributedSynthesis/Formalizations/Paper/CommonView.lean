/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.CommonView

/-!
# A common preceding view in a component

Manuscript source label: `lem:bounded-common-view`.

## Paper statement

Let $A$ be a message adversary under which consensus is repeatedly solvable
  in uniformly bounded time~$D$.
Let $r\geq D$, and let $K$ be a nonempty connected subgraph of the
  round-$r$ view complex under~$A$.
There exists a process $p\in{\cal P}$ such that
\[
  v_p(h[\dots r-D])=v_p(h'[\dots r-D])
\]
for all $h,h'\in\Sigma^r$ with $e(h),e(h')\in E(K)$.

## Reading the proof

See the [proof locations](PROOFS.md#a-common-preceding-view-in-a-component) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.CommonView

/-- Reuses `Characterisation.ComponentTrees.bounded_common_view`. -/
theorem bounded_common_view :
    ∀ {V I₁ I₂ : Type} [Nontrivial V] (A : Set (ℕ → Graph)) (D : ℕ),
      0 < D →
        (∀ (g : List Graph),
            LivePrefix A g →
              ∃ (σ : StrategyPair V V (Option V) (Option V)), ComponentGames.Consensus.SolvesBy σ (Residual A g) D) →
          ∀ (r : ℕ),
            D ≤ r →
              ∀ (C : Set (EnvHistory I₁ I₂)),
                C.Nonempty →
                  (∀ h ∈ C, List.length h = r) →
                    (∀ h ∈ C, LivePrefix A (History.graphSequence h)) →
                      (∀ (e f : ↑C),
                          Relation.ReflTransGen (fun (x y : ↑C) => ∃ (p : Proc), currentView p x.val = currentView p y.val) e f) →
                        ∃ (p : Proc),
                          ∀ h ∈ C, ∀ k ∈ C, currentView p (List.take (r - D) h) = currentView p (List.take (r - D) k) :=
  @_root_.Characterisation.ComponentTrees.bounded_common_view

end DistributedSynthesis.Paper.CommonView
