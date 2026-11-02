/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.ViewAgreement

/-!
# Agreement along a view path

Manuscript source label: `lem:agreement_on_path`.

## Paper statement

Let $f$ be a distributed algorithm, and let $r\geq 1$.
    If processes~$1$ and~$2$ output the same value in round~$r$ of every execution, then all vertices of the inputless round-$r$ view complex have the same output label under~$f$.

## Reading the proof

See the [proof locations](PROOFS.md#agreement-along-a-view-path) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis

namespace DistributedSynthesis.Paper.PathAgreement

universe u_1

/-- Reuses `DistributedSynthesis.FullViewPath.execution_agreement_implies_uniform`. -/
theorem execution_agreement_implies_uniform :
    ∀ {O : Type u_1} (σ : StrategyPair Unit Unit O O) (n : ℕ),
      (∀ (env : EnvironmentSequence Unit Unit), (execution σ env n).outputOne = (execution σ env n).outputTwo) →
        ∃ (value : O),
          ∀ (h : List Graph),
            h.length = n + 1 → σ.one (FullViewPath.evaluate h).one = value ∧ σ.two (FullViewPath.evaluate h).two = value :=
  @_root_.DistributedSynthesis.FullViewPath.execution_agreement_implies_uniform

end DistributedSynthesis.Paper.PathAgreement
