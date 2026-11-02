/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Undecidability.Adversaries

/-!
# Nowhere denseness and missing extensions

Manuscript source label: `lem:nowhere-dense-live`.

## Paper statement

Let $A\subseteq\Gamma^\omega$ be a message adversary.
    Then $\pi(A)$ is nowhere dense in $[0,1]$ if and only if, for every $h\in\Gamma^*$, there exists $k\in\Gamma^*$ such that $h\cdot k$ is not live under~$A$.

## Reading the proof

See the [proof locations](PROOFS.md#nowhere-denseness-and-missing-extensions) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.MissingExtension

/-- Reuses `Characterisation.nowhere_dense_iff_missing_extension`. -/
theorem nowhere_dense_iff_missing_extension :
    ∀ (A : Set (ℕ → Graph)),
      IsNowhereDense (geometricMap '' A) ↔ ∀ (h : List Graph), ∃ (k : List Graph), ¬LivePrefix A (h ++ k) :=
  @_root_.Characterisation.nowhere_dense_iff_missing_extension

end DistributedSynthesis.Paper.MissingExtension
