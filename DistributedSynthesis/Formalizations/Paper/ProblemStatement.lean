/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.Model

/-!
# Lossy-Link Synthesis Problem

Corresponds to the subsection of that name in the manuscript.
See `Model.lean` for the common model and its notation.

`Realizes L f` means that the fixed pair of local strategies f realizes L
against every environment sequence. `SynthesisProblem L` asks whether such a
pair exists. The graph-restricted LTL problem is `GraphAdversaries.Realizable A d`.
Its input d contains the four finite nonempty alphabets, a finite interpretation
of atomic propositions, and the LTL formula, including next.

An alphabet of size k+1 is represented by `Fin (k+1)`. The finite truth table
interprets propositions over the complete round record (both inputs, both
outputs, and the graph). This is the existing finite encoding, not a restricted
fragment of LTL or a separate definition of strategies. Taking A = Set.univ gives
LL-Synthesis; arbitrary A gives LL-Synthesis(A). Private inputs are unrestricted
in both cases. The quantifier order chooses the strategies before the inputs
and graphs, as in the paper.

These equations unfold the actual problem predicates used by the proved
results. They impose no finite-state, parity-game-certificate, or strategy oracle
assumption.
-/

namespace DistributedSynthesis.Paper.ProblemStatement

universe u v x y
variable {X₁ : Type u} {X₂ : Type v} {Y₁ : Type x} {Y₂ : Type y}

/-- LL-realization of an execution language. -/
theorem realizes_iff (L : Specification X₁ X₂ Y₁ Y₂)
    (f : StrategyPair X₁ X₂ Y₁ Y₂) :
    Realizes L f ↔ ∀ σ : EnvironmentSequence X₁ X₂, L (execution f σ) := Iff.rfl

/-- LL-realizability: one fixed pair of strategies works for every environment. -/
theorem synthesis_iff (L : Specification X₁ X₂ Y₁ Y₂) :
    SynthesisProblem L ↔
      ∃ f : StrategyPair X₁ X₂ Y₁ Y₂,
        ∀ σ : EnvironmentSequence X₁ X₂, L (execution f σ) := Iff.rfl

/-- The finite LTL decision problem under an arbitrary message adversary A. -/
theorem adversary_synthesis_iff (A : Set (Nat → Graph)) (d : GraphAdversaries.Instance) :
    GraphAdversaries.Realizable A d ↔
      ∃ f : StrategyPair
          (Fin (d.inputOneSizeMinusOne + 1)) (Fin (d.inputTwoSizeMinusOne + 1))
          (Fin (d.outputOneSizeMinusOne + 1)) (Fin (d.outputTwoSizeMinusOne + 1)),
        ∀ σ, (fun r => (σ r).graph) ∈ A →
          LTL.Satisfies (EncodedNoDirect.interp d) (execution f σ)
            (EncodedFiniteLTL.decode d.formula) := Iff.rfl

/-- With the full adversary, all input and graph sequences are allowed. -/
theorem full_synthesis_iff (d : GraphAdversaries.Instance) :
    GraphAdversaries.Realizable Set.univ d ↔
      ∃ f : StrategyPair
          (Fin (d.inputOneSizeMinusOne + 1)) (Fin (d.inputTwoSizeMinusOne + 1))
          (Fin (d.outputOneSizeMinusOne + 1)) (Fin (d.outputTwoSizeMinusOne + 1)),
        ∀ σ, LTL.Satisfies (EncodedNoDirect.interp d) (execution f σ)
          (EncodedFiniteLTL.decode d.formula) := by
  simp only [adversary_synthesis_iff, Set.mem_univ, forall_const]

end DistributedSynthesis.Paper.ProblemStatement
