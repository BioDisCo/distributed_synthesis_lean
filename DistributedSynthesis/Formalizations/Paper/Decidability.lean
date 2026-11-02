/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.Decision
import DistributedSynthesis.Formalizations.ComponentTrees.Synthesis

/-!
# Deciding realizability and constructing an algorithm

Manuscript source label: `thm:nowhere-dense-decision-procedure`.

## Paper statement

Given a deterministic parity automaton for a message adversary $A$ with nowhere-dense
  image $\pi(A)$ and an \ac{LTL} formula $\phi$, one can decide whether a
  distributed algorithm realizing $\phi$ under~$A$ exists and construct one if it does.

## Correspondence

The three-row condition encodes the paper's three communication graphs. The procedure
computes D internally; its promise is the paper's nowhere-denseness hypothesis. The
other two declarations give executable strategy extraction.

## Reading the proof

The proof first checks whether the adversary has any infinite word. If it has
none, every specification is realizable vacuously. Otherwise it computes a
consensus bound, constructs the block automaton, and decides the MSO sentence
for compressed component trees. `solve_correct` composes these equivalences;
`synthesize_complete` and `synthesize_sound` justify the returned strategies.

See the [proof locations](PROOFS.md#deciding-realizability-and-constructing-an-algorithm) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.Decidability

/-- Reuses `Characterisation.ComponentTrees.Effective.solve_correct`. -/
theorem solve_correct :
    ∀ (d : EncodedGuardedObjective.Data),
      (EncodedParityTables.rows d.1).length = 3 →
      ∀ (promise : IsNowhereDense
          (geometricMap '' {word : ℕ → Graph | (ComponentGames.graphInput d.1).Accepts word})),
        ComponentTrees.Effective.solve d promise = true ↔
          WithInputs.Realizable
            {word : ℕ → Graph | (ComponentGames.graphInput d.1).Accepts word} d.2 :=
  @_root_.Characterisation.ComponentTrees.Effective.solve_correct

/-- Reuses `Characterisation.ComponentTrees.Effective.synthesize_complete`. -/
theorem synthesize_complete :
    ∀ (d : EncodedGuardedObjective.Data),
      (EncodedParityTables.rows d.1).length = 3 →
      ∀ (promise : IsNowhereDense
          (geometricMap '' {word : ℕ → Graph | (ComponentGames.graphInput d.1).Accepts word})),
        (∃ (σ : WithInputs.Strategies d.2),
          ComponentTrees.Effective.synthesize d promise = some σ) ↔
            WithInputs.Realizable
              {word : ℕ → Graph | (ComponentGames.graphInput d.1).Accepts word} d.2 :=
  @_root_.Characterisation.ComponentTrees.Effective.synthesize_complete

/-- Reuses `Characterisation.ComponentTrees.Effective.synthesize_sound`. -/
theorem synthesize_sound :
    ∀ (d : EncodedGuardedObjective.Data),
      (EncodedParityTables.rows d.1).length = 3 →
      ∀ (promise : IsNowhereDense
          (geometricMap '' {word : ℕ → Graph | (ComponentGames.graphInput d.1).Accepts word}))
        (σ : WithInputs.Strategies d.2),
        ComponentTrees.Effective.synthesize d promise = some σ →
        ∀ (env : EnvironmentSequence
            (Fin (d.2.inputOneSizeMinusOne + 1)) (Fin (d.2.inputTwoSizeMinusOne + 1))),
          ((ComponentGames.graphInput d.1).Accepts fun (n : ℕ) => (env n).graph) →
          LTL.Satisfies (EncodedNoDirect.interp d.2) (execution σ env)
            (EncodedFiniteLTL.decode d.2.formula) :=
  @_root_.Characterisation.ComponentTrees.Effective.synthesize_sound

end DistributedSynthesis.Paper.Decidability
