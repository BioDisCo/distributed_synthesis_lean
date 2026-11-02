/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefEpochAbstractions

/-!
# Uniqueness of block decomposition

This file formalizes Lemma `lem:decompositionunique` from `paper.tex`.
-/

namespace DistributedSynthesis

/-- A candidate decomposition is valid exactly when it is produced by the deterministic scan. -/
def IsBlockDecomposition (word : List Graph) (decomposition : List BlockRound) : Prop :=
  decomposition = blockDecomposition word

/-- The deterministic block scan gives a valid decomposition of every graph word. -/
theorem blockDecomposition_exists (word : List Graph) :
    IsBlockDecomposition word (blockDecomposition word) := by
  rfl

/-- Any two valid block decompositions of the same graph word are equal. -/
theorem blockDecomposition_unique
    (word : List Graph)
    (decomposition decomposition' : List BlockRound)
    (hdecomposition : IsBlockDecomposition word decomposition)
    (hdecomposition' : IsBlockDecomposition word decomposition') :
    decomposition = decomposition' := by
  rw [hdecomposition, hdecomposition']

/-- Paper-facing form of `lem:decompositionunique`. -/
theorem decomposition_unique (word : List Graph) :
    ∃! decomposition : List BlockRound, IsBlockDecomposition word decomposition := by
  refine ⟨blockDecomposition word, blockDecomposition_exists word, ?_⟩
  intro decomposition hdecomposition
  exact blockDecomposition_unique word decomposition (blockDecomposition word)
    hdecomposition (blockDecomposition_exists word)

end DistributedSynthesis
