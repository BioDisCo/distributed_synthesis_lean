/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemOneSidedFringeElim
import DistributedSynthesis.Formalizations.Lemma.LemOmegaFringeElim

/-!
# Discharging ω-recoverability for the θ̄-game shape

For the θ̄-game the blind fringe is degenerate (`R₁ := Unit`) and the informed history is a delay-one
observation (`DelayOneObs O₂ R₂`).  This file proves that in that shape the ω-recoverability
`OmegaRecovered` (the hypothesis of `omegaFringeElim_winning_iff`) follows from a single, purely
informed condition: that each informed observation exposes the settled fringe past in its second
component (`OmegaSelfEmbedTwo`, the ω-form of `lem:delayonehierarchy`).  The blind half is automatic
(`Unit` lists are length-determined); the informed half is the delay-one embedder read at the current
observation.  So the concrete θ̄-game mapping need only supply informed self-embedding to unlock the
ω fringe elimination.
-/

namespace DistributedSynthesis

universe u₁ o v₂ w₁ w₂

variable {H₁ : Type u₁} {O₂ : Type o} {R₂ : Type v₂}
  {Out₁ : Type w₁} {Out₂ : Type w₂}

/-- The **informed ω self-embedding**: every informed observation exposes, in its `DelayOneObs`
second component, exactly the settled fringe past played so far -- the ω-form of the receiver-side
delay-one hierarchy (`lem:delayonehierarchy`). -/
def OmegaSelfEmbedTwo
    (otrace : Nat -> FringeObservationStep H₁ (DelayOneObs O₂ R₂) Unit R₂) : Prop :=
  ∀ n : Nat,
    (otrace n).historyTwo.2 = (List.range n).map fun i => (otrace i).fringeTwo

/-- **ω-recoverability holds for the θ̄-game shape given informed self-embedding.**  With a `Unit`
blind fringe the blind conjunct of `OmegaRecovered` is automatic (`Unit` lists are length-matched);
the informed conjunct is `recoverEmbedded` read at the current observation, which is the informed
self-embedding.  Thus the concrete mapping unlocks `omegaFringeElim_winning_iff` from a single
informed hypothesis. -/
theorem omegaRecovered_of_selfEmbedTwo
    (otrace : Nat -> FringeObservationStep H₁ (DelayOneObs O₂ R₂) Unit R₂)
    (h : OmegaSelfEmbedTwo otrace) :
    OmegaRecovered punitRecover recoverEmbedded otrace := by
  intro n
  refine ⟨?_, ?_⟩
  · have hfringe :
        ((List.range n).map fun i => (otrace i).fringeOne) = List.replicate n () := by
      rw [list_punit_eq_replicate ((List.range n).map fun i => (otrace i).fringeOne)]
      simp
    rw [hfringe]
    simp [punitRecover, List.length_map, List.length_range]
  · have hlast :
        ((List.range (n + 1)).map fun i => (otrace i).historyTwo).getLast? =
          some ((otrace n).historyTwo) := by
      rw [List.getLast?_map, List.range_succ, List.getLast?_concat]; rfl
    simp only [recoverEmbedded, hlast]
    exact h n

/-- **ω fringe elimination for the θ̄-game shape.**  For a degenerate-blind (`Unit`),
delay-one-informed game, a fringe-dependent strategy wins an arbitrary ω-spec on every
informed-self-embedding ω-play iff a fringe-free (summary-observable) one does.  The recoverability is
supplied entirely by `OmegaSelfEmbedTwo` (informed) plus the automatic blind half, via
`omegaRecovered_of_selfEmbedTwo`; the equivalence is the ω output preservation of `LemOmegaFringeElim`.
This is the exact interface the concrete θ̄-game mapping calls: map plays to ω-traces with informed
self-embedding (`lem:delayonehierarchy`), and the summary-observable winner drops out. -/
theorem omegaFringeElim_winning_iff_selfEmbedTwo
    (ospec : (Nat -> Out₁ × Out₂) -> Prop) :
    (∃ σ : FringeStrategyPair H₁ (DelayOneObs O₂ R₂) Unit R₂ Out₁ Out₂,
        ∀ otrace : Nat -> FringeObservationStep H₁ (DelayOneObs O₂ R₂) Unit R₂,
          OmegaSelfEmbedTwo otrace -> ospec (omegaOriginalOutputAt σ otrace)) ↔
      (∃ σ : ContingentStrategyPair H₁ (DelayOneObs O₂ R₂) Unit R₂ Out₁ Out₂,
        ∀ otrace : Nat -> FringeObservationStep H₁ (DelayOneObs O₂ R₂) Unit R₂,
          OmegaSelfEmbedTwo otrace -> ospec (omegaContingentOutputAt σ otrace)) := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨contingentifyPair punitRecover recoverEmbedded σ, fun otrace hself => ?_⟩
    rw [← omegaOriginal_eq_contingentify punitRecover recoverEmbedded σ otrace
      (omegaRecovered_of_selfEmbedTwo otrace hself)]
    exact hσ otrace hself
  · rintro ⟨σ, hσ⟩
    refine ⟨realizeContingentPair σ, fun otrace hself => ?_⟩
    rw [omegaOriginal_realize_eq σ otrace]
    exact hσ otrace hself

end DistributedSynthesis
