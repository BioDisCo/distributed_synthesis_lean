/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFringeelim

/-!
# ω-trace fringe elimination

`fringeElim_winning_iff` (`LemFringeelim`) eliminates the fringe over **finite** traces, against a
finite-trace `OutputTraceSpec`.  The θ̄-game's objective is an **ω-parity** condition, so this file
lifts fringe elimination to ω-traces `ℕ → FringeObservationStep`.

The lift is *output-preserving*, hence spec-agnostic: contingentification (and its realization)
produces the **same output at every position** on a recoverable ω-play, so the whole ω-output word is
unchanged and *any* ω-spec -- parity included -- is preserved verbatim
(`omegaOriginal_eq_contingentify`, `omegaOriginal_realize_eq`).  Consequently a fringe-*dependent*
strategy wins an arbitrary ω-spec on every recoverable ω-play iff a fringe-*free* (contingent) one
does (`omegaFringeElim_winning_iff`), with no re-derivation of the finite argument.
-/

namespace DistributedSynthesis

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {H₁ : Type u₁} {H₂ : Type u₂} {R₁ : Type v₁} {R₂ : Type v₂}
  {Out₁ : Type w₁} {Out₂ : Type w₂}

/-- The paired output of a fringe-dependent strategy at position `n` of an ω-trace: exactly the
round-`n` output of `originalPairOutputsFrom` -- each side reads its history up to and including `n`,
its settled fringe past `< n`, and the current fringe. -/
def omegaOriginalOutputAt
    (σ : FringeStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂)
    (otrace : Nat -> FringeObservationStep H₁ H₂ R₁ R₂) (n : Nat) : Out₁ × Out₂ :=
  (σ.one ((List.range (n + 1)).map fun i => (otrace i).historyOne)
      ((List.range n).map fun i => (otrace i).fringeOne) (otrace n).fringeOne,
    σ.two ((List.range (n + 1)).map fun i => (otrace i).historyTwo)
      ((List.range n).map fun i => (otrace i).fringeTwo) (otrace n).fringeTwo)

/-- The paired output of a fringe-free (contingent) strategy at position `n`: reads history up to `n`
and the current fringe only. -/
def omegaContingentOutputAt
    (σ : ContingentStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂)
    (otrace : Nat -> FringeObservationStep H₁ H₂ R₁ R₂) (n : Nat) : Out₁ × Out₂ :=
  (σ.one ((List.range (n + 1)).map fun i => (otrace i).historyOne) (otrace n).fringeOne,
    σ.two ((List.range (n + 1)).map fun i => (otrace i).historyTwo) (otrace n).fringeTwo)

/-- Both players' older fringe values are recoverable at every position of an ω-trace. -/
def OmegaRecovered
    (recoverOne : List H₁ -> List R₁) (recoverTwo : List H₂ -> List R₂)
    (otrace : Nat -> FringeObservationStep H₁ H₂ R₁ R₂) : Prop :=
  ∀ n : Nat,
    recoverOne ((List.range (n + 1)).map fun i => (otrace i).historyOne) =
        (List.range n).map (fun i => (otrace i).fringeOne) ∧
      recoverTwo ((List.range (n + 1)).map fun i => (otrace i).historyTwo) =
        (List.range n).map (fun i => (otrace i).fringeTwo)

/-- **Output preservation, ω-form.**  On a recoverable ω-play the fringe-dependent strategy and its
contingentification emit the *same* output word. -/
theorem omegaOriginal_eq_contingentify
    (recoverOne : List H₁ -> List R₁) (recoverTwo : List H₂ -> List R₂)
    (σ : FringeStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂)
    (otrace : Nat -> FringeObservationStep H₁ H₂ R₁ R₂)
    (hrec : OmegaRecovered recoverOne recoverTwo otrace) :
    omegaOriginalOutputAt σ otrace =
      omegaContingentOutputAt (contingentifyPair recoverOne recoverTwo σ) otrace := by
  funext n
  obtain ⟨h1, h2⟩ := hrec n
  simp only [omegaOriginalOutputAt, omegaContingentOutputAt, contingentifyPair,
    contingentify_apply, h1, h2]

/-- Realizing a contingent strategy back preserves the ω-output word (unconditionally). -/
theorem omegaOriginal_realize_eq
    (σ : ContingentStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂)
    (otrace : Nat -> FringeObservationStep H₁ H₂ R₁ R₂) :
    omegaOriginalOutputAt (realizeContingentPair σ) otrace =
      omegaContingentOutputAt σ otrace := by
  funext n
  simp only [omegaOriginalOutputAt, omegaContingentOutputAt, realizeContingentPair,
    realizeContingent_apply]

/-- **ω-trace fringe elimination.**  Against an *arbitrary* ω-spec (parity included), a
fringe-dependent strategy pair wins on every recoverable ω-play iff a fringe-free (contingent) one
does.  Immediate from ω-output preservation, so spec-agnostic -- the ω-lift the θ̄-game's parity
objective needs. -/
theorem omegaFringeElim_winning_iff
    (recoverOne : List H₁ -> List R₁) (recoverTwo : List H₂ -> List R₂)
    (ospec : (Nat -> Out₁ × Out₂) -> Prop) :
    (∃ σ : FringeStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂,
        ∀ otrace : Nat -> FringeObservationStep H₁ H₂ R₁ R₂,
          OmegaRecovered recoverOne recoverTwo otrace ->
            ospec (omegaOriginalOutputAt σ otrace)) ↔
      (∃ σ : ContingentStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂,
        ∀ otrace : Nat -> FringeObservationStep H₁ H₂ R₁ R₂,
          OmegaRecovered recoverOne recoverTwo otrace ->
            ospec (omegaContingentOutputAt σ otrace)) := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨contingentifyPair recoverOne recoverTwo σ, fun otrace hrec => ?_⟩
    rw [← omegaOriginal_eq_contingentify recoverOne recoverTwo σ otrace hrec]
    exact hσ otrace hrec
  · rintro ⟨σ, hσ⟩
    refine ⟨realizeContingentPair σ, fun otrace hrec => ?_⟩
    rw [omegaOriginal_realize_eq σ otrace]
    exact hσ otrace hrec

end DistributedSynthesis
