/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalPostRoundClosure

/-!
# Provenance of the two end-to-end shadows

Reality of the two components is not by itself enough for the alternating
overlap diamond: the components must be the continuation and reversal of one
common real phase on one common input.  `Coupled` retains exactly that
proof-only fact.  It adds no data to either local summary and, in particular,
does not reveal the strict orientation to a process.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-- The two candidates were produced together from one real oriented phase.
The disjunction is a correctness witness, not a run-time orientation tag. -/
def EndToEndBothCandidates.Coupled
    (candidates : EndToEndBothCandidates A package) : Prop :=
  (∃ phase move,
    IsRealEndToEndPhase A package phase ∧ phase.IsRight ∧
      (phase.enterBothFromRight A package move).2 = some candidates) ∨
  (∃ phase move,
    IsRealEndToEndPhase A package phase ∧ phase.IsLeft ∧
      (phase.enterBothFromLeft A package move).2 = some candidates)

/-- Coupling with the retained overlap anchor.  `false` records that the
pair was refreshed from its right shadow; `true` records the left-shadow
refresh.  This remains a proof-only reachability fact: neither local carrier
contains the orientation witness below. -/
def EndToEndBothCandidates.CoupledAt
    (anchor : Bool) (candidates : EndToEndBothCandidates A package) : Prop :=
  match anchor with
  | false =>
      ∃ phase move,
        IsRealEndToEndPhase A package phase ∧ phase.IsRight ∧
          (phase.enterBothFromRight A package move).2 = some candidates
  | true =>
      ∃ phase move,
        IsRealEndToEndPhase A package phase ∧ phase.IsLeft ∧
          (phase.enterBothFromLeft A package move).2 = some candidates

theorem EndToEndBothCandidates.coupled_of_enterBothFromRight
    (phase : EndToEndMatchedPhase A package)
    (hreal : IsRealEndToEndPhase A package phase)
    (hright : phase.IsRight) (move : In₁ × In₂)
    (candidates : EndToEndBothCandidates A package)
    (hnext : (phase.enterBothFromRight A package move).2 = some candidates) :
    candidates.Coupled A package := by
  exact Or.inl ⟨phase, move, hreal, hright, hnext⟩

theorem EndToEndBothCandidates.coupled_of_enterBothFromLeft
    (phase : EndToEndMatchedPhase A package)
    (hreal : IsRealEndToEndPhase A package phase)
    (hleft : phase.IsLeft) (move : In₁ × In₂)
    (candidates : EndToEndBothCandidates A package)
    (hnext : (phase.enterBothFromLeft A package move).2 = some candidates) :
    candidates.Coupled A package := by
  exact Or.inr ⟨phase, move, hreal, hleft, hnext⟩

theorem EndToEndBothCandidates.coupledAt_false_of_enterBothFromRight
    (phase : EndToEndMatchedPhase A package)
    (hreal : IsRealEndToEndPhase A package phase)
    (hright : phase.IsRight) (move : In₁ × In₂)
    (candidates : EndToEndBothCandidates A package)
    (hnext : (phase.enterBothFromRight A package move).2 = some candidates) :
    candidates.CoupledAt A package false := by
  exact ⟨phase, move, hreal, hright, hnext⟩

theorem EndToEndBothCandidates.coupledAt_true_of_enterBothFromLeft
    (phase : EndToEndMatchedPhase A package)
    (hreal : IsRealEndToEndPhase A package phase)
    (hleft : phase.IsLeft) (move : In₁ × In₂)
    (candidates : EndToEndBothCandidates A package)
    (hnext : (phase.enterBothFromLeft A package move).2 = some candidates) :
    candidates.CoupledAt A package true := by
  exact ⟨phase, move, hreal, hleft, hnext⟩

/-- Refreshing an overlap from either retained anchor produces another
coupled pair. -/
theorem EndToEndBothCandidates.coupled_of_repeatBoth
    (anchor : Bool) (candidates next : EndToEndBothCandidates A package)
    (hreal : candidates.Real A package) (move : In₁ × In₂)
    (hnext : (if anchor then candidates.repeatBothFromLeft A package move
      else candidates.repeatBothFromRight A package move).2 = some next) :
    next.Coupled A package := by
  cases anchor with
  | false =>
      exact next.coupled_of_enterBothFromRight A package candidates.right
        hreal.1 candidates.right_oriented move
        (by simpa [EndToEndBothCandidates.repeatBothFromRight] using hnext)
  | true =>
      exact next.coupled_of_enterBothFromLeft A package candidates.left
        hreal.2 candidates.left_oriented move
        (by simpa [EndToEndBothCandidates.repeatBothFromLeft] using hnext)

/-- Repeating an ambiguous round preserves the precise provenance selected
by its retained anchor. -/
theorem EndToEndBothCandidates.coupledAt_of_repeatBoth
    (anchor : Bool) (candidates next : EndToEndBothCandidates A package)
    (hreal : candidates.Real A package) (move : In₁ × In₂)
    (hnext : (if anchor then candidates.repeatBothFromLeft A package move
      else candidates.repeatBothFromRight A package move).2 = some next) :
    next.CoupledAt A package anchor := by
  cases anchor with
  | false =>
      exact next.coupledAt_false_of_enterBothFromRight A package
        candidates.right hreal.1 candidates.right_oriented move
        (by simpa [EndToEndBothCandidates.repeatBothFromRight] using hnext)
  | true =>
      exact next.coupledAt_true_of_enterBothFromLeft A package
        candidates.left hreal.2 candidates.left_oriented move
        (by simpa [EndToEndBothCandidates.repeatBothFromLeft] using hnext)

/-- Coupling entails the existing componentwise reality invariant. -/
theorem EndToEndBothCandidates.real_of_coupled
    (candidates : EndToEndBothCandidates A package)
    (hcoupled : candidates.Coupled A package) :
    candidates.Real A package := by
  rcases hcoupled with ⟨phase, move, hreal, hright, hnext⟩ |
      ⟨phase, move, hreal, hleft, hnext⟩
  · obtain ⟨actual, hactual, hrealRight, hrealLeft⟩ :=
      exists_real_endToEnd_candidates_enterBothFromRight A package phase
        hreal hright move
    rw [hnext] at hactual
    cases Option.some.inj hactual
    exact ⟨hrealRight, hrealLeft⟩
  · obtain ⟨actual, hactual, hrealRight, hrealLeft⟩ :=
      exists_real_endToEnd_candidates_enterBothFromLeft A package phase
        hreal hleft move
    rw [hnext] at hactual
    cases Option.some.inj hactual
    exact ⟨hrealRight, hrealLeft⟩

theorem EndToEndBothCandidates.coupled_of_coupledAt
    (anchor : Bool) (candidates : EndToEndBothCandidates A package)
    (hcoupled : candidates.CoupledAt A package anchor) :
    candidates.Coupled A package := by
  cases anchor with
  | false => exact Or.inl hcoupled
  | true => exact Or.inr hcoupled

theorem EndToEndBothCandidates.real_of_coupledAt
    (anchor : Bool) (candidates : EndToEndBothCandidates A package)
    (hcoupled : candidates.CoupledAt A package anchor) :
    candidates.Real A package :=
  candidates.real_of_coupled A package
    (candidates.coupled_of_coupledAt A package anchor hcoupled)

end

end DetParityAutomaton

end DistributedSynthesis
