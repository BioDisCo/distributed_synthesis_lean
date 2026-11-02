/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedStreamingEmissionLocality
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenReanchoredEvaluationOneRoundTrace

/-!
# The missing finite overlay frontier in the streaming state

The concrete streaming query accumulator records the direction summary used
at the next epoch boundary.  It intentionally leaves the symmetric bank of
per-value block queries unchanged on strict rounds.  A physical overlay does
the opposite additional work: every round advances its rational-tree control
and union-monitor state.  Consequently the current `FiniteEpochPhysicalState`
cannot reconstruct the installed overlay from `branch`, `bank`, and `query`.

This file records that fail-fast fact definitionally and introduces the
smallest lineage-safe state extension: finite *sets* of compatible right and
left overlays.  A strict round advances every member.  No member, side,
orientation, strict leader, or future persistent lineage is selected by this
transition.  Boundary population and output homogeneity remain separate
proof obligations.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-! ## Exact fail-fast fact -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- A strict streaming step changes the direction tag but leaves every
per-value rational block query in the symmetric query bank untouched. -/
@[simp] theorem
    profiledOpenWitnessedStreamingStrictQueryStep_queryBank
    (query : ProfiledOpenWitnessedTableQuery.{i, u, v, x, y, s,
      max i u v x y s, max i u v x y s} A initialCode)
    (letter : ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂)) :
    (profiledOpenWitnessedStreamingStrictQueryStep A initialCode query
      letter).1.1.2 = query.1.1.2 :=
  rfl

/-! ## Orientation-free finite frontier -/

/-- All currently compatible executable overlays.  Both sides are retained;
the state contains no selected side or selected hidden lineage. -/
structure ProfiledOpenWitnessedStreamingOverlayFrontier where
  right : Finset (ProfiledOpenWitnessedRightRoundOverlay A initialCode)
  left : Finset (ProfiledOpenWitnessedLeftRoundOverlay A initialCode)

noncomputable instance
    profiledOpenWitnessedStreamingOverlayFrontier_fintype :
    Fintype (ProfiledOpenWitnessedStreamingOverlayFrontier A initialCode) := by
  classical
  let encode : ProfiledOpenWitnessedStreamingOverlayFrontier A initialCode →
      Finset (ProfiledOpenWitnessedRightRoundOverlay A initialCode) ×
        Finset (ProfiledOpenWitnessedLeftRoundOverlay A initialCode) :=
    fun frontier ↦ (frontier.right, frontier.left)
  exact Fintype.ofInjective encode (by
    intro first second heq
    rcases first with ⟨firstRight, firstLeft⟩
    rcases second with ⟨secondRight, secondLeft⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rfl)

/-- Advance every possible overlay through the same physical input pair.
There is deliberately no graph argument. -/
noncomputable def ProfiledOpenWitnessedStreamingOverlayFrontier.step
    (frontier : ProfiledOpenWitnessedStreamingOverlayFrontier A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenWitnessedStreamingOverlayFrontier A initialCode := by
  classical
  exact
    { right := frontier.right.image fun overlay ↦
        overlay.step A initialCode inputOne inputTwo
      left := frontier.left.image fun overlay ↦
        overlay.step A initialCode inputOne inputTwo }

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    ProfiledOpenWitnessedStreamingOverlayFrontier.mem_right_step_of_mem
    (frontier : ProfiledOpenWitnessedStreamingOverlayFrontier A initialCode)
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) (hmem : overlay ∈ frontier.right) :
    overlay.step A initialCode inputOne inputTwo ∈
      (frontier.step A initialCode inputOne inputTwo).right := by
  classical
  change overlay.step A initialCode inputOne inputTwo ∈
    frontier.right.image
      (fun candidate ↦ candidate.step A initialCode inputOne inputTwo)
  exact Finset.mem_image.2 ⟨overlay, hmem, rfl⟩

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    ProfiledOpenWitnessedStreamingOverlayFrontier.mem_left_step_of_mem
    (frontier : ProfiledOpenWitnessedStreamingOverlayFrontier A initialCode)
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) (hmem : overlay ∈ frontier.left) :
    overlay.step A initialCode inputOne inputTwo ∈
      (frontier.step A initialCode inputOne inputTwo).left := by
  classical
  change overlay.step A initialCode inputOne inputTwo ∈
    frontier.left.image
      (fun candidate ↦ candidate.step A initialCode inputOne inputTwo)
  exact Finset.mem_image.2 ⟨overlay, hmem, rfl⟩

/-- Iterate the complete frontier through a finite physical epoch. -/
noncomputable def ProfiledOpenWitnessedStreamingOverlayFrontier.run :
    ProfiledOpenWitnessedStreamingOverlayFrontier A initialCode →
      List (In₁ × In₂) →
        ProfiledOpenWitnessedStreamingOverlayFrontier A initialCode
  | frontier, [] => frontier
  | frontier, input :: rest =>
      ProfiledOpenWitnessedStreamingOverlayFrontier.run
        (frontier.step A initialCode input.1 input.2) rest

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every initially represented right overlay remains represented after the
whole epoch as its literal executable overlay run. -/
theorem ProfiledOpenWitnessedStreamingOverlayFrontier.overlayRun_mem_right
    (frontier : ProfiledOpenWitnessedStreamingOverlayFrontier A initialCode)
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputs : List (In₁ × In₂)) (hmem : overlay ∈ frontier.right) :
    profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay inputs ∈
      (ProfiledOpenWitnessedStreamingOverlayFrontier.run A initialCode frontier
        inputs).right := by
  induction inputs generalizing frontier overlay with
  | nil => exact hmem
  | cons input rest ih =>
      simpa only [profiledOpenWitnessedRightRoundOverlayRun,
        ProfiledOpenWitnessedStreamingOverlayFrontier.run] using
        (ih
          (frontier := frontier.step A initialCode input.1 input.2)
          (overlay := overlay.step A initialCode input.1 input.2)
          (frontier.mem_right_step_of_mem A initialCode overlay input.1 input.2
            hmem))

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror. -/
theorem ProfiledOpenWitnessedStreamingOverlayFrontier.overlayRun_mem_left
    (frontier : ProfiledOpenWitnessedStreamingOverlayFrontier A initialCode)
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputs : List (In₁ × In₂)) (hmem : overlay ∈ frontier.left) :
    profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay inputs ∈
      (ProfiledOpenWitnessedStreamingOverlayFrontier.run A initialCode frontier
        inputs).left := by
  induction inputs generalizing frontier overlay with
  | nil => exact hmem
  | cons input rest ih =>
      simpa only [profiledOpenWitnessedLeftRoundOverlayRun,
        ProfiledOpenWitnessedStreamingOverlayFrontier.run] using
        (ih
          (frontier := frontier.step A initialCode input.1 input.2)
          (overlay := overlay.step A initialCode input.1 input.2)
          (frontier.mem_left_step_of_mem A initialCode overlay input.1 input.2
            hmem))

end

end DetParityAutomaton

end DistributedSynthesis
