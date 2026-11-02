/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageCodeLiveness
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedRecutPhase

/-!
# Audit of physical closing sides versus code-thread alternation

The hidden code-lineage monitor flips its proof-side side after every code
letter.  The streaming physical phase, however, restarts at `boundary` after
every simultaneous round; the next closing side is independently the last
strict side of that epoch (or the fixed boundary fallback).  In particular,
two successive physical epochs may close on the same side.

The lemmas below make the resulting interface condition explicit.  If one
fixed never-dead code thread is aligned with every completed physical query,
then the query sides must alternate.  Consequently the present streaming
clock cannot obtain such an alignment for all environments.  This is an
audit result, not an executable side test: no process receives any side,
leader, orientation, lineage, or hidden bit.
-/

namespace DistributedSynthesis

universe c i r u v x y s

namespace DetParityAutomaton

/-! ## The exact hidden-thread implication -/

/-- Alignment with one fixed code thread forces consecutive physical query
sides to be opposite. -/
theorem querySides_alternate_of_fixedCodeThreadAlignment
    {Code : Type c} {I : Type i} {Root : Type r}
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (word : OmegaWord Code) (initialSide : IndexedLineageSide)
    (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun initialCode currentSlots word
        initialSide lineage (n + 1)).2 ≠ .dead)
    (querySide : Nat → IndexedLineageSide)
    (halign : ∀ n,
      (codedAlternatingIndexedLineageCodeLiveAtOfNeverDead initialCode
        currentSlots word initialSide lineage hnever n).side =
          (querySide n).other)
    (n : Nat) :
    querySide (n + 1) = (querySide n).other := by
  have hflip :=
    codedAlternatingIndexedLineageCodeLiveAtOfNeverDead_side_succ initialCode
      currentSlots word initialSide lineage hnever n
  rw [halign (n + 1), halign n] at hflip
  cases hcurrent : querySide n <;>
    cases hnext : querySide (n + 1) <;>
    simp_all [IndexedLineageSide.other]

/-- In particular, two equal consecutive completed-query sides cannot both
be aligned with the same fixed code thread. -/
theorem no_fixedCodeThreadAlignment_of_equalConsecutiveQuerySides
    {Code : Type c} {I : Type i} {Root : Type r}
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (word : OmegaWord Code) (initialSide : IndexedLineageSide)
    (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun initialCode currentSlots word
        initialSide lineage (n + 1)).2 ≠ .dead)
    (querySide : Nat → IndexedLineageSide)
    (halign : ∀ n,
      (codedAlternatingIndexedLineageCodeLiveAtOfNeverDead initialCode
        currentSlots word initialSide lineage hnever n).side =
          (querySide n).other)
    (n : Nat) (hsame : querySide (n + 1) = querySide n) : False := by
  have halternates := querySides_alternate_of_fixedCodeThreadAlignment
    initialCode currentSlots word initialSide lineage hnever querySide halign n
  rw [hsame] at halternates
  cases hside : querySide n <;>
    simp only [hside, IndexedLineageSide.other] at halternates <;>
    cases halternates

/-! ## The exact repair fork for a side sequence -/

/-- Closing sides change at arbitrarily late epoch indices. -/
def IndexedSideSwitchRecurrent
    (side : Nat → IndexedLineageSide) : Prop :=
  ∀ start : Nat, ∃ n : Nat,
    start ≤ n ∧ side (n + 1) = (side n).other

/-- Closing sides stabilize after a finite prefix. -/
def IndexedSideEventuallyConstant
    (side : Nat → IndexedLineageSide) : Prop :=
  ∃ start : Nat, ∃ fixed : IndexedLineageSide,
    ∀ n : Nat, start ≤ n → side n = fixed

/-- On a two-element side type, failure to flip means equality. -/
theorem IndexedLineageSide.eq_of_ne_other
    {left right : IndexedLineageSide}
    (hne : right ≠ left.other) : right = left := by
  cases left <;> cases right <;>
    simp_all [IndexedLineageSide.other]

/-- Every closing-side sequence has exactly the proof split needed by the
repaired recurrent-synchronization argument: unboundedly many genuine side
changes, or an eventually fixed side.  This dichotomy is proof-side and does
not give a process a side detector. -/
theorem indexedSide_eventuallyConstant_or_switchRecurrent
    (side : Nat → IndexedLineageSide) :
    IndexedSideEventuallyConstant side ∨ IndexedSideSwitchRecurrent side := by
  classical
  by_cases hswitch : IndexedSideSwitchRecurrent side
  · exact Or.inr hswitch
  · left
    simp only [IndexedSideSwitchRecurrent] at hswitch
    push_neg at hswitch
    rcases hswitch with ⟨start, hstart⟩
    refine ⟨start, side start, ?_⟩
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction k with
    | zero => rfl
    | succ k ih =>
        have hsame : side (start + k + 1) = side (start + k) :=
          IndexedLineageSide.eq_of_ne_other
            (hstart (start + k) (by omega))
        rw [Nat.add_succ]
        exact hsame.trans (ih (by omega))

/-! ## The streaming phase admits repeated sides -/

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

/-- A right-only strict phase starting from a fresh epoch closes on the right
side. -/
@[simp] theorem profiledOpenFreshRightEpoch_activeSide
    (moves : Finset (ProfiledOpenIndexedBiBeliefMove A))
    (inputOne : In₁) (inputTwo : In₂) :
    let phase :=
      (profiledOpenPhysicalRecutPhaseInitial A moves).advance A initialCode
        Finset.univ Finset.univ
        { inputOne := inputOne, inputTwo := inputTwo, graph := .right }
    phase.tier.activeSide.getD .right = .right := by
  rfl

/-- The mirror fresh left epoch closes on the left side. -/
@[simp] theorem profiledOpenFreshLeftEpoch_activeSide
    (moves : Finset (ProfiledOpenIndexedBiBeliefMove A))
    (inputOne : In₁) (inputTwo : In₂) :
    let phase :=
      (profiledOpenPhysicalRecutPhaseInitial A moves).advance A initialCode
        Finset.univ Finset.univ
        { inputOne := inputOne, inputTwo := inputTwo, graph := .left }
    phase.tier.activeSide.getD .right = .left := by
  rfl

/-- Since a simultaneous close restarts the next epoch at the same fresh
boundary phase, two consecutive right-only epochs have the same completed
query side.  This concrete witness refutes unconditional side alternation in
the current streaming clock. -/
theorem profiledOpenStreaming_admits_two_consecutive_rightClosingSides
    (moves : Finset (ProfiledOpenIndexedBiBeliefMove A))
    (firstInputOne secondInputOne : In₁)
    (firstInputTwo secondInputTwo : In₂) :
    let first :=
      (profiledOpenPhysicalRecutPhaseInitial A moves).advance A initialCode
        Finset.univ Finset.univ
        { inputOne := firstInputOne, inputTwo := firstInputTwo,
          graph := .right }
    let second :=
      (profiledOpenPhysicalRecutPhaseInitial A moves).advance A initialCode
        Finset.univ Finset.univ
        { inputOne := secondInputOne, inputTwo := secondInputTwo,
          graph := .right }
    first.tier.activeSide.getD .right =
        second.tier.activeSide.getD .right ∧
      first.tier.activeSide.getD .right = .right := by
  exact ⟨rfl, rfl⟩

end

end DetParityAutomaton

end DistributedSynthesis
