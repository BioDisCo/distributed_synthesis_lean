/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmInputFreeRationalRun

/-!
# Input-free rationalization does not commute with a hidden family choice

The input-free rational-run basis starts from one nonempty run automaton and
selects one rational accepting transition policy for that automaton.  At a
blind family seam the quantifiers are different: one complete transition must
be legal for every hidden family member.

The two one-state-priority automata below are the smallest kernel-checked
separation.  Each automaton is nonempty and has the (proved, finite-direction)
input-free rational-run basis.  Nevertheless, their initial transitions
require opposite successor values, so there is no one transition legal for
both.  Consequently neither individual rational-run extraction nor a family
of individual extractions supplies the simultaneous shared move.  The family
must be formed, and shown nonempty, before rationalization.
-/

namespace DistributedSynthesis

/-- An input-free automaton whose every successor must be `required`.
All priorities are even, so the only content is the transition choice. -/
def fixedSuccessorInputFreeAutomaton (required : Bool) :
    InputFreeRunParityTreeAutomaton PUnit where
  State := Bool
  stateFinite := inferInstance
  initial := false
  delta := fun _ _ successor => ∀ branch, successor branch = required
  priority := fun _ => 0

/-- The canonical run: the root is the prescribed initial state and every
proper descendant is the required successor. -/
def fixedSuccessorInputFreeRun (required : Bool) :
    TreeNode PUnit → Bool
  | [] => false
  | _ :: _ => required

/-- Each fixed-successor automaton is nonempty. -/
theorem fixedSuccessorInputFreeAutomaton_nonemptyLanguage
    (required : Bool) :
    (fixedSuccessorInputFreeAutomaton required).NonemptyLanguage := by
  refine ⟨fixedSuccessorInputFreeRun required, ?_, ?_⟩
  · constructor
    · rfl
    · intro node branch
      cases node <;> rfl
  · intro branch
    change NatSeqMinEvenParity (fun _ => 0)
    refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
    · intro n
      exact ⟨n, le_rfl, rfl⟩
    · intro q _
      exact Nat.zero_le q

/-- Both members have the existing input-free rational-run basis.  This is
the actual checked finite-direction theorem, not an extra assumption. -/
theorem fixedSuccessorInputFreeAutomaton_rationalRunBasis
    (required : Bool) :
    (fixedSuccessorInputFreeAutomaton required).RationalRunBasis :=
  InputFreeRunParityTreeAutomaton.rationalRunBasis_of_finite _

/-- Thus pointwise rational extraction is available for both hidden members. -/
theorem fixedSuccessorInputFreeAutomaton_pointwiseHasRationalRun :
    ∀ required : Bool,
      (fixedSuccessorInputFreeAutomaton required).HasRationalRun := by
  intro required
  exact fixedSuccessorInputFreeAutomaton_rationalRunBasis required
    (fixedSuccessorInputFreeAutomaton_nonemptyLanguage required)

/-- But the two members admit no common complete transition at their common
initial state.  This is the `∀ member, ∃ move` versus
`∃ move, ∀ member` obstruction in its smallest form. -/
theorem fixedSuccessorInputFreeAutomata_no_commonInitialTransition :
    ¬ ∃ successor : PUnit → Bool,
      (fixedSuccessorInputFreeAutomaton false).delta false PUnit.unit
          successor ∧
        (fixedSuccessorInputFreeAutomaton true).delta false PUnit.unit
          successor := by
  rintro ⟨successor, hfalse, htrue⟩
  have h₀ : successor PUnit.unit = false := hfalse PUnit.unit
  have h₁ : successor PUnit.unit = true := htrue PUnit.unit
  simp [h₀] at h₁

/-- Packaged verdict: the checked basis and pointwise nonemptiness hold for a
finite Boolean family, while simultaneous transition nonemptiness fails. -/
theorem inputFreeRationalRunBasis_not_familyUniform :
    (∀ required : Bool,
        (fixedSuccessorInputFreeAutomaton required).RationalRunBasis ∧
          (fixedSuccessorInputFreeAutomaton required).NonemptyLanguage) ∧
      ¬ ∃ successor : PUnit → Bool,
        ∀ required : Bool,
          (fixedSuccessorInputFreeAutomaton required).delta false PUnit.unit
            successor := by
  constructor
  · intro required
    exact ⟨fixedSuccessorInputFreeAutomaton_rationalRunBasis required,
      fixedSuccessorInputFreeAutomaton_nonemptyLanguage required⟩
  · rintro ⟨successor, hsuccessor⟩
    exact fixedSuccessorInputFreeAutomata_no_commonInitialTransition
      ⟨successor, hsuccessor false, hsuccessor true⟩

end DistributedSynthesis
