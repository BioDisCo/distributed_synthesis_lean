/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemInputFreeBasisNotFamilyUniform
import DistributedSynthesis.Formalizations.Theorem.ThmRootGuardedPolicyActivation
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRationalTree

/-!
# Inheriting one input-free rational policy below a literal child

A persistent rational policy has no parity-reset problem: its subtree below
any first direction is again a rational policy, re-rooted at the literal
child.  This file proves that positive fact once and specializes the
re-rooting equality to the paired profiled automata.

It also records the exact limitation relevant to open root families.
Pointwise persistent policies do not manufacture a common family transition.
The Boolean counterexample from `LemInputFreeBasisNotFamilyUniform` already
has a rational policy for each member but no successor assignment legal for
both.  Hence a proof invariant carrying one policy *per anchor* still needs a
separate theorem saying that the one shared whole-block table follows every
carried policy.  The current open-root interface, which stores only
`HasRationalRun`, does not contain that compatibility equation.
-/

namespace DistributedSynthesis

universe u w

namespace InputFreeRunParityTreeAutomaton

variable {Branch : Type u}

/-- Restrict an ordinary rational transition policy to the subtree below one
literal first direction.  The successor table is retained unchanged and
parity is inherited by deleting the finite one-node prefix. -/
noncomputable def RationalTransitionPolicy.belowFirst
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (policy : A.RationalTransitionPolicy) (first : Branch) :
    (A.withInitial (policy.run [first])).RationalTransitionPolicy where
  run := fun node => policy.run ([first] ++ node)
  accepts := by
    constructor
    · constructor
      · rfl
      · intro node
        have hlegal := policy.accepts.1.2 ([first] ++ node)
        simpa only [withInitial, uniqueTree, List.append_assoc] using hlegal
    · intro tail
      have hparity := policy.accepts.2 (prefixedBranch first tail)
      have hshift := (natSeqMinEvenParity_shift
        (fun n => A.priority
          (policy.run (branchNode (prefixedBranch first tail) n))) 1).mpr
            hparity
      simpa [withInitial, branchNode_prefixedBranch, Nat.add_comm] using hshift
  successor := policy.successor
  successor_at := by
    intro node branch
    simpa only [List.append_assoc] using
      policy.successor_at ([first] ++ node) branch
  legal_at := by
    intro node
    have hlegal := policy.legal_at ([first] ++ node)
    simpa only [withInitial, uniqueTree, List.append_assoc] using hlegal

@[simp] theorem RationalTransitionPolicy.belowFirst_run
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (policy : A.RationalTransitionPolicy) (first : Branch)
    (node : TreeNode Branch) :
    (policy.belowFirst A first).run node = policy.run ([first] ++ node) :=
  rfl

@[simp] theorem RationalTransitionPolicy.belowFirst_successor
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (policy : A.RationalTransitionPolicy) (first : Branch) :
    (policy.belowFirst A first).successor = policy.successor :=
  rfl

/-- The new root is literally the old policy's selected child. -/
theorem RationalTransitionPolicy.belowFirst_initial_eq_successor
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (policy : A.RationalTransitionPolicy) (first : Branch) :
    (policy.belowFirst A first).run [] =
      policy.successor A.initial first := by
  rw [RationalTransitionPolicy.belowFirst_run]
  have hchild := policy.successor_at [] first
  simpa [policy.accepts.1.1] using hchild.symm

end InputFreeRunParityTreeAutomaton

namespace DetParityAutomaton

universe v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Paired profiled entry automata differ at different roots only in their
initial-state field. -/
theorem pairedProfiledEntryRunAutomaton_withInitial
    (source target : PairedProfiledTreeState A) :
    (pairedProfiledEntryRunAutomaton A source).withInitial target =
      pairedProfiledEntryRunAutomaton A target :=
  rfl

/-- A persistent paired policy inherited below one direction, now typed at
the literal child state. -/
noncomputable def pairedProfiledPolicyBelowFirst
    (source : PairedProfiledTreeState A)
    (policy : (pairedProfiledEntryRunAutomaton A source).RationalTransitionPolicy)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    (pairedProfiledEntryRunAutomaton A
      (policy.run [direction])).RationalTransitionPolicy := by
  simpa only [pairedProfiledEntryRunAutomaton_withInitial] using
    policy.belowFirst (pairedProfiledEntryRunAutomaton A source) direction

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Its initial state is the original policy's literal successor. -/
theorem pairedProfiledPolicyBelowFirst_initial_eq_successor
    (source : PairedProfiledTreeState A)
    (policy : (pairedProfiledEntryRunAutomaton A source).RationalTransitionPolicy)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    (pairedProfiledPolicyBelowFirst A source policy direction).run [] =
      policy.successor source direction := by
  exact policy.belowFirst_initial_eq_successor
    (pairedProfiledEntryRunAutomaton A source) direction

end

end DetParityAutomaton

/-! ## Fail-fast verdict for a family of persistent policies -/

/-- Even actual persistent rational policies for every hidden member do not
imply a common complete transition.  Therefore the missing inheritance law in
the open construction cannot be obtained by merely replacing each root's
`HasRationalRun` proof with an independently chosen policy. -/
theorem pointwisePersistentRationalPolicies_not_familyUniform :
    (∀ required : Bool,
      Nonempty
        (((fixedSuccessorInputFreeAutomaton required :
          InputFreeRunParityTreeAutomaton.{0, 0} PUnit)).RationalTransitionPolicy)) ∧
      ¬ ∃ successor : PUnit → Bool,
        ∀ required : Bool,
          (fixedSuccessorInputFreeAutomaton required).delta false PUnit.unit
            successor := by
  constructor
  · intro required
    let T : InputFreeRunParityTreeAutomaton.{0, 0} PUnit :=
      fixedSuccessorInputFreeAutomaton required
    have hrun : T.HasRationalRun := by
      simpa only [T] using
        (fixedSuccessorInputFreeAutomaton_pointwiseHasRationalRun required :
          (fixedSuccessorInputFreeAutomaton required :
            InputFreeRunParityTreeAutomaton.{0, 0} PUnit).HasRationalRun)
    exact InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
      T hrun
  · rintro ⟨successor, hsuccessor⟩
    have hfalse : successor PUnit.unit = false :=
      hsuccessor false PUnit.unit
    have htrue : successor PUnit.unit = true :=
      hsuccessor true PUnit.unit
    simp [hfalse] at htrue

end DistributedSynthesis
