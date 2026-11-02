/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemInputFreeFiniteInitialFamilyRationalization
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicySelectionOwnerFibreSafetyAutomaton

/-!
# One owner-fibre safety verifier for a finite entry family

For a fixed policy selection, all canonical recurrent entries use the same
closed-loop transition function and differ only in their initial endpoint and
objective-DPA states.  The generic finite-initial-family construction can
therefore glue all entry runs first and rationalize once.  Its direction
contains a proof-only entry index at the fresh root, but the transition
relation requires every later successor table to ignore that index.

This closes the simultaneous-entry rationalization step.  It does not select
the bank policy: `OwnerFibreSafeOn` for the fixed selection remains the exact
model-specific premise that the replacement-action construction must supply.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev SafetyState :=
  ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin

private abbrev PolicySelection :=
  ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy hwin

namespace ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection

variable (selection : PolicySelection A strategy hwin)

/-- The exact safety automaton for one finite entry family.  `base` only
supplies the overwritten initial field of the common underlying automaton;
every genuine first child is fixed by the entry subtype. -/
noncomputable def ownerFibreSafetyFamilyAutomaton
    (base : SafetyState A strategy hwin)
    (entries : Finset (SafetyState A strategy hwin)) :=
  InputFreeRunParityTreeAutomaton.finiteInitialFamily
    (selection.ownerFibreSafetyAutomaton A strategy hwin base)
    (fun entry : { state // state ∈ entries } ↦ entry.1)

/-- Once one fixed selection is safe from every entry, all entry runs glue
below one root and one finite rational transition table verifies the complete
family.  No verifier transition may depend on the proof-only entry index
after the root. -/
theorem nonempty_ownerFibreSafetyFamily_rationalTransitionPolicy
    (base : SafetyState A strategy hwin)
    (entries : Finset (SafetyState A strategy hwin))
    (hsafe : selection.OwnerFibreSafeOn A strategy hwin entries) :
    Nonempty
      ((selection.ownerFibreSafetyFamilyAutomaton A strategy hwin base entries)
        |>.RationalTransitionPolicy) := by
  apply
    InputFreeRunParityTreeAutomaton.nonempty_finiteInitialFamily_rationalTransitionPolicy
  intro entry
  let policy := selection.ownerFibreSafetyPolicy A strategy hwin entry.1
    (hsafe entry.1 entry.2)
  refine ⟨policy.run, ?_⟩
  simpa only
      [InputFreeRunParityTreeAutomaton.withInitial,
        ownerFibreSafetyAutomaton] using policy.accepts

end ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection

end

end DetParityAutomaton

end DistributedSynthesis
