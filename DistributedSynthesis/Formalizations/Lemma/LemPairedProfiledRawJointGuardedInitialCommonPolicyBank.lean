/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTreeRationalization
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointInitialCommonBothOneShot

/-!
# A finite initial bank of guarded occurrence-sensitive common policies

After two simultaneous rounds both processes know the two input pairs.  They
therefore select the same member of this finite bank.  Each member is one
occurrence-sensitive rational policy rooted at the literal incoming common
edge, not a policy reconstructed from an incidence-code representative.

The bank index consists only of physical input pairs.  It contains no graph,
orientation, leader, hidden member, or semantic world.
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

private abbrev Seed := (In₁ × In₂) × (In₁ × In₂)

/-! ## One selected package per finite two-round seed -/

/-- Literal incoming common edge after the first and second simultaneous
input pairs. -/
def profiledRawJointGuardedInitialCommonPoint
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointGuardedCommonSemanticPoint A strategy :=
  ⟨profiledRawJointInitialCommonBaseWorld A strategy seed.1.1 seed.1.2,
    seed.2⟩

/-- Select one checked occurrence-sensitive policy package for this finite
seed. -/
noncomputable def profiledRawJointGuardedInitialCommonPackage
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      (profiledRawJointGuardedInitialCommonPoint A strategy seed) :=
  Classical.choice
    (nonempty_profiledRawJointGuardedCommonPolicyPackage A strategy hwin
      (profiledRawJointGuardedInitialCommonPoint A strategy seed))

private abbrev Package
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :=
  profiledRawJointGuardedInitialCommonPackage A strategy hwin seed

/-! ## One finite runtime common-control alphabet -/

/-- Runtime common control: the finite two-round bank index and one reachable
state of its selected rational policy. -/
abbrev ProfiledRawJointGuardedInitialCommonControl :=
  Σ seed : Seed (In₁ := In₁) (In₂ := In₂),
    ProfiledRawJointGuardedCommonPolicyKey A strategy hwin
      (profiledRawJointGuardedInitialCommonPoint A strategy seed)
      (Package A strategy hwin seed).policy

noncomputable instance profiledRawJointGuardedInitialCommonControlFintype :
    Fintype
      (ProfiledRawJointGuardedInitialCommonControl A strategy hwin) := by
  classical
  infer_instance

/-- Enter the selected bank member after two actual simultaneous rounds. -/
def profiledRawJointGuardedInitialCommonControlRoot
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointGuardedInitialCommonControl A strategy hwin :=
  ⟨seed,
    ProfiledRawJointGuardedCommonPolicyKey.root A strategy hwin
      (profiledRawJointGuardedInitialCommonPoint A strategy seed)
      (Package A strategy hwin seed).policy⟩

noncomputable instance profiledRawJointGuardedInitialCommonControlInhabited :
    Inhabited
      (ProfiledRawJointGuardedInitialCommonControl A strategy hwin) :=
  ⟨profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
    ((default, default), (default, default))⟩

/-- Guarded pair chosen once at this complete finite policy key. -/
noncomputable def profiledRawJointGuardedInitialCommonControlPair
    (control : ProfiledRawJointGuardedInitialCommonControl A strategy hwin) :
    ProfiledRawJointGuardedCommonPair A strategy hwin :=
  (Package A strategy hwin control.1).pairAt control.2.state

/-- Common successor after an actual simultaneous receive. -/
def profiledRawJointGuardedInitialCommonControlNext
    (control : ProfiledRawJointGuardedInitialCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedInitialCommonControl A strategy hwin :=
  ⟨control.1, control.2.next A strategy hwin input⟩

@[simp] theorem profiledRawJointGuardedInitialCommonControlNext_seed
    (control : ProfiledRawJointGuardedInitialCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedInitialCommonControlNext A strategy hwin control
      input).1 = control.1 :=
  rfl

/-- The current pair is valid at the public incidence code stored by the
reachable policy state. -/
theorem profiledRawJointGuardedInitialCommonControlPair_valid
    (control : ProfiledRawJointGuardedInitialCommonControl A strategy hwin) :
    ProfiledRawJointGuardedCommonMoveValid A strategy hwin control.2.state.1
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
        control) :=
  (Package A strategy hwin control.1).pairAt_valid control.2.state
    control.2.reachable

/-- The common transition uses one whole successor assignment of the fixed
rational policy. -/
theorem profiledRawJointGuardedInitialCommonControlNext_state
    (control : ProfiledRawJointGuardedInitialCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedInitialCommonControlNext A strategy hwin control
        input).2.state =
      (Package A strategy hwin control.1).policy.successor control.2.state
        input :=
  rfl

/-- Its next public code is exactly the merge of the two current guarded root
targets. -/
theorem profiledRawJointGuardedInitialCommonControlNext_code
    (control : ProfiledRawJointGuardedInitialCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedInitialCommonControlNext A strategy hwin control
        input).2.state.1 =
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin control
        ).bothNextCode A strategy hwin input :=
  (Package A strategy hwin control.1).successor_code_eq_currentPair A strategy
    hwin control.2.reachable input

/-- Pair selected at the successor control is definitionally the package's
`nextPairAt` for the current state. -/
@[simp] theorem profiledRawJointGuardedInitialCommonControlNext_pair
    (control : ProfiledRawJointGuardedInitialCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedInitialCommonControlPair A strategy hwin
        (profiledRawJointGuardedInitialCommonControlNext A strategy hwin
          control input) =
      (Package A strategy hwin control.1).nextPairAt A strategy hwin
        control.2.state input :=
  rfl

end


end DetParityAutomaton

end DistributedSynthesis
