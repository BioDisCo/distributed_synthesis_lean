/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLinkedTreeRationalization
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointInitialCommonBothOneShot

/-!
# A finite initial bank of parent-linked guarded common policies

This is the parent-linked counterpart of the original guarded common policy
bank.  Its runtime index is still just the two physical input pairs observed
during the common front.  The policy state additionally carries the exact
guarded pair installed by its parent transition, so later strict/common
cross-anchor equations cannot be lost by incidence-code mosaicing.

No executable definition takes a graph, orientation, hierarchy side, leader
bit, semantic world, or history.
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

private abbrev SemanticPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

/-! ## One selected linked policy per finite seed -/

/-- Literal incoming common edge after the two simultaneous seed rounds. -/
def profiledRawJointGuardedLinkedInitialCommonPoint
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) : SemanticPoint A strategy :=
  ⟨profiledRawJointInitialCommonBaseWorld A strategy seed.1.1 seed.1.2,
    seed.2⟩

/-- Choose one finite parent-linked rational policy for the seed. -/
noncomputable def profiledRawJointGuardedLinkedInitialCommonPolicy
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      (profiledRawJointGuardedLinkedInitialCommonPoint A strategy seed) :=
  Classical.choice
    (nonempty_profiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      (profiledRawJointGuardedLinkedInitialCommonPoint A strategy seed))

private abbrev Policy (seed : Seed (In₁ := In₁) (In₂ := In₂)) :=
  profiledRawJointGuardedLinkedInitialCommonPolicy A strategy hwin seed

/-! ## Finite common controls -/

/-- Runtime common control: finite seed and reachable state of its one linked
rational policy. -/
abbrev ProfiledRawJointGuardedLinkedInitialCommonControl :=
  Σ seed : Seed (In₁ := In₁) (In₂ := In₂),
    ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin
      (profiledRawJointGuardedLinkedInitialCommonPoint A strategy seed)
      (Policy A strategy hwin seed)

noncomputable instance
    profiledRawJointGuardedLinkedInitialCommonControlFintype :
    Fintype
      (ProfiledRawJointGuardedLinkedInitialCommonControl A strategy hwin) := by
  classical
  infer_instance

/-- Root of the linked policy selected by a two-round seed. -/
def profiledRawJointGuardedLinkedInitialCommonControlRoot
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointGuardedLinkedInitialCommonControl A strategy hwin :=
  ⟨seed,
    ProfiledRawJointGuardedCommonLinkedPolicyKey.root A strategy hwin
      (profiledRawJointGuardedLinkedInitialCommonPoint A strategy seed)
      (Policy A strategy hwin seed)⟩

noncomputable instance
    profiledRawJointGuardedLinkedInitialCommonControlInhabited :
    Inhabited
      (ProfiledRawJointGuardedLinkedInitialCommonControl A strategy hwin) :=
  ⟨profiledRawJointGuardedLinkedInitialCommonControlRoot A strategy hwin
    ((default, default), (default, default))⟩

/-- Current guarded pair, stored literally in the linked policy code. -/
def profiledRawJointGuardedLinkedInitialCommonControlPair
    (control :
      ProfiledRawJointGuardedLinkedInitialCommonControl A strategy hwin) :
    CommonPair A strategy hwin :=
  control.2.pair A strategy hwin

/-- Whole linked move selected once at the current policy state. -/
noncomputable def profiledRawJointGuardedLinkedInitialCommonControlMove
    (control :
      ProfiledRawJointGuardedLinkedInitialCommonControl A strategy hwin) :
    ProfiledRawJointGuardedCommonLinkedMove A strategy hwin :=
  control.2.move A strategy hwin

/-- Follow the linked policy on one simultaneous input. -/
def profiledRawJointGuardedLinkedInitialCommonControlNext
    (control :
      ProfiledRawJointGuardedLinkedInitialCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedLinkedInitialCommonControl A strategy hwin :=
  ⟨control.1, control.2.next A strategy hwin input⟩

@[simp] theorem
    profiledRawJointGuardedLinkedInitialCommonControlNext_seed
    (control :
      ProfiledRawJointGuardedLinkedInitialCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedLinkedInitialCommonControlNext A strategy hwin
      control input).1 = control.1 :=
  rfl

/-- Current component of the selected linked move agrees with the current
control pair. -/
theorem profiledRawJointGuardedLinkedInitialCommonControlMove_current
    (control :
      ProfiledRawJointGuardedLinkedInitialCommonControl A strategy hwin) :
    (profiledRawJointGuardedLinkedInitialCommonControlMove A strategy hwin
      control).1 =
      profiledRawJointGuardedLinkedInitialCommonControlPair A strategy hwin
        control :=
  control.2.move_current A strategy hwin

/-- Pair installed at the next control is the exact child chosen by the
current complete move. -/
theorem profiledRawJointGuardedLinkedInitialCommonControlNext_pair
    (control :
      ProfiledRawJointGuardedLinkedInitialCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedLinkedInitialCommonControlPair A strategy hwin
        (profiledRawJointGuardedLinkedInitialCommonControlNext A strategy hwin
          control input) =
      (profiledRawJointGuardedLinkedInitialCommonControlMove A strategy hwin
        control).2 input :=
  control.2.next_pair A strategy hwin input

/-- The complete linked move yields an allowed child for the existing local
shadow carrier, after rewriting its current component to the control pair. -/
noncomputable def
    profiledRawJointGuardedLinkedInitialCommonControlSuccessor
    (control :
      ProfiledRawJointGuardedLinkedInitialCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonSuccessor A strategy hwin
      (profiledRawJointGuardedLinkedInitialCommonControlPair A strategy hwin
        control) input := by
  let move :=
    profiledRawJointGuardedLinkedInitialCommonControlMove A strategy hwin
      control
  refine ⟨move.2 input, ?_⟩
  rw [← profiledRawJointGuardedLinkedInitialCommonControlMove_current A
    strategy hwin control]
  exact (control.2.move_valid A strategy hwin).child_allowed A strategy hwin
    input

@[simp] theorem
    profiledRawJointGuardedLinkedInitialCommonControlSuccessor_pair
    (control :
      ProfiledRawJointGuardedLinkedInitialCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedLinkedInitialCommonControlSuccessor A strategy hwin
      control input).1 =
      profiledRawJointGuardedLinkedInitialCommonControlPair A strategy hwin
        (profiledRawJointGuardedLinkedInitialCommonControlNext A strategy hwin
          control input) := by
  exact (profiledRawJointGuardedLinkedInitialCommonControlNext_pair A strategy
    hwin control input).symm

/-- Bank-level no-mosaic law. -/
theorem profiledRawJointGuardedLinkedInitialCommonControl_parent_child
    (control :
      ProfiledRawJointGuardedLinkedInitialCommonControl A strategy hwin)
    (R : CommonPair A strategy hwin → CommonPair A strategy hwin →
      (In₁ × In₂) → Prop)
    (hsemantic : ∀ point : SemanticPoint A strategy, ∀ input,
      R (point.move A strategy hwin)
        ((point.step A strategy input).move A strategy hwin) input)
    (input : In₁ × In₂) :
    R (profiledRawJointGuardedLinkedInitialCommonControlPair A strategy hwin
        control)
      (profiledRawJointGuardedLinkedInitialCommonControlPair A strategy hwin
        (profiledRawJointGuardedLinkedInitialCommonControlNext A strategy hwin
          control input)) input :=
  control.2.parent_child A strategy hwin R hsemantic input

end


end DetParityAutomaton

end DistributedSynthesis
