/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndInitialReadback
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedFirstBlockRegularization

/-!
# Reading guarded first-block transitions from one common policy

The initial regularization exposes a guarded rational policy obtained from one
global rational policy.  This file reads the first recurrent lambda and its
children directly from that supplied policy.  In particular, a child is not
accepted merely because some unrelated rational run starts there: it must be
an actual successor of the supplied guarded policy.

The witnessing entry direction may contain an arbitrarily long finite past.
It occurs only in propositions and in the correctness proof.  The runtime
handoff key is the finite profiled child state.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-! ## Policy-level root readback -/

/-- Read a process-one profiled root from an arbitrary supplied guarded
policy.  This is the policy-parametric form of
`profiledGuardedRightEntryPolicy_root`. -/
theorem profiledGuardedRightPolicy_root
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hshape : target = .inr (.inl ((code, minimum), initialProfile))) :
    ∃ lambda : ProcOnePairedRightLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      overlap.Matches lambda ∧ PairedRightForeverAccepts A code lambda ∧
        rightInitialFirstProfile lambda = initialProfile ∧
        ∀ direction,
          policy.successor (true, target) direction =
            (false, match direction with
              | .fromOne row past move =>
                  pairedProfiledOneChild A code lambda row past move
              | .fromTwo _ _ _ => .inl PUnit.unit) := by
  have hlegal := policy.legal_at []
  rw [policy.accepts.1.1] at hlegal
  simp only [rightProfiledGuardedAutomaton,
    InputFreeRunParityTreeAutomaton.rootGuarded] at hlegal
  rcases hlegal with ⟨children, hguard, hchildren⟩
  rw [hshape] at hguard
  rcases hguard with
    ⟨lambda, hmatches, hforever, hprofile, hlambda⟩
  refine ⟨lambda, hmatches, hforever, hprofile, ?_⟩
  intro direction
  calc
    policy.successor (true, target) direction =
        (false, children direction) := by
      simpa [pairedProfiledEntryRunAutomaton] using congrFun hchildren direction
    _ = _ := by rw [hlambda direction]
                rfl

/-- Process-two mirror of `profiledGuardedRightPolicy_root`. -/
theorem profiledGuardedLeftPolicy_root
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hshape : target = .inr (.inr ((code, minimum), initialProfile))) :
    ∃ lambda : ProcTwoPairedLeftLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      overlap.Matches lambda ∧ PairedLeftForeverAccepts A code lambda ∧
        leftInitialFirstProfile lambda = initialProfile ∧
        ∀ direction,
          policy.successor (true, target) direction =
            (false, match direction with
              | .fromOne _ _ _ => .inl PUnit.unit
              | .fromTwo row past move =>
                  pairedProfiledTwoChild A code lambda row past move) := by
  have hlegal := policy.legal_at []
  rw [policy.accepts.1.1] at hlegal
  simp only [leftProfiledGuardedAutomaton,
    InputFreeRunParityTreeAutomaton.rootGuarded] at hlegal
  rcases hlegal with ⟨children, hguard, hchildren⟩
  rw [hshape] at hguard
  rcases hguard with
    ⟨lambda, hmatches, hforever, hprofile, hlambda⟩
  refine ⟨lambda, hmatches, hforever, hprofile, ?_⟩
  intro direction
  calc
    policy.successor (true, target) direction =
        (false, children direction) := by
      simpa [pairedProfiledEntryRunAutomaton] using congrFun hchildren direction
    _ = _ := by rw [hlambda direction]
                rfl

/-! ## Finite child keys with proof-only direction witnesses -/

/-- A process-one child is admitted exactly when it occurs in the supplied
guarded policy's root successor table. -/
def ProfiledGuardedRightPolicyAllows
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (child : PairedProfiledTreeState A) : Prop :=
  ∃ direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂),
    policy.successor (true, target) direction = (false, child)

/-- Process-two mirror. -/
def ProfiledGuardedLeftPolicyAllows
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (child : PairedProfiledTreeState A) : Prop :=
  ∃ direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂),
    policy.successor (true, target) direction = (false, child)

/-- Restrict the supplied process-one guarded policy below an allowed child.
The chosen direction is proof-side; the resulting policy state and successor
table are finite. -/
noncomputable def profiledGuardedRightPolicyBelowAllowedChild
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (child : PairedProfiledTreeState A)
    (hallowed : ProfiledGuardedRightPolicyAllows A target overlap policy child) :
    (pairedProfiledEntryRunAutomaton A child).RationalTransitionPolicy := by
  let direction := Classical.choose hallowed
  have hdirection := Classical.choose_spec hallowed
  have hstep := policy.successor_at [] direction
  rw [policy.accepts.1.1] at hstep
  have hstep' : policy.successor (true, target) direction =
      policy.run [direction] := by
    simpa [rightProfiledGuardedAutomaton, pairedProfiledEntryRunAutomaton,
      InputFreeRunParityTreeAutomaton.rootGuarded] using hstep
  rw [hdirection] at hstep'
  have hchild : (policy.run [direction]).2 = child := by
    simpa using congrArg Prod.snd hstep'.symm
  let childPolicy :=
    InputFreeRunParityTreeAutomaton.ordinaryPolicyBelowRootGuard
      (pairedProfiledEntryRunAutomaton A target)
      (pairedProfiledEntryRootGuard A target
        overlap.Matches (fun _ => True)) policy direction
  rw [← hchild]
  simpa [pairedProfiledEntryRunAutomaton,
    InputFreeRunParityTreeAutomaton.withInitial] using childPolicy

/-- Process-two mirror. -/
noncomputable def profiledGuardedLeftPolicyBelowAllowedChild
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (child : PairedProfiledTreeState A)
    (hallowed : ProfiledGuardedLeftPolicyAllows A target overlap policy child) :
    (pairedProfiledEntryRunAutomaton A child).RationalTransitionPolicy := by
  let direction := Classical.choose hallowed
  have hdirection := Classical.choose_spec hallowed
  have hstep := policy.successor_at [] direction
  rw [policy.accepts.1.1] at hstep
  have hstep' : policy.successor (true, target) direction =
      policy.run [direction] := by
    simpa [leftProfiledGuardedAutomaton, pairedProfiledEntryRunAutomaton,
      InputFreeRunParityTreeAutomaton.rootGuarded] using hstep
  rw [hdirection] at hstep'
  have hchild : (policy.run [direction]).2 = child := by
    simpa using congrArg Prod.snd hstep'.symm
  let childPolicy :=
    InputFreeRunParityTreeAutomaton.ordinaryPolicyBelowRootGuard
      (pairedProfiledEntryRunAutomaton A target)
      (pairedProfiledEntryRootGuard A target
        (fun _ => True) overlap.Matches) policy direction
  rw [← hchild]
  simpa [pairedProfiledEntryRunAutomaton,
    InputFreeRunParityTreeAutomaton.withInitial] using childPolicy

/-- The restricted policy starts at the exact finite child. -/
theorem profiledGuardedRightPolicyBelowAllowedChild_initial
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (child : PairedProfiledTreeState A)
    (hallowed : ProfiledGuardedRightPolicyAllows A target overlap policy child) :
    (profiledGuardedRightPolicyBelowAllowedChild A target overlap policy child
      hallowed).run [] = child :=
  (profiledGuardedRightPolicyBelowAllowedChild A target overlap policy child
    hallowed).accepts.1.1

theorem profiledGuardedLeftPolicyBelowAllowedChild_initial
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (child : PairedProfiledTreeState A)
    (hallowed : ProfiledGuardedLeftPolicyAllows A target overlap policy child) :
    (profiledGuardedLeftPolicyBelowAllowedChild A target overlap policy child
      hallowed).run [] = child :=
  (profiledGuardedLeftPolicyBelowAllowedChild A target overlap policy child
    hallowed).accepts.1.1

/-- Every allowed process-one child inherits a rational policy from the same
guarded policy. -/
theorem hasRationalRun_of_profiledGuardedRightPolicyAllows
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (child : PairedProfiledTreeState A)
    (hallowed : ProfiledGuardedRightPolicyAllows A target overlap policy child) :
    (pairedProfiledEntryRunAutomaton A child).HasRationalRun := by
  rcases hallowed with ⟨direction, hdirection⟩
  have hstep := policy.successor_at [] direction
  rw [policy.accepts.1.1] at hstep
  have hstep' : policy.successor (true, target) direction =
      policy.run [direction] := by
    simpa [rightProfiledGuardedAutomaton, pairedProfiledEntryRunAutomaton,
      InputFreeRunParityTreeAutomaton.rootGuarded] using hstep
  rw [hdirection] at hstep'
  have hchild : (policy.run [direction]).2 = child := by
    simpa using congrArg Prod.snd hstep'.symm
  let childPolicy :=
    InputFreeRunParityTreeAutomaton.ordinaryPolicyBelowRootGuard
      (pairedProfiledEntryRunAutomaton A target)
      (pairedProfiledEntryRootGuard A target
        overlap.Matches (fun _ => True)) policy direction
  have hrat := InputFreeRunParityTreeAutomaton.hasRationalRun_of_policy
    ((pairedProfiledEntryRunAutomaton A target).withInitial
      (policy.run [direction]).2) childPolicy
  rw [hchild] at hrat
  exact hrat

/-- Every allowed process-two child inherits a rational policy from the same
guarded policy. -/
theorem hasRationalRun_of_profiledGuardedLeftPolicyAllows
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (child : PairedProfiledTreeState A)
    (hallowed : ProfiledGuardedLeftPolicyAllows A target overlap policy child) :
    (pairedProfiledEntryRunAutomaton A child).HasRationalRun := by
  rcases hallowed with ⟨direction, hdirection⟩
  have hstep := policy.successor_at [] direction
  rw [policy.accepts.1.1] at hstep
  have hstep' : policy.successor (true, target) direction =
      policy.run [direction] := by
    simpa [leftProfiledGuardedAutomaton, pairedProfiledEntryRunAutomaton,
      InputFreeRunParityTreeAutomaton.rootGuarded] using hstep
  rw [hdirection] at hstep'
  have hchild : (policy.run [direction]).2 = child := by
    simpa using congrArg Prod.snd hstep'.symm
  let childPolicy :=
    InputFreeRunParityTreeAutomaton.ordinaryPolicyBelowRootGuard
      (pairedProfiledEntryRunAutomaton A target)
      (pairedProfiledEntryRootGuard A target
        (fun _ => True) overlap.Matches) policy direction
  have hrat := InputFreeRunParityTreeAutomaton.hasRationalRun_of_policy
    ((pairedProfiledEntryRunAutomaton A target).withInitial
      (policy.run [direction]).2) childPolicy
  rw [hchild] at hrat
  exact hrat

/-! ## Activations retaining the common-policy successor relation -/

/-- Semantic process-one activation read from one supplied guarded policy. -/
structure EndToEndGuardedRightActivation
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) where
  lambda : ProcOnePairedRightLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  overlap_matches : overlap.Matches lambda
  forever : PairedRightForeverAccepts A code lambda
  initial_profile : rightInitialFirstProfile lambda = initialProfile
  childAllowed : ∀ row past move,
    ProfiledGuardedRightPolicyAllows A target overlap policy
      (pairedProfiledOneChild A code lambda row past move)

/-- Select the process-one activation without choosing any new subtree
policy. -/
noncomputable def endToEndGuardedRightActivation
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hshape : target = .inr (.inl ((code, minimum), initialProfile))) :
    EndToEndGuardedRightActivation A target overlap policy code minimum
      initialProfile := by
  let hexists := profiledGuardedRightPolicy_root A target overlap policy code
    minimum initialProfile hshape
  let lambda := Classical.choose hexists
  have hspec := Classical.choose_spec hexists
  exact {
    lambda := lambda
    overlap_matches := hspec.1
    forever := hspec.2.1
    initial_profile := hspec.2.2.1
    childAllowed := fun row past move =>
      ⟨PairedEntryDirection.fromOne row past move, by
        simpa using hspec.2.2.2
          (PairedEntryDirection.fromOne row past move)⟩
  }

/-- Process-two mirror. -/
structure EndToEndGuardedLeftActivation
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)) where
  lambda : ProcTwoPairedLeftLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  overlap_matches : overlap.Matches lambda
  forever : PairedLeftForeverAccepts A code lambda
  initial_profile : leftInitialFirstProfile lambda = initialProfile
  childAllowed : ∀ row past move,
    ProfiledGuardedLeftPolicyAllows A target overlap policy
      (pairedProfiledTwoChild A code lambda row past move)

noncomputable def endToEndGuardedLeftActivation
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hshape : target = .inr (.inr ((code, minimum), initialProfile))) :
    EndToEndGuardedLeftActivation A target overlap policy code minimum
      initialProfile := by
  let hexists := profiledGuardedLeftPolicy_root A target overlap policy code
    minimum initialProfile hshape
  let lambda := Classical.choose hexists
  have hspec := Classical.choose_spec hexists
  exact {
    lambda := lambda
    overlap_matches := hspec.1
    forever := hspec.2.1
    initial_profile := hspec.2.2.1
    childAllowed := fun row past move =>
      ⟨PairedEntryDirection.fromTwo row past move, by
        simpa using hspec.2.2.2
          (PairedEntryDirection.fromTwo row past move)⟩
  }

end

end DetParityAutomaton

end DistributedSynthesis
