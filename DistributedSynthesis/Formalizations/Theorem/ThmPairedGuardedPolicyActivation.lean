/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedInitialInversion
import DistributedSynthesis.Formalizations.Theorem.ThmRootGuardedPolicyActivation
import DistributedSynthesis.Formalizations.Theorem.ThmPairedFeasiblePolicyBank

/-!
# First-block activation from guarded entry sources

The guarded rational policy is used only at the fresh recurrent root.  Its
first lambda preserves the overlap profile.  Every concrete close lands below
that root, where `ordinaryPolicyBelowRootGuard` supplies an ordinary rational
policy for the subsequent feasible-policy bank.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section Right

variable (source : GuardedRightEntrySource A)

/-- Complete semantic payload of the guarded first right block.  Every close
already carries the ordinary-bank nonemptiness needed after activation. -/
structure GuardedRightActivation
    (code : A.State × A.State) (minimum : A.State) where
  lambda : ProcOnePairedRightLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  profile_matches : source.1.2.Matches lambda
  forever : PairedRightForeverAccepts A code lambda
  childFeasible : ∀ row past move,
    (pairedEntryRunAutomaton A
      (pairedOneChild A code lambda row past move)).HasRationalRun

/-- A rational policy selected for the one-shot guarded right entry. -/
noncomputable def guardedRightEntryPolicy :
    (rightProfileGuardedAutomaton A source.1.1 source.1.2).RationalTransitionPolicy :=
  Classical.choice
    (InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
      (rightProfileGuardedAutomaton A source.1.1 source.1.2) source.2)

/-- At a live process-one source, the selected fresh transition contains a
right-block lambda matching the promised overlap profile. -/
theorem guardedRightEntryPolicy_root
    (code : A.State × A.State) (minimum : A.State)
    (hshape : source.1.1 = Sum.inr (Sum.inl (code, minimum))) :
    ∃ lambda : ProcOnePairedRightLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      source.1.2.Matches lambda ∧ PairedRightForeverAccepts A code lambda ∧
        ∀ direction,
          (guardedRightEntryPolicy A source).successor
              (true, source.1.1) direction =
            (false, match direction with
              | .fromOne row past move => pairedOneChild A code lambda row past move
              | .fromTwo _ _ _ => Sum.inl PUnit.unit) := by
  let policy := guardedRightEntryPolicy A source
  have hlegal := policy.legal_at []
  rw [policy.accepts.1.1] at hlegal
  simp only [rightProfileGuardedAutomaton,
    InputFreeRunParityTreeAutomaton.rootGuarded] at hlegal
  rcases hlegal with ⟨children, hguard, hchildren⟩
  rw [hshape] at hguard
  rcases hguard with ⟨lambda, hmatches, hforever, hlambda⟩
  refine ⟨lambda, hmatches, hforever, ?_⟩
  intro direction
  change policy.successor (true, source.1.1) direction = _
  calc
    policy.successor (true, source.1.1) direction =
        (false, children direction) := by
      simpa [pairedEntryRunAutomaton] using congrFun hchildren direction
    _ = _ := by rw [hlambda direction]
                rfl

/-- Every concrete close of the guarded first right block has an ordinary
rational run available at its child target. -/
theorem guardedRightEntry_child_hasRationalRun
    (code : A.State × A.State) (minimum : A.State)
    (hshape : source.1.1 = Sum.inr (Sum.inl (code, minimum)))
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hlambda : ∀ direction,
      (guardedRightEntryPolicy A source).successor
          (true, source.1.1) direction =
        (false, match direction with
          | .fromOne row past move => pairedOneChild A code lambda row past move
          | .fromTwo _ _ _ => Sum.inl PUnit.unit))
    (row : PairedEntryRow) (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    (pairedEntryRunAutomaton A
      (pairedOneChild A code lambda row past move)).HasRationalRun := by
  let policy := guardedRightEntryPolicy A source
  let direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
    .fromOne row past move
  have hroot : policy.run [] = (true, source.1.1) := by
    exact policy.accepts.1.1
  have hchildStep := policy.successor_at [] direction
  rw [hroot] at hchildStep
  have hlambda' : policy.successor (true, source.1.1) direction =
      (false, pairedOneChild A code lambda row past move) := by
    simpa [policy, direction] using hlambda direction
  have hchildStep' :
      (false, pairedOneChild A code lambda row past move) =
        policy.run [direction] := by
    calc
      (false, pairedOneChild A code lambda row past move) =
          policy.successor (true, source.1.1) direction := hlambda'.symm
      _ = policy.run [direction] := by simpa using hchildStep
  have hchild : (policy.run [direction]).2 =
      pairedOneChild A code lambda row past move := by
    simpa using congrArg Prod.snd hchildStep'.symm
  let childPolicy :=
    InputFreeRunParityTreeAutomaton.ordinaryPolicyBelowRootGuard
      (pairedEntryRunAutomaton A source.1.1)
      (pairedEntryRootGuard A source.1.1 source.1.2.Matches (fun _ => True))
      policy direction
  have hrat := InputFreeRunParityTreeAutomaton.hasRationalRun_of_policy
    ((pairedEntryRunAutomaton A source.1.1).withInitial
      (policy.run [direction]).2) childPolicy
  rw [hchild] at hrat
  exact hrat

/-- The concrete first close is therefore a key of the ordinary finite policy
bank. -/
noncomputable def guardedRightEntry_childFeasibleState
    (code : A.State × A.State) (minimum : A.State)
    (hshape : source.1.1 = Sum.inr (Sum.inl (code, minimum)))
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hlambda : ∀ direction,
      (guardedRightEntryPolicy A source).successor
          (true, source.1.1) direction =
        (false, match direction with
          | .fromOne row past move => pairedOneChild A code lambda row past move
          | .fromTwo _ _ _ => Sum.inl PUnit.unit))
    (row : PairedEntryRow) (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    FeasiblePairedState A :=
  ⟨pairedOneChild A code lambda row past move,
    guardedRightEntry_child_hasRationalRun A source code minimum hshape
      lambda hlambda row past move⟩

/-- Select the guarded root lambda together with all its ordinary child-bank
certificates. -/
noncomputable def guardedRightActivation
    (code : A.State × A.State) (minimum : A.State)
    (hshape : source.1.1 = Sum.inr (Sum.inl (code, minimum))) :
    GuardedRightActivation A source code minimum := by
  classical
  let hexists := guardedRightEntryPolicy_root A source code minimum hshape
  let lambda := Exists.choose hexists
  have hspec := Exists.choose_spec hexists
  exact {
    lambda := lambda
    profile_matches := hspec.1
    forever := hspec.2.1
    childFeasible := fun row past move =>
      guardedRightEntry_child_hasRationalRun A source code minimum hshape
        lambda hspec.2.2 row past move
  }

end Right

section Left

variable (source : GuardedLeftEntrySource A)

structure GuardedLeftActivation
    (code : A.State × A.State) (minimum : A.State) where
  lambda : ProcTwoPairedLeftLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  profile_matches : source.1.2.Matches lambda
  forever : PairedLeftForeverAccepts A code lambda
  childFeasible : ∀ row past move,
    (pairedEntryRunAutomaton A
      (pairedTwoChild A code lambda row past move)).HasRationalRun

/-- Process-two mirror of the selected one-shot guarded policy. -/
noncomputable def guardedLeftEntryPolicy :
    (leftProfileGuardedAutomaton A source.1.1 source.1.2).RationalTransitionPolicy :=
  Classical.choice
    (InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
      (leftProfileGuardedAutomaton A source.1.1 source.1.2) source.2)

theorem guardedLeftEntryPolicy_root
    (code : A.State × A.State) (minimum : A.State)
    (hshape : source.1.1 = Sum.inr (Sum.inr (code, minimum))) :
    ∃ lambda : ProcTwoPairedLeftLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      source.1.2.Matches lambda ∧ PairedLeftForeverAccepts A code lambda ∧
        ∀ direction,
          (guardedLeftEntryPolicy A source).successor
              (true, source.1.1) direction =
            (false, match direction with
              | .fromOne _ _ _ => Sum.inl PUnit.unit
              | .fromTwo row past move => pairedTwoChild A code lambda row past move) := by
  let policy := guardedLeftEntryPolicy A source
  have hlegal := policy.legal_at []
  rw [policy.accepts.1.1] at hlegal
  simp only [leftProfileGuardedAutomaton,
    InputFreeRunParityTreeAutomaton.rootGuarded] at hlegal
  rcases hlegal with ⟨children, hguard, hchildren⟩
  rw [hshape] at hguard
  rcases hguard with ⟨lambda, hmatches, hforever, hlambda⟩
  refine ⟨lambda, hmatches, hforever, ?_⟩
  intro direction
  change policy.successor (true, source.1.1) direction = _
  calc
    policy.successor (true, source.1.1) direction =
        (false, children direction) := by
      simpa [pairedEntryRunAutomaton] using congrFun hchildren direction
    _ = _ := by rw [hlambda direction]
                rfl

theorem guardedLeftEntry_child_hasRationalRun
    (code : A.State × A.State) (minimum : A.State)
    (hshape : source.1.1 = Sum.inr (Sum.inr (code, minimum)))
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hlambda : ∀ direction,
      (guardedLeftEntryPolicy A source).successor
          (true, source.1.1) direction =
        (false, match direction with
          | .fromOne _ _ _ => Sum.inl PUnit.unit
          | .fromTwo row past move => pairedTwoChild A code lambda row past move))
    (row : PairedEntryRow) (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    (pairedEntryRunAutomaton A
      (pairedTwoChild A code lambda row past move)).HasRationalRun := by
  let policy := guardedLeftEntryPolicy A source
  let direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
    .fromTwo row past move
  have hroot : policy.run [] = (true, source.1.1) := by
    exact policy.accepts.1.1
  have hchildStep := policy.successor_at [] direction
  rw [hroot] at hchildStep
  have hlambda' : policy.successor (true, source.1.1) direction =
      (false, pairedTwoChild A code lambda row past move) := by
    simpa [policy, direction] using hlambda direction
  have hchildStep' :
      (false, pairedTwoChild A code lambda row past move) =
        policy.run [direction] := by
    calc
      (false, pairedTwoChild A code lambda row past move) =
          policy.successor (true, source.1.1) direction := hlambda'.symm
      _ = policy.run [direction] := by simpa using hchildStep
  have hchild : (policy.run [direction]).2 =
      pairedTwoChild A code lambda row past move := by
    simpa using congrArg Prod.snd hchildStep'.symm
  let childPolicy :=
    InputFreeRunParityTreeAutomaton.ordinaryPolicyBelowRootGuard
      (pairedEntryRunAutomaton A source.1.1)
      (pairedEntryRootGuard A source.1.1 (fun _ => True) source.1.2.Matches)
      policy direction
  have hrat := InputFreeRunParityTreeAutomaton.hasRationalRun_of_policy
    ((pairedEntryRunAutomaton A source.1.1).withInitial
      (policy.run [direction]).2) childPolicy
  rw [hchild] at hrat
  exact hrat

noncomputable def guardedLeftEntry_childFeasibleState
    (code : A.State × A.State) (minimum : A.State)
    (hshape : source.1.1 = Sum.inr (Sum.inr (code, minimum)))
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hlambda : ∀ direction,
      (guardedLeftEntryPolicy A source).successor
          (true, source.1.1) direction =
        (false, match direction with
          | .fromOne _ _ _ => Sum.inl PUnit.unit
          | .fromTwo row past move => pairedTwoChild A code lambda row past move))
    (row : PairedEntryRow) (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    FeasiblePairedState A :=
  ⟨pairedTwoChild A code lambda row past move,
    guardedLeftEntry_child_hasRationalRun A source code minimum hshape
      lambda hlambda row past move⟩

noncomputable def guardedLeftActivation
    (code : A.State × A.State) (minimum : A.State)
    (hshape : source.1.1 = Sum.inr (Sum.inr (code, minimum))) :
    GuardedLeftActivation A source code minimum := by
  classical
  let hexists := guardedLeftEntryPolicy_root A source code minimum hshape
  let lambda := Exists.choose hexists
  have hspec := Exists.choose_spec hexists
  exact {
    lambda := lambda
    profile_matches := hspec.1
    forever := hspec.2.1
    childFeasible := fun row past move =>
      guardedLeftEntry_child_hasRationalRun A source code minimum hshape
        lambda hspec.2.2 row past move
  }

end Left

end DetParityAutomaton

end DistributedSynthesis
