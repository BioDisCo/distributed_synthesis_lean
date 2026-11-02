/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRootGuard
import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedDelayedHandoff

/-!
# Concrete guarded handoff into profiled recurrent policies

At an initial left/right boundary, the generated paired memory supplies both
the old one-shot overlap profile and the new recurrent initial-action profile.
The profiled root-guard theorem rationalizes these together and therefore
produces a finite feasible profiled handoff source.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Profiled right-root automaton with the concrete old-boundary guard. -/
noncomputable def rightProfiledGuardedAutomaton
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)) :=
  (pairedProfiledEntryRunAutomaton A target).rootGuarded
    (pairedProfiledEntryRootGuard A target overlap.Matches (fun _ => True))

/-- Left mirror. -/
noncomputable def leftProfiledGuardedAutomaton
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) :=
  (pairedProfiledEntryRunAutomaton A target).rootGuarded
    (pairedProfiledEntryRootGuard A target (fun _ => True) overlap.Matches)

/-- The actual paired memory immediately after an initial-left boundary. -/
def initialLeftProfiledMemory
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    PairedStrategyMemory A strategy :=
  let base := extendPrefix strategy [] (past.map leftEnvironment)
  let entry := procOneFreshPair strategy base
    (strategyGenerated_extendPrefix_basic strategy
      StrategyGeneratedPrefix.empty _) move.1 move.2
  .processOne entry
    (blockMinState A A.initial
      (extendPrefix strategy [] (past.map leftEnvironment)))

/-- Its finite profiled paired target. -/
def initialLeftProfiledTarget
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    PairedProfiledTreeState A :=
  PairedStrategyMemory.toProfiledTreeState
    (A := A) (initialLeftProfiledMemory A strategy past move)

/-- Initial-right mirror memory. -/
def initialRightProfiledMemory
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    PairedStrategyMemory A strategy :=
  let base := extendPrefix strategy [] (past.map rightEnvironment)
  let entry := procTwoFreshPair strategy base
    (strategyGenerated_extendPrefix_basic strategy
      StrategyGeneratedPrefix.empty _) move.2 move.1
  .processTwo entry
    (blockMinState A A.initial
      (extendPrefix strategy [] (past.map rightEnvironment)))

def initialRightProfiledTarget
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    PairedProfiledTreeState A :=
  PairedStrategyMemory.toProfiledTreeState
    (A := A) (initialRightProfiledMemory A strategy past move)

section Generated

variable [Inhabited In₁] [Inhabited In₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-- A realizing strategy supplies the concrete guarded profiled rational run
at every initial-left boundary. -/
theorem initialLeft_profiledGuardedHasRationalRun
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (basis : (rightProfiledGuardedAutomaton A
      (initialLeftProfiledTarget A strategy past move)
      (initialLeftNextBothProfile strategy past move)).RationalRunBasis) :
    (rightProfiledGuardedAutomaton A
      (initialLeftProfiledTarget A strategy past move)
      (initialLeftNextBothProfile strategy past move)).HasRationalRun := by
  let memory := initialLeftProfiledMemory A strategy past move
  have hallowed : PairedStrategyMemory.RootLambdaAllowed
      (A := A) memory
      (initialLeftNextBothProfile strategy past move).Matches
      (fun _ => True) := by
    dsimp [memory, initialLeftProfiledMemory,
      PairedStrategyMemory.RootLambdaAllowed]
    simpa using
      (initialLeftNextBothProfile_matches_generated strategy past move)
  apply PairedStrategyMemory.profiledRootGuarded_hasRationalRun
    A memory
    (initialLeftNextBothProfile strategy past move).Matches
    (fun _ => True)
    (memory.foreverAccepts_of_winning (A := A) hwin)
    (PairedStrategyMemory.switchingAccepts_of_winning hwin memory)
    hallowed
  simpa [memory, initialLeftProfiledTarget,
    rightProfiledGuardedAutomaton] using basis

/-- Initial-right mirror. -/
theorem initialRight_profiledGuardedHasRationalRun
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (basis : (leftProfiledGuardedAutomaton A
      (initialRightProfiledTarget A strategy past move)
      (initialRightNextBothProfile strategy past move)).RationalRunBasis) :
    (leftProfiledGuardedAutomaton A
      (initialRightProfiledTarget A strategy past move)
      (initialRightNextBothProfile strategy past move)).HasRationalRun := by
  let memory := initialRightProfiledMemory A strategy past move
  have hallowed : PairedStrategyMemory.RootLambdaAllowed
      (A := A) memory (fun _ => True)
      (initialRightNextBothProfile strategy past move).Matches := by
    dsimp [memory, initialRightProfiledMemory,
      PairedStrategyMemory.RootLambdaAllowed]
    simpa using
      (initialRightNextBothProfile_matches_generated strategy past move)
  apply PairedStrategyMemory.profiledRootGuarded_hasRationalRun
    A memory (fun _ => True)
    (initialRightNextBothProfile strategy past move).Matches
    (memory.foreverAccepts_of_winning (A := A) hwin)
    (PairedStrategyMemory.switchingAccepts_of_winning hwin memory)
    hallowed
  simpa [memory, initialRightProfiledTarget,
    leftProfiledGuardedAutomaton] using basis

end Generated

/-! ## Reading the first guarded profiled policy transition -/

/-- Finite profiled source staged after an initial-left boundary. -/
abbrev ProfiledGuardedRightEntrySource
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] :=
  {data : PairedProfiledTreeState A ×
      ProcOneEntryOverlapProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) //
    (rightProfiledGuardedAutomaton A data.1 data.2).HasRationalRun}

/-- Initial-right mirror. -/
abbrev ProfiledGuardedLeftEntrySource
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] :=
  {data : PairedProfiledTreeState A ×
      ProcTwoEntryOverlapProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂) //
    (leftProfiledGuardedAutomaton A data.1 data.2).HasRationalRun}

noncomputable instance [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] :
    Fintype (ProfiledGuardedRightEntrySource A) := by
  classical
  infer_instance

noncomputable instance [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] :
    Fintype (ProfiledGuardedLeftEntrySource A) := by
  classical
  infer_instance

section PolicyReadback

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-- Rational policy of the guarded profiled first-right block. -/
noncomputable def profiledGuardedRightEntryPolicy
    (source : ProfiledGuardedRightEntrySource A) :
    (rightProfiledGuardedAutomaton A source.1.1 source.1.2).RationalTransitionPolicy :=
  Classical.choice
    (InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
      (rightProfiledGuardedAutomaton A source.1.1 source.1.2) source.2)

/-- Its root exposes one overlap-matching lambda and all profiled children. -/
theorem profiledGuardedRightEntryPolicy_root
    (source : ProfiledGuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hshape : source.1.1 = .inr (.inl ((code, minimum), initialProfile))) :
    ∃ lambda : ProcOnePairedRightLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      source.1.2.Matches lambda ∧ PairedRightForeverAccepts A code lambda ∧
        rightInitialFirstProfile lambda = initialProfile ∧
        ∀ direction,
          (profiledGuardedRightEntryPolicy A source).successor
              (true, source.1.1) direction =
            (false, match direction with
              | .fromOne row past move =>
                  pairedProfiledOneChild A code lambda row past move
              | .fromTwo _ _ _ => .inl PUnit.unit) := by
  let policy := profiledGuardedRightEntryPolicy A source
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
  change policy.successor (true, source.1.1) direction = _
  calc
    policy.successor (true, source.1.1) direction =
        (false, children direction) := by
      simpa [pairedProfiledEntryRunAutomaton] using congrFun hchildren direction
    _ = _ := by rw [hlambda direction]
                rfl

/-- Every concrete first-right close is a feasible profiled bank target. -/
theorem profiledGuardedRightEntry_child_hasRationalRun
    (source : ProfiledGuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hlambda : ∀ direction,
      (profiledGuardedRightEntryPolicy A source).successor
          (true, source.1.1) direction =
        (false, match direction with
          | .fromOne row past move =>
              pairedProfiledOneChild A code lambda row past move
          | .fromTwo _ _ _ => .inl PUnit.unit))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    (pairedProfiledEntryRunAutomaton A
      (pairedProfiledOneChild A code lambda row past move)).HasRationalRun := by
  let policy := profiledGuardedRightEntryPolicy A source
  let direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
    .fromOne row past move
  have hroot : policy.run [] = (true, source.1.1) := policy.accepts.1.1
  have hchildStep := policy.successor_at [] direction
  rw [hroot] at hchildStep
  have hlambda' : policy.successor (true, source.1.1) direction =
      (false, pairedProfiledOneChild A code lambda row past move) := by
    simpa [policy, direction] using hlambda direction
  have hchildStep' :
      (false, pairedProfiledOneChild A code lambda row past move) =
        policy.run [direction] := by
    calc
      _ = policy.successor (true, source.1.1) direction := hlambda'.symm
      _ = policy.run [direction] := by simpa using hchildStep
  have hchild : (policy.run [direction]).2 =
      pairedProfiledOneChild A code lambda row past move := by
    simpa using congrArg Prod.snd hchildStep'.symm
  let childPolicy :=
    InputFreeRunParityTreeAutomaton.ordinaryPolicyBelowRootGuard
      (pairedProfiledEntryRunAutomaton A source.1.1)
      (pairedProfiledEntryRootGuard A source.1.1
        source.1.2.Matches (fun _ => True)) policy direction
  have hrat := InputFreeRunParityTreeAutomaton.hasRationalRun_of_policy
    ((pairedProfiledEntryRunAutomaton A source.1.1).withInitial
      (policy.run [direction]).2) childPolicy
  rw [hchild] at hrat
  exact hrat

/-- Package the concrete child directly as a feasible profiled bank state. -/
noncomputable def profiledGuardedRightEntry_childFeasibleState
    (source : ProfiledGuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hlambda : ∀ direction,
      (profiledGuardedRightEntryPolicy A source).successor
          (true, source.1.1) direction =
        (false, match direction with
          | .fromOne row past move =>
              pairedProfiledOneChild A code lambda row past move
          | .fromTwo _ _ _ => .inl PUnit.unit))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) : FeasibleProfiledPairedState A :=
  ⟨pairedProfiledOneChild A code lambda row past move,
    profiledGuardedRightEntry_child_hasRationalRun A source code minimum
      initialProfile lambda hlambda row past move⟩

/-! ### Left mirror -/

noncomputable def profiledGuardedLeftEntryPolicy
    (source : ProfiledGuardedLeftEntrySource A) :
    (leftProfiledGuardedAutomaton A source.1.1 source.1.2).RationalTransitionPolicy :=
  Classical.choice
    (InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
      (leftProfiledGuardedAutomaton A source.1.1 source.1.2) source.2)

theorem profiledGuardedLeftEntryPolicy_root
    (source : ProfiledGuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hshape : source.1.1 = .inr (.inr ((code, minimum), initialProfile))) :
    ∃ lambda : ProcTwoPairedLeftLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      source.1.2.Matches lambda ∧ PairedLeftForeverAccepts A code lambda ∧
        leftInitialFirstProfile lambda = initialProfile ∧
        ∀ direction,
          (profiledGuardedLeftEntryPolicy A source).successor
              (true, source.1.1) direction =
            (false, match direction with
              | .fromOne _ _ _ => .inl PUnit.unit
              | .fromTwo row past move =>
                  pairedProfiledTwoChild A code lambda row past move) := by
  let policy := profiledGuardedLeftEntryPolicy A source
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
  change policy.successor (true, source.1.1) direction = _
  calc
    policy.successor (true, source.1.1) direction =
        (false, children direction) := by
      simpa [pairedProfiledEntryRunAutomaton] using congrFun hchildren direction
    _ = _ := by rw [hlambda direction]
                rfl

theorem profiledGuardedLeftEntry_child_hasRationalRun
    (source : ProfiledGuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hlambda : ∀ direction,
      (profiledGuardedLeftEntryPolicy A source).successor
          (true, source.1.1) direction =
        (false, match direction with
          | .fromOne _ _ _ => .inl PUnit.unit
          | .fromTwo row past move =>
              pairedProfiledTwoChild A code lambda row past move))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    (pairedProfiledEntryRunAutomaton A
      (pairedProfiledTwoChild A code lambda row past move)).HasRationalRun := by
  let policy := profiledGuardedLeftEntryPolicy A source
  let direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
    .fromTwo row past move
  have hroot : policy.run [] = (true, source.1.1) := policy.accepts.1.1
  have hchildStep := policy.successor_at [] direction
  rw [hroot] at hchildStep
  have hlambda' : policy.successor (true, source.1.1) direction =
      (false, pairedProfiledTwoChild A code lambda row past move) := by
    simpa [policy, direction] using hlambda direction
  have hchildStep' :
      (false, pairedProfiledTwoChild A code lambda row past move) =
        policy.run [direction] := by
    calc
      _ = policy.successor (true, source.1.1) direction := hlambda'.symm
      _ = policy.run [direction] := by simpa using hchildStep
  have hchild : (policy.run [direction]).2 =
      pairedProfiledTwoChild A code lambda row past move := by
    simpa using congrArg Prod.snd hchildStep'.symm
  let childPolicy :=
    InputFreeRunParityTreeAutomaton.ordinaryPolicyBelowRootGuard
      (pairedProfiledEntryRunAutomaton A source.1.1)
      (pairedProfiledEntryRootGuard A source.1.1
        (fun _ => True) source.1.2.Matches) policy direction
  have hrat := InputFreeRunParityTreeAutomaton.hasRationalRun_of_policy
    ((pairedProfiledEntryRunAutomaton A source.1.1).withInitial
      (policy.run [direction]).2) childPolicy
  rw [hchild] at hrat
  exact hrat

noncomputable def profiledGuardedLeftEntry_childFeasibleState
    (source : ProfiledGuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hlambda : ∀ direction,
      (profiledGuardedLeftEntryPolicy A source).successor
          (true, source.1.1) direction =
        (false, match direction with
          | .fromOne _ _ _ => .inl PUnit.unit
          | .fromTwo row past move =>
              pairedProfiledTwoChild A code lambda row past move))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) : FeasibleProfiledPairedState A :=
  ⟨pairedProfiledTwoChild A code lambda row past move,
    profiledGuardedLeftEntry_child_hasRationalRun A source code minimum
      initialProfile lambda hlambda row past move⟩

end PolicyReadback

end DetParityAutomaton

end DistributedSynthesis
