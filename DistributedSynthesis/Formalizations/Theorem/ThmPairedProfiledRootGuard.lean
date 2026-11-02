/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledFeasiblePolicyBank
import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryRootGuard

/-!
# One-shot root guards for the profiled paired automaton

The exceptional first recurrent block must satisfy the old initial-boundary
overlap guard while its descendants retain the new one-round recurrent
profiles.  Both requirements coexist in one finite root-guarded profiled
automaton.  This is the bridge from the guarded initial phase to the profiled
feasible-policy bank.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Root transition of the profiled automaton with an additional one-shot
orientation guard on the selected lambda. -/
def pairedProfiledEntryRootGuard
    (initialState : PairedProfiledTreeState A)
    (rightAllowed : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) → Prop)
    (leftAllowed : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) → Prop)
    (children : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
      PairedProfiledTreeState A) : Prop :=
  match initialState with
  | .inl _ => ∀ direction, children direction = .inl PUnit.unit
  | .inr (.inl live) =>
      ∃ lambda : ProcOnePairedRightLambda
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
        rightAllowed lambda ∧ PairedRightForeverAccepts A live.1.1 lambda ∧
          rightInitialFirstProfile lambda = live.2 ∧
          ∀ direction, children direction =
            match direction with
            | .fromOne row past move =>
                pairedProfiledOneChild A live.1.1 lambda row past move
            | .fromTwo _ _ _ => .inl PUnit.unit
  | .inr (.inr live) =>
      ∃ lambda : ProcTwoPairedLeftLambda
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
        leftAllowed lambda ∧ PairedLeftForeverAccepts A live.1.1 lambda ∧
          leftInitialFirstProfile lambda = live.2 ∧
          ∀ direction, children direction =
            match direction with
            | .fromOne _ _ _ => .inl PUnit.unit
            | .fromTwo row past move =>
                pairedProfiledTwoChild A live.1.1 lambda row past move

/-- Forgetting the extra root predicate leaves a legal profiled transition. -/
theorem pairedProfiledEntryRootGuard_implies_delta
    (initialState : PairedProfiledTreeState A)
    (rightAllowed : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) → Prop)
    (leftAllowed : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) → Prop)
    {children : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
      PairedProfiledTreeState A}
    (hguard : pairedProfiledEntryRootGuard A initialState
      rightAllowed leftAllowed children) :
    pairedProfiledEntryDelta A initialState PUnit.unit children := by
  rcases initialState with sink | live
  · exact hguard
  · rcases live with right | left
    · rcases hguard with ⟨lambda, _, hforever, hprofile, hchildren⟩
      exact ⟨lambda, hforever, hprofile, hchildren⟩
    · rcases hguard with ⟨lambda, _, hforever, hprofile, hchildren⟩
      exact ⟨lambda, hforever, hprofile, hchildren⟩

namespace PairedStrategyMemory

/-- The raw profiled run satisfies the guarded transition at its root. -/
theorem profiledRootGuard_at_run
    [Inhabited In₁] [Inhabited In₂]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (initial : PairedStrategyMemory A strategy)
    (rightAllowed : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) → Prop)
    (leftAllowed : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) → Prop)
    (hforever : ForeverAccepts (A := A) initial)
    (hallowed : RootLambdaAllowed (A := A) initial rightAllowed leftAllowed) :
    pairedProfiledEntryRootGuard A
      (toProfiledTreeState (A := A) initial) rightAllowed leftAllowed
      (fun direction => profiledRun (A := A) initial [direction]) := by
  cases initial with
  | sink =>
      intro direction
      rfl
  | processOne entry minimum =>
      refine ⟨entry.lambdaOfStrategy, hallowed, ?_, rfl, ?_⟩
      · simpa [ForeverAccepts] using hforever []
      · intro direction
        simpa [profiledRun, atNode] using
          (toProfiledTreeState_step (A := A)
            (PairedStrategyMemory.processOne entry minimum) direction)
  | processTwo entry minimum =>
      refine ⟨entry.lambdaOfStrategy, hallowed, ?_, rfl, ?_⟩
      · simpa [ForeverAccepts] using hforever []
      · intro direction
        simpa [profiledRun, atNode] using
          (toProfiledTreeState_step (A := A)
            (PairedStrategyMemory.processTwo entry minimum) direction)

/-- End-to-end one-shot guarded rationalization with recurrent profiles kept
below the guarded root. -/
theorem profiledRootGuarded_hasRationalRun
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (initial : PairedStrategyMemory A strategy)
    (rightAllowed : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) → Prop)
    (leftAllowed : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) → Prop)
    (hforever : ForeverAccepts (A := A) initial)
    (hswitching : SwitchingAccepts (A := A) initial)
    (hallowed : RootLambdaAllowed (A := A) initial rightAllowed leftAllowed)
    (basis :
      ((pairedProfiledEntryRunAutomaton A
        (toProfiledTreeState (A := A) initial)).rootGuarded
          (pairedProfiledEntryRootGuard A
            (toProfiledTreeState (A := A) initial)
            rightAllowed leftAllowed)).RationalRunBasis) :
    ((pairedProfiledEntryRunAutomaton A
      (toProfiledTreeState (A := A) initial)).rootGuarded
        (pairedProfiledEntryRootGuard A
          (toProfiledTreeState (A := A) initial)
          rightAllowed leftAllowed)).HasRationalRun := by
  apply InputFreeRunParityTreeAutomaton.rootGuarded_hasRationalRun
    (pairedProfiledEntryRunAutomaton A
      (toProfiledTreeState (A := A) initial))
    (pairedProfiledEntryRootGuard A
      (toProfiledTreeState (A := A) initial) rightAllowed leftAllowed)
    (profiledRun (A := A) initial)
    (profiledIsAcceptingRun (A := A) initial hforever hswitching)
  · exact profiledRootGuard_at_run A initial rightAllowed leftAllowed
      hforever hallowed
  · exact basis

end PairedStrategyMemory

end DetParityAutomaton

end DistributedSynthesis
